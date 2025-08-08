"""Test pattern extraction utilities for model iteration.

Tests for extracting and comparing structural patterns from Z3 models
without referencing model objects directly.
"""

import unittest
import z3
from model_checker.syntactic import Syntax
from model_checker.settings import SettingsManager
from model_checker.models.constraints import ModelConstraints
from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition
from model_checker.theory_lib.logos import get_theory
from model_checker.iterate.patterns import StructuralPattern, create_structural_difference_constraint


class TestPatternExtraction(unittest.TestCase):
    """Test extraction of structural patterns from Z3 models."""
    
    def setUp(self):
        """Set up test environment with logos theory."""
        # Get logos theory
        self.theory = get_theory(['extensional'])  # Just extensional for simple test
        theory_operators = self.theory['operators']
        
        # Create settings manager with semantic theory
        self.settings_manager = SettingsManager(self.theory)
        
        # Get complete settings
        example_settings = {
            'N': 3,  # Small for testing
            'contingent': True,
            'disjoint': True,
            'non_null': True,
            'non_empty': True,
        }
        general_settings = {
            'max_time': 5000,
        }
        # Get the complete settings
        self.settings = self.settings_manager.get_complete_settings(
            example_settings, 
            general_settings, 
            None
        )
        
        # Create simple syntax for testing
        infix_premises = ['A', 'B']
        infix_conclusions = ['(A \\wedge B)']
        self.syntax = Syntax(infix_premises, infix_conclusions, theory_operators)
        
        # Create semantics and model constraints
        self.semantics = LogosSemantics(self.settings, self.syntax)
        self.model_constraints = ModelConstraints(
            self.settings,
            self.syntax,
            self.semantics,
            LogosProposition
        )
        
    def test_extract_pattern_from_model(self):
        """Pattern extraction must capture structural information."""
        # Create a solver and find a model
        solver = z3.Solver()
        solver.set("timeout", self.settings.global_settings['max_time'])
        solver.add(self.model_constraints.all_constraints)
        
        self.assertEqual(solver.check(), z3.sat, "Should find a satisfying model")
        z3_model = solver.model()
        
        # Extract pattern
        pattern = StructuralPattern(self.model_constraints, z3_model)
        
        # Verify pattern contains expected information
        self.assertIn('num_worlds', pattern.pattern)
        self.assertIn('num_possible', pattern.pattern)
        self.assertIn('world_states', pattern.pattern)
        self.assertIn('verify', pattern.pattern)
        self.assertIn('falsify', pattern.pattern)
        
        # Check that counts are valid
        self.assertIsInstance(pattern.pattern['num_worlds'], int)
        self.assertIsInstance(pattern.pattern['num_possible'], int)
        self.assertGreater(pattern.pattern['num_worlds'], 0, "Should have at least one world")
        self.assertGreaterEqual(pattern.pattern['num_possible'], pattern.pattern['num_worlds'],
                               "Possible states should include all worlds")
        
        # Check world states list
        self.assertIsInstance(pattern.pattern['world_states'], list)
        self.assertEqual(len(pattern.pattern['world_states']), pattern.pattern['num_worlds'])
        
        # Check verify/falsify patterns for each letter
        for letter in ['A', 'B']:
            self.assertIn(letter, pattern.pattern['verify'])
            self.assertIn(letter, pattern.pattern['falsify'])
            self.assertIsInstance(pattern.pattern['verify'][letter], list)
            self.assertIsInstance(pattern.pattern['falsify'][letter], list)
    
    def test_pattern_to_difference_constraint(self):
        """Pattern must generate constraint that excludes it."""
        # Create a solver and find a model
        solver = z3.Solver()
        solver.set("timeout", self.settings.global_settings['max_time'])
        solver.add(self.model_constraints.all_constraints)
        
        self.assertEqual(solver.check(), z3.sat)
        z3_model = solver.model()
        
        # Extract pattern and create difference constraint
        pattern = StructuralPattern(self.model_constraints, z3_model)
        diff_constraint = pattern.to_difference_constraint(
            self.model_constraints.semantics,
            self.model_constraints.sentence_letters
        )
        
        # The difference constraint should be a Z3 expression
        self.assertIsInstance(diff_constraint, z3.ExprRef)
        
        # Create new solver with original constraints plus difference
        new_solver = z3.Solver()
        new_solver.set("timeout", self.settings.global_settings['max_time'])
        new_solver.add(self.model_constraints.all_constraints)
        new_solver.add(diff_constraint)
        
        # Should still be satisfiable (there should be other models)
        if new_solver.check() == z3.sat:
            new_model = new_solver.model()
            
            # Extract pattern from new model
            new_pattern = StructuralPattern(self.model_constraints, new_model)
            
            # Patterns should be different
            self.assertNotEqual(pattern.pattern['world_states'], 
                              new_pattern.pattern['world_states'],
                              "Should find structurally different model")
    
    def test_multiple_pattern_exclusion(self):
        """Multiple patterns must all be excluded."""
        patterns = []
        solver = z3.Solver()
        solver.set("timeout", self.settings.global_settings['max_time'])
        solver.add(self.model_constraints.all_constraints)
        
        # Find first model
        self.assertEqual(solver.check(), z3.sat)
        model1 = solver.model()
        pattern1 = StructuralPattern(self.model_constraints, model1)
        patterns.append(pattern1)
        
        # Add exclusion for first pattern
        solver.add(pattern1.to_difference_constraint(
            self.model_constraints.semantics,
            self.model_constraints.sentence_letters
        ))
        
        # Find second model if possible
        if solver.check() == z3.sat:
            model2 = solver.model()
            pattern2 = StructuralPattern(self.model_constraints, model2)
            patterns.append(pattern2)
            
            # Create combined constraint
            combined_constraint = create_structural_difference_constraint(
                self.model_constraints,
                patterns
            )
            
            # New solver with combined constraint
            new_solver = z3.Solver()
            new_solver.set("timeout", self.settings.global_settings['max_time'])
            new_solver.add(self.model_constraints.all_constraints)
            new_solver.add(combined_constraint)
            
            # If we find another model, it should be different from both
            if new_solver.check() == z3.sat:
                model3 = new_solver.model()
                pattern3 = StructuralPattern(self.model_constraints, model3)
                
                self.assertNotEqual(pattern3.pattern['world_states'], 
                                  pattern1.pattern['world_states'])
                self.assertNotEqual(pattern3.pattern['world_states'], 
                                  pattern2.pattern['world_states'])
    
    def test_empty_pattern_list(self):
        """Empty pattern list should return trivial constraint."""
        constraint = create_structural_difference_constraint(
            self.model_constraints,
            []
        )
        
        # Should be True (no exclusions)
        self.assertEqual(constraint, z3.BoolVal(True))


if __name__ == '__main__':
    unittest.main()