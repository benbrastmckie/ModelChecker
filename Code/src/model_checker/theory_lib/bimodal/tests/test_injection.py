"""Test Z3 injection for Bimodal theory.

Following TDD approach - written BEFORE implementing inject_z3_model_values.
Tests verify Bimodal-specific injection including temporal relations.
"""

import unittest
from unittest.mock import Mock
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker import syntactic


class TestBimodalInjection(unittest.TestCase):
    """Test Bimodal theory Z3 injection functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {'N': 2, 'M': 3, 'contingent': False}
        self.semantics = BimodalSemantics(self.settings)
        
        # Create mock model constraints
        self.mock_constraints = Mock()
        self.mock_constraints.all_constraints = []
        self.mock_constraints.syntax = Mock()
        self.mock_constraints.syntax.sentence_letters = []
        self.mock_constraints.settings = {'N': 2}
    
    def test_inject_z3_model_values_exists(self):
        """Test that inject_z3_model_values method exists."""
        self.assertTrue(hasattr(self.semantics, 'inject_z3_model_values'))
        
    def test_inject_basic_constraints(self):
        """Test injection of basic constraints."""
        # Create a Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        
        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have at least world and possible constraints
        self.assertGreater(len(constraints), 0)
    
    def test_inject_truth_condition_constraints(self):
        """Test injection of truth_condition constraints."""
        # Create mock sentence letters
        letter_a = Mock()
        letter_a.sentence_letter = z3.Const('A', syntactic.AtomSort)
        self.mock_constraints.syntax.sentence_letters = [letter_a]
        
        # Create a Z3 model with truth_condition values
        solver = z3.Solver()
        atom_a = letter_a.sentence_letter
        
        # Set some truth condition values
        solver.add(self.semantics.truth_condition(0, atom_a))
        solver.add(z3.Not(self.semantics.truth_condition(1, atom_a)))
        solver.add(self.semantics.truth_condition(2, atom_a))
        solver.add(z3.Not(self.semantics.truth_condition(3, atom_a)))
        
        # Add world constraint
        solver.add(self.semantics.is_world(0))
        
        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have truth_condition constraints
        truth_constraints = [c for c in constraints if 'truth_condition' in str(c)]
        
        # 4 states * 1 letter = 4 truth_condition constraints
        self.assertEqual(len(truth_constraints), 4)
    
    def test_inject_task_constraints(self):
        """Test injection handles task relations."""
        # Bimodal has task relation between states
        self.assertTrue(hasattr(self.semantics, 'task'))
        
        # Create a Z3 model with task constraints
        solver = z3.Solver()
        
        # Set some task values
        solver.add(self.semantics.task(0, 1))
        solver.add(z3.Not(self.semantics.task(0, 2)))
        solver.add(self.semantics.task(1, 2))
        
        # Add world constraint
        solver.add(self.semantics.is_world(0))
        
        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        constraints = self.mock_constraints.all_constraints
        
        # Should have task constraints
        task_constraints = [c for c in constraints if 'Task(' in str(c)]
        
        # We inject task for all state pairs: 4*4 = 16
        self.assertEqual(len(task_constraints), 16)
    
    def test_uses_model_validator(self):
        """Test that inject_z3_model_values works correctly."""
        # Create minimal Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        solver.check()
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that injection worked
        constraints = self.mock_constraints.all_constraints
        self.assertGreater(len(constraints), 0)


if __name__ == '__main__':
