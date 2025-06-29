"""Test to ensure correct truth evaluation for empty verifiers.

This test directly checks the truth_value_at method to ensure
propositions with empty verifiers evaluate to false.
"""

import unittest
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
    exclusion_operators
)
from model_checker import model, syntactic
import z3


class TestTruthEvaluation(unittest.TestCase):
    """Test truth evaluation for propositions."""
    
    def test_empty_verifiers_are_false(self):
        """Test that propositions with empty verifiers evaluate to false."""
        # Create a minimal test case
        settings = {
            'N': 2,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
            'expectation': False,
            'print_impossible': False,
            'print_constraints': False,
            'print_z3': False,
            'save_output': False,
            'maximize': False,
        }
        
        # Create semantics
        semantics = ExclusionSemantics(settings)
        
        # Create a simple example where we know the verifiers will be empty
        # Use "\\exclude A" where A has no verifiers
        premise_str = '\\exclude A'
        conclusion_str = 'A'  # dummy conclusion
        
        # Create syntax parser
        syntax = syntactic.Syntax([premise_str], [conclusion_str], exclusion_operators)
        
        # Create model constraints
        constraints = model.ModelConstraints(
            settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        # Create model structure
        structure = ExclusionStructure(constraints, settings)
        
        if structure.z3_model:
            # Interpret sentences to create propositions
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            
            # Get the premise sentence and its proposition
            premise_sent = syntax.premises[0]
            
            # The proposition should now exist after interpretation
            self.assertIsNotNone(premise_sent.proposition, "Proposition should be created after interpretation")
            
            premise_prop = premise_sent.proposition
            main_point = structure.main_point
            
            # Check the verifiers
            print(f"\nPremise: {premise_str}")
            print(f"Verifiers: {premise_prop.verifiers}")
            print(f"Number of verifiers: {len(premise_prop.verifiers)}")
            
            # If verifiers are empty, truth value MUST be false
            if len(premise_prop.verifiers) == 0:
                truth_value = premise_prop.truth_value_at(main_point)
                self.assertFalse(truth_value, 
                               "Proposition with empty verifiers must evaluate to false")
                print(f"✓ Empty verifiers correctly evaluate to false")
            else:
                print(f"Note: Verifiers are not empty in this model")
                
    def test_disjunctive_demorgan_components(self):
        """Test the components of the problematic Disjunctive DeMorgan's RL example."""
        settings = {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
            'expectation': False,
            'print_impossible': False,
            'print_constraints': False,
            'print_z3': False,
            'save_output': False,
            'maximize': False,
        }
        
        # Create semantics
        semantics = ExclusionSemantics(settings)
        
        # Test the problematic example
        premise_str = '(\\exclude A \\uniwedge \\exclude B)'
        conclusion_str = '\\exclude (A \\univee B)'
        
        # Create syntax parser
        syntax = syntactic.Syntax([premise_str], [conclusion_str], exclusion_operators)
        
        # Create model constraints
        constraints = model.ModelConstraints(
            settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        # Create model structure
        structure = ExclusionStructure(constraints, settings)
        
        if structure.z3_model:
            # Interpret sentences to create propositions
            structure.interpret(syntax.premises)
            structure.interpret(syntax.conclusions)
            
            print("\n" + "="*60)
            print("Testing Disjunctive DeMorgan's RL components")
            print("="*60)
            
            # Check the main premise
            premise = syntax.premises[0]
            premise_prop = premise.proposition
            main_point = structure.main_point
            
            premise_truth = premise_prop.truth_value_at(main_point)
            print(f"\nMain premise: {premise_str}")
            print(f"Verifiers: {premise_prop.verifiers}")
            print(f"Truth value: {premise_truth}")
            
            # Check the components
            if premise.operator and premise.operator.name == "\\uniwedge":
                left_arg = premise.arguments[0]  # \\exclude A
                right_arg = premise.arguments[1]  # \\exclude B
                
                left_prop = left_arg.proposition
                right_prop = right_arg.proposition
                
                left_truth = left_prop.truth_value_at(main_point)
                right_truth = right_prop.truth_value_at(main_point)
                
                print(f"\nLeft component (\\exclude A):")
                print(f"  Verifiers: {left_prop.verifiers}")
                print(f"  Truth value: {left_truth}")
                
                print(f"\nRight component (\\exclude B):")
                print(f"  Verifiers: {right_prop.verifiers}")
                print(f"  Truth value: {right_truth}")
                
                # For conjunction, both must be true for the whole to be true
                expected_truth = left_truth and right_truth
                print(f"\nExpected conjunction truth (left AND right): {expected_truth}")
                print(f"Actual premise truth: {premise_truth}")
                
                self.assertEqual(premise_truth, expected_truth,
                               "Conjunction truth should equal (left AND right)")
                
                # If either component has empty verifiers, it should be false
                if len(left_prop.verifiers) == 0:
                    self.assertFalse(left_truth, "Left component with empty verifiers should be false")
                if len(right_prop.verifiers) == 0:
                    self.assertFalse(right_truth, "Right component with empty verifiers should be false")


if __name__ == '__main__':
    unittest.main(verbosity=2)