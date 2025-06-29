"""Test for empty verifier evaluation fix.

This test ensures that propositions with empty verifier sets are correctly
evaluated as false, fixing the issue where constraint formulas were incorrectly
being used for truth evaluation.
"""

import unittest
import z3
from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
    exclusion_operators
)
from model_checker import model, syntactic
from model_checker.utils import bitvec_to_substates


class TestEmptyVerifiers(unittest.TestCase):
    """Test that propositions with empty verifiers evaluate to false."""
    
    def setUp(self):
        """Set up common test settings."""
        self.settings = {
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
        
    def test_disjunctive_demorgan_rl(self):
        """Test the Disjunctive DeMorgan's RL countermodel.
        
        This tests the case: (\\exclude A \\uniwedge \\exclude B) -> \\exclude (A \\univee B)
        which should have a countermodel where the premise is true but conclusion is false.
        """
        # Create semantics
        semantics = ExclusionSemantics(self.settings)
        
        # Parse sentences
        premise_str = '(\\exclude A \\uniwedge \\exclude B)'
        conclusion_str = '\\exclude (A \\univee B)'
        
        # Create syntax parser
        syntax = syntactic.Syntax([premise_str], [conclusion_str], exclusion_operators)
        
        premise = syntax.premises[0]
        conclusion = syntax.conclusions[0]
        
        # Create model constraints
        constraints = model.ModelConstraints(
            self.settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        # Create model structure
        structure = ExclusionStructure(constraints, self.settings)
        
        # Check that we found a model
        self.assertIsNotNone(structure.z3_model, "Should find a countermodel")
        
        # Create propositions
        main_point = structure.main_point
        premise_prop = UnilateralProposition(premise, structure, main_point)
        conclusion_prop = UnilateralProposition(conclusion, structure, main_point)
        
        # The key test: premise should be true, conclusion should be false
        premise_truth = premise_prop.truth_value_at(main_point)
        conclusion_truth = conclusion_prop.truth_value_at(main_point)
        
        self.assertTrue(premise_truth, 
                       f"Premise should be true but evaluated to {premise_truth}. "
                       f"Verifiers: {premise_prop.verifiers}")
        self.assertFalse(conclusion_truth,
                        f"Conclusion should be false but evaluated to {conclusion_truth}. "
                        f"Verifiers: {conclusion_prop.verifiers}")
        
    def test_empty_verifier_evaluates_false(self):
        """Direct test that a proposition with empty verifiers evaluates to false."""
        # Create minimal semantics
        semantics = ExclusionSemantics(self.settings)
        
        # Create a simple model where we can control verifiers
        # We'll use the exclusion of a tautology, which should have no verifiers
        sentence_str = '\\exclude (A \\univee \\exclude A)'
        syntax = syntactic.Syntax([sentence_str], [], exclusion_operators)
        sentence = syntax.premises[0]
        
        # Create model constraints
        constraints = model.ModelConstraints(
            self.settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        # Create model structure
        structure = ExclusionStructure(constraints, self.settings)
        
        if structure.z3_model:
            # Create proposition
            main_point = structure.main_point
            prop = UnilateralProposition(sentence, structure, main_point)
            
            # If verifiers are empty, truth value should be false
            if not prop.verifiers:
                truth_value = prop.truth_value_at(main_point)
                self.assertFalse(truth_value,
                               "Proposition with empty verifiers should evaluate to false")
                               
    def test_triple_negation_entailment(self):
        """Test Triple Negation Entailment which was showing false premise issues.
        
        Tests: \\exclude \\exclude \\exclude A -> \\exclude A
        """
        semantics = ExclusionSemantics(self.settings)
        
        premise_str = '\\exclude \\exclude \\exclude A'
        conclusion_str = '\\exclude A'
        
        syntax = syntactic.Syntax([premise_str], [conclusion_str], exclusion_operators)
        premise = syntax.premises[0]
        conclusion = syntax.conclusions[0]
        
        constraints = model.ModelConstraints(
            self.settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        structure = ExclusionStructure(constraints, self.settings)
        
        if structure.z3_model:
            # This should NOT find a countermodel (it's a valid entailment)
            # But if it does, we want to ensure no false premise
            main_point = structure.main_point
            premise_prop = UnilateralProposition(premise, structure, main_point)
            conclusion_prop = UnilateralProposition(conclusion, structure, main_point)
            
            premise_truth = premise_prop.truth_value_at(main_point)
            conclusion_truth = conclusion_prop.truth_value_at(main_point)
            
            # If we found a countermodel, it must have true premise and false conclusion
            if premise_truth and not conclusion_truth:
                # Valid countermodel
                pass
            else:
                # Invalid countermodel - should not happen after fix
                self.fail(f"Invalid countermodel found: premise={premise_truth}, "
                         f"conclusion={conclusion_truth}")


if __name__ == '__main__':
    unittest.main()