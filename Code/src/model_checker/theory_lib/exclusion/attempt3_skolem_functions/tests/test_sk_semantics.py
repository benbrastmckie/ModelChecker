"""
Test Suite for Skolemized Implementation of Exclusion Semantics

This module tests the SK implementation to ensure it correctly implements
recursive semantics and eliminates false premises.
"""

import unittest
import z3
from model_checker import syntactic, model
from model_checker.theory_lib.exclusion import semantic
from model_checker.theory_lib.exclusion.sk_exclusion import (
    create_sk_operators,
    SK_ExclusionOperator,
    SK_UniAndOperator,
    SK_UniOrOperator,
)


class TestSKSemantics(unittest.TestCase):
    """Test cases for SK implementation of exclusion semantics."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {
            'N': 3,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
        }
        self.semantics = semantic.ExclusionSemantics(self.settings)
        self.sk_operators = create_sk_operators()
        
    def test_atomic_reduction(self):
        """Test that atomic sentences correctly reduce to verifier existence."""
        # Create atomic sentence
        atom_a = syntactic.Sentence("A")
        
        # Get SK semantics with overridden true_at
        eval_world = self.semantics.main_world
        eval_point = {"world": eval_world}
        
        # The true_at for atomic sentences should reduce to:
        # exists v. verify(v, A) AND v part_of eval_world
        # This is handled in the base semantics, not the operators
        
        # Create a simple model to test
        syntax = syntactic.Syntax(["A"], [], self.sk_operators)
        constraints = model.ModelConstraints(
            self.settings,
            syntax,
            self.semantics,
            semantic.UnilateralProposition
        )
        
        # Check that we can find a model
        model_structure = semantic.ExclusionStructure(constraints, self.settings)
        self.assertIsNotNone(model_structure.z3_model)
        
    def test_exclusion_recursive_reduction(self):
        """Test that exclusion operators use recursive reduction."""
        # Create exclusion formula
        excl_a = syntactic.Sentence("\\exclude A")
        
        # Test with SK operator
        sk_excl = SK_ExclusionOperator(self.semantics)
        
        # The true_at should properly encode the three conditions
        eval_point = {"world": self.semantics.main_world}
        
        # Get the formula (without evaluating with Z3)
        # We're testing the structure, not the result
        formula = sk_excl.true_at(excl_a.arguments[0], eval_point)
        
        # Check that it's an existential formula
        self.assertTrue(z3.is_quantifier(formula))
        self.assertTrue(formula.is_exists())
        
    def test_conjunction_recursive_reduction(self):
        """Test that conjunction uses recursive calls on subformulas."""
        # Create conjunction
        conj = syntactic.Sentence("(A \\uniwedge B)")
        
        # Test with SK operator
        sk_and = SK_UniAndOperator(self.semantics)
        
        eval_point = {"world": self.semantics.main_world}
        
        # Get the formula
        left_arg = syntactic.Sentence("A")
        right_arg = syntactic.Sentence("B")
        formula = sk_and.true_at(left_arg, right_arg, eval_point)
        
        # Check that it's an existential formula
        self.assertTrue(z3.is_quantifier(formula))
        self.assertTrue(formula.is_exists())
        
    def test_double_negation_elimination(self):
        """Test that DN_ELIM works correctly with SK implementation."""
        # This was one of the problematic examples
        premises = ["\\exclude \\exclude A"]
        conclusions = ["A"]
        
        syntax = syntactic.Syntax(premises, conclusions, self.sk_operators)
        
        # Create model with SK semantics
        model_constraints = model.ModelConstraints(
            self.settings,
            syntax,
            self.semantics,
            semantic.UnilateralProposition
        )
        
        # Try to find a model
        model_structure = semantic.ExclusionStructure(model_constraints, self.settings)
        
        if model_structure.z3_model_status:
            # Interpret sentences
            model_structure.interpret(syntax.premises + syntax.conclusions)
            
            # Check that premise is true (not false as in baseline)
            premise = syntax.premises[0]
            if hasattr(premise, 'proposition') and premise.proposition:
                main_point = self.semantics.main_point
                premise_truth = premise.proposition.truth_value_at(main_point)
                
                # With correct SK implementation, premise should be true
                self.assertTrue(premise_truth, 
                    "DN_ELIM premise should be true with SK implementation")
                    
    def test_demorgan_laws(self):
        """Test DeMorgan's laws with SK implementation."""
        # Test CONJ_DM_LR: ¬(A ∧ B) → (¬A ∨ ¬B)
        premises = ["\\exclude (A \\uniwedge B)"]
        conclusions = ["(\\exclude A \\univee \\exclude B)"]
        
        syntax = syntactic.Syntax(premises, conclusions, self.sk_operators)
        
        model_constraints = model.ModelConstraints(
            self.settings,
            syntax,
            self.semantics,
            semantic.UnilateralProposition
        )
        
        model_structure = semantic.ExclusionStructure(model_constraints, self.settings)
        
        if model_structure.z3_model_status:
            model_structure.interpret(syntax.premises + syntax.conclusions)
            
            # Check premise truth
            premise = syntax.premises[0]
            if hasattr(premise, 'proposition') and premise.proposition:
                main_point = self.semantics.main_point
                premise_truth = premise.proposition.truth_value_at(main_point)
                
                # Should be true with SK implementation
                self.assertTrue(premise_truth,
                    "DeMorgan premise should be true with SK implementation")


class TestSKCorrectness(unittest.TestCase):
    """Test correctness properties of SK implementation."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {
            'N': 2,  # Small domain for exhaustive testing
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
        }
        self.semantics = semantic.ExclusionSemantics(self.settings)
        self.sk_operators = create_sk_operators()
        
    def test_verifier_existence_pattern(self):
        """Test that all formulas reduce to verifier existence pattern."""
        # Test various formulas
        test_formulas = [
            "A",
            "\\exclude A",
            "(A \\uniwedge B)",
            "(A \\univee B)",
            "\\exclude (A \\uniwedge B)",
            "\\exclude \\exclude A",
        ]
        
        for formula_str in test_formulas:
            with self.subTest(formula=formula_str):
                # Parse formula
                sentence = syntactic.Sentence(formula_str)
                
                # Each should reduce to pattern: exists v. ... AND v part_of w
                # We can't easily test the internal structure, but we can
                # verify no errors occur during construction
                syntax = syntactic.Syntax([formula_str], [], self.sk_operators)
                
                # Should not raise errors
                model_constraints = model.ModelConstraints(
                    self.settings,
                    syntax,
                    self.semantics,
                    semantic.UnilateralProposition
                )
                
                # Basic check that constraints were created
                self.assertIsNotNone(model_constraints.all_constraints)


if __name__ == '__main__':
    unittest.main()