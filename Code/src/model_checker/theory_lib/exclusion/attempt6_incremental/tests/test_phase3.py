"""
Phase 3 tests for incremental exclusion implementation.

Tests the full integration with the ModelChecker framework
and validates that the problematic examples now work correctly.
"""

import unittest
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators
from model_checker import syntactic
from model_checker.model import ModelConstraints
from model_checker.theory_lib.default import ModelStructure
from model_checker.builder import BuildExample, BuildModule


class TestFrameworkIntegration(unittest.TestCase):
    """Test integration with the ModelChecker framework."""
    
    def setUp(self):
        self.exclusion_theory = {
            "semantics": ExclusionSemantics,
            "proposition": UnilateralProposition,
            "model": ModelStructure,
            "operators": exclusion_operators,
            "dictionary": {}
        }
        
    def create_build_example(self, premises, conclusions, settings):
        """Helper to create a BuildExample for testing."""
        # Create a mock BuildModule
        class MockBuildModule:
            def __init__(self):
                self.general_settings = {
                    "print_constraints": False,
                    "print_impossible": False,
                    "print_z3": False,
                    "save_output": False,
                    "maximize": False,
                }
                self.module_flags = None  # Use None instead of empty dict
                
        mock_module = MockBuildModule()
        example_case = [premises, conclusions, settings]
        return BuildExample(mock_module, self.exclusion_theory, example_case)
    
    def test_double_negation_elimination(self):
        """Test that double negation elimination now works."""
        premises = ['\\exclude \\exclude A']
        conclusions = ['A']
        settings = {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
            'expectation': True,
        }
        
        build_example = self.create_build_example(premises, conclusions, settings)
        result = build_example.get_result()
        
        # The example should be valid (no countermodel found)
        self.assertFalse(result["model_found"], 
                        "Double negation elimination should be valid (no countermodel)")
    
    def test_triple_negation_entailment(self):
        """Test that triple negation entailment now works."""
        premises = ['\\exclude \\exclude \\exclude A']
        conclusions = ['\\exclude A']
        settings = {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 10,
            'expectation': True,
        }
        
        build_example = self.create_build_example(premises, conclusions, settings)
        result = build_example.get_result()
        
        # The example should be valid (no countermodel found)
        self.assertFalse(result["model_found"], 
                        "Triple negation entailment should be valid (no countermodel)")
    
    def test_disjunctive_syllogism_invalid(self):
        """Test that disjunctive syllogism is correctly invalid."""
        premises = ['(A \\univee B)', '\\exclude B']
        conclusions = ['A']
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
        }
        
        build_example = self.create_build_example(premises, conclusions, settings)
        result = build_example.get_result()
        
        # The example should be invalid (countermodel found)
        self.assertTrue(result["model_found"], 
                       "Disjunctive syllogism should be invalid (countermodel exists)")
    
    def test_empty_example(self):
        """Test basic empty example for frame constraints."""
        premises = []
        conclusions = []
        settings = {
            'N': 2,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 2,
            'expectation': True,
        }
        
        build_example = self.create_build_example(premises, conclusions, settings)
        result = build_example.get_result()
        
        # Empty example should have a model
        self.assertTrue(result["model_found"], 
                       "Empty example should have a model")


class TestIncrementalEvaluation(unittest.TestCase):
    """Test incremental evaluation functionality."""
    
    def setUp(self):
        self.settings = {"N": 2}
        self.semantics = ExclusionSemantics(self.settings)
        
    def test_incremental_verification_atomic(self):
        """Test incremental verification on atomic sentences."""
        # Create atomic sentence
        A_sent = syntactic.Sentence("A")
        A_sent.sentence_letter = syntactic.AtomVal(0)
        
        # Create evaluation point
        eval_point = {"world": syntactic.z3.BitVecVal(1, 2)}
        
        # Test incremental verification
        result = self.semantics.verifier.verify_incrementally(A_sent, eval_point)
        self.assertIsInstance(result, bool)
    
    def test_incremental_verification_exclusion(self):
        """Test incremental verification on exclusion sentences."""
        # Create exclusion sentence
        A_sent = syntactic.Sentence("A")
        A_sent.sentence_letter = syntactic.AtomVal(0)
        
        excl_op = self.semantics.operators.get_operator("\\exclude")
        excl_sent = syntactic.Sentence("\\exclude A")
        excl_sent.operator = excl_op
        excl_sent.arguments = [A_sent]
        
        # Create evaluation point
        eval_point = {"world": syntactic.z3.BitVecVal(2, 2)}
        
        # Test incremental verification
        result = self.semantics.verifier.verify_incrementally(excl_sent, eval_point)
        self.assertIsInstance(result, bool)
    
    def test_witness_persistence_across_evaluations(self):
        """Test that witnesses persist across multiple evaluations."""
        # Create exclusion sentence
        A_sent = syntactic.Sentence("A")
        A_sent.sentence_letter = syntactic.AtomVal(0)
        
        excl_op = self.semantics.operators.get_operator("\\exclude")
        excl_sent = syntactic.Sentence("\\exclude A")
        excl_sent.operator = excl_op
        excl_sent.arguments = [A_sent]
        
        # First evaluation
        eval_point1 = {"world": syntactic.z3.BitVecVal(1, 2)}
        self.semantics.verifier.verify_incrementally(excl_sent, eval_point1)
        
        # Check that witnesses were registered
        witness_count1 = len(self.semantics.verifier.witness_store.skolem_witnesses)
        self.assertGreater(witness_count1, 0, "Witnesses should be registered")
        
        # Second evaluation with same verifier
        eval_point2 = {"world": syntactic.z3.BitVecVal(2, 2)}
        self.semantics.verifier.verify_incrementally(excl_sent, eval_point2)
        
        # Check that witnesses persist
        witness_count2 = len(self.semantics.verifier.witness_store.skolem_witnesses)
        self.assertEqual(witness_count1, witness_count2, 
                        "Witnesses should persist across evaluations")


class TestPerformanceOptimization(unittest.TestCase):
    """Test performance characteristics of incremental approach."""
    
    def setUp(self):
        self.settings = {"N": 3}
        self.semantics = ExclusionSemantics(self.settings)
        
    def test_early_termination_on_unsat(self):
        """Test that incremental approach terminates early on unsatisfiability."""
        # Create a contradictory formula
        A_sent = syntactic.Sentence("A")
        A_sent.sentence_letter = syntactic.AtomVal(0)
        
        and_op = self.semantics.operators.get_operator("\\uniwedge")
        excl_op = self.semantics.operators.get_operator("\\exclude")
        
        # A ∧ ¬A (contradiction)
        neg_A = syntactic.Sentence("\\exclude A")
        neg_A.operator = excl_op
        neg_A.arguments = [A_sent]
        
        contradiction = syntactic.Sentence("(A \\uniwedge \\exclude A)")
        contradiction.operator = and_op
        contradiction.arguments = [A_sent, neg_A]
        
        # Try to verify at some point
        eval_point = {"world": syntactic.z3.BitVecVal(1, 3)}
        
        # Should return False quickly due to contradiction
        result = self.semantics.verifier.verify_incrementally(contradiction, eval_point)
        self.assertFalse(result, "Contradiction should evaluate to False")


if __name__ == '__main__':
    unittest.main()