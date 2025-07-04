"""
Phase 2 tests for incremental exclusion implementation.

Tests the enhanced functionality:
- Witness extraction from Z3 models
- Incremental constraint building
- Three-level integration
- Operator witness computation
"""

import unittest
import z3
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from semantic import WitnessStore, TruthCache, IncrementalVerifier, ExclusionSemantics
from operators import ExclusionOperator, UniAndOperator, UniOrOperator
from model_checker import syntactic


class TestWitnessExtraction(unittest.TestCase):
    """Test witness extraction from Z3 models."""
    
    def setUp(self):
        self.settings = {"N": 3}
        self.semantics = ExclusionSemantics(self.settings)
        self.store = WitnessStore()
        
    def test_witness_extraction_from_model(self):
        """Test extracting witness values from a Z3 model."""
        # Create a simple Z3 model with a function
        solver = z3.Solver()
        N = 3
        h_sk = z3.Function("h_sk_test", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Add some constraints to define the function
        x = z3.BitVec("x", N)
        solver.add(h_sk(0) == 1)
        solver.add(h_sk(1) == 2)
        solver.add(h_sk(2) == 3)
        
        # Get model
        self.assertEqual(solver.check(), z3.sat)
        model = solver.model()
        
        # Register and extract witness
        self.store.register_skolem_function("h_sk_test", z3.BitVecSort(N), z3.BitVecSort(N))
        self.store.update_witness_values(model, self.semantics)
        
        # Check extracted values
        mapping = self.store.get_witness_mapping("h_sk_test")
        self.assertEqual(mapping.get(0), 1)
        self.assertEqual(mapping.get(1), 2)
        self.assertEqual(mapping.get(2), 3)
        
    def test_find_function_in_model(self):
        """Test finding function declarations in Z3 models."""
        solver = z3.Solver()
        N = 3
        test_func = z3.Function("test_func", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Add constraint to ensure function appears in model
        solver.add(test_func(0) == 1)
        
        self.assertEqual(solver.check(), z3.sat)
        model = solver.model()
        
        # Test finding function
        found_func = self.store._find_function_in_model(model, "test_func")
        self.assertIsNotNone(found_func)
        self.assertEqual(found_func.name(), "test_func")
        
        # Test not finding non-existent function
        not_found = self.store._find_function_in_model(model, "non_existent")
        self.assertIsNone(not_found)


class TestIncrementalConstraintBuilding(unittest.TestCase):
    """Test incremental constraint building and satisfiability checking."""
    
    def setUp(self):
        self.settings = {"N": 3}
        self.semantics = ExclusionSemantics(self.settings)
        self.verifier = IncrementalVerifier(self.semantics)
        
    def test_incremental_push_pop(self):
        """Test that solver maintains backtrack points correctly."""
        # Add initial constraint
        x = z3.BitVec("x", 3)
        self.verifier.solver.add(x == 1)
        self.assertEqual(self.verifier.solver.check(), z3.sat)
        
        # Push and add conflicting constraint
        self.verifier.solver.push()
        self.verifier.solver.add(x == 2)
        self.assertEqual(self.verifier.solver.check(), z3.unsat)
        
        # Pop to restore satisfiability
        self.verifier.solver.pop()
        self.assertEqual(self.verifier.solver.check(), z3.sat)
        
    def test_register_sentence_witnesses(self):
        """Test witness registration for sentences."""
        # Create exclusion sentence
        A_sent = syntactic.Sentence("A")
        excl_op = ExclusionOperator(self.semantics)
        excl_sent = syntactic.Sentence("\\exclude A")
        excl_sent.operator = excl_op
        excl_sent.arguments = [A_sent]
        
        # Register witnesses
        self.verifier._register_sentence_witnesses(excl_sent)
        
        # Check that witnesses were registered
        # The operator should have registered h_sk and y_sk functions
        self.assertTrue(len(self.verifier.witness_store.skolem_witnesses) >= 2)


class TestThreeLevelIntegration(unittest.TestCase):
    """Test integration across Syntax → Truth-Conditions → Extensions."""
    
    def setUp(self):
        self.settings = {"N": 2}  # Small N for testing
        self.semantics = ExclusionSemantics(self.settings)
        
    def test_truth_cache_with_model(self):
        """Test that truth cache can compute verifiers with model access."""
        # Create a simple model
        solver = z3.Solver()
        verify_func = self.semantics.verify
        A_atom = syntactic.AtomVal(0)  # Use AtomVal for atomic propositions
        
        # State 1 verifies A
        solver.add(verify_func(z3.BitVecVal(1, 2), A_atom))
        # State 2 doesn't verify A
        solver.add(z3.Not(verify_func(z3.BitVecVal(2, 2), A_atom)))
        
        self.assertEqual(solver.check(), z3.sat)
        model = solver.model()
        self.semantics.z3_model = model
        
        # Create sentence and compute verifiers
        A_sent = syntactic.Sentence("A")
        A_sent.sentence_letter = A_atom  # Set the atom
        verifiers = self.semantics.truth_cache.compute_atomic_verifiers(A_sent, self.semantics.witness_store)
        
        # Check that state 1 is a verifier
        self.assertIn(1, verifiers)
        # Check that state 2 is not a verifier
        self.assertNotIn(2, verifiers)


class TestOperatorWitnessComputation(unittest.TestCase):
    """Test operator methods for witness-based computation."""
    
    def setUp(self):
        self.settings = {"N": 2}
        self.semantics = ExclusionSemantics(self.settings)
        self.store = WitnessStore()
        self.cache = TruthCache(self.semantics)
        
    def test_exclusion_three_conditions_check(self):
        """Test the three-condition check with actual witness mappings."""
        excl_op = ExclusionOperator(self.semantics)
        
        # Set up witness mappings
        # h(1) = 2, y(1) = 1 (y is part of 1, and we'll say h excludes y)
        h_mapping = {1: 2}
        y_mapping = {1: 1}
        arg_verifiers = {1}
        
        # Create a mock model that says 2 excludes 1
        solver = z3.Solver()
        solver.add(self.semantics.exclusion(z3.BitVecVal(2, 2), z3.BitVecVal(1, 2)))
        self.assertEqual(solver.check(), z3.sat)
        self.semantics.z3_model = solver.model()
        
        # Test state 2 (should satisfy conditions as fusion of h values)
        state = z3.BitVecVal(2, 2)
        result = excl_op.satisfies_three_conditions(state, arg_verifiers, h_mapping, y_mapping)
        self.assertTrue(result)
        
        # Test state 3 (should not satisfy - not minimal)
        state = z3.BitVecVal(3, 2)
        result = excl_op.satisfies_three_conditions(state, arg_verifiers, h_mapping, y_mapping)
        self.assertFalse(result)
        
    def test_part_of_checking(self):
        """Test the part-of relation checking."""
        excl_op = ExclusionOperator(self.semantics)
        
        # Test integer part-of
        self.assertTrue(excl_op._is_part_of_int(0, 0))  # 0 ⊑ 0
        self.assertTrue(excl_op._is_part_of_int(0, 1))  # 0 ⊑ 1
        self.assertTrue(excl_op._is_part_of_int(1, 1))  # 1 ⊑ 1
        self.assertTrue(excl_op._is_part_of_int(1, 3))  # 1 ⊑ 3 (binary: 01 ⊑ 11)
        self.assertFalse(excl_op._is_part_of_int(2, 1)) # 2 ⊄ 1 (binary: 10 ⊄ 01)
        
    def test_fusion_computation(self):
        """Test fusion computation with integers."""
        excl_op = ExclusionOperator(self.semantics)
        
        # Test fusion
        self.assertEqual(excl_op._compute_fusion_int([1, 2]), 3)  # 01 | 10 = 11
        self.assertEqual(excl_op._compute_fusion_int([0, 0]), 0)  # 00 | 00 = 00
        self.assertEqual(excl_op._compute_fusion_int([1, 1]), 1)  # 01 | 01 = 01
        self.assertEqual(excl_op._compute_fusion_int([]), 0)      # Empty fusion


class TestIncrementalVerification(unittest.TestCase):
    """Test full incremental verification process."""
    
    def setUp(self):
        self.settings = {"N": 2}
        self.semantics = ExclusionSemantics(self.settings)
        
    def test_has_sufficient_witnesses(self):
        """Test checking for sufficient witness information."""
        verifier = self.semantics.verifier
        
        # Atomic sentence always has sufficient witnesses
        A_sent = syntactic.Sentence("A")
        A_sent.sentence_letter = syntactic.AtomVal(0)  # Mark as atomic
        self.assertTrue(verifier._has_sufficient_witnesses(A_sent))
        
        # Complex sentence needs operator support
        excl_op = ExclusionOperator(self.semantics)
        excl_sent = syntactic.Sentence("\\exclude A")
        excl_sent.operator = excl_op
        excl_sent.arguments = [A_sent]
        excl_sent.sentence_letter = None  # Not atomic
        
        # Initially no witnesses registered
        self.assertFalse(verifier._has_sufficient_witnesses(excl_sent))
        
        # Register witnesses
        excl_op.register_witnesses(A_sent, verifier.witness_store)
        
        # Still not sufficient until we have values
        self.assertFalse(verifier._has_sufficient_witnesses(excl_sent))
        
        # Add some witness values
        h_name = f"h_sk_{id(excl_op)}"
        y_name = f"y_sk_{id(excl_op)}"
        verifier.witness_store.skolem_witnesses[h_name]['values'] = {0: 0}
        verifier.witness_store.skolem_witnesses[y_name]['values'] = {0: 0}
        
        # Now should be sufficient
        self.assertTrue(verifier._has_sufficient_witnesses(excl_sent))


if __name__ == '__main__':
    unittest.main()