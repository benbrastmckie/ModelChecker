"""
Phase 1 tests for incremental exclusion implementation.

Tests the basic infrastructure components:
- WitnessStore: Persistent witness tracking
- TruthCache: Incremental truth evaluation  
- IncrementalVerifier: Unified constraint/evaluation
- Basic operator extensions with witness methods
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


class TestWitnessStore(unittest.TestCase):
    """Test the WitnessStore component."""
    
    def setUp(self):
        self.store = WitnessStore()
        
    def test_register_skolem_function(self):
        """Test registering Skolem functions."""
        self.store.register_skolem_function(
            "h_sk_1",
            z3.BitVecSort(3),
            z3.BitVecSort(3)
        )
        
        self.assertIn("h_sk_1", self.store.skolem_witnesses)
        witness_info = self.store.skolem_witnesses["h_sk_1"]
        self.assertEqual(witness_info["type"][0], z3.BitVecSort(3))
        self.assertEqual(witness_info["values"], {})
        
    def test_get_witness_mapping(self):
        """Test retrieving witness mappings."""
        self.store.register_skolem_function(
            "h_sk_1",
            z3.BitVecSort(3),
            z3.BitVecSort(3)
        )
        
        mapping = self.store.get_witness_mapping("h_sk_1")
        self.assertEqual(mapping, {})
        
        # Test non-existent function
        mapping = self.store.get_witness_mapping("non_existent")
        self.assertEqual(mapping, {})
        
    def test_is_witness_complete(self):
        """Test witness completeness checking."""
        self.store.register_skolem_function(
            "h_sk_1",
            z3.BitVecSort(3),
            z3.BitVecSort(3)
        )
        
        # Initially incomplete (no values)
        self.assertFalse(self.store.is_witness_complete("h_sk_1"))
        
        # Add some values (simplified for test)
        self.store.skolem_witnesses["h_sk_1"]["values"] = {0: 1}
        self.assertTrue(self.store.is_witness_complete("h_sk_1"))


class TestTruthCache(unittest.TestCase):
    """Test the TruthCache component."""
    
    def setUp(self):
        # Create minimal semantics for testing
        settings = {"N": 3}
        self.semantics = type('MockSemantics', (), {})()
        self.cache = TruthCache(self.semantics)
        self.store = WitnessStore()
        
    def test_initialization(self):
        """Test TruthCache initialization."""
        self.assertEqual(self.cache.partial_truths, {})
        self.assertEqual(self.cache.verifier_cache, {})
        self.assertEqual(self.cache.dependency_graph, {})
        
    def test_get_verifiers_caching(self):
        """Test verifier caching behavior."""
        # Create mock sentence
        sentence = type('Sentence', (), {
            'sentence_letter': 'A',
            'operator': None,
            'arguments': []
        })()
        
        # First call computes verifiers
        verifiers1 = self.cache.get_verifiers(sentence, self.store)
        self.assertEqual(verifiers1, set())  # Placeholder returns empty set
        
        # Add to cache manually
        self.cache.verifier_cache[sentence] = {1, 2, 3}
        
        # Second call uses cache
        verifiers2 = self.cache.get_verifiers(sentence, self.store)
        self.assertEqual(verifiers2, {1, 2, 3})


class TestIncrementalVerifier(unittest.TestCase):
    """Test the IncrementalVerifier component."""
    
    def setUp(self):
        settings = {"N": 3}
        self.semantics = ExclusionSemantics(settings)
        self.verifier = IncrementalVerifier(self.semantics)
        
    def test_initialization(self):
        """Test IncrementalVerifier initialization."""
        self.assertIsInstance(self.verifier.solver, z3.Solver)
        self.assertIsInstance(self.verifier.witness_store, WitnessStore)
        self.assertIsInstance(self.verifier.truth_cache, TruthCache)
        self.assertEqual(self.verifier.constraint_count, 0)
        
    def test_solver_persistence(self):
        """Test that solver state persists across calls."""
        # Add a simple constraint
        x = z3.BitVec('x', 3)
        self.verifier.solver.add(x == 5)
        
        # Check satisfiability
        result1 = self.verifier.solver.check()
        self.assertEqual(result1, z3.sat)
        
        # Add conflicting constraint
        self.verifier.solver.add(x == 3)
        
        # Should now be unsat due to persistent state
        result2 = self.verifier.solver.check()
        self.assertEqual(result2, z3.unsat)


class TestOperatorExtensions(unittest.TestCase):
    """Test operator extensions for incremental verification."""
    
    def setUp(self):
        settings = {"N": 3}
        self.semantics = ExclusionSemantics(settings)
        self.store = WitnessStore()
        self.cache = TruthCache(self.semantics)
        
    def test_exclusion_operator_witness_registration(self):
        """Test ExclusionOperator witness registration."""
        op = ExclusionOperator(self.semantics)
        
        # Create mock argument
        argument = type('Sentence', (), {})()
        
        # Register witnesses
        h_name, y_name = op.register_witnesses(argument, self.store)
        
        # Check registration
        self.assertTrue(h_name.startswith("h_sk_"))
        self.assertTrue(y_name.startswith("y_sk_"))
        self.assertIn(h_name, self.store.skolem_witnesses)
        self.assertIn(y_name, self.store.skolem_witnesses)
        
    def test_conjunction_has_sufficient_witnesses(self):
        """Test UniAndOperator witness sufficiency checking."""
        op = UniAndOperator(self.semantics)
        
        # Create mock atomic sentences (always sufficient)
        left = type('Sentence', (), {
            'sentence_letter': 'A',
            'operator': None,
            'arguments': []
        })()
        right = type('Sentence', (), {
            'sentence_letter': 'B',
            'operator': None,
            'arguments': []
        })()
        
        # Both atomic, so should be sufficient
        self.assertTrue(op.has_sufficient_witnesses(left, right, self.store))
        
    def test_disjunction_has_sufficient_witnesses(self):
        """Test UniOrOperator witness sufficiency checking."""
        op = UniOrOperator(self.semantics)
        
        # Create one atomic, one complex sentence
        atomic = type('Sentence', (), {
            'sentence_letter': 'A',
            'operator': None,
            'arguments': []
        })()
        
        # Mock complex sentence with insufficient witnesses
        mock_op = type('MockOp', (), {
            'has_sufficient_witnesses': lambda *args: False
        })()
        complex_sent = type('Sentence', (), {
            'sentence_letter': None,
            'operator': mock_op,
            'arguments': []
        })()
        
        # Disjunction needs only one sufficient argument
        self.assertTrue(op.has_sufficient_witnesses(atomic, complex_sent, self.store))


class TestSemanticIntegration(unittest.TestCase):
    """Test integration of incremental components with semantics."""
    
    def setUp(self):
        settings = {"N": 3}
        self.semantics = ExclusionSemantics(settings)
        
    def test_semantic_has_incremental_components(self):
        """Test that semantics properly initializes incremental components."""
        self.assertIsInstance(self.semantics.verifier, IncrementalVerifier)
        self.assertIsInstance(self.semantics.witness_store, WitnessStore)
        self.assertIsInstance(self.semantics.truth_cache, TruthCache)
        
        # Check that components are properly connected
        self.assertIs(self.semantics.witness_store, self.semantics.verifier.witness_store)
        self.assertIs(self.semantics.truth_cache, self.semantics.verifier.truth_cache)
        
    def test_exclusion_relation_setup(self):
        """Test that exclusion relation is properly initialized."""
        self.assertIsNotNone(self.semantics.exclusion)
        self.assertIn(self.semantics.exclusion, self.semantics.relation_symbols)


if __name__ == '__main__':
    unittest.main()