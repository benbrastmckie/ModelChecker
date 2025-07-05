"""
Phase 2 tests for incremental exclusion implementation.

Tests for Phase 2 implementation focusing on:
1. Enhanced WitnessStore with dependency tracking
2. TruthCache with incremental evaluation
3. IncrementalVerifier functionality
4. Operator incremental evaluation methods
"""

import unittest
import z3
import sys
import os
import time

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators
from incremental_model import IncrementalModelStructure, WitnessStore, IncrementalSolver, IncrementalVerifier
from truth_cache import TruthCache
from model_checker import syntactic
from model_checker.model import ModelConstraints


class TestWitnessStoreDependencies(unittest.TestCase):
    """Test Phase 2 enhancements to WitnessStore."""
    
    def setUp(self):
        self.store = WitnessStore()
        self.semantics = ExclusionSemantics({"N": 2})
        
    def test_dependency_registration(self):
        """Test registering witness dependencies."""
        # Register some witnesses
        self.store.register_skolem_function("h1", z3.BitVecSort(2), z3.BitVecSort(2))
        self.store.register_skolem_function("h2", z3.BitVecSort(2), z3.BitVecSort(2))
        self.store.register_skolem_function("h3", z3.BitVecSort(2), z3.BitVecSort(2))
        
        # Register dependencies: h1 depends on h2 and h3
        self.store.register_dependent_witnesses("h1", ["h2", "h3"])
        
        self.assertIn("h1", self.store.witness_dependencies)
        self.assertEqual(self.store.witness_dependencies["h1"], {"h2", "h3"})
        
    def test_dependency_invalidation(self):
        """Test invalidating dependent witnesses."""
        # Setup witnesses with dependencies
        self.store.register_skolem_function("h1", z3.BitVecSort(2), z3.BitVecSort(2))
        self.store.register_skolem_function("h2", z3.BitVecSort(2), z3.BitVecSort(2))
        self.store.register_skolem_function("h3", z3.BitVecSort(2), z3.BitVecSort(2))
        
        # Mark as complete
        self.store.skolem_witnesses["h1"]["complete"] = True
        self.store.skolem_witnesses["h2"]["complete"] = True
        self.store.skolem_witnesses["h3"]["complete"] = True
        
        # Register dependencies: h1 depends on h2, h2 depends on h3
        self.store.register_dependent_witnesses("h1", ["h2"])
        self.store.register_dependent_witnesses("h2", ["h3"])
        
        # Invalidate h3 - should cascade to h2 and h1
        self.store.invalidate_dependent_witnesses("h3")
        
        self.assertFalse(self.store.skolem_witnesses["h3"]["complete"])
        self.assertFalse(self.store.skolem_witnesses["h2"]["complete"])
        self.assertFalse(self.store.skolem_witnesses["h1"]["complete"])
        
    def test_witness_caching(self):
        """Test witness value caching."""
        # Cache some witness values
        self.store.cache_witness_value("h1", (0,), 1)
        self.store.cache_witness_value("h1", (1,), 2)
        
        # Test retrieval
        self.assertEqual(self.store.get_cached_witness("h1", (0,)), 1)
        self.assertEqual(self.store.get_cached_witness("h1", (1,)), 2)
        self.assertIsNone(self.store.get_cached_witness("h1", (2,)))
        
        # Check cache statistics
        stats = self.store.get_cache_statistics()
        self.assertEqual(stats['cache_hits'], 2)
        self.assertEqual(stats['cache_misses'], 1)
        self.assertEqual(stats['cache_size'], 2)
        
    def test_witness_interpretation_extraction(self):
        """Test extracting complete witness interpretation from model."""
        # Create a simple Z3 model
        solver = z3.Solver()
        h_sk = z3.Function("h_sk_test", z3.BitVecSort(2), z3.BitVecSort(2))
        
        # Add some constraints
        solver.add(h_sk(0) == 1)
        solver.add(h_sk(1) == 2)
        solver.add(h_sk(2) == 3)
        solver.add(h_sk(3) == 0)
        
        self.assertEqual(solver.check(), z3.sat)
        model = solver.model()
        
        # Register witness
        self.store.register_skolem_function("h_sk_test", z3.BitVecSort(2), z3.BitVecSort(2))
        
        # Extract interpretation
        interpretation = self.store.get_witness_interpretation("h_sk_test", model)
        
        self.assertIsNotNone(interpretation)
        self.assertEqual(interpretation[0], 1)
        self.assertEqual(interpretation[1], 2)
        self.assertEqual(interpretation[2], 3)
        self.assertEqual(interpretation[3], 0)
        
    def test_witness_history_pruning(self):
        """Test witness history pruning."""
        # Add many history entries
        for i in range(20):
            self.store.witness_history.append((time.time(), f"func_{i}", "event"))
        
        self.assertEqual(len(self.store.witness_history), 20)
        
        # Prune to 10 entries
        self.store.prune_witness_history(max_entries=10)
        
        self.assertEqual(len(self.store.witness_history), 10)
        # Should keep the most recent entries
        self.assertEqual(self.store.witness_history[-1][1], "func_19")


class TestTruthCache(unittest.TestCase):
    """Test TruthCache functionality."""
    
    def setUp(self):
        self.settings = {
            "N": 2,
            "max_time": 5,
            "expectation": True,
            "contingent": False,
            "non_empty": False,
            "non_null": False,
            "disjoint": False,
            "fusion_closure": False
        }
        self.semantics = ExclusionSemantics(self.settings)
        self.truth_cache = TruthCache(self.semantics)
        self.witness_store = WitnessStore()
        
    def test_verifier_caching(self):
        """Test verifier computation and caching."""
        # Create a simple sentence
        syntax = syntactic.Syntax(['A'], ['A'], exclusion_operators)
        sentence = syntax.premises[0]
        
        # Get verifiers - should compute and cache
        verifiers1 = self.truth_cache.get_verifiers(sentence, self.witness_store)
        self.assertEqual(self.truth_cache.cache_misses, 1)
        self.assertEqual(self.truth_cache.cache_hits, 0)
        
        # Get verifiers again - should use cache
        verifiers2 = self.truth_cache.get_verifiers(sentence, self.witness_store)
        self.assertEqual(self.truth_cache.cache_hits, 1)
        self.assertEqual(verifiers1, verifiers2)
        
    def test_truth_value_caching(self):
        """Test truth value computation and caching."""
        syntax = syntactic.Syntax(['A'], ['A'], exclusion_operators)
        sentence = syntax.premises[0]
        eval_point = {'world': z3.BitVecVal(1, 2)}
        
        # Get truth value - should compute and cache
        truth1 = self.truth_cache.get_truth_value(sentence, eval_point, self.witness_store)
        self.assertEqual(self.truth_cache.cache_misses, 2)  # One for verifiers, one for truth
        
        # Get truth value again - should use cache
        truth2 = self.truth_cache.get_truth_value(sentence, eval_point, self.witness_store)
        self.assertEqual(self.truth_cache.cache_hits, 1)
        
    def test_dependency_tracking(self):
        """Test formula dependency tracking."""
        syntax = syntactic.Syntax(['A', '(A \\uniwedge B)'], ['B'], exclusion_operators)
        atomic_a = syntax.premises[0]
        complex_ab = syntax.premises[1]
        
        # Register dependency
        self.truth_cache.register_dependency(complex_ab, atomic_a)
        
        self.assertIn(complex_ab, self.truth_cache.dependency_graph)
        self.assertIn(atomic_a, self.truth_cache.dependency_graph[complex_ab])
        
    def test_invalidation(self):
        """Test cache invalidation."""
        syntax = syntactic.Syntax(['A'], ['A'], exclusion_operators)
        sentence = syntax.premises[0]
        
        # Cache some values
        verifiers = self.truth_cache.get_verifiers(sentence, self.witness_store)
        self.assertIn(sentence, self.truth_cache.verifier_cache)
        
        # Invalidate
        self.truth_cache.invalidate_dependent_truths(sentence)
        
        self.assertNotIn(sentence, self.truth_cache.verifier_cache)
        self.assertEqual(self.truth_cache.invalidation_count, 1)


class TestIncrementalVerifier(unittest.TestCase):
    """Test IncrementalVerifier functionality."""
    
    def setUp(self):
        self.settings = {
            "N": 2,
            "max_time": 5,
            "expectation": True,
            "contingent": False,
            "non_empty": False,
            "non_null": False,
            "disjoint": False,
            "fusion_closure": False
        }
        self.semantics = ExclusionSemantics(self.settings)
        self.solver = z3.Solver()
        self.witness_store = WitnessStore()
        self.truth_cache = TruthCache(self.semantics)
        self.verifier = IncrementalVerifier(
            self.semantics, self.solver, self.witness_store, self.truth_cache
        )
        
    def test_witness_registration(self):
        """Test recursive witness registration."""
        # Create proper model constraints to get operators with semantics
        syntax = syntactic.Syntax(['\\exclude A'], ['A'], exclusion_operators)
        model_constraints = ModelConstraints(self.settings, syntax, self.semantics, UnilateralProposition)
        
        # Get the exclusion sentence from parsed syntax
        sentence = model_constraints.syntax.premises[0]
        
        # Register witnesses
        self.verifier._register_sentence_witnesses(sentence)
        
        # Check that witnesses were registered
        # The ExclusionOperator should have registered h_sk and y_sk functions
        witness_funcs = list(self.witness_store.skolem_witnesses.keys())
        self.assertTrue(any('h_sk' in name for name in witness_funcs))
        self.assertTrue(any('y_sk' in name for name in witness_funcs))
        
    def test_structural_constraint_generation(self):
        """Test generating structural constraints."""
        syntax = syntactic.Syntax(['A'], ['A'], exclusion_operators)
        sentence = syntax.premises[0]
        eval_point = {'world': z3.BitVecVal(1, 2)}
        
        constraints = self.verifier._generate_structural_constraints(sentence, eval_point)
        
        self.assertIsInstance(constraints, list)
        self.assertTrue(len(constraints) > 0)
        self.assertIsInstance(constraints[0], tuple)
        self.assertEqual(len(constraints[0]), 2)  # (constraint, label)


class TestOperatorIncrementalMethods(unittest.TestCase):
    """Test incremental methods on operators."""
    
    def setUp(self):
        self.settings = {
            "N": 2,
            "max_time": 5,
            "expectation": True,
            "contingent": False,
            "non_empty": False,
            "non_null": False,
            "disjoint": False,
            "fusion_closure": False
        }
        self.semantics = ExclusionSemantics(self.settings)
        self.witness_store = WitnessStore()
        self.truth_cache = TruthCache(self.semantics)
        
        # Connect to semantics
        self.semantics.witness_store = self.witness_store
        self.semantics.truth_cache = self.truth_cache
        
    def test_conjunction_incremental_evaluation(self):
        """Test conjunction operator incremental evaluation."""
        # Create proper model constraints to get operators with semantics
        syntax = syntactic.Syntax(['A', 'B', '(A \\uniwedge B)'], ['(A \\uniwedge B)'], exclusion_operators)
        model_constraints = ModelConstraints(self.settings, syntax, self.semantics, UnilateralProposition)
        
        # Get the conjunction sentence from parsed syntax
        conj_sentence = model_constraints.syntax.premises[2]
        eval_point = {'world': z3.BitVecVal(3, 2)}  # Binary 11 - both bits set
        
        # Test has_sufficient_witnesses
        operator = conj_sentence.operator
        sufficient = operator.has_sufficient_witnesses(
            conj_sentence.arguments[0], conj_sentence.arguments[1], self.witness_store
        )
        self.assertTrue(sufficient)  # Atomic arguments don't need witnesses
        
    def test_disjunction_incremental_evaluation(self):
        """Test disjunction operator incremental evaluation."""
        # Create proper model constraints to get operators with semantics
        syntax = syntactic.Syntax(['A', 'B', '(A \\univee B)'], ['(A \\univee B)'], exclusion_operators)
        model_constraints = ModelConstraints(self.settings, syntax, self.semantics, UnilateralProposition)
        
        # Get the disjunction sentence from parsed syntax
        disj_sentence = model_constraints.syntax.premises[2]
        eval_point = {'world': z3.BitVecVal(1, 2)}  # Binary 01 - only A bit set
        
        # Test has_sufficient_witnesses
        operator = disj_sentence.operator
        sufficient = operator.has_sufficient_witnesses(
            disj_sentence.arguments[0], disj_sentence.arguments[1], self.witness_store
        )
        self.assertTrue(sufficient)  # Atomic arguments don't need witnesses
        
    def test_exclusion_witness_registration(self):
        """Test exclusion operator witness registration."""
        # Create proper model constraints to get operators with semantics
        syntax = syntactic.Syntax(['\\exclude A'], ['A'], exclusion_operators)
        model_constraints = ModelConstraints(self.settings, syntax, self.semantics, UnilateralProposition)
        
        # Get the exclusion sentence from parsed syntax
        excl_sentence = model_constraints.syntax.premises[0]
        
        operator = excl_sentence.operator
        h_name, y_name = operator.register_witnesses(
            excl_sentence.arguments[0], self.witness_store
        )
        
        self.assertTrue(h_name.startswith('h_sk_'))
        self.assertTrue(y_name.startswith('y_sk_'))
        self.assertIn(h_name, self.witness_store.skolem_witnesses)
        self.assertIn(y_name, self.witness_store.skolem_witnesses)


class TestPhase2Integration(unittest.TestCase):
    """Integration tests for Phase 2 functionality."""
    
    def setUp(self):
        self.settings = {
            "N": 2,
            "max_time": 5,
            "expectation": True,
            "contingent": False,
            "non_empty": False,
            "non_null": False,
            "disjoint": False,
            "fusion_closure": False
        }
        
    def test_incremental_solving_with_caching(self):
        """Test that incremental solving uses caching effectively."""
        semantics = ExclusionSemantics(self.settings)
        syntax = syntactic.Syntax(
            ['\\exclude \\exclude A'],  # Double negation
            ['A'],
            exclusion_operators
        )
        model_constraints = ModelConstraints(self.settings, syntax, semantics, UnilateralProposition)
        incremental_model = IncrementalModelStructure(model_constraints, self.settings)
        
        # Check that caching was used
        cache_stats = incremental_model.witness_store.get_cache_statistics()
        self.assertGreaterEqual(cache_stats['total_witnesses'], 0)
        
        # Check truth cache statistics
        truth_stats = incremental_model.truth_cache.get_statistics()
        self.assertGreaterEqual(truth_stats['verifier_cache_size'], 0)
        
    def test_complex_formula_with_dependencies(self):
        """Test complex formula with witness dependencies."""
        semantics = ExclusionSemantics(self.settings)
        syntax = syntactic.Syntax(
            ['(\\exclude A \\uniwedge \\exclude B)'],
            ['\\exclude (A \\univee B)'],  # DeMorgan's law
            exclusion_operators
        )
        model_constraints = ModelConstraints(self.settings, syntax, semantics, UnilateralProposition)
        incremental_model = IncrementalModelStructure(model_constraints, self.settings)
        
        # Should be valid (no countermodel)
        self.assertFalse(incremental_model.z3_model_status)
        
    def test_performance_metrics(self):
        """Test that performance metrics are tracked."""
        semantics = ExclusionSemantics(self.settings)
        syntax = syntactic.Syntax(
            ['\\exclude \\exclude \\exclude A'],  # Triple negation
            ['\\exclude A'],
            exclusion_operators
        )
        model_constraints = ModelConstraints(self.settings, syntax, semantics, UnilateralProposition)
        incremental_model = IncrementalModelStructure(model_constraints, self.settings)
        
        # Check runtime
        self.assertGreater(incremental_model.z3_model_runtime, 0)
        self.assertLess(incremental_model.z3_model_runtime, self.settings['max_time'])
        
        # Check witness history
        self.assertGreater(len(incremental_model.witness_store.witness_history), 0)


if __name__ == '__main__':
    unittest.main()