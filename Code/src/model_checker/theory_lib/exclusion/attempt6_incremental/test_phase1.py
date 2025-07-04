"""
Phase 1 Tests: Core incremental infrastructure.

Tests the WitnessStore, TruthCache, and IncrementalVerifier components
in isolation before integrating with exclusion semantics.
"""

import z3
import unittest
from unittest.mock import Mock, MagicMock

from incremental_core import (
    WitnessStore, 
    TruthCache, 
    IncrementalVerifier,
    ThreeLevelIntegrator
)


class TestWitnessStore(unittest.TestCase):
    """Test the WitnessStore component."""
    
    def setUp(self):
        self.store = WitnessStore()
        
    def test_register_skolem_function(self):
        """Test registering a Skolem function."""
        # Register a function from BitVec(8) to BitVec(8)
        domain = z3.BitVecSort(8)
        codomain = z3.BitVecSort(8) 
        
        func = self.store.register_skolem_function("h_sk", domain, codomain)
        
        # Check function was created
        self.assertIsInstance(func, z3.FuncDeclRef)
        self.assertEqual(str(func), "h_sk")
        
        # Check witness info was stored
        self.assertIn("h_sk", self.store.skolem_witnesses)
        witness_info = self.store.skolem_witnesses["h_sk"]
        self.assertEqual(witness_info['domain_sort'], domain)
        self.assertEqual(witness_info['codomain_sort'], codomain)
        self.assertEqual(witness_info['values'], {})
        self.assertFalse(witness_info['complete'])
        
    def test_update_witness_values(self):
        """Test extracting witness values from a model."""
        # Create a simple Z3 model
        domain = z3.BitVecSort(2)  # 4 possible values
        codomain = z3.BitVecSort(2)
        
        h_sk = self.store.register_skolem_function("h_sk", domain, codomain)
        
        # Create constraints and solve
        solver = z3.Solver()
        x = z3.BitVec('x', 2)
        # Constrain h_sk(0) = 1, h_sk(1) = 2
        solver.add(h_sk(z3.BitVecVal(0, 2)) == z3.BitVecVal(1, 2))
        solver.add(h_sk(z3.BitVecVal(1, 2)) == z3.BitVecVal(2, 2))
        
        self.assertEqual(solver.check(), z3.sat)
        model = solver.model()
        
        # Update witness values
        self.store.update_witness_values(model)
        
        # Check extracted values
        mapping = self.store.get_witness_mapping("h_sk")
        self.assertIn(0, mapping)
        self.assertIn(1, mapping)
        
    def test_witness_dependencies(self):
        """Test tracking dependencies between witnesses."""
        self.store.add_witness_dependency("h_sk_1", "h_sk_0")
        self.store.add_witness_dependency("h_sk_2", "h_sk_1")
        
        self.assertIn("h_sk_1", self.store.witness_dependencies)
        self.assertEqual(self.store.witness_dependencies["h_sk_1"], {"h_sk_0"})
        self.assertEqual(self.store.witness_dependencies["h_sk_2"], {"h_sk_1"})
        
    def test_unique_witness_names(self):
        """Test generating unique witness names."""
        name1 = self.store.generate_unique_witness_name("h_sk")
        name2 = self.store.generate_unique_witness_name("h_sk")
        name3 = self.store.generate_unique_witness_name("y_sk")
        
        self.assertNotEqual(name1, name2)
        self.assertNotEqual(name1, name3)
        self.assertNotEqual(name2, name3)


class TestTruthCache(unittest.TestCase):
    """Test the TruthCache component."""
    
    def setUp(self):
        # Create mock semantics
        self.semantics = Mock()
        self.semantics.N = 2  # 4 states total
        self.semantics.is_part_of = Mock(return_value=True)
        self.semantics.verify = Mock(return_value=z3.BoolVal(True))
        
        self.cache = TruthCache(self.semantics)
        self.witness_store = WitnessStore()
        
    def test_all_states(self):
        """Test computing all states."""
        states = self.cache.all_states
        self.assertEqual(states, {0, 1, 2, 3})
        
    def test_compute_atomic_verifiers(self):
        """Test computing verifiers for atomic sentences."""
        # Create mock atomic sentence
        sentence = Mock()
        sentence.sentence_letter = 'A'
        sentence.operator = None
        sentence.arguments = []
        
        # Mock verify to return True for states 0 and 2
        def mock_verify(state, letter):
            state_val = z3.simplify(state).as_long() if hasattr(z3.simplify(state), 'as_long') else 0
            return z3.BoolVal(state_val in [0, 2])
            
        self.semantics.verify = mock_verify
        
        verifiers = self.cache.compute_atomic_verifiers(sentence)
        self.assertEqual(verifiers, {0, 2})
        
    def test_verifier_caching(self):
        """Test that verifiers are cached properly."""
        # Create mock sentence
        sentence = Mock()
        sentence.sentence_letter = 'A'
        sentence.operator = None
        sentence.arguments = []
        
        # First call computes verifiers
        verifiers1 = self.cache.get_verifiers(sentence, self.witness_store)
        
        # Second call should use cache
        verifiers2 = self.cache.get_verifiers(sentence, self.witness_store)
        
        self.assertEqual(verifiers1, verifiers2)
        self.assertIn(id(sentence), self.cache.verifier_cache)
        
    def test_dependency_tracking(self):
        """Test dependency tracking and invalidation."""
        # Add some dependencies
        self.cache.add_dependency("formula1", "formula2")
        self.cache.add_dependency("formula1", "formula3")
        
        # Add some cached values
        self.cache.verifier_cache["formula1"] = Mock(complete=True)
        self.cache.partial_truths["formula1_0"] = True
        
        # Invalidate formula2
        self.cache.invalidate_dependents("formula2")
        
        # Check formula1 was invalidated
        self.assertFalse(self.cache.verifier_cache["formula1"].complete)
        self.assertNotIn("formula1_0", self.cache.partial_truths)


class TestIncrementalVerifier(unittest.TestCase):
    """Test the IncrementalVerifier component."""
    
    def setUp(self):
        # Create mock semantics
        self.semantics = Mock()
        self.semantics.N = 2
        self.semantics.true_at = Mock(return_value=z3.BoolVal(True))
        self.semantics.is_part_of = Mock(return_value=True)
        self.semantics.get_background_constraints = Mock(return_value=None)
        
        self.verifier = IncrementalVerifier(self.semantics)
        
    def test_verify_atomic_sentence(self):
        """Test verifying an atomic sentence."""
        # Create atomic sentence
        sentence = Mock()
        sentence.sentence_letter = 'A' 
        sentence.operator = None
        sentence.arguments = []
        
        eval_point = {'world': z3.BitVecVal(0, 2)}
        
        # Mock operator methods
        sentence.operator = None
        
        result = self.verifier.verify_incrementally(sentence, eval_point)
        
        # Should have called true_at
        self.semantics.true_at.assert_called_once()
        
    def test_constraint_stacking(self):
        """Test that constraints are tracked properly."""
        # Create sentence
        sentence = Mock()
        sentence.sentence_letter = 'A'
        sentence.operator = None
        sentence.arguments = []
        
        eval_point = {'world': z3.BitVecVal(0, 2)}
        
        # Verify
        self.verifier.verify_incrementally(sentence, eval_point)
        
        # Check constraints were stacked
        self.assertGreater(len(self.verifier.constraint_stack), 0)
        constraint, context = self.verifier.constraint_stack[0]
        self.assertIn("truth", context)
        
    def test_reset(self):
        """Test resetting verifier state."""
        # Add some constraints
        self.verifier.solver.add(z3.BoolVal(True))
        self.verifier.constraint_stack.append((z3.BoolVal(True), "test"))
        self.verifier.processed_formulas.add("formula1")
        
        # Reset
        self.verifier.reset()
        
        # Check state was cleared
        self.assertEqual(len(self.verifier.constraint_stack), 0)
        self.assertEqual(len(self.verifier.processed_formulas), 0)
        # New solver instance
        self.assertIsInstance(self.verifier.solver, z3.Solver)


class TestThreeLevelIntegrator(unittest.TestCase):
    """Test the high-level ThreeLevelIntegrator."""
    
    def setUp(self):
        # Create mock semantics
        self.semantics = Mock()
        self.semantics.N = 2
        self.semantics.true_at = Mock(return_value=z3.BoolVal(True))
        self.semantics.is_part_of = Mock(return_value=True)
        self.semantics.get_background_constraints = Mock(return_value=None)
        
        self.integrator = ThreeLevelIntegrator(self.semantics)
        
    def test_check_formula(self):
        """Test the main check_formula interface."""
        # Create sentence
        sentence = Mock()
        sentence.sentence_letter = 'A'
        sentence.operator = None
        sentence.arguments = []
        
        eval_point = {'world': z3.BitVecVal(0, 2)}
        
        result = self.integrator.check_formula(sentence, eval_point)
        
        # Should return a boolean
        self.assertIsInstance(result, bool)
        
    def test_find_countermodel(self):
        """Test finding a countermodel."""
        # Create sentence that's false at world 2
        sentence = Mock()
        sentence.sentence_letter = 'A'
        sentence.operator = None
        sentence.arguments = []
        
        # Mock to return false for world 2
        def mock_verify(sent, eval_pt):
            world_val = z3.simplify(eval_pt['world']).as_long()
            return world_val != 2
            
        self.integrator.check_formula = mock_verify
        
        countermodel = self.integrator.find_countermodel(sentence)
        
        # Should find world 2 as countermodel
        self.assertIsNotNone(countermodel)
        self.assertEqual(z3.simplify(countermodel['world']).as_long(), 2)
        
    def test_witness_info_access(self):
        """Test accessing witness information."""
        # Register a witness
        self.integrator.witness_store.register_skolem_function(
            "h_sk", z3.BitVecSort(2), z3.BitVecSort(2)
        )
        
        info = self.integrator.get_witness_info("h_sk")
        
        self.assertEqual(info['name'], "h_sk")
        self.assertIn('values', info)
        self.assertIn('complete', info)
        self.assertIn('dependencies', info)


if __name__ == '__main__':
    # Run tests
    unittest.main(verbosity=2)