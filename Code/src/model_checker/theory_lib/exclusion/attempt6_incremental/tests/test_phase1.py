"""
Phase 1 tests for incremental exclusion implementation.

Tests for Phase 1 implementation focusing on:
1. Three-condition semantics implementation
2. Witness registration during constraint generation
3. No circular references in operators
4. Pure incremental constraint generation
"""

import unittest
import z3
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators, ExclusionOperator
from incremental_model import IncrementalModelStructure, WitnessStore
from model_checker import syntactic
from model_checker.model import ModelConstraints


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
        self.store.skolem_witnesses["h_sk_1"]["complete"] = True
        self.assertTrue(self.store.is_witness_complete("h_sk_1"))


class TestPhase1Architecture(unittest.TestCase):
    """Test Phase 1 architectural components."""
    
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
        
    def test_incremental_model_structure(self):
        """Test IncrementalModelStructure bypasses ModelConstraints."""
        semantics = ExclusionSemantics(self.settings)
        syntax = syntactic.Syntax(['A'], ['A'], exclusion_operators)
        model_constraints = ModelConstraints(self.settings, syntax, semantics, UnilateralProposition)
        
        # Create incremental model
        incremental_model = IncrementalModelStructure(model_constraints, self.settings)
        
        # Check components exist
        self.assertIsNotNone(incremental_model.witness_store)
        self.assertIsNotNone(incremental_model.incremental_solver)
        self.assertTrue(hasattr(incremental_model, 'solve_incrementally_pure'))
        
    def test_witness_store_has_witnesses_for(self):
        """Test has_witnesses_for method."""
        store = WitnessStore()
        
        # Register functions
        store.register_skolem_function("h1", z3.BitVecSort(2), z3.BitVecSort(2))
        store.register_skolem_function("h2", z3.BitVecSort(2), z3.BitVecSort(2))
        
        # Initially incomplete
        self.assertFalse(store.has_witnesses_for(["h1", "h2"]))
        
        # Mark as complete
        store.skolem_witnesses["h1"]["complete"] = True
        store.skolem_witnesses["h2"]["complete"] = True
        
        # Now should be complete
        self.assertTrue(store.has_witnesses_for(["h1", "h2"]))


class TestOperatorExtensions(unittest.TestCase):
    """Test operator extensions for incremental verification."""
    
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
        self.store = WitnessStore()
        
    def test_exclusion_operator_methods(self):
        """Test ExclusionOperator has required methods."""
        op = exclusion_operators.operator_dictionary["\\exclude"]
        
        # Check all required methods exist
        self.assertTrue(hasattr(op, 'true_at'))
        self.assertTrue(hasattr(op, 'extended_verify'))
        self.assertTrue(hasattr(op, 'register_witnesses'))
        self.assertTrue(hasattr(op, 'compute_verifiers'))
        self.assertTrue(hasattr(op, 'evaluate_with_witnesses'))
        self.assertTrue(hasattr(op, 'has_sufficient_witnesses'))
        
    def test_conjunction_operator_methods(self):
        """Test UniAndOperator has required methods."""
        op = exclusion_operators.operator_dictionary["\\uniwedge"]
        
        self.assertTrue(hasattr(op, 'compute_verifiers'))
        self.assertTrue(hasattr(op, 'evaluate_with_witnesses'))
        self.assertTrue(hasattr(op, 'has_sufficient_witnesses'))
        
    def test_disjunction_operator_methods(self):
        """Test UniOrOperator has required methods."""
        op = exclusion_operators.operator_dictionary["\\univee"]
        
        self.assertTrue(hasattr(op, 'compute_verifiers'))
        self.assertTrue(hasattr(op, 'evaluate_with_witnesses'))
        self.assertTrue(hasattr(op, 'has_sufficient_witnesses'))


class TestPhase1Examples(unittest.TestCase):
    """Test Phase 1 with example formulas."""
    
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
        
    def test_simple_validity(self):
        """Test simple valid and invalid formulas."""
        test_cases = [
            (['A'], ['A'], True),  # Valid
            (['A'], ['\\exclude A'], False),  # Invalid
            (['\\exclude A'], ['A'], False),  # Invalid
        ]
        
        for premises, conclusions, should_be_valid in test_cases:
            with self.subTest(premises=premises, conclusions=conclusions):
                semantics = ExclusionSemantics(self.settings)
                syntax = syntactic.Syntax(premises, conclusions, exclusion_operators)
                model_constraints = ModelConstraints(self.settings, syntax, semantics, UnilateralProposition)
                incremental_model = IncrementalModelStructure(model_constraints, self.settings)
                
                has_countermodel = incremental_model.z3_model_status
                is_valid = not has_countermodel
                
                self.assertEqual(is_valid, should_be_valid)
    
    def test_double_negation_simple_semantics(self):
        """Test double negation with current simple semantics."""
        # With simple negation semantics, ¬¬A ⊢ A should be valid
        semantics = ExclusionSemantics(self.settings)
        syntax = syntactic.Syntax(['\\exclude \\exclude A'], ['A'], exclusion_operators)
        model_constraints = ModelConstraints(self.settings, syntax, semantics, UnilateralProposition)
        incremental_model = IncrementalModelStructure(model_constraints, self.settings)
        
        # Should be valid (no countermodel)
        self.assertFalse(incremental_model.z3_model_status,
                        "Double negation should be valid with simple semantics")


if __name__ == '__main__':
    unittest.main()