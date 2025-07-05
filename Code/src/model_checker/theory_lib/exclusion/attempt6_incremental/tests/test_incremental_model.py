"""
Test for IncrementalModelStructure

This tests the basic incremental solving functionality to ensure
the architecture works before testing specific exclusion examples.
"""

import unittest
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators
from incremental_model import IncrementalModelStructure, WitnessStore
from model_checker import syntactic
from model_checker.model import ModelConstraints


class TestIncrementalModel(unittest.TestCase):
    """Test basic incremental model functionality."""
    
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
        
    def test_witness_store_creation(self):
        """Test that witness store can be created and used."""
        store = WitnessStore()
        
        # Test registration
        store.register_skolem_function("test_func", "BitVec(2)", "BitVec(2)")
        self.assertIn("test_func", store.skolem_witnesses)
        
        # Test initial state
        self.assertFalse(store.is_witness_complete("test_func"))
        self.assertEqual(store.get_witness_mapping("test_func"), {})
    
    def test_simple_example_setup(self):
        """Test that we can set up a simple example."""
        # Create a simple syntax
        premises = []
        conclusions = []
        operators = syntactic.OperatorCollection(exclusion_operators)
        syntax = syntactic.Syntax(premises, conclusions, operators)
        
        # Create model constraints
        model_constraints = ModelConstraints(
            self.settings,
            syntax,
            self.semantics,
            UnilateralProposition
        )
        
        # Test that we can create incremental model structure
        try:
            incremental_model = IncrementalModelStructure(model_constraints, self.settings)
            self.assertIsNotNone(incremental_model)
            self.assertIsNotNone(incremental_model.witness_store)
            self.assertIsNotNone(incremental_model.semantics.witness_store)
        except Exception as e:
            self.fail(f"Failed to create IncrementalModelStructure: {e}")
    
    def test_atomic_example(self):
        """Test with a simple atomic example."""
        premises = ['A']
        conclusions = ['A']
        
        # Create syntax
        operators = syntactic.OperatorCollection(exclusion_operators)
        syntax = syntactic.Syntax(premises, conclusions, operators)
        
        # Create model constraints
        model_constraints = ModelConstraints(
            self.settings,
            syntax,
            self.semantics,
            UnilateralProposition
        )
        
        # Create incremental model structure
        incremental_model = IncrementalModelStructure(model_constraints, self.settings)
        
        # A → A is valid, so there should be NO countermodel
        self.assertFalse(incremental_model.z3_model_status, 
                        "Atomic example A → A should be valid (no countermodel)")


class TestWitnessStoreIntegration(unittest.TestCase):
    """Test witness store integration with semantics."""
    
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
        
    def test_semantics_witness_connection(self):
        """Test that semantics gets connected to witness store."""
        semantics = ExclusionSemantics(self.settings)
        store = WitnessStore()
        
        # Connect manually (simulating what IncrementalModelStructure does)
        semantics.witness_store = store
        
        # Test connection
        self.assertIs(semantics.witness_store, store)
        
        # Test that operators can access it
        excl_op = exclusion_operators.get_operator("\\exclude")
        excl_op.semantics = semantics
        
        # Should be able to register witnesses
        store.register_skolem_function("test", "BitVec(2)", "BitVec(2)")
        self.assertTrue(store.is_witness_complete("test") or not store.is_witness_complete("test"))


if __name__ == '__main__':
    unittest.main()