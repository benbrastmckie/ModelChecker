"""
Basic tests for witness array exclusion implementation.

These tests verify that the basic infrastructure works correctly,
even if the fundamental Skolem function limitation persists.
"""

import sys
import os
import unittest

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))

from semantic import WitnessArraySemantics
from operators import create_operators


class TestWitnessArrayInfrastructure(unittest.TestCase):
    """Test basic witness array infrastructure."""
    
    def setUp(self):
        """Set up test semantics."""
        settings = {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
        }
        self.semantics = WitnessArraySemantics(settings)
        self.operators = create_operators(self.semantics)
    
    def test_semantics_creation(self):
        """Test that witness array semantics can be created."""
        self.assertIsInstance(self.semantics, WitnessArraySemantics)
        self.assertEqual(self.semantics.N, 3)
        self.assertEqual(self.semantics.counter, 0)
        self.assertEqual(self.semantics.array_counter, 0)
        self.assertEqual(len(self.semantics.witness_arrays), 0)
    
    def test_operators_creation(self):
        """Test that operators can be created."""
        self.assertIsNotNone(self.operators)
        self.assertIn('\\exclude', self.operators.operators)
        self.assertIn('\\uniwedge', self.operators.operators)
        self.assertIn('\\univee', self.operators.operators)
    
    def test_witness_array_creation(self):
        """Test that witness arrays can be created."""
        array_id = 1
        h_array, y_array = self.semantics.create_witness_arrays(array_id)
        
        self.assertIsNotNone(h_array)
        self.assertIsNotNone(y_array)
        # Arrays should have the correct names
        self.assertTrue(str(h_array).startswith('h_array_1'))
        self.assertTrue(str(y_array).startswith('y_array_1'))
    
    def test_witness_array_storage(self):
        """Test that witness arrays can be stored and retrieved."""
        array_id = 1
        h_array, y_array = self.semantics.create_witness_arrays(array_id)
        
        # Mock argument and state (would normally be sentences/bitvecs)
        argument = "mock_argument"
        state = "mock_state"
        
        self.semantics.store_witness_arrays(array_id, h_array, y_array, argument, state)
        
        # Check storage
        self.assertIn(array_id, self.semantics.witness_arrays)
        stored = self.semantics.witness_arrays[array_id]
        self.assertEqual(stored['h_array'], h_array)
        self.assertEqual(stored['y_array'], y_array)
        self.assertEqual(stored['argument'], argument)
        self.assertEqual(stored['state'], state)
        self.assertEqual(stored['array_id'], array_id)
    
    def test_frame_constraints(self):
        """Test that frame constraints are properly defined."""
        self.assertIsInstance(self.semantics.frame_constraints, list)
        self.assertGreater(len(self.semantics.frame_constraints), 0)
        
        # Should have basic constraints
        constraint_strs = [str(c) for c in self.semantics.frame_constraints]
        # Check for some key constraint patterns (names may vary)
        has_exclusion_constraint = any('excludes' in s for s in constraint_strs)
        self.assertTrue(has_exclusion_constraint, "Should have exclusion-related constraints")


class TestWitnessArrayOperators(unittest.TestCase):
    """Test witness array operators."""
    
    def setUp(self):
        """Set up test semantics and operators."""
        settings = {
            'N': 3,
            'possible': False,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'fusion_closure': False,
            'max_time': 5,
        }
        self.semantics = WitnessArraySemantics(settings)
        self.operators = create_operators(self.semantics)
        self.exclusion_op = self.operators.operators['\\exclude']
    
    def test_exclusion_operator_properties(self):
        """Test basic properties of the exclusion operator."""
        self.assertEqual(self.exclusion_op.name, '\\exclude')
        self.assertEqual(self.exclusion_op.arity, 1)
        self.assertEqual(self.exclusion_op.semantics, self.semantics)
    
    def test_operator_methods_exist(self):
        """Test that required operator methods exist."""
        self.assertTrue(hasattr(self.exclusion_op, 'true_at'))
        self.assertTrue(hasattr(self.exclusion_op, 'extended_verify'))
        self.assertTrue(hasattr(self.exclusion_op, 'find_verifiers'))
        self.assertTrue(hasattr(self.exclusion_op, 'print_method'))


if __name__ == '__main__':
    unittest.main()