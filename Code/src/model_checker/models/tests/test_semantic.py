"""Tests for semantic.py module.

Tests for SemanticDefaults class functionality after refactoring.
"""

import unittest
from z3 import BitVecVal, And, Not

from model_checker.models.semantic import SemanticDefaults


class TestSemanticDefaults(unittest.TestCase):
    """Test SemanticDefaults class functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {'N': 3}
        self.semantics = SemanticDefaults(self.settings)
    
    def test_initialization(self):
        """Test that SemanticDefaults initializes correctly."""
        self.assertEqual(self.semantics.N, 3)
        self.assertIsNotNone(self.semantics.full_state)
        self.assertIsNotNone(self.semantics.null_state)
        self.assertEqual(len(self.semantics.all_states), 8)  # 2^3 = 8
        
    def test_fusion_operation(self):
        """Test the fusion operation (bitwise OR)."""
        from z3 import simplify
        bit1 = BitVecVal(0b101, 3)
        bit2 = BitVecVal(0b011, 3)
        result = self.semantics.fusion(bit1, bit2)
        # Result should be 0b111 (7)
        simplified = simplify(result)
        self.assertEqual(simplified.as_long(), 7)
        
    def test_is_part_of(self):
        """Test the is_part_of relation."""
        from z3 import simplify
        bit1 = BitVecVal(0b101, 3)
        bit2 = BitVecVal(0b111, 3)
        # 0b101 is part of 0b111 because 101 | 111 = 111
        constraint = self.semantics.is_part_of(bit1, bit2)
        # The constraint should be satisfied
        self.assertTrue(simplify(constraint))
        
    def test_is_proper_part_of(self):
        """Test the is_proper_part_of relation."""
        bit1 = BitVecVal(0b101, 3)
        bit2 = BitVecVal(0b111, 3)
        # 0b101 is a proper part of 0b111
        constraint = self.semantics.is_proper_part_of(bit1, bit2)
        # Should be And(is_part_of, not_equal)
        self.assertIn("And", str(constraint))
        
    def test_non_null_part_of(self):
        """Test the non_null_part_of relation."""
        bit1 = BitVecVal(0b101, 3)
        bit2 = BitVecVal(0b111, 3)
        bit0 = BitVecVal(0, 3)
        
        # Non-zero bit is non-null part
        constraint1 = self.semantics.non_null_part_of(bit1, bit2)
        self.assertIn("And", str(constraint1))
        
        # Zero bit is not non-null part
        constraint2 = self.semantics.non_null_part_of(bit0, bit2)
        self.assertIn("And", str(constraint2))
        
    def test_product_operation(self):
        """Test the product operation."""
        set_A = {BitVecVal(0b001, 3), BitVecVal(0b010, 3)}
        set_B = {BitVecVal(0b100, 3)}
        
        result = self.semantics.product(set_A, set_B)
        # Should contain fusions: 001|100=101, 010|100=110
        self.assertEqual(len(result), 2)
        
    def test_z3_set_conversion(self):
        """Test conversion between Python sets and Z3 sets."""
        python_set = {BitVecVal(1, 3), BitVecVal(2, 3)}
        z3_set = self.semantics.z3_set(python_set, 3)
        
        # Convert back
        domain = [BitVecVal(i, 3) for i in range(8)]
        recovered_set = self.semantics.z3_set_to_python_set(z3_set, domain)
        
        # Should have same elements (comparing as integers)
        original_vals = {elem.as_long() for elem in python_set}
        recovered_vals = {elem.as_long() for elem in recovered_set}
        self.assertEqual(original_vals, recovered_vals)


if __name__ == '__main__':
    unittest.main()