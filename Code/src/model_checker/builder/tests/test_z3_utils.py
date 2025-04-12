"""Tests for the Z3 utilities."""

import unittest
from unittest.mock import Mock, patch
import z3

from model_checker.builder.z3_utils import (
    create_difference_constraint,
    extract_model_values,
    find_next_model
)

class TestZ3Utils(unittest.TestCase):
    """Test the Z3 utilities."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create Z3 variables
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        self.variables = [self.x, self.y]
        
        # Create a model
        self.solver = z3.Solver()
        self.solver.add(self.x > 0)
        self.solver.add(self.y > 0)
        assert self.solver.check() == z3.sat
        self.model = self.solver.model()
    
    def test_create_difference_constraint_none_model(self):
        """Test creating a difference constraint with None model."""
        with self.assertRaises(ValueError) as context:
            create_difference_constraint(None, self.variables)
        self.assertTrue("Cannot create difference constraint from None model" in str(context.exception))
    
    def test_create_difference_constraint_empty_variables(self):
        """Test creating a difference constraint with empty variables list."""
        with self.assertRaises(ValueError) as context:
            create_difference_constraint(self.model, [])
        self.assertTrue("No variables provided for difference constraint" in str(context.exception))
    
    def test_create_difference_constraint_invalid_variables(self):
        """Test creating a difference constraint with invalid variables."""
        with self.assertRaises(ValueError) as context:
            create_difference_constraint(self.model, ["not", "z3", "vars"])
        self.assertTrue("No valid variables provided for difference constraint" in str(context.exception))
    
    def test_create_difference_constraint_valid(self):
        """Test creating a valid difference constraint."""
        constraint = create_difference_constraint(self.model, self.variables)
        
        # Verify constraint is a Z3 boolean expression
        self.assertTrue(isinstance(constraint, z3.BoolRef))
        
        # Verify it's an OR of not-equal expressions
        self.assertEqual(constraint.decl().name(), "or")
    
    def test_extract_model_values_none_model(self):
        """Test extracting values from None model."""
        with self.assertRaises(ValueError) as context:
            extract_model_values(None, self.variables)
        self.assertTrue("Cannot extract values from None model" in str(context.exception))
    
    def test_extract_model_values_valid(self):
        """Test extracting values from a valid model."""
        values = extract_model_values(self.model, self.variables)
        
        # Verify values are extracted
        self.assertIn("x", values)
        self.assertIn("y", values)
        
        # Values should be Z3 expressions
        self.assertTrue(isinstance(values["x"], z3.ExprRef))
        self.assertTrue(isinstance(values["y"], z3.ExprRef))
    
    def test_find_next_model_none_solver(self):
        """Test finding next model with None solver."""
        with self.assertRaises(ValueError) as context:
            find_next_model(None, self.model, self.variables)
        self.assertTrue("Solver cannot be None" in str(context.exception))
    
    def test_find_next_model_none_model(self):
        """Test finding next model with None model."""
        with self.assertRaises(ValueError) as context:
            find_next_model(self.solver, None, self.variables)
        self.assertTrue("Previous model cannot be None" in str(context.exception))

if __name__ == "__main__":
    unittest.main()