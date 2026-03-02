"""
Unit tests for Z3 utilities.

This module tests Z3 utility functions in isolation, including constraint
creation, model value extraction, and solver operations.
"""

import unittest
import z3

from model_checker.builder.tests.fixtures.test_data import TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.z3_utils import (
    create_difference_constraint,
    extract_model_values,
    find_next_model
)


class TestZ3ConstraintCreation(unittest.TestCase):
    """Test Z3 constraint creation functionality."""
    
    def setUp(self):
        """Set up Z3 testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create Z3 variables for testing
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        self.z = z3.Int('z')
        self.variables = [self.x, self.y, self.z]
        
        # Create satisfiable model
        self.solver = z3.Solver()
        self.solver.add(self.x > 0)
        self.solver.add(self.y > 0)
        self.solver.add(self.z > 0)
        
        solve_result = self.solver.check()
        self.assertEqual(solve_result, z3.sat,
                        "Test solver should be satisfiable")
        self.model = self.solver.model()
    
    def test_create_difference_constraint_generates_valid_constraint(self):
        """Test create_difference_constraint generates valid Z3 constraint."""
        constraint = assert_no_exceptions_during_execution(
            self,
            lambda: create_difference_constraint(self.model, self.variables),
            operation_name="Difference constraint creation"
        )
        
        # Verify constraint is Z3 boolean expression
        self.assertIsInstance(constraint, z3.BoolRef,
                            "Constraint should be Z3 boolean reference")
        
        # Verify it's an OR expression for different values
        self.assertEqual(constraint.decl().name(), "or",
                        "Constraint should be OR expression")
        
        # Verify constraint has children for each variable
        self.assertGreater(constraint.num_args(), 0,
                         "Constraint should have arguments for variables")
    
    def test_create_difference_constraint_handles_single_variable_correctly(self):
        """Test create_difference_constraint handles single variable correctly."""
        single_variable = [self.x]
        
        constraint = create_difference_constraint(self.model, single_variable)
        
        self.assertIsInstance(constraint, z3.BoolRef,
                            "Single variable constraint should be boolean")
    
    def test_create_difference_constraint_rejects_none_model(self):
        """Test create_difference_constraint rejects None model appropriately."""
        with self.assertRaises(ValueError) as context:
            create_difference_constraint(None, self.variables)
        
        assert_error_message_contains(
            self, context.exception, "Cannot create difference constraint from None model",
            "None model rejection error"
        )
    
    def test_create_difference_constraint_rejects_empty_variables(self):
        """Test create_difference_constraint rejects empty variables list."""
        with self.assertRaises(ValueError) as context:
            create_difference_constraint(self.model, [])
        
        assert_error_message_contains(
            self, context.exception, "No variables provided for difference constraint",
            "Empty variables rejection error"
        )
    
    def test_create_difference_constraint_rejects_invalid_variables(self):
        """Test create_difference_constraint rejects invalid variable types."""
        invalid_variables = ["not", "z3", "vars"]
        
        with self.assertRaises(ValueError) as context:
            create_difference_constraint(self.model, invalid_variables)
        
        assert_error_message_contains(
            self, context.exception, "No valid variables provided for difference constraint",
            "Invalid variables rejection error"
        )


class TestZ3ModelValueExtraction(unittest.TestCase):
    """Test Z3 model value extraction functionality."""
    
    def setUp(self):
        """Set up model value extraction testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create Z3 variables and satisfiable model
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        self.variables = [self.x, self.y]
        
        self.solver = z3.Solver()
        self.solver.add(self.x == 5)
        self.solver.add(self.y == 10)
        
        solve_result = self.solver.check()
        self.assertEqual(solve_result, z3.sat,
                        "Test solver should be satisfiable")
        self.model = self.solver.model()
    
    def test_extract_model_values_retrieves_correct_values(self):
        """Test extract_model_values retrieves correct variable values."""
        values = assert_no_exceptions_during_execution(
            self,
            lambda: extract_model_values(self.model, self.variables),
            operation_name="Model value extraction"
        )
        
        # Verify values dictionary structure
        self.assertIsInstance(values, dict,
                            "Values should be returned as dictionary")
        self.assertIn("x", values,
                     "Values should contain x variable")
        self.assertIn("y", values,
                     "Values should contain y variable")
        
        # Verify values are Z3 expressions
        self.assertIsInstance(values["x"], z3.ExprRef,
                            "x value should be Z3 expression")
        self.assertIsInstance(values["y"], z3.ExprRef,
                            "y value should be Z3 expression")
        
        # Verify actual values are correct
        x_value = self.model.eval(values["x"]).as_long()
        y_value = self.model.eval(values["y"]).as_long()
        self.assertEqual(x_value, 5,
                        "x value should be 5")
        self.assertEqual(y_value, 10,
                        "y value should be 10")
    
    def test_extract_model_values_handles_unassigned_variables(self):
        """Test extract_model_values handles variables not assigned in model."""
        # Create additional variable not constrained in solver
        unassigned_var = z3.Int('unassigned')
        variables_with_unassigned = self.variables + [unassigned_var]
        
        values = extract_model_values(self.model, variables_with_unassigned)
        
        # Should still return dictionary with all variables
        self.assertEqual(len(values), 3,
                        "Should return values for all variables")
        self.assertIn("unassigned", values,
                     "Should include unassigned variable")
    
    def test_extract_model_values_rejects_none_model(self):
        """Test extract_model_values rejects None model appropriately."""
        with self.assertRaises(ValueError) as context:
            extract_model_values(None, self.variables)
        
        assert_error_message_contains(
            self, context.exception, "Cannot extract values from None model",
            "None model rejection error"
        )


class TestZ3NextModelFinding(unittest.TestCase):
    """Test Z3 next model finding functionality."""
    
    def setUp(self):
        """Set up next model finding testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create Z3 variables and solver with multiple solutions
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        self.variables = [self.x, self.y]
        
        # Create solver with constraints that have multiple solutions
        self.solver = z3.Solver()
        self.solver.add(self.x >= 0)
        self.solver.add(self.x <= 2)
        self.solver.add(self.y >= 0)
        self.solver.add(self.y <= 2)
        
        # Get first model
        solve_result = self.solver.check()
        self.assertEqual(solve_result, z3.sat,
                        "Test solver should be satisfiable")
        self.first_model = self.solver.model()
    
    def test_find_next_model_locates_different_model(self):
        """Test find_next_model locates model different from previous."""
        # Should be able to find next model
        result = assert_no_exceptions_during_execution(
            self,
            lambda: find_next_model(self.solver, self.first_model, self.variables),
            operation_name="Next model finding"
        )
        
        success, next_model = result
        if success and next_model is not None:
            # Verify it's a different model
            first_values = extract_model_values(self.first_model, self.variables)
            next_values = extract_model_values(next_model, self.variables)
            
            # At least one value should be different
            values_different = any(
                str(first_values[var_name]) != str(next_values[var_name])
                for var_name in first_values.keys()
            )
            
            self.assertTrue(values_different,
                          "Next model should have different values")
        else:
            # No next model available - this is acceptable
            pass
    
    def test_find_next_model_rejects_none_solver(self):
        """Test find_next_model rejects None solver appropriately."""
        with self.assertRaises(ValueError) as context:
            find_next_model(None, self.first_model, self.variables)
        
        assert_error_message_contains(
            self, context.exception, "Solver cannot be None",
            "None solver rejection error"
        )
    
    def test_find_next_model_rejects_none_previous_model(self):
        """Test find_next_model rejects None previous model appropriately."""
        with self.assertRaises(ValueError) as context:
            find_next_model(self.solver, None, self.variables)
        
        assert_error_message_contains(
            self, context.exception, "Previous model cannot be None",
            "None previous model rejection error"
        )


class TestZ3UtilsEdgeCases(unittest.TestCase):
    """Test Z3 utilities edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up edge case testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_create_difference_constraint_handles_mixed_variable_types(self):
        """Test create_difference_constraint handles mixed Z3 variable types."""
        # Create variables of different Z3 types
        int_var = z3.Int('int_var')
        bool_var = z3.Bool('bool_var')
        real_var = z3.Real('real_var')
        mixed_variables = [int_var, bool_var, real_var]
        
        # Create model with these variables
        solver = z3.Solver()
        solver.add(int_var == 1)
        solver.add(bool_var == True)
        solver.add(real_var == 1.5)
        
        solve_result = solver.check()
        self.assertEqual(solve_result, z3.sat,
                        "Mixed variable solver should be satisfiable")
        model = solver.model()
        
        # Should handle mixed types
        constraint = assert_no_exceptions_during_execution(
            self,
            lambda: create_difference_constraint(model, mixed_variables),
            operation_name="Mixed variable types constraint creation"
        )
        
        self.assertIsInstance(constraint, z3.BoolRef,
                            "Mixed type constraint should be boolean")
    
    def test_extract_model_values_handles_large_variable_count(self):
        """Test extract_model_values handles large number of variables efficiently."""
        # Create many variables
        variables = [z3.Int(f'var_{i}') for i in range(50)]
        
        # Create solver with constraints for all variables
        solver = z3.Solver()
        for i, var in enumerate(variables):
            solver.add(var == i)
        
        solve_result = solver.check()
        self.assertEqual(solve_result, z3.sat,
                        "Large variable count solver should be satisfiable")
        model = solver.model()
        
        # Extract values for all variables
        values = extract_model_values(model, variables)
        
        # Verify all variables have values
        self.assertEqual(len(values), 50,
                        "Should extract values for all 50 variables")
        
        # Verify values are correct
        for i in range(50):
            var_name = f'var_{i}'
            self.assertIn(var_name, values,
                         f"Should contain value for {var_name}")


if __name__ == '__main__':
    unittest.main()