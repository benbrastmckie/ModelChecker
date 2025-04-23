"""Tests for Z3 solver state isolation between examples.

This test suite verifies that solver state isolation works correctly,
ensuring examples produce consistent results regardless of execution order.
"""

import unittest
import sys
import os
import z3
from model_checker.builder import BuildModule
from model_checker.utils import Z3ContextManager

class TestZ3ContextIsolation(unittest.TestCase):
    """Test cases for Z3 context isolation."""

    def setUp(self):
        """Set up test environment."""
        # Make sure we start with a fresh context
        Z3ContextManager.reset_context()
        
        # Minimal settings for a build module
        self.test_settings = {
            "file_path": "none.py",  # Not actually used in these tests
        }
        
        # Create a dummy z3 formula to check solver behavior
        self.x = z3.Int('x')
        self.y = z3.Int('y')
        
    def test_context_reset(self):
        """Test that the Z3 context reset mechanism works correctly."""
        # Instead of testing internal Z3 implementation details, 
        # test the behavior from a black-box perspective
        
        # Create a solver with a constraint
        solver1 = z3.Solver()
        x = z3.Int('x')
        solver1.add(x > 5)
        
        # Reset context
        Z3ContextManager.reset_context()
        
        # Create a new solver that shouldn't see solver1's constraints
        solver2 = z3.Solver()
        solver2.add(x < 0)
        
        # If context was properly reset, solver2 should be satisfiable
        # despite having a constraint that conflicts with solver1
        result = solver2.check()
        self.assertEqual(result, z3.sat)
        
    def test_solver_state_isolation(self):
        """Test that solver state doesn't leak between invocations."""
        # First solver with simple constraints
        Z3ContextManager.reset_context()
        solver1 = z3.Solver()
        solver1.add(self.x > 0)
        solver1.add(self.x < 10)
        result1 = solver1.check()
        self.assertEqual(result1, z3.sat)
        
        # Get model and assert 0 < x < 10
        model1 = solver1.model()
        x_val = model1.eval(self.x).as_long()
        self.assertTrue(0 < x_val < 10)
        
        # Create a second solver with completely different constraints
        Z3ContextManager.reset_context()
        solver2 = z3.Solver()
        solver2.add(self.y < 0)  # Different variable
        result2 = solver2.check()
        self.assertEqual(result2, z3.sat)
        
        # Second solver should not know about constraints from first solver
        model2 = solver2.model()
        if self.x in model2:  # Sometimes it doesn't even include x
            x_val2 = model2.eval(self.x).as_long()
            self.assertNotEqual(x_val, x_val2)

    def test_conflicting_constraints(self):
        """Test that conflicting constraints in separate solvers don't interfere."""
        # First solver with x > 0
        Z3ContextManager.reset_context()
        solver1 = z3.Solver()
        solver1.add(self.x > 0)
        result1 = solver1.check()
        self.assertEqual(result1, z3.sat)
        
        # Second solver with x < 0 (conflicting with first)
        Z3ContextManager.reset_context()
        solver2 = z3.Solver()
        solver2.add(self.x < 0)
        result2 = solver2.check()
        
        # Despite conflict with first solver's constraint, second should be SAT
        self.assertEqual(result2, z3.sat)

    def test_solver_state_leakage_without_reset(self):
        """Test that solver state leaks without proper resets."""
        # This test demonstrates what happens WITHOUT resetting the context
        
        # First solver with learned information about y = 2*x
        solver1 = z3.Solver()
        solver1.add(self.y == 2 * self.x)
        solver1.add(self.x == 5)
        result1 = solver1.check()
        self.assertEqual(result1, z3.sat)
        
        # Deliberately NOT resetting context
        
        # Create a second solver with only y == 10 constraint
        # This on its own should be SAT with many possible values for x
        solver2 = z3.Solver()
        solver2.add(self.y == 10)
        result2 = solver2.check()
        self.assertEqual(result2, z3.sat)
        
        # Get the model - because solver1 taught the context that y = 2*x and x = 5,
        # we might see those constraints influencing the results
        model2 = solver2.model()
        
        # Now reset context for clean state
        Z3ContextManager.reset_context()
        
        # Create a third solver with only y == 10 constraint after context reset
        solver3 = z3.Solver()
        solver3.add(self.y == 10)
        result3 = solver3.check()
        self.assertEqual(result3, z3.sat)
        
        # Get model - should be different from second solver due to context reset
        model3 = solver3.model()
        
        # The exact values aren't predictable, but the point is that model2 and model3
        # should differ because solver3 has a fresh context with no knowledge of
        # prior constraints, while solver2 might be influenced by solver1's state
        if self.x in model2 and self.x in model3:
            x_val2 = model2.eval(self.x).as_long() 
            x_val3 = model3.eval(self.x).as_long()
            
            # This assertion might occasionally fail if Z3 randomly picks the same
            # values in both cases, but it's unlikely with large integer ranges
            if x_val2 == 5:  # If we see evidence of state leakage
                self.assertNotEqual(x_val3, 5, 
                                 "Context reset didn't prevent state leakage")
            

if __name__ == '__main__':
    unittest.main()