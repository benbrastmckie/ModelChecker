"""Tests for Z3 solver state isolation between examples.

This test suite verifies that solver state isolation works correctly via
isolated_z3_context(), ensuring examples produce consistent results regardless
of execution order.

IMPORTANT: Z3 expressions (Int, Bool, etc.) are context-bound. Always create
them INSIDE isolated_z3_context() blocks so they belong to the fresh context.
"""

import unittest
import z3
import z3.z3
from model_checker.utils.context import isolated_z3_context


class TestZ3ContextIsolation(unittest.TestCase):
    """Test cases for Z3 context isolation via isolated_z3_context()."""

    def test_isolated_context_creates_fresh_context(self):
        """Test that isolated_z3_context creates a truly fresh Z3 context."""
        original_ctx = z3.z3._main_ctx
        with isolated_z3_context():
            inner_ctx = z3.z3._main_ctx
            self.assertIsNot(inner_ctx, original_ctx,
                             "Fresh context must differ from the outer context")
        self.assertIs(z3.z3._main_ctx, original_ctx,
                      "Outer context must be restored after the with block")

    def test_context_reset(self):
        """Test that the Z3 context isolation mechanism works correctly.

        Create a solver with a constraint, then verify a fresh solver in the
        next isolated block is unaffected.
        """
        with isolated_z3_context():
            solver1 = z3.Solver()
            x = z3.Int('x')
            solver1.add(x > 5)
            self.assertEqual(solver1.check(), z3.sat)

        with isolated_z3_context():
            # New context -- solver1's constraints must not be present
            solver2 = z3.Solver()
            x = z3.Int('x')
            solver2.add(x < 0)
            result = solver2.check()
            self.assertEqual(result, z3.sat)

    def test_solver_state_isolation(self):
        """Test that solver state doesn't leak between invocations.

        Variables must be created inside each isolated block because they are
        context-bound -- sharing z3.Int() objects across context boundaries
        raises Z3Exception.
        """
        with isolated_z3_context():
            x = z3.Int('x')
            solver1 = z3.Solver()
            solver1.add(x > 0)
            solver1.add(x < 10)
            result1 = solver1.check()
            self.assertEqual(result1, z3.sat)
            model1 = solver1.model()
            x_val = model1.eval(x).as_long()
            self.assertTrue(0 < x_val < 10)

        with isolated_z3_context():
            y = z3.Int('y')
            solver2 = z3.Solver()
            solver2.add(y < 0)
            result2 = solver2.check()
            self.assertEqual(result2, z3.sat)

    def test_conflicting_constraints(self):
        """Test that conflicting constraints in separate solvers don't interfere."""
        with isolated_z3_context():
            x = z3.Int('x')
            solver1 = z3.Solver()
            solver1.add(x > 0)
            result1 = solver1.check()
            self.assertEqual(result1, z3.sat)

        with isolated_z3_context():
            x = z3.Int('x')
            solver2 = z3.Solver()
            solver2.add(x < 0)
            result2 = solver2.check()
            # Despite conflict with first solver's constraint, second should be SAT
            self.assertEqual(result2, z3.sat)

    def test_solver_state_leakage_prevented(self):
        """Test that isolated_z3_context prevents state leakage between blocks.

        Variables are created inside each block because they are context-bound.
        """
        with isolated_z3_context():
            x = z3.Int('x')
            y = z3.Int('y')
            solver1 = z3.Solver()
            solver1.add(y == 2 * x)
            solver1.add(x == 5)
            result1 = solver1.check()
            self.assertEqual(result1, z3.sat)

        # After the first block the context is discarded; this block starts fresh
        with isolated_z3_context():
            x = z3.Int('x')
            y = z3.Int('y')
            solver2 = z3.Solver()
            solver2.add(y == 10)
            result2 = solver2.check()
            self.assertEqual(result2, z3.sat)

    def test_restores_context_on_exception(self):
        """Test that the original context is restored even if an exception occurs."""
        original_ctx = z3.z3._main_ctx
        try:
            with isolated_z3_context():
                raise RuntimeError("deliberate test error")
        except RuntimeError:
            pass
        self.assertIs(z3.z3._main_ctx, original_ctx,
                      "Context must be restored after exception inside with block")


if __name__ == '__main__':
    unittest.main()
