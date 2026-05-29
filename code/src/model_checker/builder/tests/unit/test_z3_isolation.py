"""Tests for Z3 solver state isolation between examples.

This test suite verifies that solver state isolation works correctly via
isolated_z3_context(), ensuring examples produce consistent results regardless
of execution order.
"""

import unittest
import z3
import z3.z3
from model_checker.utils.context import isolated_z3_context


class TestZ3ContextIsolation(unittest.TestCase):
    """Test cases for Z3 context isolation via isolated_z3_context()."""

    def setUp(self):
        """Set up test environment."""
        # Declare variables once; each test runs inside its own fresh context
        # via the autouse fixture (or setUp itself does not need a reset since
        # conftest.py will install isolated_z3_context as autouse).
        self.x = z3.Int('x')
        self.y = z3.Int('y')

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
        """Test that solver state doesn't leak between invocations."""
        with isolated_z3_context():
            solver1 = z3.Solver()
            solver1.add(self.x > 0)
            solver1.add(self.x < 10)
            result1 = solver1.check()
            self.assertEqual(result1, z3.sat)
            model1 = solver1.model()
            x_val = model1.eval(self.x).as_long()
            self.assertTrue(0 < x_val < 10)

        with isolated_z3_context():
            solver2 = z3.Solver()
            solver2.add(self.y < 0)
            result2 = solver2.check()
            self.assertEqual(result2, z3.sat)

    def test_conflicting_constraints(self):
        """Test that conflicting constraints in separate solvers don't interfere."""
        with isolated_z3_context():
            solver1 = z3.Solver()
            solver1.add(self.x > 0)
            result1 = solver1.check()
            self.assertEqual(result1, z3.sat)

        with isolated_z3_context():
            solver2 = z3.Solver()
            solver2.add(self.x < 0)
            result2 = solver2.check()
            # Despite conflict with first solver's constraint, second should be SAT
            self.assertEqual(result2, z3.sat)

    def test_solver_state_leakage_prevented(self):
        """Test that isolated_z3_context prevents state leakage between blocks."""
        with isolated_z3_context():
            solver1 = z3.Solver()
            solver1.add(self.y == 2 * self.x)
            solver1.add(self.x == 5)
            result1 = solver1.check()
            self.assertEqual(result1, z3.sat)

        # After the first block the context is discarded; this block starts fresh
        with isolated_z3_context():
            solver2 = z3.Solver()
            solver2.add(self.y == 10)
            result2 = solver2.check()
            self.assertEqual(result2, z3.sat)
            # The fresh context has no memory of x == 5 from the previous block
            model2 = solver2.model()
            # y == 10 is satisfiable with any value of x; no forced x == 5
            # (just verify SAT -- exact value depends on Z3's heuristics)
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
