"""Tests for solver equivalence between Z3 and cvc5.

These tests verify that both backends produce equivalent results.
They are skipped when cvc5 is not installed.
"""

import pytest

from model_checker.solver import detect_cvc5, create_solver, SolverResult
from model_checker.solver.registry import set_cli_backend, clear_cli_backend, reset_registry


# Skip all tests in this module if cvc5 is not available
pytestmark = pytest.mark.skipif(
    not detect_cvc5(),
    reason="cvc5 not installed"
)


@pytest.fixture(autouse=True)
def reset_state():
    """Reset registry state before and after each test."""
    reset_registry()
    yield
    reset_registry()


@pytest.fixture
def z3_solver():
    """Create a Z3 solver."""
    set_cli_backend("z3")
    return create_solver()


@pytest.fixture
def cvc5_solver():
    """Create a cvc5 solver."""
    set_cli_backend("cvc5")
    return create_solver()


class TestBasicEquivalence:
    """Basic equivalence tests between Z3 and cvc5."""

    def test_simple_sat_equivalence(self, z3_solver, cvc5_solver):
        """Both solvers should find sat for simple satisfiable constraint."""
        import z3
        from cvc5.pythonic import BitVec as CVC5BitVec

        # Z3
        z3_x = z3.BitVec("x", 8)
        z3_solver.add(z3_x > 5)
        z3_result = z3_solver.check()

        # cvc5
        cvc5_x = CVC5BitVec("x", 8)
        cvc5_solver.add(cvc5_x > 5)
        cvc5_result = cvc5_solver.check()

        assert SolverResult.is_sat(z3_result)
        assert SolverResult.is_sat(cvc5_result)

    def test_simple_unsat_equivalence(self, z3_solver, cvc5_solver):
        """Both solvers should detect unsat for contradictory constraints."""
        import z3
        from cvc5.pythonic import BitVec as CVC5BitVec

        # Z3
        z3_x = z3.BitVec("x", 8)
        z3_solver.add(z3_x > 10)
        z3_solver.add(z3_x < 5)
        z3_result = z3_solver.check()

        # cvc5
        cvc5_x = CVC5BitVec("x", 8)
        cvc5_solver.add(cvc5_x > 10)
        cvc5_solver.add(cvc5_x < 5)
        cvc5_result = cvc5_solver.check()

        assert SolverResult.is_unsat(z3_result)
        assert SolverResult.is_unsat(cvc5_result)


class TestBitvectorEquivalence:
    """Bitvector operation equivalence tests."""

    def test_bitvec_arithmetic(self, z3_solver, cvc5_solver):
        """Both solvers should handle bitvector arithmetic equivalently."""
        import z3
        from cvc5.pythonic import BitVec as CVC5BitVec

        # Z3
        z3_x = z3.BitVec("x", 8)
        z3_y = z3.BitVec("y", 8)
        z3_solver.add(z3_x + z3_y == 100)
        z3_solver.add(z3_x == 40)
        z3_result = z3_solver.check()

        # cvc5
        cvc5_x = CVC5BitVec("x", 8)
        cvc5_y = CVC5BitVec("y", 8)
        cvc5_solver.add(cvc5_x + cvc5_y == 100)
        cvc5_solver.add(cvc5_x == 40)
        cvc5_result = cvc5_solver.check()

        assert SolverResult.is_sat(z3_result)
        assert SolverResult.is_sat(cvc5_result)

        # Check model values
        z3_model = z3_solver.model()
        cvc5_model = cvc5_solver.model()

        z3_y_val = z3_model.eval(z3_y).as_long()
        # cvc5 model access may differ slightly
        try:
            cvc5_y_val = cvc5_model.eval(cvc5_y).as_long()
        except AttributeError:
            cvc5_y_val = int(str(cvc5_model[cvc5_y]))

        assert z3_y_val == 60
        assert cvc5_y_val == 60


class TestPushPopEquivalence:
    """Push/pop equivalence tests."""

    def test_push_pop_sat_transitions(self, z3_solver, cvc5_solver):
        """Both solvers should handle push/pop transitions equivalently."""
        import z3
        from cvc5.pythonic import BitVec as CVC5BitVec

        # Use values contradictory under signed comparison (BitVec > and < are signed)
        # Z3
        z3_x = z3.BitVec("x", 8)
        z3_solver.add(z3_x > 0)
        z3_solver.push()
        z3_solver.add(z3_x > 50)
        z3_solver.add(z3_x < 10)
        z3_result_1 = z3_solver.check()
        z3_solver.pop()
        z3_result_2 = z3_solver.check()

        # cvc5
        cvc5_x = CVC5BitVec("x", 8)
        cvc5_solver.add(cvc5_x > 0)
        cvc5_solver.push()
        cvc5_solver.add(cvc5_x > 50)
        cvc5_solver.add(cvc5_x < 10)
        cvc5_result_1 = cvc5_solver.check()
        cvc5_solver.pop()
        cvc5_result_2 = cvc5_solver.check()

        # Both should be unsat in first check, sat after pop
        assert SolverResult.is_unsat(z3_result_1)
        assert SolverResult.is_unsat(cvc5_result_1)
        assert SolverResult.is_sat(z3_result_2)
        assert SolverResult.is_sat(cvc5_result_2)
