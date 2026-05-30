"""Tests for Z3 solver adapter."""

import pytest
import z3

from model_checker.solver import create_solver, SolverResult
from model_checker.solver.z3_adapter import Z3SolverAdapter
from model_checker.solver.protocols import SolverProtocol, TrackedSolverProtocol


class TestZ3AdapterBasic:
    """Basic functionality tests for Z3 adapter."""

    def test_create_adapter(self):
        """Should be able to create Z3 adapter."""
        adapter = Z3SolverAdapter()
        assert adapter is not None

    def test_adapter_satisfies_protocol(self):
        """Z3 adapter should satisfy SolverProtocol."""
        adapter = Z3SolverAdapter()
        assert isinstance(adapter, SolverProtocol)

    def test_simple_sat(self):
        """Should find satisfying model for simple constraint."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)
        adapter.add(x > 5)
        result = adapter.check()
        assert SolverResult.is_sat(result)

    def test_simple_unsat(self):
        """Should detect unsatisfiability."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)
        adapter.add(x > 10)
        adapter.add(x < 5)
        result = adapter.check()
        assert SolverResult.is_unsat(result)

    def test_model_evaluation(self):
        """Should be able to evaluate expressions in model."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)
        y = z3.BitVec("y", 8)
        adapter.add(x + y == 10)
        adapter.add(x == 4)
        result = adapter.check()
        assert SolverResult.is_sat(result)

        model = adapter.model()
        assert model.eval(x).as_long() == 4
        assert model.eval(y).as_long() == 6


class TestZ3AdapterTracking:
    """Tests for tracked assertions and unsat cores."""

    def test_assert_tracked(self):
        """Should be able to add tracked assertions."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)
        adapter.assert_tracked(x > 5, "c1")
        adapter.assert_tracked(x < 10, "c2")
        result = adapter.check()
        assert SolverResult.is_sat(result)

    def test_unsat_core_extraction(self):
        """Should extract unsat core labels."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)
        adapter.assert_tracked(x > 10, "greater_than_10")
        adapter.assert_tracked(x < 5, "less_than_5")
        result = adapter.check()
        assert SolverResult.is_unsat(result)

        core = adapter.unsat_core()
        assert isinstance(core, list)
        # Both constraints should be in the core
        assert len(core) == 2


class TestZ3AdapterPushPop:
    """Tests for push/pop scoping."""

    def test_push_pop_basic(self):
        """Should support push/pop for incremental solving."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)

        adapter.add(x > 0)
        adapter.push()
        adapter.add(x > 100)  # This with x > 0 and bitvec(8) is unsat (max 255)
        adapter.add(x < 50)   # Contradiction
        result = adapter.check()
        assert SolverResult.is_unsat(result)

        adapter.pop()
        # After pop, only x > 0 remains
        result = adapter.check()
        assert SolverResult.is_sat(result)


class TestZ3AdapterOptions:
    """Tests for solver options."""

    def test_set_timeout(self):
        """Should be able to set timeout."""
        adapter = Z3SolverAdapter()
        adapter.set_timeout(1000)  # 1 second
        # Just verify it doesn't raise
        assert True

    def test_reset(self):
        """Should be able to reset solver state."""
        adapter = Z3SolverAdapter()
        x = z3.BitVec("x", 8)
        adapter.add(x > 5)
        adapter.reset()
        # After reset, solver should be empty
        assert len(adapter.assertions()) == 0

    def test_raw_solver_access(self):
        """Should be able to access raw Z3 solver."""
        adapter = Z3SolverAdapter()
        raw = adapter.raw_solver
        assert isinstance(raw, z3.Solver)
