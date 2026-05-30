"""Tests for solver protocols and result handling."""

import pytest
import z3

from model_checker.solver.protocols import (
    SolverProtocol,
    TrackedSolverProtocol,
    ModelProtocol,
    SolverResult,
)


class TestSolverResult:
    """Tests for SolverResult conversion and checking."""

    def test_result_constants(self):
        """Result constants should have correct values."""
        assert SolverResult.SAT == "sat"
        assert SolverResult.UNSAT == "unsat"
        assert SolverResult.UNKNOWN == "unknown"

    def test_from_z3_sat(self):
        """Should convert Z3 sat result correctly."""
        solver = z3.Solver()
        solver.add(z3.Bool("x"))
        result = solver.check()
        assert SolverResult.from_z3(result) == SolverResult.SAT

    def test_from_z3_unsat(self):
        """Should convert Z3 unsat result correctly."""
        solver = z3.Solver()
        x = z3.Bool("x")
        solver.add(x)
        solver.add(z3.Not(x))
        result = solver.check()
        assert SolverResult.from_z3(result) == SolverResult.UNSAT

    def test_is_sat(self):
        """is_sat should correctly identify sat results."""
        assert SolverResult.is_sat(SolverResult.SAT) is True
        assert SolverResult.is_sat(SolverResult.UNSAT) is False
        assert SolverResult.is_sat(SolverResult.UNKNOWN) is False

    def test_is_unsat(self):
        """is_unsat should correctly identify unsat results."""
        assert SolverResult.is_unsat(SolverResult.UNSAT) is True
        assert SolverResult.is_unsat(SolverResult.SAT) is False
        assert SolverResult.is_unsat(SolverResult.UNKNOWN) is False


class TestProtocolCompliance:
    """Tests for protocol compliance."""

    def test_z3_solver_matches_protocol(self):
        """Z3 Solver should match SolverProtocol."""
        solver = z3.Solver()
        # Protocol check via isinstance (runtime_checkable)
        assert isinstance(solver, SolverProtocol)

    def test_z3_model_matches_protocol(self):
        """Z3 ModelRef should match ModelProtocol."""
        solver = z3.Solver()
        x = z3.Bool("x")
        solver.add(x)
        solver.check()
        model = solver.model()
        assert isinstance(model, ModelProtocol)
