"""Tests for Z3 context management."""

import pytest
import z3
import z3.z3


def test_isolated_z3_context_importable():
    """Test that isolated_z3_context can be imported."""
    from model_checker.utils import isolated_z3_context
    from model_checker.utils.context import isolated_z3_context as ctx2
    assert isolated_z3_context is not None
    assert isolated_z3_context is ctx2


def test_isolated_z3_context_is_callable():
    """Test that isolated_z3_context is a callable context manager factory."""
    from model_checker.utils.context import isolated_z3_context
    assert callable(isolated_z3_context)


def test_isolated_z3_context_creates_fresh_context():
    """Test that isolated_z3_context creates a distinct C-level context."""
    from model_checker.utils.context import isolated_z3_context

    original_ctx = z3.z3._main_ctx
    with isolated_z3_context():
        inner_ctx = z3.z3._main_ctx
        assert inner_ctx is not original_ctx, "Fresh context should differ from original"
    restored_ctx = z3.z3._main_ctx
    assert restored_ctx is original_ctx, "Original context should be restored on exit"


def test_isolated_z3_context_restores_on_exception():
    """Test that the original context is restored even if an exception is raised."""
    from model_checker.utils.context import isolated_z3_context

    original_ctx = z3.z3._main_ctx
    try:
        with isolated_z3_context():
            raise RuntimeError("deliberate error")
    except RuntimeError:
        pass
    assert z3.z3._main_ctx is original_ctx, "Context must be restored after exception"


def test_isolated_z3_context_provides_isolation():
    """Test that Z3 state does not leak between two consecutive isolated blocks."""
    from model_checker.utils.context import isolated_z3_context

    # First block: create a solver with x > 100
    with isolated_z3_context():
        x = z3.Int('x')
        solver1 = z3.Solver()
        solver1.add(x > 100)
        assert solver1.check() == z3.sat

    # Second block: new context, x > 100 should have no influence
    with isolated_z3_context():
        x = z3.Int('x')
        solver2 = z3.Solver()
        solver2.add(x < 0)
        result = solver2.check()
        # Must still be SAT because x < 0 is satisfiable independently
        assert result == z3.sat


def test_multiple_nested_uses():
    """Test that sequential isolated_z3_context calls work correctly."""
    from model_checker.utils.context import isolated_z3_context

    original = z3.z3._main_ctx
    for _ in range(3):
        with isolated_z3_context():
            s = z3.Solver()
            b = z3.Bool('b')
            s.add(b)
            assert s.check() == z3.sat
    # Context must be back to original after all iterations
    assert z3.z3._main_ctx is original
