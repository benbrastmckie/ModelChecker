"""Pytest configuration for utils tests.

This module provides shared fixtures and configuration for all
utils package tests.
"""

import pytest
import z3


@pytest.fixture
def z3_context_isolation():
    """Provide a fresh Z3 C-level context for a single test.

    Use this fixture explicitly in tests that need Z3 context isolation.
    Do not mark as autouse: Z3 expressions created in setUp() belong to the
    outer context and cannot be used inside a fresh context.

    Usage::

        def test_something(z3_context_isolation):
            with z3_context_isolation:
                x = z3.Int('x')
                solver = z3.Solver()
                solver.add(x > 0)
                assert solver.check() == z3.sat
    """
    from model_checker.utils.context import isolated_z3_context
    return isolated_z3_context()
