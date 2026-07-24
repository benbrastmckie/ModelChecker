"""Pytest configuration and fixtures for imposition theory tests.

This module provides common test fixtures and configuration for both example tests and unit
tests, mirroring the pattern already established in exclusion/tests/conftest.py and
logos/tests/conftest.py -- see docs/THEORY_ARCHITECTURE.md's Theory Contract, which lists
tests/conftest.py as part of the canonical per-theory test layout.
"""

import pytest

from model_checker.theory_lib.imposition import (
    ImpositionSemantics,
    imposition_operators,
)


@pytest.fixture
def imposition_theory():
    """Standard imposition theory with imposition operators."""
    return {
        'operators': imposition_operators,
        'semantics': ImpositionSemantics,
    }


@pytest.fixture
def basic_settings():
    """Standard settings for most tests, matching
    ImpositionSemantics.DEFAULT_EXAMPLE_SETTINGS."""
    return {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'max_time': 1,
        'iterate': 1,
        'expectation': None,
    }


@pytest.fixture
def minimal_settings():
    """Minimal settings for quick tests."""
    return {
        'N': 2,
        'max_time': 1,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'expectation': None,
    }


@pytest.fixture
def complex_settings():
    """Settings for more complex tests."""
    return {
        'N': 4,
        'max_time': 5,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'expectation': None,
    }


@pytest.fixture
def imposition_semantics(basic_settings):
    """Fresh ImpositionSemantics instance for tests."""
    return ImpositionSemantics(basic_settings)
