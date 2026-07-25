"""Pytest configuration and fixtures for bimodal theory tests.

This module provides common test fixtures and configuration for both
example tests and unit tests, matching the conftest.py layout used by the
exclusion and logos theories.
"""

import pytest
from model_checker.theory_lib import bimodal


@pytest.fixture
def bimodal_theory():
    """Standard bimodal theory configuration (semantics, proposition, model, operators)."""
    return bimodal.get_theory()


@pytest.fixture
def basic_settings():
    """Standard settings for most tests.

    Includes 'M' (bimodal's temporal dimension parameter, required by
    BimodalSemantics.__init__ to size its WitnessRegistry) alongside the
    common 'N', which the other three theories' settings fixtures don't need.
    """
    return {
        'N': 3,
        'M': 2,
        'max_time': 1,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': False,
        'expectation': True,
        'iterate': 1,
    }


@pytest.fixture
def minimal_settings():
    """Minimal settings for quick tests."""
    return {
        'N': 2,
        'max_time': 1,
        'expectation': True,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': True,
    }


@pytest.fixture
def complex_settings():
    """Settings for more complex tests."""
    return {
        'N': 4,
        'max_time': 5,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': True,
        'expectation': True,
    }


@pytest.fixture
def witness_registry(basic_settings):
    """Fresh witness registry for tests."""
    from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry
    return WitnessRegistry(N=basic_settings['N'], M=basic_settings['M'])


@pytest.fixture
def constraint_generator(basic_settings):
    """Constraint generator with a fresh bimodal semantics instance."""
    from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
    from model_checker.theory_lib.bimodal.semantic.witness_constraints import WitnessConstraintGenerator
    semantics = BimodalSemantics(basic_settings)
    return WitnessConstraintGenerator(semantics)
