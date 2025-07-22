"""Pytest configuration and fixtures for exclusion theory tests.

This module provides common test fixtures and configuration for both
example tests and unit tests.
"""

import pytest
from model_checker.theory_lib.exclusion import (
    WitnessSemantics, 
    witness_operators,
    WitnessRegistry,
    WitnessConstraintGenerator
)


@pytest.fixture
def exclusion_theory():
    """Standard exclusion theory with witness operators."""
    return {
        'operators': witness_operators,
        'semantics': WitnessSemantics,
    }


@pytest.fixture
def basic_settings():
    """Standard settings for most tests."""
    return {
        'N': 3,
        'max_time': 1,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': False,
        'expectation': True,
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
    return WitnessRegistry(N=basic_settings['N'])


@pytest.fixture
def constraint_generator(basic_settings, witness_registry):
    """Constraint generator with basic settings."""
    from model_checker.theory_lib.exclusion.semantic import WitnessSemantics
    semantics = WitnessSemantics(basic_settings, witness_registry)
    return WitnessConstraintGenerator(semantics)