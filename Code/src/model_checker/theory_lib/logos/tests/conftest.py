"""Pytest configuration and fixtures for logos theory tests.

This module provides common test fixtures and configuration for both
example tests and unit tests.
"""

import pytest
from model_checker.theory_lib import logos


@pytest.fixture
def logos_theory():
    """Full logos theory with all subtheories loaded."""
    return logos.get_theory()


@pytest.fixture  
def extensional_theory():
    """Logos theory with only extensional subtheory."""
    return logos.get_theory(['extensional'])


@pytest.fixture
def modal_theory():
    """Logos theory with extensional and modal subtheories."""
    return logos.get_theory(['extensional', 'modal'])


@pytest.fixture
def constitutive_theory():
    """Logos theory with extensional, modal, and constitutive subtheories."""
    return logos.get_theory(['extensional', 'modal', 'constitutive'])


@pytest.fixture
def counterfactual_theory():
    """Logos theory with extensional, modal, and counterfactual subtheories."""
    return logos.get_theory(['extensional', 'modal', 'counterfactual'])


@pytest.fixture
def relevance_theory():
    """Logos theory with extensional, modal, constitutive, and relevance subtheories."""
    return logos.get_theory(['extensional', 'modal', 'constitutive', 'relevance'])


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