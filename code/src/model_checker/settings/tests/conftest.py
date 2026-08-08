"""Pytest configuration for settings tests.

This module provides shared fixtures and configuration for all
settings package tests.
"""

import pytest


@pytest.fixture
def valid_settings():
    """Create valid settings for testing."""
    return {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'max_time': 5,
        'iterate': 1
    }