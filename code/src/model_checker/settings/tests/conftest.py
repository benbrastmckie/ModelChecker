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


@pytest.fixture
def invalid_settings():
    """Create various invalid settings for testing."""
    return [
        {'N': 0},  # Invalid N value
        {'N': 65},  # N too large
        {'max_time': -1},  # Negative time
        {'iterate': 0},  # Invalid iteration count
        {}  # Missing required settings
    ]