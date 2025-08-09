"""Pytest configuration and fixtures for models package tests.

Provides common test fixtures and configuration for all models tests.
"""

import pytest
from z3 import BitVecVal


@pytest.fixture
def standard_settings():
    """Provide standard test settings."""
    return {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'non_null': False
    }


@pytest.fixture
def semantic_instance(standard_settings):
    """Provide a configured SemanticDefaults instance."""
    from model_checker.models.semantic import SemanticDefaults
    return SemanticDefaults(standard_settings)


@pytest.fixture
def sample_bitvectors():
    """Provide sample bit vectors for testing."""
    return {
        'zero': BitVecVal(0b000, 3),
        'one': BitVecVal(0b001, 3),
        'three': BitVecVal(0b011, 3),
        'five': BitVecVal(0b101, 3),
        'seven': BitVecVal(0b111, 3)
    }


@pytest.fixture
def sample_states():
    """Provide a sample set of states."""
    return {BitVecVal(i, 3) for i in [1, 2, 4]}


# Test markers
def pytest_configure(config):
    """Register custom markers."""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )
    config.addinivalue_line(
        "markers", "integration: marks tests as integration tests"
    )