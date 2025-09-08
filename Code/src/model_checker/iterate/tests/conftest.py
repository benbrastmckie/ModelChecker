"""Pytest configuration for iterate tests.

This module provides shared fixtures and configuration for all
iterate package tests.
"""

import pytest
import z3
from unittest.mock import Mock
from model_checker.builder.example import BuildExample
from model_checker.iterate.core import BaseModelIterator


@pytest.fixture
def mock_build_example():
    """Create a mock BuildExample for testing."""
    example = Mock(spec=BuildExample)
    example.theory_name = "test_theory"
    example.name = "test_example"
    example.example = ["assumptions", "conclusions", {"N": 3}]
    return example


@pytest.fixture
def z3_context():
    """Create a fresh Z3 context for each test."""
    ctx = z3.Context()
    yield ctx
    # Cleanup handled by Z3 garbage collection


@pytest.fixture
def mock_iterator():
    """Create a mock iterator for testing."""
    class TestIterator(BaseModelIterator):
        def __init__(self):
            # Initialize without calling super().__init__
            self.N = 3
            self.original_constraints = []
            self.stats = {"iterations": 0}
            
        def get_all_constraints(self):
            return []
            
        def extract_semantic_condition(self, model):
            return z3.BoolVal(True)
    
    return TestIterator()


@pytest.fixture(autouse=True)
def cleanup_z3():
    """Ensure Z3 is properly cleaned up after each test."""
    yield
    # Z3 cleanup happens automatically with context garbage collection