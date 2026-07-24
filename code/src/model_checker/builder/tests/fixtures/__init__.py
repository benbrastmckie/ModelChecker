"""
Centralized test fixtures for builder test suite.

This module exports commonly used fixtures and test data to ensure
consistency across all test files.
"""

from .test_data import TestTheories, TestExamples, TestModules, TestFlags
from .mock_objects import MockObjectFactory
from .temp_resources import TempFileCleanup
from .assertions import (
    assert_valid_theory_structure,
    assert_build_module_initialized, 
    assert_error_message_contains
)

__all__ = [
    # New centralized fixtures
    'TestTheories',
    'TestExamples', 
    'TestModules',
    'TestFlags',
    'MockObjectFactory',
    'TempFileCleanup',
    'assert_valid_theory_structure',
    'assert_build_module_initialized',
    'assert_error_message_contains'
]