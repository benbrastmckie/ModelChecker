"""Pytest configuration for syntactic tests.

This module provides shared fixtures and configuration for all
syntactic package tests.
"""

import pytest
from model_checker.syntactic import Syntax
from model_checker.syntactic.operators import Operator


@pytest.fixture
def basic_syntax():
    """Create a basic Syntax instance for testing."""
    return Syntax()


@pytest.fixture
def sample_operators():
    """Create sample operators for testing."""
    return {
        'wedge': Operator('wedge', '∧', 2),
        'vee': Operator('vee', '∨', 2),
        'neg': Operator('neg', '¬', 1),
        'implies': Operator('implies', '→', 2),
        'iff': Operator('iff', '↔', 2),
    }


@pytest.fixture
def sample_atoms():
    """Create sample atomic propositions."""
    return ['p', 'q', 'r', 's']


@pytest.fixture
def sample_formulas():
    """Create sample formulas for testing."""
    return [
        'p',
        '¬p',
        'p ∧ q',
        'p ∨ q',
        'p → q',
        'p ↔ q',
        '¬(p ∧ q)',
        '(p ∨ q) → r',
        '¬¬p',
        '((p ∧ q) ∨ r) → s'
    ]