"""Core interfaces and abstractions for ModelChecker.

This module provides the fundamental interfaces that decouple
the framework components from specific theory implementations.
"""

from .interfaces import TheoryInterface, ExampleInterface
from .validators import validate_premises, validate_conclusions, validate_settings

__all__ = [
    'TheoryInterface',
    'ExampleInterface',
    'validate_premises',
    'validate_conclusions',
    'validate_settings',
]