"""
Interfaces for model checker components.

This package defines abstract interfaces that establish contracts between
components, enabling refactoring without breaking dependencies.
"""

from .model_interface import ModelInterface, ModelAccessor
from .solver_interface import SolverInterface, SolverManager
from .constraint_interface import ConstraintInterface, ConstraintBuilder

__all__ = [
    'ModelInterface',
    'ModelAccessor', 
    'SolverInterface',
    'SolverManager',
    'ConstraintInterface',
    'ConstraintBuilder'
]