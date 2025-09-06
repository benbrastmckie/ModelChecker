"""Models subpackage for ModelChecker framework.

This package contains the refactored components from the original model.py module,
organized into logical submodules for better maintainability and clarity.

Components:
    semantic.py - SemanticDefaults class and related functionality
    proposition.py - PropositionDefaults class and related functionality  
    constraints.py - ModelConstraints class and Z3 constraint generation
    structure.py - ModelDefaults core structure and Z3 solving
    errors.py - Custom exception hierarchy for model operations

The refactoring follows the NO BACKWARDS COMPATIBILITY principle - all imports
have been updated throughout the codebase to use the new structure directly.
"""

# Core model components
from .semantic import SemanticDefaults
from .proposition import PropositionDefaults
from .constraints import ModelConstraints
from .structure import ModelDefaults

# Error hierarchy
from .errors import (
    ModelError,
    ModelConstraintError,
    ModelSolverError,
    ModelInterpretationError,
    ModelStateError,
    SemanticError,
    PropositionError,
)

__all__ = [
    # Core components
    'SemanticDefaults',
    'PropositionDefaults',
    'ModelConstraints',
    'ModelDefaults',
    # Errors
    'ModelError',
    'ModelConstraintError',
    'ModelSolverError',
    'ModelInterpretationError',
    'ModelStateError',
    'SemanticError',
    'PropositionError',
]