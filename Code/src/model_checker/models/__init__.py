"""Models subpackage for ModelChecker framework.

This package contains the refactored components from the original model.py module,
organized into logical submodules for better maintainability and clarity.

Components:
    semantic.py - SemanticDefaults class and related functionality
    proposition.py - PropositionDefaults class and related functionality  
    constraints.py - ModelConstraints class and Z3 constraint generation
    structure.py - ModelDefaults core structure and Z3 solving
    printing.py - Model printing and display functionality
    analysis.py - Model analysis and utility functions

The refactoring follows the NO BACKWARDS COMPATIBILITY principle - all imports
have been updated throughout the codebase to use the new structure directly.
"""

# Import all classes for backward compatibility during transition
# These will be removed in Phase 1.7 after all imports are updated

from .semantic import SemanticDefaults
from .proposition import PropositionDefaults
from .constraints import ModelConstraints

# Placeholder imports - will be populated as classes are moved
# from ..model import (
#     ModelDefaults,
# )

__all__ = [
    'SemanticDefaults',
    'PropositionDefaults',
    'ModelConstraints',
]