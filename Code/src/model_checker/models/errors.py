"""Error hierarchy for the models package.

This module defines custom exceptions for model-related errors,
following the pattern established by BuilderError.
"""


class ModelError(Exception):
    """Base exception for all model-related errors.
    
    This is the root of the models package error hierarchy.
    All model-specific exceptions should inherit from this class.
    """
    pass


class ModelConstraintError(ModelError):
    """Raised when there are issues with model constraints.
    
    This includes problems with:
    - Constraint generation
    - Constraint validation
    - Constraint inconsistencies
    """
    pass


class ModelSolverError(ModelError):
    """Raised when Z3 solver encounters issues.
    
    This includes:
    - Solver initialization failures
    - Solving timeouts
    - Unexpected solver states
    """
    pass


class ModelInterpretationError(ModelError):
    """Raised when model interpretation fails.
    
    This includes:
    - Missing Z3 model when interpretation is attempted
    - Invalid proposition values
    - Recursive interpretation failures
    """
    pass


class ModelStateError(ModelError):
    """Raised when model is in an invalid state.
    
    This includes:
    - Accessing results before solving
    - Invalid state transitions
    - Missing required attributes
    """
    pass


class SemanticError(ModelError):
    """Raised when semantic operations fail.
    
    This includes:
    - Invalid semantic configurations
    - Missing semantic components
    - Semantic computation errors
    """
    pass


class PropositionError(ModelError):
    """Raised when proposition operations fail.
    
    This includes:
    - Invalid proposition types
    - Missing proposition attributes
    - Proposition evaluation errors
    """
    pass