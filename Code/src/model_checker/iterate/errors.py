"""Error hierarchy for iterate package.

This module defines custom exceptions for the iteration functionality,
providing clear error messages and context for debugging.
"""

from typing import Dict, Any, Optional


class IterateError(Exception):
    """Base exception for iteration errors.
    
    All iteration-specific exceptions inherit from this class.
    Provides context storage for debugging and error analysis.
    """
    
    def __init__(self, message: str, context: Optional[Dict[str, Any]] = None):
        """Initialize with message and optional context.
        
        Args:
            message: Human-readable error description
            context: Additional data for debugging (model numbers, states, etc.)
        """
        super().__init__(message)
        self.context = context or {}
        
    def __str__(self) -> str:
        """String representation with context if available."""
        base_msg = super().__str__()
        if self.context:
            context_str = ", ".join(f"{k}={v}" for k, v in self.context.items())
            return f"{base_msg} [Context: {context_str}]"
        return base_msg


class IterationLimitError(IterateError):
    """Raised when iteration limit exceeded.
    
    Indicates that the maximum number of requested models has been
    reached or that iteration cannot continue due to limits.
    """
    
    def __init__(self, limit: int, found: int, reason: str = ""):
        """Initialize with limit and models found.
        
        Args:
            limit: The maximum iteration limit
            found: Number of models actually found
            reason: Optional explanation for why limit was reached
        """
        message = f"Iteration limit of {limit} models reached (found {found})"
        if reason:
            message += f": {reason}"
        context = {'limit': limit, 'found': found}
        if reason:
            context['reason'] = reason
        super().__init__(message, context)


class IterationStateError(IterateError):
    """Raised when iteration state is invalid.
    
    Indicates corruption or inconsistency in the iteration state,
    such as missing required attributes or invalid configurations.
    """
    
    def __init__(self, state: str, reason: str, suggestion: str = ""):
        """Initialize with state and reason.
        
        Args:
            state: The invalid state description
            reason: Why the state is invalid
            suggestion: Actionable suggestion for fixing the issue
        """
        message = f"Invalid iteration state '{state}': {reason}"
        if suggestion:
            message += f". Suggestion: {suggestion}"
        context = {'state': state, 'reason': reason}
        if suggestion:
            context['suggestion'] = suggestion
        super().__init__(message, context)


class ModelExtractionError(IterateError):
    """Raised when model extraction fails.
    
    Indicates failure to extract or build a model structure from
    Z3 solver output, often due to incomplete or invalid models.
    """
    
    def __init__(self, model_num: int, reason: str, suggestion: str = ""):
        """Initialize with model number and failure reason.
        
        Args:
            model_num: The model number that failed to extract
            reason: Why extraction failed
            suggestion: Actionable suggestion for resolution
        """
        message = f"Failed to extract model {model_num}: {reason}"
        if suggestion:
            message += f". Suggestion: {suggestion}"
        context = {'model_num': model_num, 'reason': reason}
        if suggestion:
            context['suggestion'] = suggestion
        super().__init__(message, context)


class ConstraintGenerationError(IterateError):
    """Raised when constraint generation fails.
    
    Indicates failure to generate exclusion constraints for
    finding distinct models, often due to invalid formulas.
    """
    
    def __init__(self, constraint_type: str, reason: str, model_num: Optional[int] = None):
        """Initialize with constraint type and reason.
        
        Args:
            constraint_type: Type of constraint that failed (e.g., 'exclusion', 'stronger')
            reason: Why generation failed
            model_num: Optional model number if constraint is model-specific
        """
        message = f"Failed to generate {constraint_type} constraint: {reason}"
        context = {'type': constraint_type, 'reason': reason}
        if model_num is not None:
            message = f"Failed to generate {constraint_type} constraint for model {model_num}: {reason}"
            context['model_num'] = model_num
        super().__init__(message, context)


class IsomorphismCheckError(IterateError):
    """Raised when isomorphism checking fails.
    
    Indicates failure during graph isomorphism checking between
    models, used to identify semantically equivalent structures.
    """
    
    def __init__(self, model1: int, model2: int, reason: str):
        """Initialize with model numbers and reason.
        
        Args:
            model1: First model number in comparison
            model2: Second model number in comparison  
            reason: Why the check failed
        """
        message = f"Isomorphism check failed between models {model1} and {model2}: {reason}"
        context = {'model1': model1, 'model2': model2, 'reason': reason}
        super().__init__(message, context)


class IterationTimeoutError(IterateError):
    """Raised when iteration exceeds time limit.
    
    Indicates that the iteration process has exceeded the configured
    timeout, often due to complex constraints or large search spaces.
    """
    
    def __init__(self, timeout: float, elapsed: float, models_found: int):
        """Initialize with timeout information.
        
        Args:
            timeout: The configured timeout in seconds
            elapsed: Actual elapsed time in seconds
            models_found: Number of models found before timeout
        """
        message = f"Iteration timeout ({timeout}s) exceeded after {elapsed:.2f}s with {models_found} models found"
        context = {'timeout': timeout, 'elapsed': elapsed, 'models_found': models_found}
        super().__init__(message, context)


class ModelValidationError(IterateError):
    """Raised when model validation fails.
    
    Indicates that a generated model does not meet validity criteria,
    such as having no world states or violating theory constraints.
    """
    
    def __init__(self, model_num: int, validation_error: str):
        """Initialize with model number and validation error.
        
        Args:
            model_num: The model number that failed validation
            validation_error: Specific validation failure
        """
        message = f"Model {model_num} failed validation: {validation_error}"
        context = {'model_num': model_num, 'validation_error': validation_error}
        super().__init__(message, context)