"""Centralized error definitions for the builder package.

This module defines consistent error types used throughout the builder
package to provide clear, actionable error messages.
"""


class BuilderError(Exception):
    """Base exception for all builder package errors.
    
    All builder-specific exceptions should inherit from this class
    to allow for easy catching of builder-related errors.
    """
    pass


class ModuleLoadError(BuilderError):
    """Raised when a module cannot be loaded or imported.
    
    This includes issues with:
    - Missing files
    - Syntax errors in modules
    - Import errors
    - Missing required attributes
    """
    
    def __init__(self, module_name: str, path: str = None, suggestion: str = None):
        """Initialize with detailed error information.
        
        Args:
            module_name: Name of the module that failed to load
            path: Optional file path that was attempted
            suggestion: Optional suggestion for fixing the issue
        """
        message = f"Failed to load module '{module_name}'"
        
        if path:
            message += f"\nPath: {path}"
        
        if suggestion:
            message += f"\nSuggestion: {suggestion}"
        
        super().__init__(message)
        self.module_name = module_name
        self.path = path
        self.suggestion = suggestion


class ValidationError(BuilderError):
    """Raised when validation fails for inputs or configurations.
    
    This includes:
    - Invalid semantic theory structure
    - Invalid example case format
    - Invalid settings values
    - Type mismatches
    """
    
    def __init__(self, item_type: str, issue: str, expected: str = None):
        """Initialize with validation details.
        
        Args:
            item_type: Type of item that failed validation
            issue: Description of the validation issue
            expected: Optional description of what was expected
        """
        message = f"Validation failed for {item_type}: {issue}"
        
        if expected:
            message += f"\nExpected: {expected}"
        
        super().__init__(message)
        self.item_type = item_type
        self.issue = issue
        self.expected = expected


class ModelCheckError(BuilderError):
    """Raised during model checking operations.
    
    This includes:
    - Z3 solver failures
    - Constraint generation errors
    - Model extraction errors
    - Iteration failures
    """
    
    def __init__(self, operation: str, details: str = None, example_name: str = None):
        """Initialize with model checking details.
        
        Args:
            operation: The operation that failed
            details: Optional details about the failure
            example_name: Optional name of the example being checked
        """
        message = f"Model checking failed during {operation}"
        
        if example_name:
            message = f"Model checking failed for '{example_name}' during {operation}"
        
        if details:
            message += f"\nDetails: {details}"
        
        super().__init__(message)
        self.operation = operation
        self.details = details
        self.example_name = example_name


class ConfigurationError(BuilderError):
    """Raised when configuration is invalid or inconsistent.
    
    This includes:
    - Invalid settings combinations
    - Missing required configuration
    - Conflicting flags
    """
    
    def __init__(self, config_type: str, issue: str, resolution: str = None):
        """Initialize with configuration details.
        
        Args:
            config_type: Type of configuration that has issues
            issue: Description of the configuration problem
            resolution: Optional suggested resolution
        """
        message = f"Configuration error in {config_type}: {issue}"
        
        if resolution:
            message += f"\nResolution: {resolution}"
        
        super().__init__(message)
        self.config_type = config_type
        self.issue = issue
        self.resolution = resolution


class TheoryNotFoundError(BuilderError):
    """Raised when a requested theory cannot be found.
    
    This includes:
    - Unknown theory names
    - Missing theory implementations
    - Theory loading failures
    """
    
    def __init__(self, theory_name: str, available_theories: list = None):
        """Initialize with theory information.
        
        Args:
            theory_name: Name of the theory that wasn't found
            available_theories: Optional list of available theory names
        """
        message = f"Theory '{theory_name}' not found"
        
        if available_theories:
            message += f"\nAvailable theories: {', '.join(available_theories)}"
        
        super().__init__(message)
        self.theory_name = theory_name
        self.available_theories = available_theories


class ExampleNotFoundError(BuilderError):
    """Raised when a requested example cannot be found.
    
    This includes:
    - Unknown example names
    - Missing example definitions
    """
    
    def __init__(self, example_name: str, available_examples: list = None):
        """Initialize with example information.
        
        Args:
            example_name: Name of the example that wasn't found
            available_examples: Optional list of available example names
        """
        message = f"Example '{example_name}' not found"
        
        if available_examples:
            message += f"\nAvailable examples: {', '.join(available_examples)}"
        
        super().__init__(message)
        self.example_name = example_name
        self.available_examples = available_examples


class IterationError(BuilderError):
    """Raised when model iteration fails.
    
    This includes:
    - Iteration limit exceeded
    - No more models found
    - Iteration function errors
    """
    
    def __init__(self, reason: str, iteration_count: int = None, max_iterations: int = None):
        """Initialize with iteration details.
        
        Args:
            reason: Reason for iteration failure
            iteration_count: Optional current iteration count
            max_iterations: Optional maximum iterations allowed
        """
        message = f"Iteration failed: {reason}"
        
        if iteration_count is not None and max_iterations is not None:
            message += f"\nIteration {iteration_count}/{max_iterations}"
        
        super().__init__(message)
        self.reason = reason
        self.iteration_count = iteration_count
        self.max_iterations = max_iterations


class OutputError(BuilderError):
    """Raised when output operations fail.
    
    This includes:
    - File writing errors
    - Directory creation failures
    - Permission issues
    """
    
    def __init__(self, operation: str, path: str = None, reason: str = None):
        """Initialize with output operation details.
        
        Args:
            operation: The output operation that failed
            path: Optional file/directory path involved
            reason: Optional reason for failure
        """
        message = f"Output operation '{operation}' failed"
        
        if path:
            message += f"\nPath: {path}"
        
        if reason:
            message += f"\nReason: {reason}"
        
        super().__init__(message)
        self.operation = operation
        self.path = path
        self.reason = reason


# Helper function for consistent error formatting
def format_error_with_context(error: Exception, context: dict = None) -> str:
    """Format an error with additional context information.
    
    Args:
        error: The exception to format
        context: Optional dictionary of context information
        
    Returns:
        str: Formatted error message with context
    """
    lines = [str(error)]
    
    if context:
        lines.append("\nContext:")
        for key, value in context.items():
            lines.append(f"  {key}: {value}")
    
    if hasattr(error, '__traceback__'):
        import traceback
        lines.append("\nTraceback (most recent call last):")
        tb_lines = traceback.format_tb(error.__traceback__, limit=3)
        lines.extend(tb_lines)
    
    return '\n'.join(lines)