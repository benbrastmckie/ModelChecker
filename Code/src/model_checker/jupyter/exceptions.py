"""
Custom exceptions for the Jupyter integration package.

This module defines a hierarchy of exceptions for better error handling
and debugging in Jupyter environments.
"""


class JupyterError(Exception):
    """Base exception for all Jupyter integration errors."""
    pass


class JupyterEnvironmentError(JupyterError):
    """Raised when there are issues with the Jupyter environment setup."""
    pass


class JupyterDependencyError(JupyterError):
    """Raised when required dependencies are missing or incompatible."""
    
    def __init__(self, dependency: str, feature: str = None):
        """
        Initialize dependency error.
        
        Args:
            dependency: Name of the missing dependency
            feature: Optional feature that requires the dependency
        """
        if feature:
            message = f"{feature} requires {dependency}. Install with 'pip install model-checker[jupyter]'"
        else:
            message = f"Missing required dependency: {dependency}"
        super().__init__(message)
        self.dependency = dependency
        self.feature = feature


class JupyterWidgetError(JupyterError):
    """Raised when there are issues with widget creation or interaction."""
    pass


class JupyterVisualizationError(JupyterError):
    """Raised when visualization fails."""
    
    def __init__(self, viz_type: str, reason: str = None):
        """
        Initialize visualization error.
        
        Args:
            viz_type: Type of visualization that failed
            reason: Optional reason for failure
        """
        message = f"Failed to create {viz_type} visualization"
        if reason:
            message += f": {reason}"
        super().__init__(message)
        self.viz_type = viz_type
        self.reason = reason


class JupyterFormulaError(JupyterError):
    """Raised when there are issues with formula processing."""
    
    def __init__(self, formula: str, issue: str):
        """
        Initialize formula error.
        
        Args:
            formula: The problematic formula
            issue: Description of the issue
        """
        message = f"Error processing formula '{formula}': {issue}"
        super().__init__(message)
        self.formula = formula
        self.issue = issue


class JupyterTheoryError(JupyterError):
    """Raised when there are issues with theory loading or execution."""
    
    def __init__(self, theory_name: str, issue: str):
        """
        Initialize theory error.
        
        Args:
            theory_name: Name of the problematic theory
            issue: Description of the issue
        """
        message = f"Error with theory '{theory_name}': {issue}"
        super().__init__(message)
        self.theory_name = theory_name
        self.issue = issue


class JupyterTimeoutError(JupyterError):
    """Raised when an operation times out."""
    
    def __init__(self, operation: str, timeout: float):
        """
        Initialize timeout error.
        
        Args:
            operation: The operation that timed out
            timeout: The timeout value in seconds
        """
        message = f"{operation} timed out after {timeout} seconds"
        super().__init__(message)
        self.operation = operation
        self.timeout = timeout