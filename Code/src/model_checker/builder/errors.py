"""Error hierarchy for builder package.

This module defines the error hierarchy for the builder package,
following the fail-fast philosophy with helpful error messages.
No backwards compatibility is maintained.
"""


class BuilderError(Exception):
    """Base exception for builder package errors."""
    pass


class PackageError(BuilderError):
    """Base error for package-related issues.
    
    All errors include context and suggestions for resolution.
    """
    
    def __init__(self, message: str, context: str = "", suggestion: str = ""):
        """Initialize with message, context, and suggestion.
        
        Args:
            message: Main error message
            context: Additional context about the error
            suggestion: Suggestion for resolving the error
        """
        self.context = context
        self.suggestion = suggestion
        
        full_message = message
        if context:
            full_message += f"\nContext: {context}"
        if suggestion:
            full_message += f"\nSuggestion: {suggestion}"
            
        super().__init__(full_message)


class PackageStructureError(PackageError):
    """Package structure does not meet requirements.
    
    Raised when:
    - Missing .modelchecker marker
    - Missing __init__.py
    - Invalid directory structure
    """
    pass


class PackageFormatError(PackageError):
    """Package format is invalid.
    
    Raised when:
    - .modelchecker marker has invalid content
    - __init__.py missing required exports
    - Package metadata is malformed
    """
    pass


class PackageImportError(PackageError, ImportError):
    """Package cannot be imported.
    
    Raised when:
    - Import statement fails
    - Module not found in package
    - Circular import detected
    
    Inherits from both PackageError and ImportError for compatibility.
    """
    pass


class PackageNotImportableError(PackageError):
    """Generated package is not in importable state.
    
    Raised when:
    - Package not in sys.path
    - Parent directory not accessible
    - Package dependencies missing
    """
    pass


# Other existing error types (kept for compatibility within builder)
class ModuleLoadError(BuilderError):
    """Module loading and import failures."""
    pass


class ValidationError(BuilderError):
    """Input validation failures."""
    pass


class ModelCheckError(BuilderError):
    """Model checking operation failures."""
    pass


class ConfigurationError(BuilderError):
    """Configuration and settings errors."""
    pass


class TheoryNotFoundError(BuilderError):
    """Theory loading and discovery errors."""
    pass