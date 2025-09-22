"""Error hierarchy for builder package.

This module defines the error hierarchy for the builder package,
following the fail-fast philosophy with helpful error messages.
No backwards compatibility is maintained.
"""


class BuilderError(Exception):
    """Base exception for builder package errors."""
    pass


class PackageError(BuilderError):
    """Base error for package-related issues."""
    
    def __init__(self, message: str, *details: str):
        """Initialize with main message and optional details.
        
        Args:
            message: Main error message
            *details: Additional details to help user resolve the issue
        """
        full_message = message
        if details:
            full_message += "\nDetails:\n" + "\n".join(f"  - {d}" for d in details)
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


class PackageImportError(PackageError):
    """Package cannot be imported.
    
    Raised when:
    - Import statement fails
    - Module not found in package
    - Circular import detected
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