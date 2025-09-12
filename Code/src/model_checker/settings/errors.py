"""Custom exceptions for the settings package.

This module provides a hierarchy of exceptions for handling various error
conditions that can occur during settings validation and processing.
"""

from typing import TYPE_CHECKING, Optional, Dict, Any, List
from .types import SettingName, SettingValue, TheoryName

if TYPE_CHECKING:
    pass


class SettingsError(Exception):
    """Base exception for settings-related errors.
    
    This is the base class for all settings exceptions, providing common
    functionality for storing context and suggestions.
    
    Attributes:
        message: The error message
        setting: The name of the setting that caused the error (if applicable)
        suggestion: A helpful suggestion for fixing the error
        context: Additional context information
    """
    
    def __init__(self, message: str, setting: Optional[SettingName] = None, 
                 suggestion: Optional[str] = None, context: Optional[Dict[str, Any]] = None) -> None:
        """Initialize a SettingsError.
        
        Args:
            message: The error message
            setting: The name of the setting that caused the error
            suggestion: A helpful suggestion for fixing the error
            context: Additional context information
        """
        super().__init__(message)
        self.setting = setting
        self.suggestion = suggestion
        self.context = context or {}
        
    def __str__(self) -> str:
        """Return a formatted error message with suggestion if available."""
        msg = super().__str__()
        if self.setting:
            msg = f"Setting '{self.setting}': {msg}"
        if self.suggestion:
            msg = f"{msg}\nSuggestion: {self.suggestion}"
        return msg


class ValidationError(SettingsError):
    """Raised when settings validation fails.
    
    This exception is raised when a setting value doesn't meet validation
    requirements, such as being the wrong type or out of range.
    """
    pass


class TypeConversionError(SettingsError):
    """Raised when type conversion of a setting fails.
    
    This exception is raised when a setting value cannot be converted
    to the expected type.
    """
    
    def __init__(self, setting: SettingName, value: SettingValue, expected_type: type, 
                 suggestion: Optional[str] = None) -> None:
        """Initialize a TypeConversionError.
        
        Args:
            setting: The name of the setting
            value: The value that failed conversion
            expected_type: The expected type
            suggestion: A helpful suggestion for fixing the error
        """
        message = f"Cannot convert value '{value}' to {expected_type.__name__}"
        if not suggestion:
            suggestion = f"Provide a value of type {expected_type.__name__}"
        super().__init__(message, setting=setting, suggestion=suggestion)
        self.value = value
        self.expected_type = expected_type


class RangeError(SettingsError):
    """Raised when a setting value is out of acceptable range.
    
    This exception is raised when a numeric setting is outside its
    valid range.
    """
    
    def __init__(self, setting: SettingName, value: SettingValue, min_value: Optional[SettingValue] = None, 
                 max_value: Optional[SettingValue] = None) -> None:
        """Initialize a RangeError.
        
        Args:
            setting: The name of the setting
            value: The out-of-range value
            min_value: The minimum acceptable value (if any)
            max_value: The maximum acceptable value (if any)
        """
        if min_value is not None and max_value is not None:
            message = f"Value {value} is out of range [{min_value}, {max_value}]"
            suggestion = f"Provide a value between {min_value} and {max_value}"
        elif min_value is not None:
            message = f"Value {value} is below minimum {min_value}"
            suggestion = f"Provide a value >= {min_value}"
        elif max_value is not None:
            message = f"Value {value} is above maximum {max_value}"
            suggestion = f"Provide a value <= {max_value}"
        else:
            message = f"Value {value} is out of range"
            suggestion = "Check the documentation for valid ranges"
            
        super().__init__(message, setting=setting, suggestion=suggestion)
        self.value = value
        self.min_value = min_value
        self.max_value = max_value


class MissingRequiredError(SettingsError):
    """Raised when a required setting is missing.
    
    This exception is raised when a setting that is required for proper
    operation is not provided.
    """
    
    def __init__(self, setting: SettingName, suggestion: Optional[str] = None) -> None:
        """Initialize a MissingRequiredError.
        
        Args:
            setting: The name of the missing required setting
            suggestion: A helpful suggestion for fixing the error
        """
        message = f"Required setting '{setting}' is missing"
        if not suggestion:
            suggestion = f"Add '{setting}' to your settings configuration"
        super().__init__(message, setting=setting, suggestion=suggestion)


class UnknownSettingError(SettingsError):
    """Raised when an unknown setting is provided.
    
    This exception can be raised in strict mode when a setting that
    is not recognized is provided.
    """
    
    def __init__(self, setting: SettingName, available_settings: Optional[List[SettingName]] = None) -> None:
        """Initialize an UnknownSettingError.
        
        Args:
            setting: The name of the unknown setting
            available_settings: List of available setting names
        """
        message = f"Unknown setting '{setting}'"
        suggestion = None
        if available_settings:
            # Find similar settings using simple string matching
            similar = [s for s in available_settings if setting.lower() in s.lower() or s.lower() in setting.lower()]
            if similar:
                suggestion = f"Did you mean one of: {', '.join(similar[:3])}?"
            else:
                suggestion = f"Available settings: {', '.join(sorted(available_settings)[:5])}..."
        
        super().__init__(message, setting=setting, suggestion=suggestion)
        self.available_settings = available_settings


class TheoryCompatibilityError(SettingsError):
    """Raised when settings are incompatible with the theory.
    
    This exception is raised when settings that are valid in general
    are not compatible with the specific theory being used.
    """
    
    def __init__(self, setting: SettingName, theory_name: TheoryName, reason: str, 
                 suggestion: Optional[str] = None) -> None:
        """Initialize a TheoryCompatibilityError.
        
        Args:
            setting: The name of the incompatible setting
            theory_name: The name of the theory
            reason: Why the setting is incompatible
            suggestion: A helpful suggestion for fixing the error
        """
        message = f"Setting '{setting}' is incompatible with {theory_name}: {reason}"
        super().__init__(message, setting=setting, suggestion=suggestion)
        self.theory_name = theory_name
        self.reason = reason