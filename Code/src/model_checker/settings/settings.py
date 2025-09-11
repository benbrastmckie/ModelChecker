"""Settings management module for ModelChecker.

This module provides centralized settings management for the ModelChecker framework,
including validation, merging, and overriding of settings from different sources.

The settings system follows a clear priority order:
1. Default settings defined in semantic theories
2. User-defined general settings at the module level
3. User-defined example-specific settings
4. Command-line flags (highest priority)

The module ensures appropriate validation and warning messages for unknown settings.
"""

import os
from typing import Dict, Any, Optional, Set
from .errors import (
    SettingsError, ValidationError, TypeConversionError,
    RangeError, MissingRequiredError, UnknownSettingError,
    TheoryCompatibilityError
)

# Configuration via environment variables
VERBOSE_SETTINGS = os.environ.get('MODELCHECKER_VERBOSE', '').lower() == 'true'
SUPPRESS_COMPARISON_WARNINGS = os.environ.get(
    'MODELCHECKER_SUPPRESS_COMPARISON_WARNINGS', ''
).lower() == 'true'

class SettingsManager:
    """Manages settings across different sources with proper validation and overriding.
    
    This class is responsible for:
    - Validating user-provided settings against theory defaults
    - Warning about unknown settings without failing
    - Merging settings according to priority rules
    - Applying command-line flag overrides
    
    Attributes:
        semantic_theory: The semantic theory containing default settings
        DEFAULT_GENERAL_SETTINGS: General settings defaults for the module
        DEFAULT_EXAMPLE_SETTINGS: Example-specific settings defaults
    """
    
    def __init__(self, semantic_theory: Dict[str, Any], global_defaults: Optional[Dict[str, Any]] = None, 
                 theory_name: Optional[str] = None, is_comparison: bool = False, 
                 strict_mode: bool = False) -> None:
        """Initialize SettingsManager with a semantic theory.
        
        Args:
            semantic_theory: Dictionary containing semantic theory implementation
            global_defaults: Optional global defaults to use if theory doesn't define them
            theory_name: Name of the theory for context in warnings
            is_comparison: Whether multiple theories are being compared
            strict_mode: If True, raise exceptions for unknown settings instead of warnings
        """
        self.semantic_theory: Dict[str, Any] = semantic_theory
        self.theory_name: Optional[str] = theory_name
        self.is_comparison: bool = is_comparison
        self.strict_mode: bool = strict_mode
        
        # Get DEFAULT_GENERAL_SETTINGS from theory or fall back to global defaults
        semantics_class = semantic_theory.get("semantics")
        theory_defaults = getattr(semantics_class, "DEFAULT_GENERAL_SETTINGS", None)
        
        # Always prefer theory-specific defaults over global defaults
        self.DEFAULT_GENERAL_SETTINGS: Dict[str, Any] = theory_defaults if theory_defaults is not None else (global_defaults or {})
        
        # Get DEFAULT_EXAMPLE_SETTINGS from theory
        self.DEFAULT_EXAMPLE_SETTINGS: Dict[str, Any] = semantic_theory["semantics"].DEFAULT_EXAMPLE_SETTINGS
        
        # If no theory name provided, try to get it from the semantics class
        if self.theory_name is None:
            self.theory_name = getattr(semantics_class, '__name__', 'unknown').replace('Semantics', '')
    
    def validate_general_settings(self, user_general_settings: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        """Validate user general settings against defaults and warn about unknown settings.
        
        Args:
            user_general_settings: Dictionary of user-provided general settings or None
            
        Returns:
            Dictionary of merged settings starting with defaults and applying valid user settings
            
        Note:
            Prints warnings for any settings not defined in DEFAULT_GENERAL_SETTINGS or DEFAULT_EXAMPLE_SETTINGS
        """
        
        if user_general_settings is None:
            return self.DEFAULT_GENERAL_SETTINGS.copy()
            
        merged_settings: Dict[str, Any] = self.DEFAULT_GENERAL_SETTINGS.copy()
        
        # Check for unknown settings (but don't warn if they're valid example settings)
        for key in user_general_settings:
            if key not in self.DEFAULT_GENERAL_SETTINGS and key not in self.DEFAULT_EXAMPLE_SETTINGS:
                self._warn_unknown_setting(key, 'general')
        
        # Merge valid settings
        valid_keys: Set[str] = set(user_general_settings.keys()).intersection(self.DEFAULT_GENERAL_SETTINGS.keys())
        
        for key in valid_keys:
            merged_settings[key] = user_general_settings[key]
            
        return merged_settings
    
    def validate_example_settings(self, user_example_settings: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        """Validate user example settings against defaults and warn about unknown settings.
        
        Args:
            user_example_settings: Dictionary of user-provided example settings or None
            
        Returns:
            Dictionary of merged settings starting with defaults and applying valid user settings
            
        Note:
            Prints warnings for any settings not defined in DEFAULT_EXAMPLE_SETTINGS
        """
        if user_example_settings is None:
            return self.DEFAULT_EXAMPLE_SETTINGS.copy()
            
        merged_settings: Dict[str, Any] = self.DEFAULT_EXAMPLE_SETTINGS.copy()
        
        # Check for unknown settings
        for key in user_example_settings:
            if key not in self.DEFAULT_EXAMPLE_SETTINGS:
                self._warn_unknown_setting(key, 'example')
        
        # Merge valid settings
        valid_keys: Set[str] = set(user_example_settings.keys()).intersection(self.DEFAULT_EXAMPLE_SETTINGS.keys())
        for key in valid_keys:
            merged_settings[key] = user_example_settings[key]
            
        return merged_settings
    
    def apply_flag_overrides(self, settings: Dict[str, Any], module_flags: Any) -> Dict[str, Any]:
        """Apply module flags as final overrides to the settings.
        
        Args:
            settings: Dictionary of already merged settings
            module_flags: Object containing command-line flags
            
        Returns:
            Dictionary of settings with flag overrides applied
        
        Note:
            Prints warnings only for flags actually provided by the user that don't 
            correspond to an existing setting
        """
        if module_flags is None:
            return settings
            
        merged_settings: Dict[str, Any] = settings.copy()
        
        # Determine if this is a mock object and which flags were provided
        is_mock: bool = self._is_mock_object(module_flags)
        user_provided_flags: Set[str] = self._extract_user_provided_flags(module_flags, is_mock)
        
        # Apply overrides from flags
        self._apply_overrides(merged_settings, module_flags, user_provided_flags, is_mock)
                
        return merged_settings
    
    def _is_mock_object(self, module_flags: Any) -> bool:
        """Check if module_flags is a mock object for testing.
        
        Args:
            module_flags: Object containing command-line flags
            
        Returns:
            True if this is a mock object, False otherwise
        """
        return not hasattr(module_flags, '_parsed_args')
    
    def _extract_user_provided_flags(self, module_flags: Any, is_mock: bool) -> Set[str]:
        """Extract which flags were actually provided by the user.
        
        Args:
            module_flags: Object containing command-line flags
            is_mock: Whether this is a mock object
            
        Returns:
            Set of flag names that were explicitly provided
        """
        user_provided_flags: Set[str] = set()
        
        # For real argparse objects, extract flags from the raw command line arguments
        if not is_mock and hasattr(module_flags, '_parsed_args') and module_flags._parsed_args:
            for arg in module_flags._parsed_args:
                if arg.startswith('--'):
                    # Long format (--flag)
                    flag_name = arg[2:]
                    # Handle arguments with values (--flag=value)
                    if '=' in flag_name:
                        flag_name = flag_name.split('=')[0]
                    user_provided_flags.add(flag_name)
                elif arg.startswith('-') and len(arg) == 2:
                    # Short format (-f)
                    short_flag = arg[1]
                    # Convert to long name if mapping exists
                    if hasattr(module_flags, '_short_to_long'):
                        long_name = module_flags._short_to_long.get(short_flag)
                        if long_name:
                            user_provided_flags.add(long_name)
        
        return user_provided_flags
    
    def _apply_overrides(self, merged_settings: Dict[str, Any], module_flags: Any, 
                        user_provided_flags: Set[str], is_mock: bool) -> None:
        """Apply flag overrides to the merged settings.
        
        Args:
            merged_settings: Dictionary to update with overrides
            module_flags: Object containing command-line flags
            user_provided_flags: Set of flags explicitly provided by user
            is_mock: Whether this is a mock object
        """
        # Standard args that don't correspond to settings
        standard_args = {'load_theory', 'upgrade', 'version', 'save', 
                        'interactive', 'output_mode', 'sequential_files'}
        
        for key, value in vars(module_flags).items():
            # Skip internal attributes and file_path
            if key.startswith('_') or key == 'file_path':
                continue
                
            # For real argparse objects, only override if flag was explicitly provided
            # For mock objects in tests, apply all attributes as flags
            if is_mock or key in user_provided_flags:
                # Override if the setting exists in merged settings
                if key in merged_settings:
                    merged_settings[key] = value
                # Or if it exists in DEFAULT_EXAMPLE_SETTINGS but not yet in merged_settings
                elif key in self.DEFAULT_EXAMPLE_SETTINGS:
                    # Add it to merged settings so it's available
                    merged_settings[key] = value
                # Only warn if it's not found in either location and not a standard arg
                elif key not in standard_args:
                    print(f"Warning: Flag '{key}' doesn't correspond to any known setting")
    
    def _warn_unknown_setting(self, setting_name: str, setting_type: str) -> None:
        """Centralized warning logic with context awareness.
        
        Args:
            setting_name: Name of the unknown setting
            setting_type: Type of setting ('general' or 'example')
        
        Raises:
            UnknownSettingError: If strict_mode is True
        """
        if self.strict_mode:
            # In strict mode, raise an exception
            if setting_type == 'general':
                available = list(self.DEFAULT_GENERAL_SETTINGS.keys())
            else:
                available = list(self.DEFAULT_EXAMPLE_SETTINGS.keys())
            raise UnknownSettingError(setting_name, available)
        
        if self.is_comparison:
            # During comparison, suppress warnings unless verbose mode is on
            if VERBOSE_SETTINGS and not SUPPRESS_COMPARISON_WARNINGS:
                print(f"Info: Setting '{setting_name}' not supported by {self.theory_name}")
        else:
            # Normal warning for single theory usage
            print(f"Warning: Unknown {setting_type} setting '{setting_name}' "
                  f"not in {self.theory_name}'s DEFAULT_{setting_type.upper()}_SETTINGS")
    
    def _validate_setting_type(self, setting_name: str, value: Any, expected_type: type) -> Any:
        """Validate and convert a setting to the expected type.
        
        Args:
            setting_name: Name of the setting
            value: The value to validate
            expected_type: The expected type
            
        Returns:
            The validated/converted value
            
        Raises:
            TypeConversionError: If conversion fails
        """
        if isinstance(value, expected_type):
            return value
            
        # Try to convert
        try:
            if expected_type == bool:
                # Special handling for bool conversion
                if isinstance(value, str):
                    return value.lower() in ('true', '1', 'yes', 'on')
                return bool(value)
            elif expected_type == int:
                return int(value)
            elif expected_type == float:
                return float(value)
            elif expected_type == str:
                return str(value)
            else:
                return expected_type(value)
        except (ValueError, TypeError) as e:
            raise TypeConversionError(setting_name, value, expected_type) from e
    
    def _validate_setting_range(self, setting_name: str, value: Any, 
                               min_value: Optional[Any] = None, 
                               max_value: Optional[Any] = None) -> None:
        """Validate that a setting is within the acceptable range.
        
        Args:
            setting_name: Name of the setting
            value: The value to validate
            min_value: Minimum acceptable value
            max_value: Maximum acceptable value
            
        Raises:
            RangeError: If value is out of range
        """
        if min_value is not None and value < min_value:
            raise RangeError(setting_name, value, min_value=min_value)
        if max_value is not None and value > max_value:
            raise RangeError(setting_name, value, max_value=max_value)
    
    def get_complete_settings(self, user_general_settings: Optional[Dict[str, Any]], 
                              user_example_settings: Optional[Dict[str, Any]], 
                              module_flags: Any) -> Dict[str, Any]:
        """Get complete settings with all validations and overrides applied.
        
        Args:
            user_general_settings: Dictionary of user-provided general settings or None
            user_example_settings: Dictionary of user-provided example settings or None
            module_flags: Object containing command-line flags
            
        Returns:
            Dictionary of final merged settings with all validations and overrides applied
        """
        # Start with validated general settings
        general_settings: Dict[str, Any] = self.validate_general_settings(user_general_settings)
        
        # Then validate and merge example settings
        example_settings: Dict[str, Any] = self.validate_example_settings(user_example_settings)
        
        # Combine general and example settings (example settings take precedence)
        combined_settings: Dict[str, Any] = general_settings.copy()
        combined_settings.update(example_settings)
        
        # Apply flag overrides as final step
        final_settings: Dict[str, Any] = self.apply_flag_overrides(combined_settings, module_flags)
        
        return final_settings

# Global defaults as a fallback if theory doesn't define them
DEFAULT_GENERAL_SETTINGS: Dict[str, Any] = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "align_vertically": False,
}
