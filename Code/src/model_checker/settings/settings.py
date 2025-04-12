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
    
    def __init__(self, semantic_theory, global_defaults=None):
        """Initialize SettingsManager with a semantic theory.
        
        Args:
            semantic_theory: Dictionary containing semantic theory implementation
            global_defaults: Optional global defaults to use if theory doesn't define them
        """
        self.semantic_theory = semantic_theory
        
        # Get DEFAULT_GENERAL_SETTINGS from theory or fall back to global defaults
        semantics_class = semantic_theory.get("semantics")
        theory_defaults = getattr(semantics_class, "DEFAULT_GENERAL_SETTINGS", None)
        
        # Always prefer theory-specific defaults over global defaults
        self.DEFAULT_GENERAL_SETTINGS = theory_defaults if theory_defaults is not None else (global_defaults or {})
        
        # Get DEFAULT_EXAMPLE_SETTINGS from theory
        self.DEFAULT_EXAMPLE_SETTINGS = semantic_theory["semantics"].DEFAULT_EXAMPLE_SETTINGS
    
    def validate_general_settings(self, user_general_settings):
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
            
        merged_settings = self.DEFAULT_GENERAL_SETTINGS.copy()
        
        # Check for unknown settings (but don't warn if they're valid example settings)
        for key in user_general_settings:
            if key not in self.DEFAULT_GENERAL_SETTINGS and key not in self.DEFAULT_EXAMPLE_SETTINGS:
                print(f"Warning: Unknown general setting '{key}' not found in any settings definition")
        
        # Merge valid settings
        valid_keys = set(user_general_settings.keys()).intersection(self.DEFAULT_GENERAL_SETTINGS.keys())
        
        for key in valid_keys:
            merged_settings[key] = user_general_settings[key]
            
        return merged_settings
    
    def validate_example_settings(self, user_example_settings):
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
            
        merged_settings = self.DEFAULT_EXAMPLE_SETTINGS.copy()
        
        # Check for unknown settings
        for key in user_example_settings:
            if key not in self.DEFAULT_EXAMPLE_SETTINGS:
                print(f"Warning: Unknown example setting '{key}' not in DEFAULT_EXAMPLE_SETTINGS")
        
        # Merge valid settings
        valid_keys = set(user_example_settings.keys()).intersection(self.DEFAULT_EXAMPLE_SETTINGS.keys())
        for key in valid_keys:
            merged_settings[key] = user_example_settings[key]
            
        return merged_settings
    
    def apply_flag_overrides(self, settings, module_flags):
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
            
        merged_settings = settings.copy()
        
        # For test compatibility: if this is a mock object, treat all attributes as provided flags
        is_mock = not hasattr(module_flags, '_parsed_args')
        
        # Determine which flags were actually provided on the command line
        # This is based on the raw arguments stored in _parsed_args
        user_provided_flags = set()
        
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
        
        # Apply flag overrides 
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
                # Only warn if it's not found in either location and not a standard arg like load_theory
                elif key not in ['load_theory', 'upgrade', 'version']:
                    print(f"Warning: Flag '{key}' doesn't correspond to any known setting")
                
        return merged_settings
    
    def get_complete_settings(self, user_general_settings, user_example_settings, module_flags):
        """Get complete settings with all validations and overrides applied.
        
        Args:
            user_general_settings: Dictionary of user-provided general settings or None
            user_example_settings: Dictionary of user-provided example settings or None
            module_flags: Object containing command-line flags
            
        Returns:
            Dictionary of final merged settings with all validations and overrides applied
        """
        # Start with validated general settings
        general_settings = self.validate_general_settings(user_general_settings)
        
        # Then validate and merge example settings
        example_settings = self.validate_example_settings(user_example_settings)
        
        # Combine general and example settings (example settings take precedence)
        combined_settings = general_settings.copy()
        combined_settings.update(example_settings)
        
        # Apply flag overrides as final step
        final_settings = self.apply_flag_overrides(combined_settings, module_flags)
        
        return final_settings

# Global defaults as a fallback if theory doesn't define them
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "align_vertically": False,
}
