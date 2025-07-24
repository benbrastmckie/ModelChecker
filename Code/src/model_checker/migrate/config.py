"""
Configuration migration utilities.

This module provides tools for migrating old dictionary-based settings
to new typed configuration objects.
"""

import warnings
from typing import Dict, Any, Optional, Set
from dataclasses import dataclass, field


@dataclass
class ModelConfig:
    """Modern configuration object for ModelChecker.
    
    This replaces the old dictionary-based settings with a typed configuration
    object that provides better validation and documentation.
    """
    num_propositions: int = 3
    max_time: float = 5.0
    contingent: bool = True
    expect_valid: bool = True
    non_empty_valuations: bool = True
    debug_constraints: bool = False
    model: bool = True
    iteration_limit: Optional[int] = None
    
    # Additional advanced settings
    z3_timeout: Optional[int] = None
    use_parallel: bool = False
    random_seed: Optional[int] = None
    
    def __post_init__(self):
        """Validate configuration after initialization."""
        if self.num_propositions < 1:
            raise ValueError("num_propositions must be at least 1")
        if self.max_time <= 0:
            raise ValueError("max_time must be positive")
        if self.iteration_limit is not None and self.iteration_limit < 1:
            raise ValueError("iteration_limit must be at least 1")
    
    @classmethod
    def from_dict(cls, settings: Dict[str, Any]) -> 'ModelConfig':
        """Create ModelConfig from old-style settings dictionary."""
        return migrate_settings_dict(settings)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for backward compatibility."""
        return {
            'N': self.num_propositions,
            'max_time': self.max_time,
            'contingent': self.contingent,
            'expectation': self.expect_valid,
            'non_empty': self.non_empty_valuations,
            'print_constraints': self.debug_constraints,
            'model': self.model,
        }


class SettingsTranslator:
    """Utility class for translating between old and new settings formats."""
    
    # Mapping from old setting names to new ModelConfig attributes
    SETTING_MAPPINGS = {
        'N': 'num_propositions',
        'max_time': 'max_time',
        'contingent': 'contingent',
        'expectation': 'expect_valid',
        'non_empty': 'non_empty_valuations',
        'print_constraints': 'debug_constraints',
        'model': 'model',
        'iteration_limit': 'iteration_limit',
        'z3_timeout': 'z3_timeout',
        'use_parallel': 'use_parallel',
        'random_seed': 'random_seed',
    }
    
    # Settings that have been deprecated and should be ignored
    DEPRECATED_SETTINGS = {
        'old_style_output',
        'legacy_mode',
        'verbose_logging',
    }
    
    # Settings that need value transformation
    VALUE_TRANSFORMATIONS = {
        'expect_valid': lambda x: bool(x) if x is not None else True,
        'num_propositions': lambda x: int(x) if x is not None else 3,
        'max_time': lambda x: float(x) if x is not None else 5.0,
    }
    
    @classmethod
    def translate_dict(cls, old_settings: Dict[str, Any]) -> Dict[str, Any]:
        """Translate an old settings dictionary to new format.
        
        Args:
            old_settings: Dictionary with old-style settings
            
        Returns:
            Dictionary with new-style settings
        """
        new_settings = {}
        warnings_issued = set()
        
        for old_key, value in old_settings.items():
            if old_key in cls.DEPRECATED_SETTINGS:
                if old_key not in warnings_issued:
                    warnings.warn(
                        f"Setting '{old_key}' is deprecated and will be ignored",
                        DeprecationWarning,
                        stacklevel=3
                    )
                    warnings_issued.add(old_key)
                continue
            
            if old_key in cls.SETTING_MAPPINGS:
                new_key = cls.SETTING_MAPPINGS[old_key]
                
                # Apply value transformation if needed
                if new_key in cls.VALUE_TRANSFORMATIONS:
                    try:
                        transformed_value = cls.VALUE_TRANSFORMATIONS[new_key](value)
                        new_settings[new_key] = transformed_value
                    except (ValueError, TypeError) as e:
                        warnings.warn(
                            f"Could not transform value for '{old_key}': {e}. Using default.",
                            UserWarning,
                            stacklevel=3
                        )
                else:
                    new_settings[new_key] = value
            else:
                # Unknown setting - warn but preserve
                if old_key not in warnings_issued:
                    warnings.warn(
                        f"Unknown setting '{old_key}' - please check if this is still needed",
                        UserWarning,
                        stacklevel=3
                    )
                    warnings_issued.add(old_key)
                new_settings[old_key] = value
        
        return new_settings
    
    @classmethod
    def reverse_translate_dict(cls, new_settings: Dict[str, Any]) -> Dict[str, Any]:
        """Translate new settings back to old format for backward compatibility.
        
        Args:
            new_settings: Dictionary with new-style settings
            
        Returns:
            Dictionary with old-style settings
        """
        reverse_mapping = {v: k for k, v in cls.SETTING_MAPPINGS.items()}
        old_settings = {}
        
        for new_key, value in new_settings.items():
            if new_key in reverse_mapping:
                old_key = reverse_mapping[new_key]
                old_settings[old_key] = value
            else:
                # Keep unknown settings as-is
                old_settings[new_key] = value
        
        return old_settings


def migrate_settings_dict(old_settings: Dict[str, Any]) -> ModelConfig:
    """Convert old settings dictionary to new ModelConfig object.
    
    This is the main entry point for migrating settings from the old
    dictionary-based format to the new typed configuration object.
    
    Args:
        old_settings: Dictionary containing old-style settings
        
    Returns:
        ModelConfig object with migrated settings
        
    Raises:
        ValueError: If settings contain invalid values
    """
    if not isinstance(old_settings, dict):
        raise TypeError(f"Expected dict, got {type(old_settings)}")
    
    # Translate the settings
    new_settings = SettingsTranslator.translate_dict(old_settings)
    
    # Create ModelConfig object
    try:
        return ModelConfig(**new_settings)
    except TypeError as e:
        # Handle unexpected keyword arguments
        valid_fields = {f.name for f in ModelConfig.__dataclass_fields__.values()}
        filtered_settings = {k: v for k, v in new_settings.items() if k in valid_fields}
        
        invalid_keys = set(new_settings.keys()) - valid_fields
        if invalid_keys:
            warnings.warn(
                f"Ignoring unknown settings: {invalid_keys}",
                UserWarning,
                stacklevel=2
            )
        
        return ModelConfig(**filtered_settings)


def create_default_config(**overrides) -> ModelConfig:
    """Create a default ModelConfig with optional overrides.
    
    Args:
        **overrides: Keyword arguments to override default values
        
    Returns:
        ModelConfig with default values and overrides applied
    """
    return ModelConfig(**overrides)


def validate_settings_compatibility(old_settings: Dict[str, Any]) -> Dict[str, Any]:
    """Validate that old settings can be successfully migrated.
    
    Args:
        old_settings: Dictionary with old-style settings
        
    Returns:
        Dictionary with validation results:
        - 'valid': bool - whether settings can be migrated
        - 'warnings': list - list of warning messages
        - 'errors': list - list of error messages
        - 'translated': dict - the translated settings (if valid)
    """
    result = {
        'valid': True,
        'warnings': [],
        'errors': [],
        'translated': {}
    }
    
    try:
        # Capture warnings during translation
        with warnings.catch_warnings(record=True) as warning_list:
            warnings.simplefilter("always")
            
            config = migrate_settings_dict(old_settings)
            result['translated'] = config.to_dict()
            
            # Convert warnings to strings
            result['warnings'] = [str(w.message) for w in warning_list]
            
    except Exception as e:
        result['valid'] = False
        result['errors'].append(str(e))
    
    return result


# Example usage and testing
def _example_migrations():
    """Examples of settings migration for testing."""
    
    test_cases = [
        # Basic settings
        {
            "N": 3,
            "max_time": 5,
            "contingent": True,
            "expectation": True
        },
        
        # Settings with deprecated keys
        {
            "N": 4,
            "max_time": 10,
            "old_style_output": True,  # deprecated
            "contingent": False
        },
        
        # Settings with unknown keys
        {
            "N": 2,
            "custom_setting": "value",
            "experimental_feature": True
        },
        
        # Settings with type issues
        {
            "N": "3",  # string instead of int
            "max_time": "5.0",  # string instead of float
            "contingent": "true"  # string instead of bool
        }
    ]
    
    for i, test_case in enumerate(test_cases, 1):
        print(f"\n=== Test Case {i} ===")
        print(f"Original: {test_case}")
        
        # Validate migration
        validation = validate_settings_compatibility(test_case)
        print(f"Valid: {validation['valid']}")
        
        if validation['warnings']:
            print("Warnings:")
            for warning in validation['warnings']:
                print(f"  - {warning}")
        
        if validation['errors']:
            print("Errors:")
            for error in validation['errors']:
                print(f"  - {error}")
        
        if validation['valid']:
            # Perform actual migration
            try:
                config = migrate_settings_dict(test_case)
                print(f"Migrated: {config}")
                print(f"Back to dict: {config.to_dict()}")
            except Exception as e:
                print(f"Migration failed: {e}")


if __name__ == "__main__":
    _example_migrations()