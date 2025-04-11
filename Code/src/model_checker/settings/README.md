# Settings System Implementation

This document describes the implementation of the settings management system for ModelChecker according to the specification in notes/settings.md.

## Overview

We have implemented a centralized settings management system using the SettingsManager class. This implementation provides:

1. **Explicit Defaults**: Each semantic theory defines its own default settings
2. **Validation**: Settings are validated against defaults with warnings for unknown settings
3. **Clear Priority**: Settings flow from defaults to user general settings to example settings to flags
4. **No Silent Failures**: Unknown settings trigger warnings rather than being silently ignored
5. **Clear Data Flow**: Settings are explicitly passed between components

## Implementation Details

### 1. SettingsManager Class

The core of the implementation is the `SettingsManager` class in `settings.py`. This class handles:

- Validating general and example settings against their defaults
- Warning about unknown settings without failing
- Merging settings according to priority rules
- Applying command-line flag overrides as the final step

The class follows the specified guidelines:
- Only settings defined in DEFAULT_GENERAL_SETTINGS and DEFAULT_EXAMPLE_SETTINGS are allowed
- Unknown settings trigger warnings
- Flag overrides are applied as the final step

### 2. Integration with BuildModule and BuildExample

Both `BuildModule` and `BuildExample` have been updated to use the `SettingsManager`:

- `BuildModule` initializes a SettingsManager with the default theory
- Each `BuildExample` gets its own SettingsManager with its specific theory
- The full settings pipeline flows consistently through both classes

### 3. Theory-Specific General Settings

Theories can now define their own DEFAULT_GENERAL_SETTINGS, as shown in the BimodalSemantics class:

```python
# Bimodal-specific general settings defaults
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}
```

### 4. Tests

A comprehensive test suite validates the settings system:

- Unit tests in `test_settings.py` verify each SettingsManager method
- Integration tests in `test_settings_pipeline.py` verify the complete settings flow
- Tests confirm that unknown settings are properly warned about and filtered out

## Usage

To use the settings system in a semantic theory:

1. Define DEFAULT_EXAMPLE_SETTINGS in your semantic theory class
2. Optionally define DEFAULT_GENERAL_SETTINGS for theory-specific general settings
3. Access the merged settings via self.settings in your components

For example:

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        # ... other example-specific settings
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        'print_z3': False,
        # ... other general settings
    }
```

## Benefits

This implementation offers several advantages:

1. **Centralized Management**: All settings logic is in one place
2. **Explicit Validation**: Unknown settings are caught and warned about
3. **Clearer Errors**: Specific warnings about unknown settings
4. **Theory-Specific Settings**: Each theory can define its own defaults
5. **Maintainability**: Simpler code that follows the Single Responsibility Principle

## Future Improvements

Potential enhancements for the future:

1. **Type Checking**: Validate that settings have the correct types
2. **Required vs Optional**: Distinguish between required and optional settings
3. **Documentation**: Generate settings documentation from the code
4. **Schema Validation**: More sophisticated schema validation for complex settings
5. **UI Components**: Settings UI for interactive environments
