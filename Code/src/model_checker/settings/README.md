# Settings System Implementation

This document describes the implementation of the settings management system for ModelChecker.

## Overview

We have implemented a centralized settings management system using the SettingsManager class. This implementation provides:

1. **Explicit Defaults**: Each semantic theory defines its own appropriate default settings
2. **Validation**: Settings are validated against theory-specific defaults with warnings for unknown settings
3. **Clear Priority**: Settings flow from defaults to user general settings to example settings to flags
4. **No Silent Failures**: Unknown settings trigger warnings rather than being silently ignored
5. **Clear Data Flow**: Settings are explicitly passed between components

## Implementation Details

### 1. SettingsManager Class

The core of the implementation is the `SettingsManager` class in `settings.py`. This class handles:

- Validating general and example settings against their theory-specific defaults
- Warning about unknown settings without failing
- Merging settings according to priority rules
- Applying command-line flag overrides as the final step

The class follows these guidelines:
- Only settings defined in DEFAULT_GENERAL_SETTINGS and DEFAULT_EXAMPLE_SETTINGS are allowed for a theory
- Unknown settings trigger warnings when provided by the user
- Flag overrides are applied as the final step and only trigger warnings when explicitly provided by the user

### 2. Integration with BuildModule and BuildExample

Both `BuildModule` and `BuildExample` have been updated to use the `SettingsManager`:

- `BuildModule` initializes a SettingsManager with the default theory
- Each `BuildExample` gets its own SettingsManager with its specific theory
- The full settings pipeline flows consistently through both classes

### 3. Theory-Specific Settings

Importantly, **each theory only needs to define settings that are relevant to it**. There's no requirement to include every possible setting in every theory. For example:

```python
# Bimodal-specific general settings include align_vertically
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "align_vertically": False,  # Only relevant for bimodal theory
}

# Default theory doesn't include align_vertically as it's not applicable
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}
```

Similarly, DEFAULT_EXAMPLE_SETTINGS should only include settings that make sense for the specific theory:

```python
# Bimodal example settings include 'M' for temporal dimension
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 2,           # Number of world states
    'M': 2,           # Number of times (only relevant for bimodal)
    'contingent': False,
    'disjoint': False,
    'max_time': 1,
    'expectation': True,
}

# Default theory doesn't include 'M' since it doesn't have a temporal dimension
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 3,
    'contingent': False,
    'disjoint': False,
    'max_time': 1,
    'expectation': True,
}
```

### Warnings

The settings system has been designed to only warn about unknown settings when:

1. A user explicitly provides a flag that doesn't correspond to a setting in the theory
2. A user includes a setting in example_settings that isn't defined in the theory's DEFAULT_EXAMPLE_SETTINGS
3. A user includes a setting in general_settings that isn't defined in the theory's DEFAULT_GENERAL_SETTINGS

This means that if a flag like `-e` (non_empty) is provided but the theory doesn't define 'non_empty' in its settings, a warning will be displayed - but only if the user explicitly used that flag.

## Usage

To use the settings system in a semantic theory:

1. Define DEFAULT_EXAMPLE_SETTINGS in your semantic theory class with **only the settings relevant to your theory**
2. Optionally define DEFAULT_GENERAL_SETTINGS for theory-specific general settings, again only including relevant settings
3. Access the merged settings via self.settings in your components

For example:

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,                # Always include N for state count
        'max_time': 1,         # Always include max_time for solver timeout
        'contingent': False,   # Include if your theory supports contingency
        # Do NOT include settings that don't apply to your theory
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        'print_z3': False,     # Include debugging settings as needed
        'save_output': False,  # Include output settings as needed
        # Only include settings that make sense for your theory
    }
```

## Benefits

This implementation offers several advantages:

1. **Centralized Management**: All settings logic is in one place
2. **Explicit Validation**: Unknown settings are caught and warned about only when explicitly provided
3. **Clearer Errors**: Specific warnings about unknown settings
4. **Theory-Specific Settings**: Each theory defines only the settings relevant to it
5. **Maintainability**: Simpler code that follows the Single Responsibility Principle

## Common Settings by Category

### General Settings

These settings control output, debugging, and general behavior:

- **print_impossible**: Print impossible states in output (boolean)
- **print_constraints**: Print constraints when no model found (boolean)
- **print_z3**: Print raw Z3 model or unsat core (boolean)
- **save_output**: Prompt to save output (boolean)
- **maximize**: Compare semantic theories by maximizing model size (boolean)
- **align_vertically**: Display world histories vertically (boolean, primarily for bimodal theory)

### Example Settings

These settings control model generation for specific examples:

- **N**: Number of atomic states (integer, required by all theories)
- **M**: Number of time points (integer, required only by temporal theories like bimodal)
- **contingent**: Make atomic propositions contingent (boolean)
- **disjoint**: Make atomic propositions have disjoint subject-matters (boolean)
- **non_empty**: Make atomic propositions have non-empty verifier/falsifier sets (boolean)
- **non_null**: Prevent null states from being verifiers/falsifiers (boolean)
- **max_time**: Maximum solver execution time (integer, required by all theories)
- **expectation**: Whether a model is expected to exist (boolean, for testing)

## Future Improvements

Potential enhancements for the future:

1. **Type Checking**: Validate that settings have the correct types
2. **Required vs Optional**: Distinguish between required and optional settings
3. **Documentation**: Generate settings documentation from the code
4. **Schema Validation**: More sophisticated schema validation for complex settings
5. **UI Components**: Settings UI for interactive environments
