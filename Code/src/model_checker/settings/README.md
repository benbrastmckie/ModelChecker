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

## Implementing New Settings

When implementing new settings for existing or new theories in the ModelChecker framework, follow these guidelines to ensure consistency and proper integration with the settings system.

### Adding Settings to a Theory

1. **Identify Need**: Determine if your theory genuinely needs a new setting. New settings should:
   - Control specific aspects of semantics relevant to your theory
   - Modify constraint generation behavior
   - Configure output or visualization features

2. **Define in DEFAULT_EXAMPLE_SETTINGS or DEFAULT_GENERAL_SETTINGS**:
   ```python
   class YourSemantics(SemanticDefaults):
       DEFAULT_EXAMPLE_SETTINGS = {
           # Existing settings
           'N': 3,
           'max_time': 1,
           # New setting with default value
           'your_new_setting': default_value,
       }
   ```

3. **Use the Setting in Code**: Access through the `self.settings` dictionary:
   ```python
   if self.settings['your_new_setting']:
       # Implement behavior when setting is enabled
   ```

4. **Document the Setting**: Add comments explaining the purpose and impact of your setting.

### Adding Command-Line Flags

To expose a setting as a command-line flag:

1. **Update the CLI Module**: Add your flag to the appropriate argument parser in `cli.py`:
   ```python
   parser.add_argument(
       '--your-flag', '-y',  # Long and short forms
       dest='your_new_setting',  # Must match the setting name
       action='store_true',  # For boolean flags
       help='Description of what this flag does'
   )
   ```

2. **For Non-Boolean Settings**: Use appropriate argument type:
   ```python
   parser.add_argument(
       '--value-flag', '-v',
       dest='value_setting',
       type=int,  # Specify type (int, float, str)
       default=None,  # Allow None to detect if user provided it
       help='Description of what this flag does'
   )
   ```

### Testing New Settings

1. **Add Unit Tests**: Create test cases that verify:
   - Setting is properly passed from CLI to example
   - Setting triggers expected behavior changes
   - Setting defaults work correctly

2. **Test Flag Overrides**: Verify command-line flags properly override defaults:
   ```python
   # In test_settings.py
   def test_your_new_setting_flag_override():
       # Setup mock args with your flag
       mock_args = Mock()
       mock_args.your_new_setting = True
       # Verify it overrides the default in the final settings
   ```

### Example: Adding a "normalize" Setting

Here's a complete example of adding a new "normalize" setting that normalizes state representations:

1. **Update the Semantic Class**:
   ```python
   class YourSemantics(SemanticDefaults):
       DEFAULT_EXAMPLE_SETTINGS = {
           'N': 3,
           'max_time': 1,
           'normalize': False,  # New setting
       }
       
       def process_state(self, state):
           if self.settings['normalize']:
               return self.normalize_state(state)
           return state
           
       def normalize_state(self, state):
           # Implementation of normalization
           pass
   ```

2. **Add CLI Flag**:
   ```python
   # In cli.py
   parser.add_argument(
       '--normalize', '-n',
       dest='normalize',
       action='store_true',
       help='Normalize state representations for cleaner output'
   )
   ```

3. **Document the Setting**:
   - Add to this README.md under "Example Settings"
   - Update any relevant theory documentation
   - Include examples of usage in docstrings

### Best Practices

1. **Theory-Specific vs. Global**: Consider if your setting should be theory-specific or available to all theories
2. **Default Values**: Choose defaults that make the system work without user intervention
3. **Naming**: Use clear, descriptive names that indicate the setting's purpose
4. **Fail Fast**: If a setting is used incorrectly, let errors occur naturally rather than adding complex validation
5. **Consistency**: Follow existing naming patterns and behavior conventions
6. **Documentation**: Always update this documentation when adding new settings
