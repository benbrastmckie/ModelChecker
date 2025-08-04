# Settings Package: Configuration Management Framework

[← Back to ModelChecker API](../README.md) | [Theory Library →](../theory_lib/README.md) | [Builder Package →](../builder/README.md)

## Directory Structure
```
settings/
├── README.md               # This file - settings system overview
├── __init__.py            # Package exports and SettingsManager
├── settings_manager.py     # Core settings management and validation
├── default_settings.py     # Global default settings definitions
└── validation.py          # Settings validation utilities
```

## Overview

The **Settings Package** provides comprehensive configuration management for the ModelChecker framework, enabling **centralized settings coordination**, **theory-specific validation**, and **flexible parameter customization** across all components and semantic theories.

The system implements a **priority-based configuration hierarchy** where settings flow from theory defaults through user preferences to command-line overrides. It handles **theory-specific settings**, **validation and warnings**, and **comparison mode adaptation** to ensure consistent behavior across different semantic frameworks.

This centralized approach eliminates configuration inconsistencies, provides clear error messages for invalid settings, and enables seamless integration between command-line interfaces, interactive notebooks, and programmatic usage patterns throughout the framework.

## Configuration Architecture

### Priority-Based Configuration Hierarchy

Settings flow through a structured priority system:

```python
# Priority order (highest to lowest)
1. Command-line flags          # --print-z3, -N 4, etc.
2. Example-specific settings   # settings={'N': 3} in BuildExample
3. User general preferences    # general_settings in configuration
4. Theory-specific defaults    # DEFAULT_EXAMPLE_SETTINGS per theory
5. Framework global defaults   # Baseline settings for all theories
```

### SettingsManager Core Features

The `SettingsManager` provides centralized coordination:

- **Theory-Specific Validation**: Only settings defined in theory defaults are accepted
- **Warning System**: Unknown settings trigger warnings without failing operations
- **Comparison Mode Detection**: Automatically adjusts behavior for multi-theory operations
- **Type Checking**: Validates setting values against expected types and ranges
- **Clear Error Messages**: Specific guidance for configuration issues

### Framework Integration

The settings system integrates across all ModelChecker components:

- **Builder Package**: `BuildExample` and `BuildModule` use theory-specific settings managers
- **Command-Line Interface**: CLI flags are automatically mapped to settings validation  
- **Jupyter Integration**: Interactive widgets respect settings priorities and validation
- **Theory Implementations**: Each theory defines only settings relevant to its semantics

## Theory-Specific Configuration

### Semantic Theory Settings

Each theory defines only settings relevant to its semantic framework:

```python
# Bimodal theory includes temporal settings
class BimodalSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 2,                    # World states
        'M': 2,                    # Time points (bimodal-specific)
        'max_time': 1,
        'contingent': False,
        'align_vertically': False,  # Display setting for temporal models
    }

# Logos theory focuses on hyperintensional settings
class LogosSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,                    # More states for complex hyperintensional models
        'max_time': 1,
        'contingent': False,
        'disjoint': False,         # Subject-matter separation
        'non_empty': False,        # Verifier/falsifier requirements
    }

# Exclusion theory adds unilateral semantics settings
class ExclusionSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        'contingent': False,
        'coherence_check': True,   # Exclusion-specific validation
        'witness_optimization': False,  # Performance tuning
    }
```

### Settings Categories

**General Settings** (theory-wide behavior):
- Output control (`print_z3`, `print_constraints`, `save_output`)
- Debugging options (`print_impossible`, `maximize`)
- Theory-specific display (`align_vertically` for bimodal)

**Example Settings** (per-model configuration):
- Model size (`N` for states, `M` for time points)
- Semantic constraints (`contingent`, `disjoint`, `non_empty`)
- Solver configuration (`max_time`, `expectation`)
- Theory-specific options (coherence checks, optimization flags)

## Usage Patterns

### Basic Settings Management

```python
from model_checker import BuildExample, get_theory

# Create model with custom settings
theory = get_theory("exclusion")
model = BuildExample("test", theory,
                     settings={'N': 4, 'contingent': True, 'max_time': 5000})

# Settings are automatically validated against theory defaults
result = model.check_validity()
```

### Command-Line Integration

```bash
# Flag overrides take highest priority
./dev_cli.py -N 4 --contingent --print-z3 examples/modal.py

# Settings in example files are merged with flag overrides
# Example file: settings = {'N': 3, 'max_time': 2000}
# Final result: N=4 (from flag), max_time=2000 (from file), print_z3=True (from flag)
```

### Available Command-Line Flags

#### Core Settings Flags

**Model Configuration:**
- `-N <int>` or `--N <int>` - Number of atomic states in model space
- `--max-time <int>` - Maximum Z3 solver execution time in milliseconds
- `--expectation` - Whether a model is expected to exist (for testing)

**Semantic Constraints:**
- `--contingent` - Make atomic propositions contingent
- `--disjoint` - Require disjoint subject-matters
- `--non-empty` - Require non-empty verifier/falsifier sets
- `--non-null` - Prevent null states as verifiers/falsifiers

**Model Iteration:**
- `--iterate <int>` - Number of distinct models to find

#### Theory-Specific Flags

**Bimodal Theory:**
- `-M <int>` or `--M <int>` - Number of time points for temporal dimension
- `--align-vertically` - Display world histories vertically

**Exclusion Theory:**
- `--coherence-check` - Enable exclusion coherence validation
- `--witness-optimization` - Optimize witness structure generation

**Imposition Theory:**
- `--imposition-depth <int>` - Maximum depth for imposition operations
- `--state-modification` - Allow state modification patterns

#### Output and Debugging Flags

- `--print-impossible` - Show impossible states in output
- `--print-constraints` or `-p` - Display Z3 constraints when no model found
- `--print-z3` or `-z` - Show raw Z3 model or unsat core
- `--save-output` - Prompt to save output to file
- `--maximize` - Compare theories by maximizing model size

#### Usage Examples

```bash
# Basic model configuration
model-checker -N 5 examples/test.py

# Multiple flags with short and long forms
model-checker -p -z --contingent --iterate=3 examples/complex.py

# Theory-specific configuration
model-checker --M 4 --align-vertically examples/bimodal_test.py
model-checker --coherence-check --witness-optimization examples/exclusion_test.py

# Full debugging output
model-checker --print-z3 --print-constraints --print-impossible --max-time=10000 examples/debug.py
```

### Multi-Theory Comparison

```python
# Comparison mode automatically handles theory differences
from model_checker.builder import BuildModule

module = BuildModule({'compare': True, 'theories': ['logos', 'exclusion']})
module.run_comparison()  # Warnings suppressed for theory-specific settings
```

### Environment Variable Control

```bash
# Debug theory comparison behavior
MODELCHECKER_VERBOSE=true ./dev_cli.py examples.py

# Suppress comparison warnings entirely
MODELCHECKER_SUPPRESS_COMPARISON_WARNINGS=true ./dev_cli.py examples.py
```

## Validation and Warning System

### Warning Behavior

The settings system warns about unknown settings only when explicitly provided:

1. **Command-line flags** not defined in theory settings
2. **Example settings** not in theory's `DEFAULT_EXAMPLE_SETTINGS`
3. **General settings** not in theory's `DEFAULT_GENERAL_SETTINGS`

```python
# Example: logos theory doesn't define 'M' (time points)
# This triggers warning only if user explicitly sets it
model = BuildExample("test", logos_theory, settings={'M': 3})
# Warning: "Unknown setting 'M' for logos theory"
```

### Comparison Mode Adaptation

**Single Theory Mode**: Normal validation and warnings
**Multi-Theory Mode**: Suppressed warnings since theories have different capabilities

```python
# Single theory - settings warnings shown when using non-relevant settings
# Multi-theory comparison - warnings suppressed since theories have different capabilities
# See the Examples Standard documentation for how to properly configure settings
```

## Documentation

### For New Users
- **[ModelChecker API Guide](../README.md)** - Basic framework usage and configuration
- **[Theory Selection Guide](../theory_lib/README.md#theory-selection-guide)** - Understanding theory-specific settings
- **[Command-Line Reference](../../../../CLAUDE.md#quick-reference)** - CLI flags and options

### For Researchers  
- **[Advanced Configuration](#advanced-configuration)** - Complex settings patterns and optimization
- **[Multi-Theory Comparison](#multi-theory-comparison)** - Settings behavior across semantic frameworks
- **[Environment Variables](#environment-variable-control)** - Debug and control options

### For Developers
- **[Implementing New Settings](#implementing-new-settings)** - Adding settings to theories and CLI
- **[Architecture Documentation](#configuration-architecture)** - Settings system design and extension points
- **[Testing Guide](#testing-new-settings)** - Validation and testing procedures

## Settings Reference

### Core Framework Settings

Required by all theories:

| Setting | Type | Default | Description |
|---------|------|---------|-------------|
| `N` | integer | 3 | Number of atomic states in model space |
| `max_time` | integer | 1 | Maximum Z3 solver execution time (milliseconds) |
| `expectation` | boolean | True | Whether a model is expected to exist (for testing) |

### Optional Framework Settings

Available to theories that support them:

| Setting | Type | Default | Description |
|---------|------|---------|-------------|
| `contingent` | boolean | False | Make atomic propositions contingent |
| `disjoint` | boolean | False | Require disjoint subject-matters |
| `non_empty` | boolean | False | Require non-empty verifier/falsifier sets |
| `non_null` | boolean | False | Prevent null states as verifiers/falsifiers |
| `iterate` | integer | 1 | Number of distinct models to find |

### Theory-Specific Settings

**Bimodal Theory**:
- `M` (integer): Number of time points for temporal dimension
- `align_vertically` (boolean): Display world histories vertically

**Exclusion Theory**:
- `coherence_check` (boolean): Enable exclusion coherence validation
- `witness_optimization` (boolean): Optimize witness structure generation

**Imposition Theory**:
- `imposition_depth` (integer): Maximum depth for imposition operations
- `state_modification` (boolean): Allow state modification patterns

### General Settings (Output and Debugging)

| Setting | Type | Default | Description |
|---------|------|---------|-------------|
| `print_impossible` | boolean | False | Show impossible states in output |
| `print_constraints` | boolean | False | Display Z3 constraints when no model found |
| `print_z3` | boolean | False | Show raw Z3 model or unsat core |
| `save_output` | boolean | False | Prompt to save output to file |
| `maximize` | boolean | False | Compare theories by maximizing model size |

## Advanced Configuration

### Custom Settings Profiles

```python
# Define reusable settings profiles
DEBUG_PROFILE = {
    'print_z3': True,
    'print_constraints': True,
    'print_impossible': True,
    'max_time': 10000
}

PERFORMANCE_PROFILE = {
    'N': 2,
    'max_time': 500,
    'iterate': 1
}

# Apply profiles
model = BuildExample("debug_test", theory, settings=DEBUG_PROFILE)
fast_model = BuildExample("quick_check", theory, settings=PERFORMANCE_PROFILE)
```

### Settings Inheritance

```python
# Base settings for a research project
BASE_RESEARCH_SETTINGS = {
    'N': 4,
    'contingent': True,
    'max_time': 5000
}

# Specialized settings for specific experiments
COUNTERFACTUAL_SETTINGS = {**BASE_RESEARCH_SETTINGS, 'disjoint': True}
MODAL_SETTINGS = {**BASE_RESEARCH_SETTINGS, 'non_empty': True, 'N': 5}

# Use in examples
cf_model = BuildExample("counterfactual", theory, settings=COUNTERFACTUAL_SETTINGS)
modal_model = BuildExample("modal", theory, settings=MODAL_SETTINGS)
```

### Dynamic Settings Adaptation

```python
# Automatically adjust settings based on formula complexity
def adaptive_settings(formula, base_settings):
    adapted = base_settings.copy()
    
    # Complex formulas need more time and space
    if formula.count('\\') > 5:  # Many operators
        adapted['N'] = min(adapted['N'] + 1, 6)
        adapted['max_time'] *= 2
    
    # Modal formulas benefit from contingency
    if '\\Box' in formula or '\\Diamond' in formula:
        adapted['contingent'] = True
        
    return adapted

formula = "\\Box (p \\rightarrow \\Diamond q) \\wedge \\Diamond (q \\rightarrow \\Box r)"
settings = adaptive_settings(formula, {'N': 3, 'max_time': 1000})
model = BuildExample("complex", theory, settings=settings)
```

## Implementing New Settings

### Development Guidelines

When adding new settings to theories or the framework:

#### 1. Theory-Specific Settings

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,                    # Required: state space size
        'max_time': 1,             # Required: solver timeout
        'your_theory_setting': False,  # New theory-specific setting
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        'print_z3': False,         # Debugging options
        'custom_display': False,   # Theory-specific display option
    }
    
    def generate_constraints(self):
        # Use the setting in constraint generation
        if self.settings['your_theory_setting']:
            # Implement theory-specific behavior
            pass
```

#### 2. Command-Line Integration

```python
# In cli.py - add argument parser entries
parser.add_argument(
    '--your-setting', '-ys',
    dest='your_theory_setting',
    action='store_true',
    help='Enable your theory-specific feature'
)

# For non-boolean settings
parser.add_argument(
    '--complexity-level', '-cl',
    dest='complexity_level',
    type=int,
    default=None,
    help='Set theory complexity level (1-5)'
)
```

#### 3. Testing Implementation

```python
# In test_settings.py
def test_new_setting_integration():
    theory = get_theory("your_theory")
    manager = SettingsManager(theory)
    
    # Test default behavior
    settings = manager.merge_settings()
    assert settings['your_theory_setting'] == False
    
    # Test override behavior
    settings = manager.merge_settings(
        example_settings={'your_theory_setting': True}
    )
    assert settings['your_theory_setting'] == True
    
    # Test flag override
    mock_flags = {'your_theory_setting': True}
    settings = manager.merge_settings(flags=mock_flags)
    assert settings['your_theory_setting'] == True
```

### Best Practices

1. **Semantic Relevance**: Only add settings that control semantic behavior or essential functionality
2. **Theory Specificity**: Define settings only in theories where they're meaningful
3. **Clear Naming**: Use descriptive names that indicate purpose and scope
4. **Documentation**: Update this README and theory documentation
5. **Default Values**: Choose defaults that work without user intervention
6. **Type Safety**: Ensure settings have appropriate types and validation

## Testing

The settings package includes comprehensive testing:

```bash
# Test settings system
python test_package.py --components settings

# Test settings with specific theories
python test_theories.py --theories logos exclusion --settings-tests

# Test CLI integration
python test_package.py --components settings.cli --verbose

# Test validation behavior
python test_package.py --components settings.validation
```

## References

### Implementation Architecture
- Settings system follows centralized management patterns with theory-specific specialization
- Priority-based configuration hierarchy ensures predictable behavior across components

### Related Components
- **[Builder Package](../builder/README.md)** - Model construction with settings integration
- **[Theory Library](../theory_lib/README.md)** - Theory-specific settings definitions
- **[Command-Line Interface](../../../../CLAUDE.md#quick-reference)** - CLI flags and configuration

## License

Part of the ModelChecker framework, licensed under GPL-3.0.

---

[← Back to ModelChecker API](../README.md) | [Builder Package →](../builder/README.md) | [Theory Library →](../theory_lib/README.md)
