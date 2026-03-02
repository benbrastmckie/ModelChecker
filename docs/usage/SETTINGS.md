# Settings Configuration Guide

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)

## Table of Contents

1. [Overview](#overview)
2. [Settings Hierarchy](#settings-hierarchy)
3. [Core Settings](#core-settings)
   - [Required Settings](#required-settings)
   - [Performance Settings](#performance-settings)
   - [Iteration Settings](#iteration-settings)
4. [Theory-Specific Settings](#theory-specific-settings)
   - [Modal Logic Settings](#modal-logic-settings)
   - [Constraint Testing Settings](#constraint-testing-settings)
5. [Command-Line Overrides](#command-line-overrides)
6. [Settings Precedence](#settings-precedence)
7. [Common Configurations](#common-configurations)
8. [Troubleshooting](#troubleshooting)

## Overview

Settings control the behavior of the ModelChecker, from basic parameters like the number of atomic propositions to advanced theory-specific constraints. This guide covers how to configure settings effectively for different use cases.

**Architecture References**:
- [Settings Architecture](../architecture/SETTINGS.md) - Complete settings system design and hierarchy
- [Builder Architecture](../architecture/BUILDER.md) - How settings flow through the pipeline
- [Theory Library Architecture](../architecture/THEORY_LIB.md) - Theory-specific settings management

## Settings Hierarchy

Settings follow a clear precedence order (highest to lowest):

1. **Command-line flags** - Override all other settings
2. **Example settings** - Defined in example files
3. **User settings** - Personal defaults
4. **Theory defaults** - Theory-specific defaults
5. **System defaults** - Framework defaults

**Architecture Deep Dive**: For the complete implementation of settings precedence and merging logic, see [Settings Architecture](../architecture/SETTINGS.md#settings-precedence).

```python
# Example showing settings at different levels
MY_TEST_settings = {
    'N': 4  # Example-level setting (overrides theory default)
}

# Note: N and iterate must be set in example settings, not via CLI
# Command line flags like --contingent override general/example settings
```

## Core Settings

### Required Settings

Every example must specify these settings:

| Setting | Type | Description | Default | Range |
|---------|------|-------------|---------|-------|
| `N` | int | Maximum atomic propositions | Required | 1-10 (practical) |

```python
# Minimal valid settings
settings = {'N': 3}
```

### Performance Settings

Control solver behavior and resource usage:

| Setting | Type | Description | Default | Range |
|---------|------|-------------|---------|-------|
| `max_time` | int | Solver timeout (seconds) | 30 | 1-3600 |
| `iterate` | int | Number of models to find | 1 | 1-100 |

```python
# Performance-optimized settings
PERFORMANCE_settings = {
    'N': 3,
    'max_time': 60,       # 1 minute timeout
    'iterate': 5          # Find up to 5 models
}
```

### Iteration Settings

Control model iteration behavior:

| Setting | Type | Description | Default |
|---------|------|-------------|---------|
| `iterate` | int | Number of distinct models to find | 1 |
| `expectation` | bool | Whether expecting countermodel (True) or theorem (False) | None |

```python
# Iteration-focused settings
ITERATE_settings = {
    'N': 4,
    'iterate': 3,         # Find up to 3 distinct models
    'expectation': True   # Expecting countermodel
}
```

## Theory-Specific Settings

Different theories support different settings. Always check theory documentation for available options.

### Modal Logic Settings

For theories supporting modal operators:

| Setting | Type | Description | Default |
|---------|------|-------------|---------|
| `reflexive` | bool | Reflexive accessibility | False |
| `transitive` | bool | Transitive accessibility | False |
| `euclidean` | bool | Euclidean accessibility | False |
| `serial` | bool | Serial accessibility | False |

```python
# S4 modal logic configuration
S4_settings = {
    'N': 3,
    'reflexive': True,   # T axiom
    'transitive': True   # 4 axiom
}

# S5 modal logic configuration  
S5_settings = {
    'N': 3,
    'reflexive': True,   # T axiom
    'transitive': True,  # 4 axiom
    'euclidean': True    # 5 axiom
}
```

### Constraint Testing Settings

For testing semantic constraints:

| Setting | Type | Description | Default |
|---------|------|-------------|---------|
| `test_<constraint>` | bool | Test specific constraint | False |
| `derive_<property>` | bool | Derive property | False |
| `contingent` | bool | Allow contingent propositions | True |
| `non_empty` | bool | Require non-empty models | True |

```python
# Constraint testing configuration
CONSTRAINT_settings = {
    'N': 3,
    'test_frame_definability': True,
    'derive_imposition': True,
    'contingent': False,  # Only necessary propositions
    'non_empty': True     # No empty models
}
```

## Command-Line Overrides

Available command-line flags override settings in example files:

```bash
# Boolean constraint flags
model-checker example.py --contingent    # -c: Make propositions contingent
model-checker example.py --disjoint      # -d: Disjoint verifier/falsifier sets
model-checker example.py --non-empty     # -e: Non-empty verifier/falsifier sets
model-checker example.py --non-null      # -n: Exclude null state from models

# Debug and output flags
model-checker example.py --print-constraints  # -p: Show Z3 constraints
model-checker example.py --print-z3          # -z: Show Z3 model details
model-checker example.py --print-impossible  # -i: Show impossible states

# Theory and comparison flags
model-checker example.py --maximize          # -m: Compare theories with increasing N
model-checker example.py --load-theory logos # -l: Load specific theory

# Output formatting
model-checker example.py --save json         # -s: Save output format
model-checker example.py --align-vertically  # -a: Vertical display format
model-checker example.py --sequential        # -q: Sequential model saving
```

**Note**: Settings like `N`, `max_time`, and theory-specific options (e.g., `reflexive`) must be set in the Python example file, not via command-line flags.

## Settings Precedence

Understanding precedence helps debug unexpected behavior:

```python
# System default (in semantic.py base class)
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "sequential": False,
    "maximize": False
}

# Theory-specific defaults (overrides system)
THEORY_SETTINGS = {
    'N': 3,           # Set in example file
    'max_time': 30    # Theory-specific default
}

# Example settings (overrides theory)
EXAMPLE_settings = {
    'N': 4,
    'max_time': 60
}

# Command line (overrides general settings only)
# model-checker example.py --contingent
# Note: N and iterate must be set in example settings
```

## Common Configurations

### Quick Testing

For rapid validation during development:

```python
QUICK_TEST_settings = {
    'N': 2,              # Minimal propositions
    'max_time': 5,       # 5 second timeout
    'max_iterations': 1  # Single model only
}
```

### Thorough Analysis

For comprehensive exploration:

```python
THOROUGH_settings = {
    'N': 5,                  # More propositions
    'max_time': 120,         # 2 minute timeout
    'max_iterations': 20,    # Many models
    'iterate': 10            # Find multiple models
}
```

### Debugging

For troubleshooting issues:

```python
DEBUG_settings = {
    'N': 3,
    'max_time': 300,           # 5 minutes
    'print_constraints': True,  # Show Z3 constraints
    'print_z3': True,          # Show Z3 model
    'print_impossible': True   # Show impossible states
}
```

### CI/CD Pipeline

For automated testing:

```python
CI_settings = {
    'N': 3,
    'max_time': 30,
    'save_output': True,     # Enable output saving
    'output_format': 'json'  # Machine-readable format
}
```

## Troubleshooting

### Common Issues

**Issue**: "Settings key 'N' not found"
```python
# Solution: Always include N
settings = {'N': 3}  # Required
```

**Issue**: Solver timeout
```python
# Solution: Increase timeout or reduce N
settings = {
    'N': 3,           # Reduce from 4
    'max_time': 60    # Increase from 30
}
```

**Issue**: Out of memory
```python
# Solution: Reduce N or increase memory limit
settings = {
    'N': 3,
    'memory_limit': 8192  # 8GB
}
```

**Issue**: Conflicting settings
```python
# Bad: Contradictory settings
settings = {
    'contingent': False,
    'non_contingent': True  # Conflicts!
}

# Good: Use one setting
settings = {
    'contingent': False
}
```

### Validation Tips

1. **Start small**: Begin with N=2 or N=3
2. **Increase gradually**: Add complexity incrementally
3. **Check theory docs**: Not all settings work with all theories
4. **Use verbose mode**: Add `'verbose': True` for debugging
5. **Test settings**: Run with `--print-constraints` to verify

## See Also

### Usage Guides
- [Workflow Guide](WORKFLOW.md) - Using settings in practice
- [Examples Guide](EXAMPLES.md) - Settings in example files
- [Constraints Guide](SEMANTICS.md) - Settings for constraint testing

### Technical Documentation
- [Settings Architecture](../architecture/SETTINGS.md) - Complete system design and precedence rules
- [Pipeline Architecture](../architecture/PIPELINE.md) - How settings affect the processing pipeline
- [Settings Implementation](../../Code/src/model_checker/settings/README.md) - API reference
- [Theory Defaults](../../Code/src/model_checker/theory_lib/README.md) - Theory-specific settings

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)
