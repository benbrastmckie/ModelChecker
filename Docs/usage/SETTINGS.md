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

For architectural details about the settings system, see [Settings Architecture](../architecture/SETTINGS.md).

## Settings Hierarchy

Settings follow a clear precedence order (highest to lowest):

1. **Command-line flags** - Override all other settings
2. **Example settings** - Defined in example files
3. **User settings** - Personal defaults
4. **Theory defaults** - Theory-specific defaults
5. **System defaults** - Framework defaults

```python
# Example showing settings at different levels
MY_TEST_settings = {
    'N': 4  # Example-level setting (overrides theory default)
}

# Command line override
# model-checker test.py --N=5  # This would override the example setting
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
| `max_iterations` | int | Maximum models to find | 10 | 1-100 |
| `memory_limit` | int | Memory limit (MB) | 2048 | 512-8192 |

```python
# Performance-optimized settings
PERFORMANCE_settings = {
    'N': 3,
    'max_time': 60,       # 1 minute timeout
    'max_iterations': 5,  # Find up to 5 models
    'memory_limit': 4096  # 4GB memory limit
}
```

### Iteration Settings

Control model iteration behavior:

| Setting | Type | Description | Default |
|---------|------|-------------|---------|
| `find_all_models` | bool | Find all possible models | False |
| `iso_check` | bool | Check for isomorphisms | True |
| `difference_threshold` | float | Minimum difference between models | 0.1 |

```python
# Iteration-focused settings
ITERATE_settings = {
    'N': 4,
    'find_all_models': True,
    'iso_check': True,
    'difference_threshold': 0.2  # Require 20% difference
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

Command-line flags override all other settings:

```bash
# Override N value
model-checker example.py --N=5

# Override multiple settings
model-checker example.py --N=4 --max-time=60 --reflexive

# Boolean flags (no value needed)
model-checker example.py --verbose --print-constraints

# Disable boolean settings with --no- prefix
model-checker example.py --no-contingent --no-iso-check
```

## Settings Precedence

Understanding precedence helps debug unexpected behavior:

```python
# System default
DEFAULT_N = 2

# Theory default (overrides system)
DEFAULT_GENERAL_SETTINGS = {
    'N': 3,
    'max_time': 30
}

# Example settings (overrides theory)
EXAMPLE_settings = {
    'N': 4,
    'max_time': 60
}

# Command line (overrides all)
# model-checker example.py --N=5
# Final N value: 5
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
    'find_all_models': True, # Exhaustive search
    'verbose': True          # Detailed output
}
```

### Debugging

For troubleshooting issues:

```python
DEBUG_settings = {
    'N': 3,
    'max_time': 300,           # 5 minutes
    'verbose': True,
    'print_constraints': True,  # Show Z3 constraints
    'print_z3': True,          # Show Z3 model
    'iso_debug': True          # Debug isomorphism checking
}
```

### CI/CD Pipeline

For automated testing:

```python
CI_settings = {
    'N': 3,
    'max_time': 30,
    'quiet': True,     # Minimal output
    'save': 'json'     # Machine-readable output
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
- [Constraints Guide](CONSTRAINTS.md) - Settings for constraint testing

### Technical Documentation
- [Settings Architecture](../architecture/SETTINGS.md) - System design
- [Settings Implementation](../../Code/src/model_checker/settings/README.md) - API reference
- [Theory Defaults](../../Code/src/model_checker/theory_lib/README.md) - Theory-specific settings

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)