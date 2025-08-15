# Logos Theory Settings Documentation: Configuration Reference

[← Back to Documentation](README.md) | [Iteration →](ITERATE.md)

## Table of Contents

1. [Overview](#overview)
2. [Example Settings](#example-settings)
   - [Core Settings](#core-settings)
   - [Solver Settings](#solver-settings)
3. [General Settings](#general-settings)
4. [Usage Examples](#usage-examples)
   - [Finding Complex Countermodels](#finding-complex-countermodels)
   - [Testing Logical Principles](#testing-logical-principles)
   - [Exploring Hyperintensional Phenomena](#exploring-hyperintensional-phenomena)
5. [Theory-Specific Behavior](#theory-specific-behavior)
6. [Tips and Best Practices](#tips-and-best-practices)
7. [Advanced Settings](#advanced-settings)
   - [Model Iteration Settings](#model-iteration-settings)
   - [Experimental Settings](#experimental-settings)
8. [Subtheory-Specific Considerations](#subtheory-specific-considerations)
   - [Modal Subtheory](#modal-subtheory)
   - [Constitutive Subtheory](#constitutive-subtheory)
   - [Counterfactual Subtheory](#counterfactual-subtheory)
   - [Relevance Subtheory](#relevance-subtheory)
9. [Performance Tuning](#performance-tuning)
   - [Memory vs Speed Trade-offs](#memory-vs-speed-trade-offs)
   - [Solver Timeout Guidelines](#solver-timeout-guidelines)
10. [Common Configurations](#common-configurations)
    - [Research Configuration](#research-configuration)
    - [Teaching Configuration](#teaching-configuration)
    - [Testing Configuration](#testing-configuration)
    - [Development Configuration](#development-configuration)
11. [Troubleshooting](#troubleshooting)
    - [Common Issues](#common-issues)
    - [Debugging Settings](#debugging-settings)
    - [Setting Interactions](#setting-interactions)
12. [Environment Variables](#environment-variables)
13. [See Also](#see-also)

## Overview

The Logos theory provides hyperintensional truthmaker semantics with support for modular operator loading and subtheory coordination. Settings control state generation, frame constraints, solver behavior, and model iteration. Understanding these settings is crucial for effective use of the theory's advanced features.

## Example Settings

These settings control model generation for specific examples:

### Core Settings

- **N** (integer, default: 16): Number of atomic states in the model. Higher values allow more complex models but increase computation time.

- **contingent** (boolean, default: True): When enabled, requires atomic propositions to have both verifiers and falsifiers, making them contingent rather than necessary/impossible.

- **non_empty** (boolean, default: True): When enabled, prevents atomic propositions from having empty verifier or falsifier sets.

- **non_null** (boolean, default: True): When enabled, prevents the null state from being a verifier or falsifier for any atomic proposition.

- **disjoint** (boolean, default: True): When enabled, ensures atomic propositions have disjoint subject-matters (no overlapping verifier/falsifier states).

### Solver Settings

- **max_time** (integer, default: 10000): Maximum time in milliseconds for the Z3 solver to find a model. Increase for more complex formulas.

- **iterate** (boolean/integer, default: False): When set to an integer, attempts to find multiple distinct models. Useful for exploring the space of countermodels.

- **iteration_attempts** (integer, default: 5): Maximum number of attempts to find a new model in each iteration.

- **expectation** (boolean/None, default: None): Expected result for testing. Set to True if a model should exist, False if not, None to skip expectation checking.

## General Settings

The logos theory uses the standard general settings defined in the base semantic framework. See the [main settings documentation](../../settings/README.md) for details on:
- print_impossible
- print_constraints
- print_z3
- save_output
- maximize

## Usage Examples

### Finding Complex Countermodels

```python
logos_complex_settings = {
    'N': 32,  # More states for complex models
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,
    'max_time': 30000,  # 30 seconds for complex formulas
    'iterate': 5,  # Find up to 5 different models
}
```

### Testing Logical Principles

```python
logos_test_settings = {
    'N': 8,  # Smaller for faster testing
    'contingent': False,  # Allow necessary/impossible props
    'non_empty': False,  # Allow empty extensions
    'non_null': False,  # Allow null verifiers/falsifiers
    'disjoint': False,  # Allow overlapping content
    'max_time': 5000,
    'expectation': False,  # Expect no model (testing invalidity)
}
```

### Exploring Hyperintensional Phenomena

```python
logos_hyperintensional_settings = {
    'N': 16,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,  # Essential for proper hyperintensionality
    'iterate': 10,  # Explore multiple models
    'max_time': 2000,  # 2 seconds for iteration attempts
}
```

## Theory-Specific Behavior

The logos theory implements several key features that interact with these settings:

1. **State Structure**: States are represented as bitvectors, with fusion operations and parthood relations.

2. **Verification/Falsification**: The theory uses separate verify and falsify functions to determine truth conditions.

3. **Possibility Constraint**: The possible() function enforces downward closure - if a state is possible, all its parts are possible.

4. **Compatibility**: Two states are compatible if their fusion is possible, which affects model construction.

## Tips and Best Practices

1. **Start with default settings** - The defaults are chosen to work well for most logical investigations.

2. **Adjust N carefully** - Doubling N roughly squares the search space. Start small and increase as needed.

3. **Use iterate for exploration** - When investigating a formula, use iterate to find multiple countermodels and understand the range of invalidating scenarios.

4. **Disable constraints for testing** - When testing whether certain constraints are necessary, disable them (set to False) to see if countermodels arise.

5. **Monitor solver timeouts** - If you frequently hit max_time limits, either increase the timeout or reduce N.

## Advanced Settings

### Model Iteration Settings

These settings control the behavior when finding multiple models:

- **iteration_solver_timeout** (integer, default: 10000): Maximum milliseconds for Z3 solver during iteration attempts. Separate from base max_time.

- **max_invalid_attempts** (integer, default: 5): Maximum consecutive invalid models before giving up. Invalid models have no possible worlds.

- **escape_attempts** (integer, default: 5): Number of attempts to escape isomorphic models using stronger constraints.

### Experimental Settings

These settings are for advanced users and researchers:

- **world_limit** (integer, optional): Maximum number of possible worlds to allow. Can help control model complexity.

- **verification_limit** (integer, optional): Maximum number of verifiers per proposition. Useful for constraining model size.

## Subtheory-Specific Considerations

Different Logos subtheories may interpret settings differently:

### Modal Subtheory
- **N**: Affects the complexity of accessibility relations
- **disjoint**: Important for distinguishing modal operators
- **iterate**: Useful for exploring different modal structures

### Constitutive Subtheory
- **non_empty**: Critical for meaningful ground/essence relations
- **disjoint**: Helps create clear subject-matter boundaries
- **contingent**: Important for testing constitutive principles

### Counterfactual Subtheory
- **N**: Keep smaller (3-4) due to computational complexity
- **non_null**: Essential for proper similarity orderings
- **max_time**: May need higher values (20000-30000)

### Relevance Subtheory
- **disjoint**: Critical for relevance distinctions
- **non_empty**: Ensures meaningful relevance relations

## Performance Tuning

### Memory vs Speed Trade-offs

```python
# Memory-efficient configuration
memory_settings = {
    'N': 3,  # Minimal state space
    'max_time': 5000,  # Moderate timeout
    'iterate': False,  # Single model only
}

# Speed-optimized configuration
speed_settings = {
    'N': 4,  # Balanced state space
    'contingent': True,  # Reduce search space
    'disjoint': True,  # Clear boundaries
    'max_time': 2000,  # Quick timeout
}

# Comprehensive exploration
thorough_settings = {
    'N': 5,  # Larger state space
    'iterate': 10,  # Multiple models
    'max_time': 30000,  # Extended timeout
    'iteration_solver_timeout': 20000,
}
```

### Solver Timeout Guidelines

Based on formula complexity and N value:

| N Value | Simple Formula | Complex Formula | With Iteration |
|---------|---------------|-----------------|----------------|
| 3 | 1000ms | 5000ms | 10000ms |
| 4 | 2000ms | 10000ms | 20000ms |
| 5 | 5000ms | 20000ms | 40000ms |
| 6+ | 10000ms | 60000ms | 120000ms |

## Common Configurations

### Research Configuration

For academic research and thorough investigation:

```python
research_settings = {
    'N': 16,  # Default for rich models
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,
    'max_time': 30000,
    'iterate': 5,
    # max_time already set above
    'iteration_solver_timeout': 20000,
}
```

### Teaching Configuration

For classroom demonstrations:

```python
teaching_settings = {
    'N': 3,  # Quick and clear
    'contingent': True,
    'non_empty': True,
    'max_time': 2000,
    'iterate': 2,  # Show variation
}
```

### Testing Configuration

For automated testing:

```python
test_settings = {
    'N': 4,
    'max_time': 5000,
    'expectation': True,  # Or False
    'iterate': False,  # Deterministic
}
```

### Development Configuration

For developing new operators:

```python
dev_settings = {
    'N': 3,  # Fast iteration
    'max_time': 1000,
    'print_constraints': True,  # Debug
    'print_z3': True,  # Full output
}
```

## Troubleshooting

### Common Issues

1. **"Z3 timeout" with default settings**
   - Reduce N to 3 or 4
   - Increase max_time to 20000 or more
   - Enable fewer constraints (set some to False)

2. **"No model found" when model should exist**
   - Check constraint conflicts (all True may be too restrictive)
   - Try disabling disjoint or non_empty
   - Verify formula syntax

3. **"Too many consecutive invalid models" during iteration**
   - Ensure non_empty is True
   - Reduce N to avoid empty model space
   - Check that premises aren't contradictory

4. **Memory errors with large N**
   - N=6 creates 64 possible states
   - N=7 creates 128 possible states
   - Consider using world_limit setting

### Debugging Settings

```python
debug_settings = {
    'N': 3,
    'print_impossible': True,  # See all states
    'print_constraints': True,  # See Z3 constraints
    'print_z3': True,  # See solver output
    'max_time': 60000,  # Don't timeout
}
```

### Setting Interactions

Some settings interact in important ways:

1. **contingent + non_empty**: Ensures meaningful propositions
2. **non_null + non_empty**: Prevents trivial models
3. **disjoint + high N**: May make models impossible
4. **iterate + low max_time**: May prevent finding all models

## Environment Variables

In addition to settings, environment variables affect behavior:

- `MODELCHECKER_VERBOSE`: Shows detailed theory loading
- `MODELCHECKER_SUPPRESS_COMPARISON_WARNINGS`: Relevant when comparing theories

## See Also

- **[General Settings Documentation](../../settings/README.md)** - Framework-wide settings
- **[User Guide](USER_GUIDE.md)** - Practical usage examples
- **[Architecture](ARCHITECTURE.md)** - How settings affect internals
- **[Model Iteration](ITERATE.md)** - Iteration-specific settings
- **[Main README](../README.md)** - Theory overview

---

[← Back to Documentation](README.md) | [User Guide →](USER_GUIDE.md)