# Logos Theory Settings Documentation

This document describes all available settings for the logos theory implementation in ModelChecker.

## Overview

The logos theory provides hyperintensional truthmaker semantics with support for modular operator loading and subtheory coordination. Settings control state generation, frame constraints, and solver behavior.

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

- **iteration_timeout** (float, default: 1.0): Time in seconds allowed for each iteration attempt when using iterate mode.

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
    'iteration_timeout': 2.0,
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

## See Also

- [General Settings Documentation](../../settings/README.md)
- [Logos Theory README](../README.md)
- [Logos Theory Notebooks](../notebooks/README.md)