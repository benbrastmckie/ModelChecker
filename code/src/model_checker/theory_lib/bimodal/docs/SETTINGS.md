# Bimodal Theory Settings Documentation

This document describes all available settings for the bimodal theory implementation in ModelChecker.

## Overview

The bimodal theory implements a two-dimensional modal logic with both world states and time points, enabling reasoning about temporal evolution and task transitions. Settings control the model dimensions, constraints, and display options.

## Example Settings

These settings control model generation for specific examples:

### Dimension Settings

- **N** (integer, default: 2): Number of world states in the model. Each world state represents a distinct configuration or situation.

- **M** (integer, default: 2): Number of time points in the model. This creates a temporal dimension for reasoning about change over time.

### Constraint Settings

- **contingent** (boolean, default: False): When enabled, sentence letters are assigned to contingent propositions (true in some world-time pairs, false in others).

- **disjoint** (boolean, default: False): When enabled, sentence letters are assigned to distinct (non-overlapping) world states.

### Solver Settings

- **max_time** (integer, default: 1): Maximum time in seconds for the Z3 solver to find a model.

- **expectation** (boolean, default: True): Expected result for testing. Set to True if a model should exist, False if not.

- **iterate** (integer, default: 1): Number of model iterations to generate. Useful for finding multiple distinct models.

## General Settings

The bimodal theory supports all standard general settings plus:

### Display Settings

- **align_vertically** (boolean, default: True): When enabled, displays world histories vertically in the output, making temporal evolution easier to visualize. This is particularly useful for bimodal models where you want to see how worlds evolve over time.

For other general settings, see the [main settings documentation](../../settings/README.md).

## Usage Examples

### Simple Temporal Model
```python
bimodal_simple_settings = {
    'N': 2,  # Two world states
    'M': 3,  # Three time points
    'contingent': True,  # Allow change over time
    'disjoint': False,
    'max_time': 1,
}
```

### Complex Task Transition Model
```python
bimodal_complex_settings = {
    'N': 4,  # Four world states for richer structure
    'M': 5,  # Five time points for extended sequences
    'contingent': True,
    'disjoint': True,  # Distinct world states
    'max_time': 10,  # More time for complex models
    'iterate': 3,  # Find multiple models
}
```

### Testing Modal Principles
```python
bimodal_test_settings = {
    'N': 3,
    'M': 2,
    'contingent': False,  # Fixed truth values
    'disjoint': False,
    'expectation': False,  # Expect no model
    'max_time': 5,
}
```

## Theory-Specific Behavior

The bimodal theory implements several features that interact with these settings:

1. **Two-Dimensional Structure**: Models have both world states (N) and time points (M), creating an N×M grid of world-time pairs.

2. **Task Transitions**: The theory includes task transitions that can change world states over time.

3. **Temporal Operators**: Supports reasoning about what's true "always", "sometimes", and at specific times.

4. **Vertical Display**: The align_vertically setting helps visualize temporal evolution by showing each world's history as a column.

## Display Format Example

With align_vertically = True:
```
World 0: [State at t0] → [State at t1] → [State at t2]
World 1: [State at t0] → [State at t1] → [State at t2]
```

With align_vertically = False:
```
Time 0: World 0: [State], World 1: [State]
Time 1: World 0: [State], World 1: [State]
```

## Tips and Best Practices

1. **Start small**: Begin with N=2, M=2 to understand the basic structure before increasing dimensions.

2. **Use vertical alignment**: The default align_vertically=True is usually clearer for understanding temporal evolution.

3. **Balance dimensions**: Very large N or M values can make models hard to interpret and slow to compute.

4. **Contingency for dynamics**: Enable contingent=True when modeling systems that change over time.

5. **Disjoint for clarity**: Enable disjoint=True when you want sentence letters to pick out specific world states.

## See Also

- [General Settings Documentation](../../settings/README.md)
- [Bimodal Theory README](../README.md)