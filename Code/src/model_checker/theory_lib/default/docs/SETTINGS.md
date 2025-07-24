# Default Theory Settings Documentation

This document describes all available settings for the default theory implementation in ModelChecker.

## Overview

The default theory provides the foundational semantic framework for modal logic with exact truthmaker semantics. It uses state-based verification and falsification conditions, implementing a bit-vector representation where possible worlds are maximal consistent states.

## Example Settings

These settings control model generation for specific examples:

### Core Settings

- **N** (integer, default: 3): Number of atomic states in the model. This determines the size of the state space (2^N possible states).

### Constraint Settings

- **contingent** (boolean, default: False): When enabled, atomic propositions must have both verifiers and falsifiers, making them neither necessary nor impossible.

- **non_empty** (boolean, default: False): When enabled, prevents atomic propositions from having empty verifier or falsifier sets.

- **non_null** (boolean, default: False): When enabled, prevents the null state (empty state) from being a verifier or falsifier for any atomic proposition.

- **disjoint** (boolean, default: False): When enabled, ensures atomic propositions have disjoint extensions (no state can verify/falsify multiple atoms).

### Solver Settings

- **max_time** (integer, default: 1): Maximum time in seconds for the Z3 solver to find a model.

- **iterate** (integer, default: 1): Number of model iterations to generate. When greater than 1, finds multiple distinct models.

- **iteration_timeout** (float, default: 1.0): Time in seconds allowed for each iteration attempt when using iterate mode.

- **iteration_attempts** (integer, default: 5): Maximum number of attempts to find a new model in each iteration.

- **expectation** (boolean/None, default: None): Expected result for testing. Set to True if a model should exist, False if not, None to skip expectation checking.

## General Settings

The default theory defines the standard general settings used across all theories:

- **print_impossible** (boolean, default: False): Print impossible states in the model output.

- **print_constraints** (boolean, default: False): Print the constraints when no model is found.

- **print_z3** (boolean, default: False): Print the raw Z3 model or unsat core.

- **save_output** (boolean, default: False): Prompt to save the output to a file.

- **maximize** (boolean, default: False): Compare semantic theories by maximizing model size.

See the [main settings documentation](../../settings/README.md) for more details.

## Usage Examples

### Basic Modal Logic
```python
default_basic_settings = {
    'N': 3,  # Standard size for simple examples
    'contingent': False,  # Allow necessary/impossible props
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'max_time': 1,
}
```

### Contingent Propositions Only
```python
default_contingent_settings = {
    'N': 4,
    'contingent': True,  # Force contingency
    'non_empty': True,   # No empty extensions
    'non_null': True,    # Null state not involved
    'disjoint': False,   # Allow overlapping content
    'max_time': 5,
}
```

### Testing Invalid Formulas
```python
default_test_settings = {
    'N': 2,  # Minimal size for faster testing
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'expectation': False,  # Expect no model
    'iterate': 3,  # Try to find multiple countermodels
}
```

## Theory-Specific Behavior

The default theory implements the core features of exact truthmaker semantics:

1. **State Space**: States are represented as bit vectors of size N, giving 2^N possible states.

2. **Verification/Falsification**: Truth is determined by state-based verifiers and falsifiers.

3. **Possible Worlds**: Worlds are maximal consistent states that are possible.

4. **Frame Constraints**: Includes possibility downward closure - if a state is possible, all its parts are possible.

## Impact of Settings

### N (State Count)
- N=1: 2 states (null and one atom)
- N=2: 4 states
- N=3: 8 states (default)
- N=4: 16 states
- Each increase doubles the state space

### Constraint Combinations
Different constraint combinations create different logical environments:

- All False: Most permissive, allows any assignment
- contingent=True: Excludes tautologies and contradictions
- non_empty=True: Every proposition has content
- non_null=True: The empty state plays no semantic role
- disjoint=True: Propositions partition the state space

## Tips and Best Practices

1. **Start with defaults**: The default settings (N=3, all constraints False) work well for exploring basic modal logic.

2. **Increment N gradually**: Each increase in N doubles the search space, so increment carefully.

3. **Use constraints purposefully**: Enable constraints only when they're relevant to what you're investigating.

4. **Small models for testing**: Use N=2 or N=3 when testing logical principles for faster results.

5. **Iterate for understanding**: Use iterate>1 to see multiple models and understand why a formula is invalid.

## See Also

- [General Settings Documentation](../../settings/README.md)
- [Default Theory README](../README.md)