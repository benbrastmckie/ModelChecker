# Imposition Theory Settings Documentation

This document describes all available settings for the imposition theory implementation in ModelChecker.

## Overview

The imposition theory implements Kit Fine's imposition semantics for counterfactual reasoning. It extends the logos base functionality while implementing Fine's distinctive counterfactual semantics through the imposition operation. This enables sophisticated reasoning about alternative worlds and counterfactual scenarios.

## Example Settings

These settings control model generation for specific examples:

### Core Settings

- **N** (integer, default: 3): Number of atomic states in the model. This determines the size of the state space for imposition operations.

### Constraint Settings

- **contingent** (boolean, default: False): When enabled, atomic propositions must have both verifiers and falsifiers, making them contingent.

- **non_empty** (boolean, default: False): When enabled, prevents atomic propositions from having empty verifier or falsifier sets.

- **non_null** (boolean, default: False): When enabled, prevents the null state from being a verifier or falsifier for any atomic proposition.

- **disjoint** (boolean, default: False): When enabled, ensures atomic propositions have disjoint extensions.

### Solver Settings

- **max_time** (integer, default: 1): Maximum time in seconds for the Z3 solver to find a model.

- **iterate** (integer, default: 1): Number of model iterations to generate. Useful for exploring multiple counterfactual scenarios.

- **expectation** (boolean/None, default: None): Expected result for testing. Set to True if a model should exist, False if not, None to skip expectation checking.

## General Settings

The imposition theory uses the standard general settings:
- print_impossible
- print_constraints
- print_z3
- save_output
- maximize

See the [main settings documentation](../../settings/README.md) for details.

## Usage Examples

### Basic Counterfactual Reasoning
```python
imposition_basic_settings = {
    'N': 3,  # Standard size for counterfactuals
    'contingent': True,  # Contingent propositions for realistic scenarios
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'max_time': 1,
}
```

### Complex Counterfactual Models
```python
imposition_complex_settings = {
    'N': 5,  # Larger state space for complex impositions
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,  # Clear proposition boundaries
    'max_time': 10,
    'iterate': 3,  # Explore multiple alternative worlds
}
```

### Testing Counterfactual Principles
```python
imposition_test_settings = {
    'N': 2,  # Minimal size for principle testing
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'expectation': False,  # Test for invalidity
    'max_time': 5,
}
```

## Theory-Specific Behavior

The imposition theory implements several key features:

1. **Imposition Operation**: The core operation that takes a state and world, producing an outcome world representing the counterfactual scenario.

2. **Frame Constraints**: 
   - Inclusion: Imposed states are part of outcome worlds
   - Actuality: Every part of a world can be imposed
   - Incorporation: Imposition respects fusion
   - Completeness: Imposition results in complete worlds

3. **Alternative World Calculation**: Uses imposition to determine the nearest possible worlds for counterfactual evaluation.

4. **Compatibility**: States are compatible if their fusion is possible, which constrains imposition operations.

## Comparison with Logos

While imposition inherits from logos for consistency, it differs in:
- Focus on counterfactual rather than modal reasoning
- Imposition operation as the central semantic primitive
- Different frame constraints tailored to counterfactual semantics
- Alternative world calculation based on imposition

## Tips and Best Practices

1. **Start simple**: Use N=3 (default) to understand basic imposition behavior before increasing complexity.

2. **Enable contingency**: For realistic counterfactual scenarios, enable contingent=True.

3. **Use iterate**: When exploring counterfactuals, iterate helps find different imposition scenarios.

4. **Monitor solver time**: Imposition constraints can be complex; increase max_time for larger models.

5. **Compare with logos**: Run the same formulas in both theories to understand the differences in counterfactual treatment.

## See Also

- [General Settings Documentation](../../settings/README.md)
- [Imposition Theory README](../README.md)
- [Kit Fine's Work on Counterfactuals](../references.md)