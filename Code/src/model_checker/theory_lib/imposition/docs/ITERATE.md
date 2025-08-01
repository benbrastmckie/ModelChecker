# Model Iteration: Finding Multiple Counterfactual Models

[← Back to Documentation](README.md) | [Settings →](SETTINGS.md) | [Imposition Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # Design and implementation
├── ITERATE.md         # This file - model iteration guide
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration parameters
└── USER_GUIDE.md      # Tutorial and introduction
```

## Overview

The **Model Iteration** guide explains how to find and explore multiple distinct models for counterfactual formulas in the imposition theory. This capability is essential for understanding the semantic space of counterfactuals and exploring different imposition patterns.

Within the imposition theory framework, model iteration reveals how different state configurations can satisfy the same counterfactual constraints. The iterator tracks changes in verification patterns, imposition relationships, and alternative world structures, providing insights into the flexibility of Fine's semantics.

This guide serves researchers exploring counterfactual semantics and developers building applications that require multiple model generation.

## Finding Multiple Models

```python
# Find multiple counterfactual models
from model_checker.theory_lib.imposition import get_theory, iterate_example
from model_checker import BuildExample

# Create counterfactual example
theory = get_theory()
example = BuildExample("sobel", theory,
    premises=['A \\boxright X',           # If A then must X
              '\\neg ((A \\wedge B) \\boxright X)'],  # Not: if A and B then must X
    conclusions=[],  # Just exploring models
    settings={'N': 4, 'iterate': 5}
)

# Find 5 distinct models
models = iterate_example(example, max_iterations=5)
print(f"Found {len(models)} distinct models")

# Examine differences
for i, model in enumerate(models[1:], 1):
    print(f"\nModel {i+1} differences:")
    model.print_model_differences()
```

## Basic Usage

### Finding Multiple Models

The simplest way to find multiple models is using the `iterate_example()` function:

```python
from model_checker import BuildExample
from model_checker.theory_lib.imposition import get_theory, iterate_example

# Create an example
theory = get_theory()
example = BuildExample("my_counterfactual", theory)
example.add_premise("\\neg A")
example.add_premise("A \\boxright B")
example.add_conclusion("A \\diamondright C")

# Find up to 5 distinct models
models = iterate_example(example, max_iterations=5)

print(f"Found {len(models)} distinct models")
for i, model in enumerate(models):
    print(f"\nModel {i+1}:")
    model.print_model()
```

### Using the Iterator Class

For more control, use the `ImpositionModelIterator` class directly:

```python
from model_checker.theory_lib.imposition import ImpositionModelIterator

# Create iterator
iterator = ImpositionModelIterator(example)

# Configure iteration
iterator.max_iterations = 10
iterator.escape_threshold = 3  # Try harder to find non-isomorphic models

# Perform iteration
models = iterator.iterate()
```

## Configuration

### Iteration Settings

The iterator can be configured through the example's settings:

```python
settings = {
    'N': 4,           # Number of atomic states (affects model complexity)
    'max_time': 2,    # Z3 solver timeout per iteration
    'iterate': 5,     # Number of models to find (alternative to max_iterations)
    'maximize': True, # Maximize structural diversity between models
}

example = BuildExample("test", theory, settings)
models = iterate_example(example)
```

### Iterator Attributes

The `ImpositionModelIterator` class has several configurable attributes:

- `max_iterations` (int): Maximum number of models to find (default: from settings or 5)
- `escape_threshold` (int): Number of isomorphic models before trying stronger constraints (default: 3)
- `debug` (bool): Enable debug output (default: False)

## Understanding Results

### Model Differences

When multiple models are found, each model (except the first) includes information about how it differs from the previous model:

```python
for i, model in enumerate(models):
    print(f"\nModel {i+1}:")
    model.print_model()
    
    # Print differences from previous model
    if hasattr(model, 'print_model_differences'):
        model.print_model_differences()
```

### Types of Differences

The iterator tracks several types of differences between models:

1. **World Changes**: States that become or cease to be worlds
2. **Possible State Changes**: States that become possible or impossible
3. **Verification Changes**: Changes in which states verify sentence letters
4. **Falsification Changes**: Changes in which states falsify sentence letters
5. **Imposition Changes**: Changes in imposition relationships

Example output:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + {B} (now a world)
  - {A, B} (no longer a world)

Verification Changes:
  Letter A:
    + {A} now verifies A
    - {A, B} no longer verifies A

Imposition Changes:
  + {A} can now impose on {B}
```

### Isomorphic Models

Sometimes the iterator may find models that are structurally identical (isomorphic) despite having different Z3 assignments. The iterator detects and skips these:

```python
# Enable debug mode to see when isomorphic models are detected
iterator = ImpositionModelIterator(example)
iterator.debug = True
models = iterator.iterate()
```

## Performance Tips

### 1. Optimal State Space Size

The number of atomic states (`N`) significantly affects performance:

```python
# Smaller state space - faster iteration
settings = {'N': 3, 'iterate': 10}

# Larger state space - more diverse models but slower
settings = {'N': 5, 'iterate': 10}
```

### 2. Timeout Configuration

Adjust timeouts based on formula complexity:

```python
# Simple formulas
settings = {'max_time': 1}

# Complex formulas with nested counterfactuals
settings = {'max_time': 5}
```

### 3. Early Termination

Stop iteration when sufficient models are found:

```python
models = []
iterator = ImpositionModelIterator(example)

for model in iterator.iterate_generator():
    models.append(model)
    if len(models) >= 3 and all_models_similar(models):
        break  # Stop if models are becoming similar
```

### 4. Constraint Optimization

The iterator uses increasingly strong constraints to find diverse models. You can influence this:

```python
# Encourage structural diversity
settings = {'maximize': True}

# Focus on specific differences
iterator = ImpositionModelIterator(example)
iterator.focus_on_imposition = True  # Prioritize imposition differences
```

## Examples

### Example 1: Exploring Counterfactual Antecedent Strengthening

```python
from model_checker.theory_lib.imposition import get_theory, iterate_example
from model_checker import BuildExample

theory = get_theory()

# Create the antecedent strengthening example
example = BuildExample("antecedent_strengthening", theory)
example.add_premise("\\neg A")
example.add_premise("A \\boxright C")
example.add_conclusion("(A \\wedge B) \\boxright C")

# Find countermodels
models = iterate_example(example, max_iterations=5)

print(f"Found {len(models)} countermodels to antecedent strengthening")
for i, model in enumerate(models):
    print(f"\n=== Countermodel {i+1} ===")
    model.print_model()
    if i > 0:
        model.print_model_differences()
```

### Example 2: Sobel Sequences

```python
# Explore Sobel sequences with multiple models
example = BuildExample("sobel_sequence", theory)
example.add_premise("A \\boxright X")
example.add_premise("\\neg ((A \\wedge B) \\boxright X)")

# Find models showing different imposition patterns
settings = {'N': 4, 'max_time': 2, 'iterate': 3}
example.update_settings(settings)

models = iterate_example(example)
for model in models:
    print("\nImposition patterns in this model:")
    # Custom analysis of imposition relations
    analyze_imposition_patterns(model)
```

### Example 3: Comparing Verification Patterns

```python
# Find models with different verification patterns
example = BuildExample("verification_test", theory)
example.add_premise("A \\diamondright B")
example.add_premise("\\neg A")

# Configure for diversity in verification
settings = {
    'N': 4,
    'iterate': 6,
    'maximize': True,  # Maximize structural differences
}

example.update_settings(settings)
models = iterate_example(example)

# Analyze verification patterns
for i, model in enumerate(models):
    print(f"\nModel {i+1} verification summary:")
    for letter in ['A', 'B']:
        verifiers = count_verifiers(model, letter)
        print(f"  {letter}: {verifiers} verifying states")
```

### Example 4: Theory Comparison

```python
# Compare imposition models with logos models
from model_checker.theory_lib.imposition import examples

# Get a standard example
example_data = examples.IM_CM_1_example
premises, conclusions, settings = example_data

# Find multiple imposition models
imposition_theory = get_theory()
imp_example = BuildExample("comparison", imposition_theory)
for p in premises:
    imp_example.add_premise(p)
for c in conclusions:
    imp_example.add_conclusion(c)
imp_example.update_settings(settings)

imp_models = iterate_example(imp_example, max_iterations=3)

# Compare with logos theory (if compatible formulas)
# ... comparison code ...
```

## Advanced Usage

### Custom Difference Detection

You can extend the iterator to detect custom differences:

```python
class CustomImpositionIterator(ImpositionModelIterator):
    def _calculate_differences(self, new_structure, previous_structure):
        # Get standard differences
        differences = super()._calculate_differences(new_structure, previous_structure)
        
        # Add custom difference detection
        differences['custom_property'] = self._check_custom_property(
            new_structure, previous_structure
        )
        
        return differences
```

### Constraint Strategies

Implement custom constraint strategies:

```python
class StrategicIterator(ImpositionModelIterator):
    def _create_difference_constraint(self, previous_models):
        # Force specific structural properties
        constraints = []
        
        # Example: Force different numbers of imposition relations
        for prev_model in previous_models:
            imp_count = self._count_impositions(prev_model)
            constraints.append(
                self._imposition_count() != imp_count
            )
        
        return z3.And(constraints)
```

## Troubleshooting

### No Additional Models Found

If iteration stops after one model:

1. **Increase state space**: Try larger `N` value
2. **Relax constraints**: Remove `contingent`, `disjoint` requirements
3. **Extend timeout**: Increase `max_time`
4. **Check formula**: Ensure formula allows multiple models

### All Models Are Similar

If models lack diversity:

1. **Enable maximize**: Set `'maximize': True`
2. **Increase escape threshold**: `iterator.escape_threshold = 5`
3. **Use stronger formulas**: Add more constraints
4. **Larger state space**: Increase `N`

### Performance Issues

If iteration is too slow:

1. **Reduce state space**: Use smaller `N`
2. **Decrease timeout**: Lower `max_time`
3. **Limit iterations**: Set reasonable `max_iterations`
4. **Simplify formulas**: Remove nested operators

## Documentation

### For Model Explorers

- **[Basic Usage](#basic-usage)** - Finding multiple models
- **[Understanding Results](#understanding-results)** - Model differences
- **[Examples](#examples)** - Practical iteration scenarios

### For Developers

- **[Configuration](#configuration)** - Iterator settings
- **[Advanced Usage](#advanced-usage)** - Custom iteration strategies
- **[Performance Tips](#performance-tips)** - Optimization techniques

### For Researchers

- **[Types of Differences](#types-of-differences)** - What varies between models
- **[Theory Comparison](#example-4-theory-comparison)** - Cross-theory exploration
- **[Troubleshooting](#troubleshooting)** - Common issues and solutions

## Key Features

1. **Imposition Tracking**: Changes in counterfactual relationships
2. **Alternative Worlds**: Different outcome configurations
3. **Verification Patterns**: How atomic propositions vary
4. **Isomorphism Detection**: Avoid duplicate structures
5. **Performance Optimization**: Efficient constraint generation

## References

### Implementation Files

- **[Iterate Module](../iterate.py)** - ImpositionModelIterator implementation
- **[Examples Module](../examples.py)** - Iteration examples
- **[Tests](../tests/test_iterate.py)** - Iterator validation

### Related Documentation

- **[API Reference](API_REFERENCE.md#model-iteration)** - Technical details
- **[Settings](SETTINGS.md)** - Configuration options
- **[User Guide](USER_GUIDE.md)** - General usage patterns

---

[← Back to Documentation](README.md) | [Settings →](SETTINGS.md) | [Imposition Theory →](../README.md)