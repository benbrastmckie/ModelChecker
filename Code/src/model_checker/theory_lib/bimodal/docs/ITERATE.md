# Bimodal Theory Model Iteration Guide

This guide explains how to find multiple distinct models for bimodal logic formulas using the model iteration feature.

## Table of Contents

- [Overview](#overview)
- [Basic Usage](#basic-usage)
- [Configuration](#configuration)
- [Understanding Results](#understanding-results)
- [Performance Tips](#performance-tips)
- [Examples](#examples)

## Overview

Model iteration in bimodal theory allows you to find multiple distinct models that satisfy your premises while violating your conclusions. This is particularly useful for:

- **Exploring semantic space**: Understanding different ways temporal-modal formulas can be satisfied
- **Testing robustness**: Checking if countermodels exist across various world history configurations
- **Research applications**: Investigating the relationship between temporal and modal dimensions
- **Educational purposes**: Demonstrating non-uniqueness of models

The bimodal iterator specifically handles:
- World histories (time-indexed sequences of states)
- Time intervals for each world
- Task transitions between consecutive states
- Modal accessibility across worlds at fixed times
- Time-shift relations between world histories

## Basic Usage

### Simple Iteration

```python
from model_checker import BuildExample
from model_checker.theory_lib import bimodal
from model_checker.theory_lib.bimodal.iterate import iterate_example

# Get theory
theory = bimodal.get_theory()

# Create example
example = BuildExample("modal_temporal", theory, [
    ["\\Box p"],           # p is necessary
    ["\\Future \\Box p"],  # In the future, p will be necessary
    {"M": 3, "N": 1, "iterate": 3}  # Request 3 models
])

# Find multiple models
models = iterate_example(example)
print(f"Found {len(models)} distinct models")

# Display each model
for i, model in enumerate(models):
    print(f"\n=== Model {i+1} ===")
    model.print_world_histories_vertical()
```

### Using the Iterator Class Directly

```python
from model_checker.theory_lib.bimodal.iterate import BimodalModelIterator

# Create iterator
iterator = BimodalModelIterator(example)

# Configure iteration
iterator.max_iterations = 5

# Perform iteration
models = iterator.iterate()

# Access iteration statistics
print(f"Total attempts: {iterator.iteration_count}")
print(f"Isomorphic models found: {iterator.isomorphic_count}")
```

## Configuration

### Iteration Settings

The `iterate` setting in your example configuration controls iteration behavior:

```python
settings = {
    "M": 3,                    # Number of time points
    "N": 2,                    # Number of atomic propositions
    "iterate": 5,              # Find up to 5 models
    "max_time": 10,           # Overall timeout for first model
}
```

### Iterator Configuration

When using the iterator directly, you can configure:

```python
iterator = BimodalModelIterator(example)

# Maximum models to find
iterator.max_iterations = 10

# Enable debug output
import logging
logging.getLogger('model_checker.theory_lib.bimodal.iterate').setLevel(logging.DEBUG)
```

### Difference Detection Settings

The bimodal iterator tracks differences in:
1. **World histories**: Changes in state sequences over time
2. **Truth conditions**: Different valuations for atomic propositions
3. **Task relations**: Changes in allowed state transitions
4. **Time intervals**: Different temporal extents for worlds
5. **Time-shift relations**: How worlds relate through time translation

## Understanding Results

### Model Differences

Each generated model includes difference information:

```python
model = models[1]  # Second model
if hasattr(model, 'model_differences'):
    diffs = model.model_differences
    
    # World history changes
    if 'world_histories' in diffs:
        for world_id, changes in diffs['world_histories'].items():
            print(f"World {world_id} changed:")
            for time, change in changes.items():
                print(f"  Time {time}: {change['old']} -> {change['new']}")
```

### Displayed Differences

The iterator automatically displays differences between consecutive models:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World History Changes:
  World W_0 changed:
    Time -1: a -> b
    Time 0: a -> a,b
  + World W_2 added
    History: (-1:b) -> (0:a) -> (1:∅)

Truth Condition Changes:
  Letter a:
    State b: False -> True

Time Interval Changes:
  World W_2 interval: None -> (-1, 1)

Time Shift Relations:
  World W_2 shifts:
    + Shift +1: -> W_1
    + Shift -1: -> W_0
```

### Interpreting Bimodal Differences

Key aspects to understand:

1. **World Histories**: Show how states evolve over time within each world
2. **Time Intervals**: Indicate the temporal extent of each world
3. **Task Relations**: Define allowed transitions between states
4. **Truth Conditions**: Determine which propositions hold in which states
5. **Time Shifts**: Show how worlds relate through temporal translation

## Performance Tips

### 1. Optimize Initial Settings

Start with minimal settings and increase as needed:

```python
# Start small
settings = {"M": 2, "N": 1, "iterate": 3}

# Increase if no models found
settings = {"M": 3, "N": 2, "iterate": 5}
```

### 2. Use Appropriate Timeouts

Balance between finding models and performance:

```python
settings = {
    "max_time": 5,            # Initial model timeout
}
```

### 3. Limit Iteration Count

For complex formulas, limit iterations:

```python
# For exploration
models = iterate_example(example, max_iterations=3)

# For exhaustive search (careful with performance)
models = iterate_example(example, max_iterations=20)
```

### 4. Monitor Progress

Enable debug logging for long-running iterations:

```python
import logging
logger = logging.getLogger('model_checker.theory_lib.bimodal.iterate')
logger.setLevel(logging.INFO)

# Now iteration will show progress
models = iterate_example(example)
```

### 5. Understand Complexity

Bimodal models are complex due to:
- Multiple worlds with independent histories
- Time intervals that can overlap or be disjoint
- Task relations creating a transition graph
- Modal accessibility at each time point

Complexity grows with:
- Number of time points (M)
- Number of propositions (N)
- Number of worlds found

## Examples

### Example 1: Temporal-Modal Interaction

Find models showing different relationships between necessity and future:

```python
# "Necessary p" doesn't imply "Always p in the future"
example = BuildExample("necessity_vs_future", theory, [
    ["\\Box p"],
    ["\\Future p"],
    {"M": 3, "N": 1, "iterate": 5}
])

models = iterate_example(example)

# Examine how different world structures satisfy Box p but not Future p
for i, model in enumerate(models):
    print(f"\nModel {i+1}:")
    print("World histories where p is necessary at time 0:")
    for world_id, history in model.world_histories.items():
        # Check if p is true at time 0 in all worlds
        if 0 in history:
            print(f"  W_{world_id} at t=0: {history[0]}")
```

### Example 2: Exploring Contingency

Find models with different contingency patterns:

```python
# Contingent propositions with temporal operators
example = BuildExample("contingent_temporal", theory, [
    ["\\Future p \\vee \\Past p"],
    [],  # No conclusions - just explore
    {
        "M": 4, 
        "N": 2, 
        "contingent": True,  # Force contingent valuations
        "iterate": 4
    }
])

models = iterate_example(example)

# Analyze contingency patterns
for i, model in enumerate(models):
    print(f"\nModel {i+1} contingency pattern:")
    for letter in ['a', 'b']:
        true_states = set()
        false_states = set()
        
        for world_id, history in model.world_histories.items():
            for time, state in history.items():
                if letter in state:
                    true_states.add(state)
                else:
                    false_states.add(state)
        
        print(f"  {letter}: true in {len(true_states)} states, false in {len(false_states)} states")
```

### Example 3: Complex Bimodal Patterns

Explore intricate temporal-modal relationships:

```python
# Complex formula with nested operators
example = BuildExample("complex_bimodal", theory, [
    ["\\Diamond \\Future p", "\\Box \\Past q"],
    ["\\Future (\\Diamond p \\wedge \\Box q)"],
    {
        "M": 3,
        "N": 2,
        "iterate": 6,
        "align_vertically": True  # Better visualization
    }
])

models = iterate_example(example)

# Focus on time-shift relations
for i, model in enumerate(models[1:], 1):
    print(f"\nModel {i} time-shift structure:")
    for source_id, shifts in model.time_shift_relations.items():
        print(f"  W_{source_id}:")
        for shift, target_id in shifts.items():
            if shift != 0:  # Skip identity
                print(f"    shift by {shift:+d} -> W_{target_id}")
```

### Example 4: Performance Comparison

Compare iteration performance with different settings:

```python
import time

configs = [
    {"M": 2, "N": 1, "iterate": 5},
    {"M": 3, "N": 1, "iterate": 5},
    {"M": 3, "N": 2, "iterate": 5},
]

for config in configs:
    example = BuildExample("perf_test", theory, [
        ["\\Box p \\vee \\Diamond q"],
        ["\\Future (p \\wedge q)"],
        config
    ])
    
    start = time.time()
    models = iterate_example(example)
    elapsed = time.time() - start
    
    print(f"Config {config}: {len(models)} models in {elapsed:.2f}s")
    print(f"  Average: {elapsed/len(models):.2f}s per model")
```

## Advanced Topics

### Custom Difference Constraints

The bimodal iterator uses sophisticated constraints to ensure model diversity:

1. **Truth Condition Variation**: Forces different truth values for atomic propositions
2. **Task Relation Modification**: Changes allowed state transitions
3. **World Count Variation**: Generates models with different numbers of worlds
4. **Interval Shifting**: Creates worlds with different temporal extents
5. **History Permutation**: Rearranges state sequences while preserving task constraints

### Isomorphism Detection

The iterator detects and skips isomorphic models based on:
- Bijective world mappings preserving all relations
- Time-shift equivalence
- Truth condition permutations

### Escape Strategies

When stuck in isomorphic model loops, the iterator employs:
1. Dramatically different world counts
2. Interval mirroring (negative to positive)
3. Truth condition inversion
4. Task relation reversal

## Troubleshooting

### No Additional Models Found

If iteration stops after one model:
- Increase `M` (time points) for more structural variety
- Add more atomic propositions (`N`)
- Check if your formula heavily constrains the model space
- Try relaxing constraints (e.g., remove `contingent` requirement)

### Slow Iteration

If iteration is taking too long:
- Reduce `max_time` in settings
- Limit `max_iterations`
- Simplify your formula
- Use smaller values for `M` and `N`

### Many Isomorphic Models

If seeing "Skipped isomorphic model" frequently:
- This is normal and indicates the iterator is working correctly
- The iterator will eventually escape the isomorphic loop
- Consider whether your formula admits limited structural variety

## See Also

- [API Reference](API_REFERENCE.md#model-iteration) - Detailed API documentation
- [Architecture](ARCHITECTURE.md#model-iteration) - Implementation details
- [User Guide](USER_GUIDE.md#advanced-usage) - General usage patterns
- [Settings Reference](SETTINGS.md#iteration-settings) - Configuration options