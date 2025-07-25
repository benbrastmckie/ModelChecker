# Bimodal Theory API Reference

This document provides comprehensive API documentation for the bimodal theory implementation in ModelChecker.

## Table of Contents

- [Overview](#overview)
- [Core Functions](#core-functions)
- [Classes](#classes)
- [Operators](#operators)
- [Model Iteration](#model-iteration)
- [Type Definitions](#type-definitions)
- [Examples](#examples)
- [Error Handling](#error-handling)

## Overview

The bimodal theory API provides a complete framework for temporal-modal logic reasoning. It combines:
- **Temporal operators** for reasoning about time (past/future)
- **Modal operators** for reasoning about possibility/necessity
- **World histories** representing sequences of states over time

All code examples use LaTeX notation (e.g., `\\Box`, `\\Future`) as required by the ModelChecker parser.

## Core Functions

### `get_theory(config=None)`

Get the bimodal theory configuration object.

**Parameters:**
- `config` (dict, optional): Custom configuration overrides

**Returns:**
- dict: Theory configuration with semantics, proposition, model, and operators

**Example:**
```python
from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()
# Use with BuildExample
example = BuildExample("my_example", theory, [
    ["\\Box p"],  # Premises
    ["\\Future p"],  # Conclusions
    {"M": 3, "N": 1}  # Settings
])
```

### `get_examples()`

Get all example formulas defined in the theory.

**Returns:**
- dict: Dictionary mapping example names to example configurations

**Example:**
```python
examples = bimodal.get_examples()
# Access specific example
modal_example = examples["MD_CM_1"]
```

### `get_test_examples()`

Get the subset of examples used for testing.

**Returns:**
- dict: Dictionary of test examples

## Classes

### `BimodalSemantics`

Core semantic framework implementing temporal-modal logic semantics.

**Inherits from:** `SemanticDefaults`

**Key Attributes:**
- `N` (int): Number of atomic propositions
- `M` (int): Number of time points
- `world_function`: Z3 function mapping world IDs to world histories
- `task`: Z3 relation for transitions between world states
- `truth_condition`: Z3 function for atomic proposition truth

**Key Methods:**

#### `__init__(self, settings)`
Initialize the semantic framework with given settings.

#### `true_at(self, sentence, eval_point)`
Evaluate if a sentence is true at the given evaluation point.

**Parameters:**
- `sentence`: The sentence to evaluate
- `eval_point` (dict): Dictionary with keys:
  - `"world"` (int): World ID
  - `"time"` (int): Time point

**Returns:**
- Z3 formula that is satisfied when sentence is true

#### `extract_model_elements(self, z3_model)`
Extract world histories and relationships from a Z3 model.

**Returns:**
- Tuple of (world_histories, main_world_history, world_arrays, time_shift_relations)

### `BimodalProposition`

Represents propositions in bimodal logic with evaluation across worlds and times.

**Inherits from:** `PropositionDefaults`

**Key Attributes:**
- `sentence`: The sentence this proposition represents
- `extension` (dict): Maps world IDs to (true_times, false_times) pairs
- `eval_world` (int): World ID for evaluation
- `eval_time` (int): Time point for evaluation

**Key Methods:**

#### `__init__(self, sentence, model_structure, eval_world='main', eval_time='now')`
Create a proposition for the given sentence.

#### `truth_value_at(self, eval_world, eval_time)`
Check if the proposition is true at a specific world and time.

**Parameters:**
- `eval_world` (int): World ID
- `eval_time` (int): Time point

**Returns:**
- bool: True if proposition holds at the given world and time

### `BimodalStructure`

Model structure for bimodal logic systems.

**Inherits from:** `ModelDefaults`

**Key Attributes:**
- `M` (int): Number of time points
- `main_world` (int): Main world ID (default: 0)
- `main_time` (int): Main evaluation time
- `world_histories` (dict): Maps world IDs to time-state mappings
- `world_arrays` (dict): Maps world IDs to Z3 world arrays
- `time_shift_relations` (dict): Time-shift relationships between worlds

**Key Methods:**

#### `get_world_history(self, world_id)`
Get the time-to-state mapping for a world.

**Parameters:**
- `world_id` (int): World identifier

**Returns:**
- dict: Mapping from time points to world states

#### `print_world_histories_vertical(self, output=sys.stdout)`
Print world histories with time flowing vertically (bimodal-specific feature).

## Operators

### Extensional Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| NegationOperator | ¬ | `\\neg` | 1 | Logical negation |
| AndOperator | ∧ | `\\wedge` | 2 | Logical conjunction |
| OrOperator | ∨ | `\\vee` | 2 | Logical disjunction |
| ConditionalOperator | → | `\\rightarrow` | 2 | Material implication |
| BiconditionalOperator | ↔ | `\\leftrightarrow` | 2 | Material biconditional |

### Extremal Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| BotOperator | ⊥ | `\\bot` | 0 | Always false |
| TopOperator | ⊤ | `\\top` | 0 | Always true |

### Modal Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| NecessityOperator | □ | `\\Box` | 1 | True in all possible worlds |
| DefPossibilityOperator | ◇ | `\\Diamond` | 1 | True in some possible world |

### Temporal Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| FutureOperator | ⏵ | `\\Future` | 1 | True at all future times |
| PastOperator | ⏴ | `\\Past` | 1 | True at all past times |
| DefFutureOperator | ⏵ | `\\future` | 1 | True at some future time |
| DefPastOperator | ⏴ | `\\past` | 1 | True at some past time |

### Operator Usage Example

```python
# Temporal necessity: "It is necessary that p will always be true"
formula1 = "\\Box \\Future p"

# Modal future: "In the future, p will be necessary"
formula2 = "\\Future \\Box p"

# Combined: "It's possible that p was true in the past"
formula3 = "\\Diamond \\Past p"
```

## Model Iteration

### `iterate_example(example, max_iterations=None)`

Find multiple distinct models for a bimodal theory example.

**Parameters:**
- `example`: BuildExample instance with bimodal theory
- `max_iterations` (int, optional): Maximum models to find

**Returns:**
- list: List of distinct model structures

**Example:**
```python
from model_checker import BuildExample
from model_checker.theory_lib.bimodal.iterate import iterate_example

example = BuildExample("modal_example", theory, [
    ["\\Box p"],
    ["\\Diamond q"],
    {"M": 2, "N": 2, "iterate": 3}
])

models = iterate_example(example, max_iterations=5)
for i, model in enumerate(models):
    print(f"Model {i+1}:")
    model.print_all()
```

### `BimodalModelIterator`

Model iterator class for finding multiple bimodal models.

**Inherits from:** `BaseModelIterator`

**Key Methods:**
- `_calculate_differences()`: Detect differences between models
- `_create_difference_constraint()`: Generate constraints for new models
- `_create_non_isomorphic_constraint()`: Force structural differences
- `display_model_differences()`: Format differences for display

## Type Definitions

### Time Points
- Time points range from `-M+1` to `M-1` (centered around 0)
- Type: `int`

### World IDs
- World identifiers are non-negative integers
- Type: `int` (0, 1, 2, ...)

### Evaluation Points
```python
eval_point = {
    "world": 0,    # World ID (int)
    "time": 0      # Time point (int)
}
```

### World States
- Represented as bit vectors in Z3
- String representation uses comma-separated letters (e.g., "a,b,c")

## Examples

### Basic Model Checking

```python
from model_checker import BuildExample
from model_checker.theory_lib import bimodal

# Get theory
theory = bimodal.get_theory()

# Create example: "Necessarily p implies always p in the future"
example = BuildExample("temporal_necessity", theory, [
    ["\\Box p"],                    # Premise
    ["\\Future p"],                 # Conclusion  
    {"M": 3, "N": 1, "max_time": 5} # Settings
])

# Check validity
result = example.check_result()
if result['model_found']:
    print("Countermodel found - inference is invalid")
else:
    print("No countermodel - inference may be valid")
```

### Advanced Usage with Time Intervals

```python
# Example with multiple time points and modal operators
example = BuildExample("complex_bimodal", theory, [
    ["\\Diamond \\Future p", "\\Box \\Past q"],  # Premises
    ["\\Future \\Diamond (p \\wedge q)"],        # Conclusion
    {
        "M": 4,               # 4 time points
        "N": 2,               # 2 atomic propositions
        "max_time": 10,       # Solver timeout
        "align_vertically": True  # Bimodal-specific display
    }
])

model = example.model_structure
if model.z3_model:
    # Access world histories
    for world_id, history in model.world_histories.items():
        print(f"World {world_id}:")
        for time, state in sorted(history.items()):
            print(f"  Time {time}: {state}")
```

### Model Iteration Example

```python
from model_checker.theory_lib.bimodal.iterate import iterate_example

# Find multiple models showing different temporal-modal patterns
example = BuildExample("iterate_demo", theory, [
    ["\\Diamond p \\vee \\Diamond q"],
    [],  # No conclusions - explore all models
    {"M": 2, "N": 2, "iterate": 5}
])

models = iterate_example(example)
print(f"Found {len(models)} distinct models")

# Examine differences
for i in range(1, len(models)):
    print(f"\nDifferences between model {i-1} and {i}:")
    models[i].display_model_differences()
```

## Error Handling

### Common Exceptions

#### `ValueError`
- Invalid world ID or time point
- Missing required settings
- Incompatible operator combinations

#### `KeyError`
- Accessing non-existent world in world_histories
- Missing time point in world history
- Invalid operator name

#### `z3.Z3Exception`
- Solver timeout (increase `max_time`)
- Unsatisfiable constraints
- Invalid Z3 expressions

### Error Handling Example

```python
try:
    example = BuildExample("test", theory, [
        ["\\Box p"],
        ["p"],
        {"M": 1, "N": 1}  # May be too constrained
    ])
    result = example.check_result()
except ValueError as e:
    print(f"Configuration error: {e}")
except z3.Z3Exception as e:
    print(f"Solver error: {e}")
    # Try with increased resources
    example.settings["M"] = 2
    example.settings["max_time"] = 10
```

### Debugging Tips

1. **Enable Z3 output**: Set `"print_z3": True` in settings
2. **Check constraints**: Set `"print_constraints": True`
3. **Increase time points**: Some formulas need `M > 2`
4. **Verify intervals**: Check `world_time_intervals` in semantics
5. **Use vertical display**: Set `"align_vertically": True` for clarity

## See Also

- [User Guide](USER_GUIDE.md) - Practical usage patterns
- [Architecture](ARCHITECTURE.md) - Implementation details
- [Settings Reference](SETTINGS.md) - Configuration options
- [Model Iteration](ITERATE.md) - Finding multiple models