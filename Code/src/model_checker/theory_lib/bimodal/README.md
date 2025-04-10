# Bimodal Logic Implementation

## Overview

The bimodal theory implements a temporal-modal logic with two types of operators:
1. A temporal operators for reasoning about what is true at different times
2. A modal operators for reasoning about other world histories

This implementation is designed to study bimodal logics where:
- World histories are sequences of world states over time
- Each world state is an instantaneous configuration of the system
- World histories follow lawful transitions between consecutive states
- Time points can be negative, zero, or positive integers, constituting convex intervals

## Contents

This package includes the following components:
- `__init__.py` to expose definitions
- `examples.py` defines a number of examples to test
- `operators.py` defines the primitive and derived operators
- `semantic.py` defines the core semantics for the bimodal logic

## Z3 Implementation Details

### World and Time Representation

In the bimodal implementation:
- World states are represented as bitvectors (fusions of atomic states)
- Time points are integers (allowing negative times)
- World histories are modeled as arrays mapping time points to world states
- Each world history has a valid time interval within which it is defined
- The time of evaluation is set to `0` where all time-shifted worlds that overlap with `0` are required to exist.

### Dual Representation Challenge

A significant technical challenge in this implementation is handling Z3's dual representation of arrays:

**Problem:** Z3 may represent the same conceptual array in two different ways:

1. **`ArrayRef` representation** - A concrete array with explicit values for each index
   ```
   K(Int, 0)  // A constant array mapping everything to 0
   Store(K(Int, 1), -1, 0)  // An array of all 1s except at index -1 where it's 0
   ```

2. **`QuantifierRef` (Lambda) representation** - A function describing the array content
   ```
   Lambda(k!0, If(And(1 <= k!0, Not(2 <= k!0)), 1, 0))  // Array where k!0=1 maps to 1, else 0
   ```

**Consequence:** The standard Z3 array access method (`z3.Select`) works only with `ArrayRef`, not with `QuantifierRef`, causing errors like:
```
TypeError: 'QuantifierRef' object has no attribute 'domain_n'
```

### Solution: Dynamic Selection Evaluation

To handle both representations consistently, we implemented a `safe_select` function that:

1. Automatically detects the array representation type
2. For `ArrayRef`, uses the standard `z3.Select` operation
3. For `QuantifierRef`, uses variable substitution in the Lambda body
4. Handles type conversion between Python integers and Z3 integer values

This ensures consistent array access throughout the code, regardless of how Z3 chooses to represent world histories internally.

```python
def safe_select(z3_model, world_array, time):
    """Safely select from either ArrayRef or QuantifierRef (Lambda) arrays."""
    if isinstance(world_array, z3.ArrayRef):
        return z3_model.eval(z3.Select(world_array, z3.IntVal(time)))
    elif isinstance(world_array, z3.QuantifierRef):
        return z3_model.eval(z3.substitute(
            world_array.body(), 
            (z3.Var(0, z3.IntSort()), z3.IntVal(time))
        ))
    else:
        raise TypeError(f"Cannot select from world array type {type(world_array)}")
```

### Why This Happens

Z3's solver optimization strategies can produce different array representations:
- Arrays with simple patterns might be represented as Lambda functions
- Arrays with irregular patterns might be represented as concrete arrays
- The same formula can yield different representations across runs
- Different world histories in the same model can have different representations

The `safe_select` approach ensures the code works reliably regardless of these representation differences.

## Basic Usage

### Creating a Bimodal Model

```python
from model_checker import BuildExample, get_theory

# Load the bimodal theory
theory = get_theory("bimodal")

# Create a model with default settings
model = BuildExample("temporal_example", theory)

# Check a temporal formula
result = model.check_formula("A \\rightarrow \\Future A")
```

### Custom Settings

The bimodal theory supports several settings:
- `N`: Number of world states (default: 2)
- `M`: Number of time points (default: 2)
- `contingent`: Whether sentence letters are assigned to contingent propositions
- `disjoint`: Whether sentence letters are assigned to distinct world states

Example with custom settings:
```python
settings = {
    'N': 3,        # 3 possible world states
    'M': 4,        # 4 times including time 0
    'contingent': True
}
model = BuildExample("my_example", theory, settings=settings)
```

## Operators

The bimodal theory implements the following operators:

### Temporal Operators
- `\\Future` - It always will be the case that
- `\\Past` - It always has been the case that

### Modal Operators
- `\\Box` - Necessity operator (true in all accessible worlds)
- `\\Diamond` - Possibility operator (true in some accessible world)

### Classical Operators
- `\\neg` - Negation
- `\\wedge` - Conjunction
- `\\vee` - Disjunction
- `\\rightarrow` - Material implication
- `\\leftrightarrow` - Material equivalence

## Known Limitations

- Performance degrades with many time points or complex formulas
- Z3 timeout can occur for complex models (adjust the `max_time` setting)
- Counterfactual evaluation requires careful handling of world/time relationships
