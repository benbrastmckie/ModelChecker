# API Reference: Technical Documentation for Imposition Theory

[← Back to Documentation](README.md) | [Architecture →](ARCHITECTURE.md) | [Imposition Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # This file - complete technical reference
├── ARCHITECTURE.md    # Implementation design and patterns
├── ITERATE.md         # Model iteration for counterfactuals
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration parameters
└── USER_GUIDE.md      # Tutorial and introduction
```

## Overview

The **API Reference** provides comprehensive technical documentation for the imposition theory implementation, covering Kit Fine's counterfactual semantics within the ModelChecker framework. The theory implements the imposition operation for counterfactual reasoning, extending the Logos hyperintensional foundation.

Within the imposition theory framework, this API enables exploration of counterfactual logic through Fine's semantics, where "if A then must B" is evaluated by imposing verifiers of A on the evaluation world. The implementation includes both must-counterfactuals (□→) and might-counterfactuals (◇→), providing a complete computational framework for counterfactual reasoning.

This reference serves developers implementing counterfactual logic systems, providing detailed specifications for all components, operators, and integration points.

## Core Usage

```python
# Core imposition theory usage
from model_checker.theory_lib.imposition import get_theory

# Load the theory
theory = get_theory()
semantics_class = theory['semantics']
operators = theory['operators']

# Example formulas (conceptual - see examples.py for complete implementation)
# "A \\boxright B"  # If A then must B (must-counterfactual)
# "A \\diamondright B"  # If A then might B (might-counterfactual)

# Access semantic methods
# semantics = semantics_class(settings={'N': 3})
# alt_worlds = semantics.calculate_alternative_worlds(
#     verifiers={1, 2},  # A's verifiers
#     eval_point={'world': 0},
#     model_structure=model_structure
# )
```

## Core Functions

### `get_theory(config=None)`

Get the imposition theory configuration.

**Parameters:**
- `config` (dict, optional): Configuration dictionary (currently unused)

**Returns:**
- `dict`: Theory configuration with the following keys:
  - `semantics`: ImpositionSemantics class
  - `proposition`: Proposition class (from logos)
  - `model`: ModelStructure class (from logos)
  - `operators`: Dictionary of available operators

**Example:**
```python
from model_checker.theory_lib.imposition import get_theory

theory = get_theory()
semantics_class = theory['semantics']
operators = theory['operators']

# See examples.py for complete implementation examples
```

### `get_examples()`

Get the example range for the imposition theory.

**Returns:**
- `dict`: Dictionary mapping example names to example configurations

**Example:**
```python
from model_checker.theory_lib.imposition import get_examples

examples = get_examples()
for name, example in examples.items():
    premises, conclusions, settings = example
    print(f"{name}: {premises} => {conclusions}")

# See examples.py for complete implementation examples
```

### `get_test_examples()`

Get test examples for the imposition theory.

**Returns:**
- `dict`: Dictionary of test cases including both countermodels and theorems

**Example:**
```python
from model_checker.theory_lib.imposition import get_test_examples

tests = get_test_examples()
# Access specific test categories
countermodels = {k: v for k, v in tests.items() if k.startswith('IM_CM_')}
theorems = {k: v for k, v in tests.items() if k.startswith('IM_TH_')}

# See examples.py for complete implementation examples
```

## Classes

### `ImpositionSemantics`

Core semantic framework implementing Fine's imposition semantics.

**Inheritance:** Extends `LogosSemantics`

**Key Methods:**

#### `__init__(self, settings)`
Initialize the imposition semantics with given settings.

**Parameters:**
- `settings` (dict): Configuration settings

#### `imposition(self, state, world, outcome)`
Z3 function representing the imposition relation.

**Parameters:**
- `state`: BitVec representing the imposed state
- `world`: BitVec representing the world being imposed on
- `outcome`: BitVec representing the outcome world

**Returns:**
- `z3.BoolRef`: Boolean indicating if the imposition holds

#### `is_alternative(self, outcome_world, state, eval_point)`
Check if outcome_world is an alternative to eval_point via state.

**Parameters:**
- `outcome_world`: The potential alternative world
- `state`: The imposed state
- `eval_point`: Dictionary with 'world' key for evaluation

**Returns:**
- `bool`: True if outcome_world is an alternative

#### `calculate_alternative_worlds(self, verifiers, eval_point, model_structure)`
Calculate all alternative worlds given verifiers and evaluation point.

**Parameters:**
- `verifiers`: Set of verifying states
- `eval_point`: Dictionary with 'world' key
- `model_structure`: The model structure instance

**Returns:**
- `set`: Set of alternative worlds

### `Proposition`

Represents logical propositions in the imposition theory.

**Note:** Imported from logos theory for consistency.

### `ModelStructure`

Represents model structures for the imposition theory.

**Note:** Imported from logos theory for consistency.

## Operators

The imposition theory provides the following operators:

### Extensional Operators (inherited from logos)

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| Negation | ¬ | `\\neg` | 1 | Logical negation |
| Conjunction | ∧ | `\\wedge` | 2 | Logical AND |
| Disjunction | ∨ | `\\vee` | 2 | Logical OR |
| Conditional | → | `\\to` | 2 | Material conditional |
| Biconditional | ↔ | `\\leftrightarrow` | 2 | If and only if |

### Modal Operators (inherited from logos)

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| Necessity | □ | `\\Box` | 1 | It is necessary that |
| Possibility | ◇ | `\\Diamond` | 1 | It is possible that |

### Imposition Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| Imposition | □→ | `\\boxright` | 2 | If A then must B |
| Could | ◇→  | `\\diamondright` | 2 | If A then might B |

### Extremal Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| Top | ⊤ | `\\top` | 0 | Logical truth |
| Bottom | ⊥ | `\\bot` | 0 | Logical falsehood |

### Operator Classes

#### `ImpositionOperator`

The core counterfactual operator implementing Fine's imposition semantics.

**Attributes:**
- `name`: "\\boxright"
- `arity`: 2

**Methods:**
- `true_at(self, leftarg, rightarg, eval_point)`: Defines truth conditions
- `false_at(self, leftarg, rightarg, eval_point)`: Defines falsity conditions
- `print_method(self, sentence_obj, eval_point, indent_num, use_colors)`: Custom printing

#### `MightImpositionOperator`

The might-counterfactual operator, defined as the dual of imposition.

**Attributes:**
- `name`: "\\diamondright"
- `arity`: 2

**Definition:** `A \\diamondright B` ≡ `\\neg(A \\boxright \\neg B)`

## Model Iteration

### `iterate_example(example, max_iterations=None)`

Find multiple distinct models for an imposition theory example.

**Parameters:**
- `example`: An example instance with an imposition theory model
- `max_iterations` (int, optional): Maximum number of models to find

**Returns:**
- `list`: List of distinct model structures

**Example:**
```python
from model_checker.theory_lib.imposition import iterate_example, get_theory

# Load theory for iteration
theory = get_theory()

# Example usage (see examples.py for complete implementation):
# models = iterate_example(example, max_iterations=5)
# for i, model in enumerate(models):
#     print(f"Model {i+1}:")
#     model.print_model()
```

### `ImpositionModelIterator`

Class for iterating through distinct models for imposition theory formulas.

**Inheritance:** Extends `BaseModelIterator`

**Key Methods:**

#### `__init__(self, build_example)`
Initialize the iterator with an example instance.

**Parameters:**
- `build_example`: An example instance

#### `iterate(self)`
Find multiple distinct models.

**Returns:**
- `list`: List of model structures

#### `display_model_differences(self, model_structure, output=sys.stdout)`
Display differences between models in a formatted way.

**Parameters:**
- `model_structure`: Model structure with differences
- `output`: Output stream (default: sys.stdout)

## Type Definitions

### Settings Dictionary

The imposition theory uses the following settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 3,              # Number of atomic states
    'contingent': False, # Whether sentence letters must be contingent
    'non_empty': False,  # Whether all states must be non-empty
    'non_null': False,   # Whether to exclude the null state
    'disjoint': False,   # Whether atomic states must be disjoint
    'max_time': 1,       # Z3 solver timeout in seconds
    'iterate': 1,        # Number of models to find
    'expectation': None, # Expected result (True/False/None)
}

DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,  # Print impossible states
    "print_constraints": False, # Print Z3 constraints
    "print_z3": False,         # Print Z3 output
    "save_output": False,      # Save output to file
    "maximize": False,         # Maximize model diversity
}
```

## Examples

### Basic Usage

```python
from model_checker.theory_lib.imposition import get_theory, get_examples

# Get the theory
theory = get_theory()
semantics_class = theory['semantics']
operators = theory['operators']

# Example formulas for counterfactual reasoning:
# "\\neg A"           # A is false
# "A \\boxright B"    # If A then must B
# "A \\diamondright C" # If A then might C

# See examples.py for complete implementation examples
```

### Using Model Iteration

```python
from model_checker.theory_lib.imposition import iterate_example

# Model iteration example (see examples.py for complete implementation):
# models = iterate_example(example, max_iterations=3)
# print(f"Found {len(models)} distinct models")
# 
# for i, model in enumerate(models):
#     print(f"\\nModel {i+1}:")
#     model.print_model()
#     if hasattr(model, 'print_model_differences'):
#         model.print_model_differences()
```

### Working with Operators

```python
from model_checker.theory_lib.imposition import get_theory

# Access operators through theory configuration
theory = get_theory()
operators = theory['operators']

# Example operator access (see examples.py for complete implementation):
# ImpositionOp = operators["\\boxright"]
# CouldOp = operators["\\diamondright"]
# 
# print(f"Imposition arity: {ImpositionOp.arity}")
# print(f"Could operator name: {CouldOp.name}")
```

## Error Handling

### Common Exceptions

- `ValueError`: Invalid operator name or formula syntax
- `z3.Z3Exception`: Z3 solver errors (timeout, unsatisfiability)
- `KeyError`: Missing required settings or operators

### Error Scenarios

```python
# Error handling examples (see examples.py for complete implementation):
# try:
#     # Invalid formula syntax
#     semantics = semantics_class(settings)
#     # Process formula with invalid operator "A \\invalid B"
# except ValueError as e:
#     print(f"Formula error: {e}")
# 
# try:
#     # Solver timeout scenario
#     settings = {'max_time': 0.001}  # Very short timeout
#     semantics = semantics_class(settings)
#     # Attempt complex satisfiability check
# except z3.Z3Exception as e:
#     print(f"Solver timeout: {e}")
```

## Documentation

### For API Users

- **[Core Functions](#core-functions)** - get_theory, get_examples, get_test_examples
- **[Classes](#classes)** - ImpositionSemantics, model components
- **[Operators](#operators)** - Complete operator reference

### For Developers

- **[Model Iteration](#model-iteration)** - Finding multiple counterfactual models
- **[Type Definitions](#type-definitions)** - Settings and configuration
- **[Error Handling](#error-handling)** - Common exceptions and scenarios

### For Researchers

- **[Imposition Semantics](#impositionsemantics)** - Fine's counterfactual framework
- **[Alternative Worlds](#calculate_alternative_worldsself-verifiers-eval_point-model_structure)** - Core semantic calculation
- **[Examples](#examples)** - Usage patterns and test cases

## Operator Summary

The imposition theory provides 11 operators total:

**Inherited from Logos** (9 operators):
- Extensional: ¬, ∧, ∨, →, ↔, ⊤, ⊥ (7 operators)
- Modal: □, ◇ (2 operators)

**Imposition-Specific** (2 operators):
- **Imposition** (□→): Must-counterfactual
- **Could** (◇→): Might-counterfactual

## Example Summary

The theory includes 32 comprehensive test examples:
- **Countermodels** (21): Invalid counterfactual inferences
- **Theorems** (11): Valid counterfactual principles

## References

### Implementation Files

- **[Semantic Module](../semantic.py)** - ImpositionSemantics implementation
- **[Operators Module](../operators.py)** - Counterfactual operators
- **[Examples Module](../examples.py)** - 32 test cases

### Related Documentation

- **[Architecture](ARCHITECTURE.md)** - Design patterns and implementation
- **[User Guide](USER_GUIDE.md)** - Tutorial with examples
- **[Settings](SETTINGS.md)** - Configuration options

---

[← Back to Documentation](README.md) | [Architecture →](ARCHITECTURE.md) | [Imposition Theory →](../README.md)
