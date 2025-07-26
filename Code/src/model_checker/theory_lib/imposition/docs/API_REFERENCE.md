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

Within the imposition theory framework, this API enables exploration of counterfactual logic through Fine's semantics, where "if A then must B" is evaluated by imposing verifiers of A on the evaluation world. The implementation includes both must-counterfactuals (↪) and might-counterfactuals (⟂), providing a complete computational framework for counterfactual reasoning.

This reference serves developers implementing counterfactual logic systems, providing detailed specifications for all components, operators, and integration points.

## Quick Start

```python
# Core imposition theory usage
from model_checker.theory_lib.imposition import get_theory
from model_checker import BuildExample

# Create counterfactual example
theory = get_theory()
model = BuildExample("counterfactual", theory,
    premises=['A', 'A \\imposition B'],  # A is true, if A then must B
    conclusions=['B'],                    # Therefore B
    settings={'N': 3}
)

# Check validity (tests counterfactual modus ponens)
result = model.check_validity()
print(f"Counterfactual modus ponens: {result}")  # True - valid

# Access alternative worlds
if hasattr(model.model_structure, 'semantics'):
    alt_worlds = model.model_structure.semantics.calculate_alternative_worlds(
        verifiers={1, 2},  # A's verifiers
        eval_point={'world': 0},
        model_structure=model.model_structure
    )
    print(f"Alternative worlds: {alt_worlds}")
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
| Imposition | ↪ | `\\imposition` | 2 | If A then must B |
| Could | ⟂ | `\\could` | 2 | If A then might B |

### Extremal Operators

| Operator | Symbol | LaTeX | Arity | Description |
|----------|--------|-------|-------|-------------|
| Top | ⊤ | `\\top` | 0 | Logical truth |
| Bottom | ⊥ | `\\bot` | 0 | Logical falsehood |

### Operator Classes

#### `ImpositionOperator`

The core counterfactual operator implementing Fine's imposition semantics.

**Attributes:**
- `name`: "\\imposition"
- `arity`: 2

**Methods:**
- `true_at(self, leftarg, rightarg, eval_point)`: Defines truth conditions
- `false_at(self, leftarg, rightarg, eval_point)`: Defines falsity conditions
- `print_method(self, sentence_obj, eval_point, indent_num, use_colors)`: Custom printing

#### `MightImpositionOperator`

The might-counterfactual operator, defined as the dual of imposition.

**Attributes:**
- `name`: "\\could"
- `arity`: 2

**Definition:** `A \\could B` ≡ `\\neg(A \\imposition \\neg B)`

## Model Iteration

### `iterate_example(example, max_iterations=None)`

Find multiple distinct models for an imposition theory example.

**Parameters:**
- `example`: A BuildExample instance with an imposition theory model
- `max_iterations` (int, optional): Maximum number of models to find

**Returns:**
- `list`: List of distinct model structures

**Example:**
```python
from model_checker import BuildExample
from model_checker.theory_lib.imposition import iterate_example, get_theory

# Create an example
theory = get_theory()
example = BuildExample("my_example", theory)

# Find up to 5 models
models = iterate_example(example, max_iterations=5)
for i, model in enumerate(models):
    print(f"Model {i+1}:")
    model.print_model()
```

### `ImpositionModelIterator`

Class for iterating through distinct models for imposition theory formulas.

**Inheritance:** Extends `BaseModelIterator`

**Key Methods:**

#### `__init__(self, build_example)`
Initialize the iterator with a build example.

**Parameters:**
- `build_example`: A BuildExample instance

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
from model_checker import BuildExample

# Get the theory
theory = get_theory()

# Create a simple example
example = BuildExample("counterfactual_test", theory)
example.add_premise("\\neg A")
example.add_premise("A \\imposition B")
example.add_conclusion("A \\could C")

# Check validity
result = example.check_validity()
if result:
    print("The argument is valid")
else:
    print("Found countermodel:")
    example.print_model()
```

### Using Model Iteration

```python
from model_checker.theory_lib.imposition import iterate_example

# Find multiple models
models = iterate_example(example, max_iterations=3)
print(f"Found {len(models)} distinct models")

for i, model in enumerate(models):
    print(f"\nModel {i+1}:")
    model.print_model()
    if hasattr(model, 'print_model_differences'):
        model.print_model_differences()
```

### Working with Operators

```python
from model_checker.theory_lib.imposition import imposition_operators

# Access operator classes
ImpositionOp = imposition_operators.get_operator("\\imposition")
CouldOp = imposition_operators.get_operator("\\could")

# Check operator properties
print(f"Imposition arity: {ImpositionOp.arity}")
print(f"Could operator name: {CouldOp.name}")
```

## Error Handling

### Common Exceptions

- `ValueError`: Invalid operator name or formula syntax
- `z3.Z3Exception`: Z3 solver errors (timeout, unsatisfiability)
- `KeyError`: Missing required settings or operators

### Error Scenarios

```python
try:
    # Attempt to create example
    example = BuildExample("test", theory)
    example.add_premise("A \\invalid B")  # Invalid operator
except ValueError as e:
    print(f"Formula error: {e}")

try:
    # Check with insufficient time
    settings = {'max_time': 0.001}  # Very short timeout
    example = BuildExample("test", theory, settings)
    result = example.check_validity()
except z3.Z3Exception as e:
    print(f"Solver timeout: {e}")
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
- **Imposition** (↪): Must-counterfactual
- **Could** (⟂): Might-counterfactual

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