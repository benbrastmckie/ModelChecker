# Logos Theory API Reference

[← Back to Documentation](README.md) | [User Guide →](USER_GUIDE.md)

## Table of Contents

1. [Overview](#overview)
2. [Core Functions](#core-functions)
   - [get_theory()](#get_theorysubtheoriesnone)
   - [get_examples()](#get_examples)
   - [get_test_examples()](#get_test_examples)
   - [list_subtheories()](#list_subtheories)
   - [get_examples_by_subtheory()](#get_examples_by_subtheorysubtheory_name)
   - [get_examples_by_type()](#get_examples_by_typeexample_type)
   - [get_example_stats()](#get_example_stats)
3. [Classes](#classes)
   - [LogosSemantics](#logossemantics)
   - [LogosProposition](#logosproposition)
   - [LogosModelStructure](#logosmodelstructure)
   - [LogosOperatorRegistry](#logosoperatorregistry)
4. [Operators](#operators)
   - [Extensional Operators](#extensional-operators)
   - [Modal Operators](#modal-operators)
   - [Constitutive Operators](#constitutive-operators)
   - [Counterfactual Operators](#counterfactual-operators)
   - [Relevance Operators](#relevance-operators)
5. [Model Iteration](#model-iteration)
   - [LogosModelIterator](#logosmodeliterator)
   - [iterate_example()](#iterate_exampleexample-max_iterationsnone)
6. [Type Definitions](#type-definitions)
   - [Constants](#constants)
   - [Default Settings](#default-settings)
7. [Examples](#examples)
   - [Basic Model Checking](#basic-model-checking)
   - [Using Specific Subtheories](#using-specific-subtheories)
   - [Working with Propositions](#working-with-propositions)
   - [Model Iteration Example](#model-iteration-example)
   - [Custom Settings](#custom-settings)
8. [Error Handling](#error-handling)
   - [Common Exceptions](#common-exceptions)
   - [Error Examples](#error-examples)
   - [Validation](#validation)
9. [See Also](#see-also)

## Overview

The Logos Theory provides a modular implementation of hyperintensional truthmaker semantics with support for extensional, modal, constitutive, counterfactual, and relevance operators. This API reference documents all public functions, classes, and operators available in the logos theory.

## Core Functions

### `get_theory(subtheories=None)`

Get a logos theory instance with specified subtheories.

**Parameters:**
- `subtheories` (list[str], optional): List of subtheory names to load. Available options:
  - `'extensional'` - Extensional operators
  - `'modal'` - Necessity and possibility operators
  - `'constitutive'` - Identity, ground, essence, and relevance operators
  - `'counterfactual'` - Counterfactual conditional operators
  - `'relevance'` - Content relevance operators (loads from constitutive)
  
  If None, loads default set: ['extensional', 'modal', 'constitutive', 'counterfactual']

**Returns:**
- `dict`: Dictionary containing:
  - `'semantics'`: LogosSemantics class
  - `'proposition'`: LogosProposition class
  - `'model'`: LogosModelStructure class
  - `'operators'`: OperatorCollection with loaded operators

**Example:**
```python
from model_checker.theory_lib.logos import get_theory

# Load all default subtheories
theory = get_theory()

# Load only specific subtheories
theory = get_theory(['extensional', 'modal'])

# Access components
semantics_class = theory['semantics']
operators = theory['operators']
```

### `get_examples()`

Get logos theory example formulas and test cases.

**Returns:**
- `dict`: Mapping of example names to example cases

**Example:**
```python
from model_checker.theory_lib.logos import get_examples

examples = get_examples()
for name, example in examples.items():
    print(f"Example: {name}")
```

### `get_test_examples()`

Get logos theory unit test cases.

**Returns:**
- `dict`: Mapping of test names to test cases

**Example:**
```python
from model_checker.theory_lib.logos import get_test_examples

tests = get_test_examples()
```

### `list_subtheories()`

Get available subtheories with descriptions.

**Returns:**
- `dict`: Dictionary mapping subtheory names to descriptions

**Example:**
```python
from model_checker.theory_lib.logos import list_subtheories

subtheories = list_subtheories()
# {'extensional': 'Extensional operators (¬,∧,∨,→,↔,⊤,⊥)', ...}
```

### `get_examples_by_subtheory(subtheory_name)`

Get examples specific to a subtheory.

**Parameters:**
- `subtheory_name` (str): Name of the subtheory

**Returns:**
- `dict`: Examples from that subtheory

### `get_examples_by_type(example_type)`

Get examples of a specific type (e.g., 'validity', 'invalidity').

**Parameters:**
- `example_type` (str): Type of examples to retrieve

**Returns:**
- `dict`: Examples of the specified type

### `get_example_stats()`

Get statistics about available examples.

**Returns:**
- `dict`: Statistics about example distribution

## Classes

### `LogosSemantics`

Shared semantic framework for all logos subtheories. Provides hyperintensional truthmaker semantics with support for modular operator loading.

**Inheritance:** `SemanticDefaults`

**Key Attributes:**
- `verify`: Z3 function for state verification of atoms
- `falsify`: Z3 function for state falsification of atoms
- `possible`: Z3 function determining if a state is possible
- `main_world`: The designated evaluation world
- `main_point`: Dictionary containing the main evaluation point

**Key Methods:**

#### `__init__(combined_settings=None, operator_registry=None, **kwargs)`
Initialize the semantic framework.

#### `load_subtheories(subtheories=None)`
Load specified subtheories into the semantic framework.

#### `compatible(state_x, state_y)`
Determines if the fusion of two states is possible.

#### `maximal(state_w)`
Determines if a state is maximal with respect to compatibility.

#### `is_world(state_w)`
Determines if a state represents a possible world in the model.

#### `true_at(sentence, eval_point)`
Determines if a sentence is true at a given evaluation point.

#### `false_at(sentence, eval_point)`
Determines if a sentence is false at a given evaluation point.

#### `extended_verify(state, sentence, eval_point)`
Determines if a state verifies a sentence at an evaluation point.

#### `extended_falsify(state, sentence, eval_point)`
Determines if a state falsifies a sentence at an evaluation point.

#### `max_compatible_part(state_x, state_w, state_y)`
Determines if state_x is the maximal part of state_w compatible with state_y.

#### `is_alternative(state_u, state_y, state_w)`
Determines if a state represents an alternative world for counterfactual evaluation.

#### `calculate_alternative_worlds(verifiers, eval_point, model_structure)`
Calculates alternative worlds for counterfactual evaluation.

#### `product(set_A, set_B)`
Compute the set of all pairwise fusions between elements of two sets.

#### `coproduct(set_A, set_B)`
Compute the union of two sets closed under pairwise fusion.

#### `closer_world(world_u, world_v, eval_point)`
Determines if world_u is closer than world_v to the evaluation world.

**Default Settings:**
```python
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 16,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,
    'max_time': 10000,          # Also used for iteration attempts
    'iterate': False,
    'iteration_attempts': 5,
    'expectation': None,
}
```

### `LogosProposition`

Proposition class with modular operator support. Represents propositional content in the logos semantic framework.

**Inheritance:** `PropositionDefaults`

**Key Methods:**

#### `__init__(sentence, model_structure, eval_world='main')`
Initialize a LogosProposition instance.

**Parameters:**
- `sentence`: The sentence whose proposition is being represented
- `model_structure`: The model structure containing semantic definitions
- `eval_world` (str|BitVecRef): The world at which to evaluate the proposition

#### `proposition_constraints(sentence_letter)`
Generates Z3 constraints for a sentence letter based on semantic settings.

#### `find_proposition()`
Computes the verifier and falsifier sets for this proposition.

**Returns:**
- `tuple[set, set]`: (verifiers, falsifiers)

#### `truth_value_at(eval_world)`
Determines the truth value of the proposition at a given world.

#### `print_proposition(eval_point, indent_num, use_colors)`
Print the proposition with its truth value at the given evaluation point.

### `LogosModelStructure`

Model structure with modular operator support. Manages the overall semantic model structure.

**Inheritance:** `ModelDefaults`

**Key Attributes:**
- `main_world`: The main evaluation world
- `z3_main_world`: Z3 model value for main world
- `z3_possible_states`: List of possible states in the model
- `z3_world_states`: List of world states in the model
- `loaded_subtheories`: List of loaded subtheory names

**Key Methods:**

#### `__init__(model_constraints, settings)`
Initialize the model structure.

#### `load_subtheories(subtheories)`
Load specified subtheories into the model.

#### `get_available_operators()`
Get all operators from loaded subtheories.

#### `print_model_info()`
Print information about the loaded model.

#### `print_all(default_settings, example_name, theory_name, output=sys.stdout)`
Print a complete overview of the model structure and evaluation results.

#### `print_to(default_settings, example_name, theory_name, print_constraints=None, output=sys.stdout)`
Print the model details to the specified output stream.

#### `print_model_differences(output=sys.stdout)`
Print differences between this model and the previous one.

### `LogosOperatorRegistry`

Dynamic registry for loading and managing subtheory operators.

**Key Methods:**

#### `__init__()`
Initialize the operator registry.

#### `load_subtheory(name)`
Load a specific subtheory and its operators.

#### `load_subtheories(names)`
Load multiple subtheories.

#### `get_operators()`
Get all loaded operators as an OperatorCollection.

#### `get_loaded_subtheories()`
Get list of currently loaded subtheory names.

#### `get_operator_by_name(operator_name)`
Get a specific operator by name.

#### `list_available_operators()`
List all available operators from loaded subtheories.

#### `get_subtheory_operators(subtheory_name)`
Get operators specific to a subtheory.

#### `validate_operator_compatibility()`
Validate that all loaded operators are compatible.

## Operators

The logos theory provides operators through its modular subtheory system. Below are the operators available in each subtheory:

### Extensional Operators

- **Negation** (`\\neg`): Logical negation
- **Conjunction** (`\\wedge`): Logical AND
- **Disjunction** (`\\vee`): Logical OR
- **Material Implication** (`\\rightarrow`): Material conditional
- **Biconditional** (`\\leftrightarrow`): If and only if
- **Top** (`\\top`): Logical truth
- **Bottom** (`\\bot`): Logical falsehood

### Modal Operators

- **Necessity** (`\\Box`): Modal necessity
- **Possibility** (`\\Diamond`): Modal possibility
- **Counterfactual Necessity** (`\\CFBox`): Counterfactual necessity
- **Counterfactual Possibility** (`\\CFDiamond`): Counterfactual possibility

### Constitutive Operators

**Primitive Operators:**
- **Identity** (`\\equiv`): Hyperintensional identity
- **Ground** (`\\leq`): Grounding relation
- **Essence** (`\\sqsubseteq`): Essential dependence
- **Relevance** (`\\preceq`): Subject-matter relevance

**Defined Operator:**
- **Reduction** (`\\Rightarrow`): Reductive explanation (defined as ground and essence)

### Counterfactual Operators

- **Counterfactual Conditional** (`\\boxright`): Would counterfactual
- **Might Counterfactual** (`\\diamondright`): Might counterfactual

### Relevance Operators

The relevance operator (`\\preceq`) is imported from the constitutive subtheory and explored in depth with specialized examples.

**Example Usage:**
```python
from model_checker.theory_lib.logos import get_theory
from model_checker import parse

# Load theory with specific operators
theory = get_theory(['extensional', 'modal'])
operators = theory['operators']

# Parse formulas using LaTeX notation
formula1 = parse("\\Box p \\rightarrow p")  # Box p implies p
formula2 = parse("p \\wedge q")           # p and q
formula3 = parse("\\neg (p \\vee q)")      # not (p or q)
```

## Model Iteration

### `LogosModelIterator`

Model iterator for the logos theory, providing specialized difference detection and constraint generation.

**Inheritance:** `BaseModelIterator`

**Key Methods:**

#### `_calculate_differences(new_structure, previous_structure)`
Calculate differences between two logos theory model structures.

#### `_create_difference_constraint(previous_models)`
Create a Z3 constraint requiring difference from all previous models.

#### `_create_non_isomorphic_constraint(z3_model)`
Create a constraint that forces structural differences to avoid isomorphism.

### `iterate_example(example, max_iterations=None)`

Iterate a logos theory example to find multiple models.

**Parameters:**
- `example`: An example instance with logos theory
- `max_iterations` (int, optional): Maximum number of models to find

**Returns:**
- `list`: List of model structures with distinct models

**Example:**
```python
from model_checker.theory_lib.logos import get_theory, iterate_example

# Load theory
theory = get_theory()

# Example formula: Modal T Axiom
formula = "\\Box p \\rightarrow p"
# See examples.py for complete implementation

# Model iteration finds multiple satisfying models
# models = iterate_example(example, max_iterations=5)
```

## Type Definitions

### Constants

```python
AVAILABLE_SUBTHEORIES = [
    'extensional',
    'modal', 
    'constitutive',
    'counterfactual',
    'relevance'
]
```

### Default Settings

The logos theory uses these default settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 16,                    # Bit vector size
    'contingent': True,         # Require contingent propositions
    'non_empty': True,          # Require non-empty verifier/falsifier sets
    'non_null': True,           # Prevent null states as verifiers/falsifiers
    'disjoint': True,           # Require disjoint verifier/falsifier sets
    'max_time': 10000,          # Z3 timeout in milliseconds (also used for iteration)
    'iterate': False,           # Enable model iteration
    'iteration_attempts': 5,    # Max attempts per iteration
    'expectation': None,        # Expected validity result
}
```

## Examples

### Basic Model Checking

```python
from model_checker.theory_lib.logos import get_theory

# Load theory with default subtheories
theory = get_theory()

# Access components
semantics_class = theory['semantics']
operators = theory['operators']

# Example formula: Modal T Axiom
formula = "\\Box p \\rightarrow p"
# See examples.py for complete implementation and validity checking
```

### Using Specific Subtheories

```python
# Load only extensional and modal operators
theory = get_theory(['extensional', 'modal'])

# Example formula with limited operators
formula = "p \\wedge \\Box q"
# See examples.py for complete implementation
```

### Working with Propositions

```python
from model_checker import parse
from model_checker.theory_lib.logos import get_theory

# Load theory
theory = get_theory()

# Example sentence: Classical tautology
sentence = parse("p \\vee \\neg p")

# Access proposition class
Proposition = theory['proposition']
# prop = Proposition(sentence, model_structure)
# See examples.py for complete proposition usage
```

### Model Iteration Example

```python
from model_checker.theory_lib.logos import get_theory, iterate_example

# Load extensional subtheory
theory = get_theory(['extensional'])

# Example formula: Disjunction
formula = "p \\vee q"
# See examples.py for complete iteration implementation

# Model iteration finds multiple satisfying models
# models = iterate_example(example, max_iterations=5)
```

### Custom Settings

```python
# Load theory
theory = get_theory()

# Custom settings for model checking
custom_settings = {
    'N': 8,                  # Smaller state space
    'contingent': False,     # Allow non-contingent propositions
    'max_time': 5000,        # 5 second timeout
    'iterate': True,         # Enable iteration
}

# Example formula: Custom evaluation
formula = "\\Box (p \\rightarrow q)"
# See examples.py for complete custom settings usage
```

## Error Handling

### Common Exceptions

- **ValueError**: Raised when invalid subtheory names are provided
- **ImportError**: Raised when a subtheory cannot be loaded
- **Z3Exception**: Raised when Z3 encounters an error during solving
- **TimeoutError**: Raised when model search exceeds max_time

### Error Examples

```python
try:
    # Invalid subtheory name
    theory = get_theory(['invalid_subtheory'])
except ValueError as e:
    print(f"Error: {e}")

try:
    # Load theory for timeout example
    theory = get_theory()
    # Complex formula example
    formula = "\\Box (p \\wedge q) \\rightarrow (\\Box p \\wedge \\Box q)"
    # See examples.py for timeout handling in model checking
except Exception as e:
    print(f"Error during model checking: {e}")
```

### Validation

The logos theory validates:
- Subtheory names before loading
- Operator compatibility when loading multiple subtheories
- State space size (N) is appropriate for the formulas
- Settings are compatible with each other

## See Also

- **[User Guide](USER_GUIDE.md)** - Practical usage guide
- **[Architecture](ARCHITECTURE.md)** - Technical implementation details  
- **[Settings](SETTINGS.md)** - Configuration options
- **[Model Iteration](ITERATE.md)** - Finding multiple models
- **[Documentation Hub](README.md)** - All documentation

---

[← Back to Documentation](README.md) | [Architecture →](ARCHITECTURE.md)