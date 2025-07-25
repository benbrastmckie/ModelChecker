# Logos Theory API Reference

## Overview

The Logos Theory provides a modular implementation of hyperintensional truthmaker semantics with support for extensional, modal, constitutive, counterfactual, and relevance operators. This API reference documents all public functions, classes, and operators available in the logos theory.

## Core Functions

### `get_theory(subtheories=None)`

Get a logos theory instance with specified subtheories.

**Parameters:**
- `subtheories` (list[str], optional): List of subtheory names to load. Available options:
  - `'extensional'` - Truth-functional operators
  - `'modal'` - Necessity and possibility operators
  - `'constitutive'` - Ground, essence, and identity operators
  - `'counterfactual'` - Counterfactual conditional operators
  - `'relevance'` - Content-sensitive relevance operators
  
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
# {'extensional': 'Truth-functional operators (¬,∧,∨,→,↔,⊤,⊥)', ...}
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
Determines if a state represents an alternative world.

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
    'max_time': 10000,
    'iterate': False,
    'iteration_timeout': 1.0,
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

- **Identity** (`\\equiv`): Hyperintensional identity
- **Ground** (`\\leq`): Grounding relation
- **Essence** (`\\sqsubseteq`): Essential dependence
- **Relevance** (`\\preceq`): Relevance relation
- **Reduction** (`\\Rightarrow`): Reductive explanation

### Counterfactual Operators

- **Counterfactual Conditional** (`\\boxright`): Would counterfactual
- **Might Counterfactual** (`\\diamondright`): Might counterfactual

### Relevance Operators

Content-sensitive operators that capture relevance relations between propositions.

**Example Usage:**
```python
from model_checker.theory_lib.logos import get_theory
from model_checker import parse

# Load theory with specific operators
theory = get_theory(['extensional', 'modal'])
operators = theory['operators']

# Parse formulas using LaTeX notation
formula1 = parse("\\Box p \\to p")  # Box p implies p
formula2 = parse("p \\wedge q")     # p and q
formula3 = parse("\\neg (p \\vee q)")  # not (p or q)
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
- `example`: A BuildExample instance with logos theory
- `max_iterations` (int, optional): Maximum number of models to find

**Returns:**
- `list`: List of model structures with distinct models

**Example:**
```python
from model_checker import BuildExample
from model_checker.theory_lib.logos import get_theory, iterate_example

# Create example
theory = get_theory()
example = BuildExample("my_example", theory)
example.add_constraint("\\Box p \\to p")

# Find multiple models
models = iterate_example(example, max_iterations=5)
print(f"Found {len(models)} distinct models")
```

## Type Definitions and Constants

### `AVAILABLE_SUBTHEORIES`

List of all available subtheory names:
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
    'max_time': 10000,          # Z3 timeout in milliseconds
    'iterate': False,           # Enable model iteration
    'iteration_timeout': 1.0,   # Timeout per iteration attempt
    'iteration_attempts': 5,    # Max attempts per iteration
    'expectation': None,        # Expected validity result
}
```

## Examples

### Basic Model Checking

```python
from model_checker import BuildExample
from model_checker.theory_lib.logos import get_theory

# Create theory with default subtheories
theory = get_theory()

# Build a model
model = BuildExample("modal_example", theory)
model.add_formula("\\Box p \\to p")  # T axiom

# Check validity
if model.check_validity():
    print("Formula is valid")
else:
    print("Formula is invalid")
    model.print_countermodel()
```

### Using Specific Subtheories

```python
# Load only extensional and modal operators
theory = get_theory(['extensional', 'modal'])

# Create example with limited operators
model = BuildExample("limited_example", theory)
model.add_formula("p \\wedge \\Box q")
```

### Working with Propositions

```python
from model_checker import parse
from model_checker.theory_lib.logos import get_theory

theory = get_theory()
model = BuildExample("prop_example", theory)

# Parse a sentence
sentence = parse("p \\vee \\neg p")

# Create proposition
prop = theory['proposition'](sentence, model.model_structure)

# Check verifiers and falsifiers
print(f"Verifiers: {prop.verifiers}")
print(f"Falsifiers: {prop.falsifiers}")

# Check truth at main world
truth_value = prop.truth_value_at(model.model_structure.main_world)
print(f"True at main world: {truth_value}")
```

### Model Iteration

```python
from model_checker.theory_lib.logos import get_theory, iterate_example

theory = get_theory(['extensional'])
model = BuildExample("iterate_example", theory)
model.add_formula("p \\vee q")

# Find up to 5 models
models = iterate_example(model, max_iterations=5)

for i, m in enumerate(models):
    print(f"\nModel {i+1}:")
    m.print_evaluation()
```

### Custom Settings

```python
# Create theory with custom settings
custom_settings = {
    'N': 8,                  # Smaller state space
    'contingent': False,     # Allow non-contingent propositions
    'max_time': 5000,        # 5 second timeout
    'iterate': True,         # Enable iteration
}

theory = get_theory()
model = BuildExample("custom_example", theory, **custom_settings)
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
    # Timeout handling
    model = BuildExample("complex", theory, max_time=100)
    model.add_formula("very_complex_formula")
    model.check_validity()
except TimeoutError:
    print("Model search timed out")
```

### Validation

The logos theory validates:
- Subtheory names before loading
- Operator compatibility when loading multiple subtheories
- State space size (N) is appropriate for the formulas
- Settings are compatible with each other

## See Also

- [User Guide](USER_GUIDE.md) - Practical usage guide
- [Architecture](ARCHITECTURE.md) - Technical implementation details
- [Settings](SETTINGS.md) - Configuration options
- [Model Iteration](ITERATE.md) - Finding multiple models
- [Documentation Hub](README.md) - All documentation