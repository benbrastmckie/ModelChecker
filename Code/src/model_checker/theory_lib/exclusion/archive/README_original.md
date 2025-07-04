# Exclusion Semantics Implementation

## Table of Contents

- [Overview](#overview)
  - [Package Contents](#package-contents)
- [Basic Usage](#basic-usage)
  - [Settings](#settings)
  - [Example Structure](#example-structure)
  - [Running Examples](#running-examples)
    - [1. From the Command Line](#1-from-the-command-line)
    - [2. In VSCodium/VSCode](#2-in-vscodiumvscode)
    - [3. In Development Mode](#3-in-development-mode)
    - [4. Using the API](#4-using-the-api)
  - [Theory Configuration](#theory-configuration)
- [Key Classes](#key-classes)
  - [ExclusionSemantics](#exclusionsemantics)
  - [UnilateralProposition](#unilateralproposition)
  - [ExclusionStructure](#exclusionstructure)
- [Exclusion Language](#exclusion-language)
- [Model Iteration](#model-iteration)
  - [Iteration Framework](#iteration-framework)
  - [Using Iteration](#using-iteration)
  - [Understanding Model Differences](#understanding-model-differences)
- [Testing](#testing)
- [Basic Architecture](#basic-architecture)

## Overview

This document provides an overview of the package contents for the _exclusion semantics_ defended by [Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html).
The exclusion semantics uses a unilateral framework with an exclusion operator to define negation, providing a means to evaluate logical relationships in a language with special operators.

### Package Contents

The _exclusion semantics_ includes the following modules:

- `README.md`: Documentation of usage and implementation details
- `__init__.py`: Exposes definitions to be imported elsewhere
- `examples.py`: Defines examples to test the semantics
- `semantic.py`: Defines the exclusion semantics for the operators
- `operators.py`: Defines the primitive and derived operators
- `iterate.py`: Implements model iteration functionality

## Basic Usage

The exclusion theory provides a unilateral framework with an exclusion operator that serves as a negation-like operator. This section explains how to use the theory's main components and run examples.

### Settings

The exclusion theory supports the following configurable settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # Core settings used by all theories
    'N': 3,                   # Number of atomic states
    'max_time': 1,            # Maximum solver time
    
    # Exclusion-specific settings
    'possible': False,        # Whether states must be possible
    'contingent': False,      # Whether propositions must be contingent
    'disjoint': False,        # Whether propositions must have disjoint subject matters
    'non_empty': False,       # Whether propositions must have non-empty verifier/falsifier sets
    'non_null': False,        # Whether null states can be verifiers/falsifiers
    'fusion_closure': False,  # Whether to enforce fusion closure
    'iterate': 1,             # Number of models to find
    'expectation': True,      # Expected result for testing
}
```

The exclusion theory defines several settings not found in other theories:
1. **possible**: Controls whether states must be possible
2. **fusion_closure**: Controls whether fusion closure is enforced
3. **non_empty**: Controls whether propositions must have non-empty verifier sets
4. **non_null**: Controls whether null states can be verifiers

### Example Structure

Each example is structured as a list containing three elements:

```python
[premises, conclusions, settings]
```

Where:
- `premises`: List of formulas that must be true in the model
- `conclusions`: List of formulas to check (invalid if all premises are true and at least one conclusion is false)
- `settings`: Dictionary of settings for this example

Here's a complete example definition:

```python
# DOUBLE NEGATION ELIMINATION IDENTITY
EX_CM_1_premises = []
EX_CM_1_conclusions = ['(A \\uniequiv \\exclude \\exclude A)']
EX_CM_1_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 1,
    'expectation': True,
}
EX_CM_1_example = [
    EX_CM_1_premises,
    EX_CM_1_conclusions,
    EX_CM_1_settings,
]
```

### Running Examples

You can run examples in several ways:

#### 1. From the Command Line

```bash
# Run the default example from examples.py
model-checker path/to/examples.py

# Run with constraints printed 
model-checker -p path/to/examples.py

# Run with Z3 output
model-checker -z path/to/examples.py

# Run with fusion closure enabled
model-checker -f path/to/examples.py
```

#### 2. In VSCodium/VSCode

1. Open the `examples.py` file in VSCodium/VSCode
2. Use one of these methods:
   - Click the "Run Python File" play button in the top-right corner
   - Right-click in the editor and select "Run Python File in Terminal"
   - Use keyboard shortcut (Shift+Enter) to run selected lines

#### 3. In Development Mode

For development purposes, you can use the `dev_cli.py` script from the project root directory:

```bash
# Run the default example from examples.py
./dev_cli.py path/to/examples.py

# Run with constraints printed 
./dev_cli.py -p path/to/examples.py

# Run with Z3 output
./dev_cli.py -z path/to/examples.py

# Run with fusion closure enabled
./dev_cli.py -f path/to/examples.py
```

#### 4. Using the API

The exclusion theory exposes a clean API:

```python
from model_checker.theory_lib.exclusion import (
    ExclusionSemantics, UnilateralProposition, ExclusionStructure, exclusion_operators
)
from model_checker import ModelConstraints
from model_checker.theory_lib import get_examples

# Get examples
examples = get_examples('exclusion')
example_data = examples['EX_CM_1']
premises, conclusions, settings = example_data

# Create semantic structure
semantics = ExclusionSemantics(settings)
model_constraints = ModelConstraints(semantics, exclusion_operators)
model = ExclusionStructure(model_constraints, settings)

# Check a formula
prop = UnilateralProposition("\\exclude A", model)
is_true = prop.truth_value_at(model.main_world)
```

### Theory Configuration

The exclusion theory is defined by combining several components:

```python
exclusion_theory = {
    "semantics": ExclusionSemantics,
    "proposition": UnilateralProposition,
    "model": ExclusionStructure,
    "operators": exclusion_operators,
}

# Define which theories to use when running examples
semantic_theories = {
    "ChampollionBernard": exclusion_theory,
    # Compare with default theory if desired
    # "Brast-McKie": default_theory,
}
```

## Key Classes

The exclusion theory is built around three main classes:

### ExclusionSemantics

The `ExclusionSemantics` class defines the core semantic model for exclusion logic, including:

- **Primitive relations**: Unilateral verification and exclusion relations between states
- **Frame constraints**: Rules that define valid model structures
- **Truth conditions**: How to evaluate atomic propositions in unilateral semantics

The `ExclusionSemantics` class inherits from the `ModelDefaults` class and provides the foundation for unilateral truthmaker semantics with an exclusion operator.

### UnilateralProposition

The `UnilateralProposition` class handles the interpretation of sentences in the unilateral framework:

- **Verification**: Computes which states verify a proposition
- **Exclusion**: Determines which states are excluded by a proposition
- **Truth evaluation**: Checks truth values at specific world states
- **Proposition display**: Visualizes propositions in the model

This class is particularly important as it implements the unilateral approach where propositions have verifiers but not falsifiers, with negation handled through the exclusion relation.

### ExclusionStructure

The `ExclusionStructure` class manages the model structure and provides:

- **State space construction**: Creates the world states and their relationships
- **Exclusion relation management**: Tracks which states exclude which other states
- **Model evaluation**: Provides methods to evaluate formulas in the model
- **Visualization**: Methods to display the resulting model structure

## Exclusion Language

The exclusion theory implements a special set of operators for unilateral semantics:

1. **Exclusion Operator** (`\\exclude`): The fundamental operator that represents state exclusion
2. **Unilateral Conjunction** (`\\uniwedge`): Conjunction for the unilateral framework
3. **Unilateral Disjunction** (`\\univee`): Disjunction for the unilateral framework
4. **Unilateral Equivalence** (`\\uniequiv`): Equivalence for the unilateral framework

The unilateral operators differ from their bilateral counterparts in that they operate within a framework where propositions only have verifiers, not falsifiers, with negation handled via exclusion.

## Model Iteration

The exclusion theory includes a powerful model iteration system through the `ExclusionModelIterator` class defined in `iterate.py`. This feature allows you to find multiple distinct semantic models that satisfy the same logical constraints.

### Iteration Framework

The model iteration system is designed specifically for exclusion theory and operates based on:

1. **Exclusion-Specific Difference Detection**: Identifies meaningful differences between models in terms of:
   - World state changes (added or removed worlds)
   - Possible state changes (states that become possible/impossible)
   - Changes in verification of sentence letters (unilateral verification)
   - Changes in exclusion relationships between states

2. **Exclusion Theory Constraints**: Generates Z3 constraints to force the next model to differ from previous ones by requiring at least one change in:
   - Verification of atomic propositions
   - Exclusion relationships between states
   - Possible state or world status

3. **Isomorphism Escape Strategies**: When the solver finds models that are too similar, increasingly stronger constraints are applied:
   - First attempt: Target significantly different world counts or verification patterns
   - Later attempts: Force extreme properties like minimal worlds, total exclusion flips, etc.

### Using Iteration

You can enable model iteration in two ways:

1. **Via Example Settings**:

```python
EX_CM_settings = {
    'N': 3,
    'max_time': 1,
    'iterate': 3,               # Find up to 3 models
    'iteration_timeout': 1.0,   # Set timeout per iteration
    'iteration_attempts': 5     # Number of attempts for difficult cases
}
```

2. **Programmatically**:

```python
from model_checker.theory_lib.exclusion.iterate import iterate_example

# Create a BuildExample instance first
models = iterate_example(example, max_iterations=3)
```

### Understanding Model Differences

When in iteration mode, the system will display differences between successive models:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + 110 (world)
  - 011 (world)

Possible State Changes:
  + 100
  - 001

Proposition Changes:
  A:
    Verifiers: + {100}
    Verifiers: - {001}

Exclusion Relationship Changes:
  100,010: now excludes
  001,110: no longer excludes
```

In exclusion theory, the differences highlight changes in the exclusion relationship between states, which is central to the unilateral semantic framework.

## Testing

You can run tests for the exclusion theory in several ways:

```bash
# Run all exclusion theory tests
pytest src/model_checker/theory_lib/exclusion/tests/

# Run tests with more detail
pytest -v src/model_checker/theory_lib/exclusion/tests/

# Run a specific test file
pytest src/model_checker/theory_lib/exclusion/tests/test_exclusion.py
```

The test suite verifies that the exclusion semantics correctly implements the logical properties of the unilateral framework with the exclusion operator.

## Advanced Features

The exclusion theory offers several advanced features beyond basic model checking:

### Theory Comparison

You can compare the exclusion theory with the default theory by configuring both in your semantic_theories:

```python
from model_checker.theory_lib.default import (
    Semantics, Proposition, ModelStructure, default_operators
)

# Define the translation dictionary
default_dictionary = {
    "\\exclude": "\\neg",
    "\\uniwedge": "\\wedge",
    "\\univee": "\\vee",
    "\\uniequiv": "\\equiv",
}

# Configure the default theory
default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": default_operators,
    "dictionary": default_dictionary,
}

# Configure both theories for comparison
semantic_theories = {
    "ChampollionBernard": exclusion_theory,
    "Brast-McKie": default_theory,
}
```

This allows you to directly compare how the unilateral exclusion semantics differs from bilateral semantics for the same logical examples.

### Exclusion-Specific Characteristics

The exclusion theory has several unique characteristics:

1. **Unilateral Verification**: Unlike bilateral theories which track both verifiers and falsifiers, exclusion theory only tracks verifiers, with falsehood handled through the exclusion relation.

2. **Exclusion Relations**: The system tracks the primitive exclusion relationship between states, which serves as the foundation for negation-like behavior.

3. **Restricted Fusion Closure**: When enabled with fusion_closure=True, the theory maintains fusion closure of compatible states, providing stronger semantic properties.

### Performance Considerations

- The exclusion theory can sometimes run more efficiently than bilateral semantics for certain classes of problems
- For complex problems, consider:
  - Increasing `max_time` for more complex formulas
  - Reducing `N` (number of atomic states) to decrease the search space
  - Using `fusion_closure=True` to restrict the model space (may speed up some queries)
- The `-p` (print constraints) flag can be helpful for understanding why certain models aren't being found

## References

For more information on the exclusion semantics:

- The original paper by [Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html)
- The test suite in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/tests/`
- The full ModelChecker documentation in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/README.md`
