# Example Modules for Default Theory

This directory contains organized collections of logical examples for the default theory implementation, separated by operator type. Each module is structured to be independently runnable while also providing examples for the test suite.

## Table of Contents

- [Module Organization](#module-organization)
- [Example Format](#example-format)
- [Running Examples](#running-examples)
- [Example Categories](#example-categories)
- [Example Collections](#example-collections)
- [Testing with Examples](#testing-with-examples)
- [Adding New Examples](#adding-new-examples)
- [Jupyter Notebooks](#jupyter-notebooks)

## Module Organization

The examples are organized into the following modules:

| Module | Description | Example Prefix |
|--------|-------------|---------------|
| `counterfactual.py` | Counterfactual conditionals | CF_CM_*, CF_TH_* |
| `modal.py` | Modal operators (necessity/possibility) | ML_CM_*, ML_TH_*, ML_DEF_* |
| `constitutive.py` | Constitutive operators (ground/essence/identity) | CL_CM_*, CL_TH_* |
| `extensional.py` | Extensional operators (conjunction/disjunction) | EL_CM_*, EL_TH_* |
| `relevance.py` | Relevance operators | RL_CM_*, RL_TH_* |

Each module follows a consistent naming convention:
- CM: Countermodel examples (invalid inferences)
- TH: Theorem examples (valid inferences)
- DEF: Examples testing defined operators

## Example Format

Each example is structured as a list with three elements:

```python
example_name = [
    premises,           # List of formula strings that must be true
    conclusions,        # List of formula strings to check
    settings,           # Dictionary of model settings
]
```

An inference is invalid if all premises can be true while at least one conclusion is false.

## Running Examples

You can run examples in several ways:

### 1. Individual Module Execution

Each module can be run independently:

```bash
# Direct execution
model-checker path/to/counterfactual.py

# Development mode
./dev_cli.py path/to/counterfactual.py

# With command line flags
model-checker -p -z path/to/counterfactual.py
```

### 2. Combined Execution

The `__init__.py` file can execute examples from multiple modules:

```bash
model-checker path/to/examples/__init__.py
```

### 3. Programmatic Access

Import examples for use in your code:

```python
# Import collections
from model_checker.theory_lib.default.examples import (
    counterfactual_examples,
    modal_examples
)

# Access specific examples
example = counterfactual_examples["CF_CM_1"]
```

## Example Categories

### Counterfactual Examples (`counterfactual.py`)

Tests for counterfactual conditionals, including:

- Antecedent strengthening
- Transitivity
- Contraposition
- Sobel sequences

### Modal Examples (`modal.py`)

Tests for necessity and possibility operators, including:

- Distribution over disjunction
- K, T, 4, B, and 5 axioms
- Defined vs. primitive operator equivalence

### Constitutive Examples (`constitutive.py`)

Tests for ground, essence, and identity operators, including:

- Relationships between ground and essence
- Absorption and distribution properties
- Negation transparency
- Identity reduction

### Extensional Examples (`extensional.py`)

Tests for basic truth-functional operators, including:

- Modus ponens
- Distribution
- De Morgan's laws
- Contraposition

### Relevance Examples (`relevance.py`)

Tests for relevance operators, including:

- Relationships with ground/essence
- Distribution properties
- Content-based implications

## Example Collections

Each module provides several collections:

1. **Category-Specific Collections**
   - `counterfactual_cm_examples`: Only counterfactual countermodels
   - `counterfactual_th_examples`: Only counterfactual theorems

2. **Combined Collections**
   - `counterfactual_examples`: All counterfactual examples
   - `modal_examples`: All modal examples
   - etc.

3. **Consolidated Collections** (in `__init__.py`)
   - `test_example_range`: All examples for testing
   - `example_range`: Examples to run by default

## Testing with Examples

The module provides examples for unit testing:

```python
# Import test examples
from model_checker.theory_lib import get_test_examples

# Get all test examples
examples = get_test_examples("default")

# Get a specific test example
example = examples["CF_CM_1"]
```

## Adding New Examples

To add a new example:

1. Determine the appropriate module (based on operators used)
2. Follow the naming convention (e.g., `CF_CM_22` for a new counterfactual countermodel)
3. Create the example with premises, conclusions, and settings:

```python
# New example
NEW_CM_1_premises = ['A']
NEW_CM_1_conclusions = ['\\neg A']
NEW_CM_1_settings = {
    'N': 3,
    'contingent': True,
    'max_time': 1,
}
NEW_CM_1_example = [
    NEW_CM_1_premises,
    NEW_CM_1_conclusions,
    NEW_CM_1_settings,
]
```

4. Add to the appropriate collection:

```python
# Update collections
new_cm_examples = {
    "NEW_CM_1": NEW_CM_1_example,
    # other examples...
}

# Combined collection
new_examples = {**new_cm_examples, **new_th_examples}
```

5. To run locally, add to the `example_range`:

```python
example_range = {
    "NEW_CM_1": NEW_CM_1_example,
    # uncomment other examples as needed
}
```

## Jupyter Notebooks

Interactive Jupyter notebooks are available for each example category in the [notebooks](../notebooks/) directory. These notebooks provide a more interactive way to explore the examples and visualize the model structures.

| Example Module | Corresponding Notebook |
|----------------|------------------------|
| `counterfactual.py` | [counterfactual.ipynb](../notebooks/counterfactual.ipynb) |
| `constitutive.py` | [constitutive.ipynb](../notebooks/constitutive.ipynb) |
| `modal.py` | [modal.ipynb](../notebooks/modal.ipynb) |
| `extensional.py` | [extensional.ipynb](../notebooks/extensional.ipynb) |
| `relevance.py` | [relevance.ipynb](../notebooks/relevance.ipynb) |

For detailed documentation on the notebooks, see the [notebooks README](../notebooks/README.md).