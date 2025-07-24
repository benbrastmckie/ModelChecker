# Imposition Theory

The imposition theory implements Kit Fine's imposition semantics for counterfactual reasoning. This theory provides an alternative approach to counterfactuals through the imposition operation, developed as a separate theory for comparison with the default theory's hyperintensional semantics.

## Overview

The imposition theory extends logos semantics with Fine's distinctive counterfactual framework based on the imposition operation. This enables sophisticated reasoning about alternative worlds and counterfactual scenarios through a different semantic approach than the default theory.

## Contents

This package includes the following components:
  - `README.md` - This documentation file
  - `__init__.py` - Public API and theory registration
  - `examples.py` - Test examples for counterfactual reasoning
  - `operators.py` - Imposition and counterfactual operators
  - `semantic.py` - Core imposition semantics implementation
  - `docs/` - Additional documentation
    - `SETTINGS.md` - Complete settings reference
  
## Settings

The imposition theory supports various settings to control model generation and semantic constraints. For comprehensive documentation of all available settings, see **[docs/SETTINGS.md](docs/SETTINGS.md)**.

Key settings include:
- **N**: Number of atomic states (default: 3)
- **contingent**: Require contingent propositions (default: False)
- **non_empty**: Prevent empty verifier/falsifier sets (default: False)
- **max_time**: Solver timeout in seconds (default: 1)

For general settings that apply across all theories, see the [main settings documentation](../../settings/README.md).

## Accessing Examples

You can access examples from this theory using the parent module's functions:

```python
from model_checker.theory_lib import get_examples, get_test_examples, get_semantic_theories

# Get all examples from the imposition theory
examples = get_examples('imposition')

# Access a specific example
example = examples['IM_CM_1'] # Replace with an actual example name from this theory
premises, conclusions, settings = example

# Get test examples for automated testing
test_examples = get_test_examples('imposition')

# Get semantic theory implementations
theories = get_semantic_theories('imposition')
```

## Basic Usage

```python
from model_checker import BuildExample, get_theory

# Load the imposition theory
theory = get_theory("imposition")

# Create a model
model = BuildExample("imposition_example", theory,
    premises=['A \\imposition B'],
    conclusions=['A \\boxright B'],
    settings={'N': 3}
)

# Check validity
result = model.check_formula()
```

## Comparison with Default Theory

While both theories handle counterfactuals, they differ in approach:
- **Default theory**: Uses alternative world semantics
- **Imposition theory**: Uses Fine's imposition operation

This allows for direct comparison of the two semantic frameworks.

## Testing

Run `pytest` from the project directory to evaluate the examples included in `examples.py`:

```bash
# Run all imposition tests
python test_theories.py --theories imposition

# Run specific test
python test_theories.py --theories imposition --examples
```

