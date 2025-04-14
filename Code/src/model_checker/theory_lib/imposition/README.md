# Model-Checker Instructions

> TODO: expand these instructions

## Contents

This package includes the following templates:
  - `README.md` to document usage and changes.
  - `__init__.py` to expose definitions.
  - `examples.py` defines a number of examples to test.
  - `operators.py` defines the primitive and derived operators.
  - `semantic.py` defines the default semantics for the operators included.
  
### Accessing Examples

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

> TO BE CONTINUED...

## Testing

Run `pytest` from the project directory to quickly evaluate whether the examples included in `examples.py` return the expected result.

