# Code Organization Standards

[← README Standards](README_STANDARDS.md) | [Back to Maintenance](README.md) | [Testing Standards →](TESTING_STANDARDS.md)

## Overview

This document defines code organization standards for the ModelChecker codebase, including file naming, import organization, and naming conventions.

## File Naming Conventions

- **Python files**: Use lowercase with underscores: `my_module.py`
- **Test files**: Prefix with `test_`: `test_semantic.py`
- **Documentation**: Use UPPERCASE.md for standard docs: `README.md`, `API_REFERENCE.md`
- **Notebooks**: Use descriptive names with underscores: `modal_logic_tutorial.ipynb`

## Import Organization

Organize imports in three groups separated by blank lines:

```python
# Standard library imports
import os
import sys
from typing import Dict, List, Optional

# Third-party imports
import z3
import numpy as np

# Local imports
from model_checker.base import BaseClass
from .local_module import LocalClass
```

Within each group, sort imports alphabetically.

## Naming Conventions

### Classes
Use PascalCase for all class names:
```python
class BimodalSemantics:
    pass

class LogosOperatorRegistry:
    pass
```

### Functions and Methods
Use snake_case for all functions:
```python
def get_theory():
    pass

def check_validity(premises, conclusions):
    pass
```

### Constants
Use UPPER_SNAKE_CASE for module-level constants:
```python
DEFAULT_SETTINGS = {
    'N': 3,
    'max_time': 10,
}

MAX_ITERATIONS = 100
```

### Private Members
Use leading underscore for private methods and attributes:
```python
class TheoryClass:
    def __init__(self):
        self._internal_state = {}
    
    def _internal_method(self):
        pass
```

## Module Structure

Each module should follow this general structure:

```python
"""
Module docstring describing purpose and usage.
"""

# Imports (organized as above)

# Constants
DEFAULT_VALUE = 42

# Classes
class MainClass:
    """Class docstring."""
    pass

# Functions
def utility_function():
    """Function docstring."""
    pass

# Module initialization (if needed)
if __name__ == "__main__":
    main()
```

## Theory Module Organization

Theory modules must follow this structure:

```
theory_name/
├── __init__.py         # Public API exports
├── semantic.py         # Core semantic classes
├── operators.py        # Operator definitions
├── examples.py         # Example formulas
├── iterate.py          # Model iteration (if applicable)
├── settings.py         # Default settings
└── utils.py           # Helper functions
```

### __init__.py Requirements

Export the public API clearly:

```python
"""Theory public API."""

from .semantic import TheorySemantics, TheoryProposition, TheoryStructure
from .operators import theory_operators, get_operators
from .examples import unit_tests, example_range

__all__ = [
    'TheorySemantics',
    'TheoryProposition', 
    'TheoryStructure',
    'theory_operators',
    'get_operators',
    'unit_tests',
    'example_range',
]
```

## Docstring Standards

### Module Docstrings
```python
"""
Brief one-line summary.

Longer description providing context and usage information.
This module implements...

Example:
    Basic usage example::
    
        >>> from module import function
        >>> result = function(arg)
"""
```

### Class Docstrings
```python
class ExampleClass:
    """
    Brief one-line summary.
    
    Longer description of the class purpose and behavior.
    
    Attributes:
        attribute1: Description of attribute1
        attribute2: Description of attribute2
    
    Example:
        >>> obj = ExampleClass()
        >>> obj.method()
    """
```

### Function Docstrings
```python
def example_function(param1: str, param2: int = 0) -> bool:
    """
    Brief one-line summary.
    
    Longer description if needed.
    
    Args:
        param1: Description of param1
        param2: Description of param2 (default: 0)
    
    Returns:
        Description of return value
        
    Raises:
        ValueError: When param1 is invalid
        
    Example:
        >>> example_function("test", 42)
        True
    """
```

## Type Annotations

Use type hints for all public functions and methods:

```python
from typing import Dict, List, Optional, Tuple, Union

def process_formulas(
    premises: List[str],
    conclusions: List[str],
    settings: Optional[Dict[str, Any]] = None
) -> Tuple[bool, Optional[str]]:
    """Process logical formulas."""
    pass
```

## Error Messages

Provide helpful, specific error messages:

```python
# GOOD
if not os.path.exists(file_path):
    raise FileNotFoundError(
        f"Example file '{file_path}' not found. "
        f"Check that the file exists and the path is correct."
    )

# BAD
if not os.path.exists(file_path):
    raise FileNotFoundError("File not found")
```

## Code Comments

- Use comments sparingly - code should be self-documenting
- Explain WHY, not WHAT
- Keep comments up to date with code changes
- Use complete sentences with proper capitalization

```python
# Calculate bit vector size based on number of atomic propositions
# This ensures sufficient bits for all possible state combinations
bit_size = 2 ** N
```

---

[← README Standards](README_STANDARDS.md) | [Back to Maintenance](README.md) | [Testing Standards →](TESTING_STANDARDS.md)