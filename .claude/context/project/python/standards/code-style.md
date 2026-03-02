# Python Code Style Guide

Python coding standards for the ModelChecker project.

## General Principles

From `CLAUDE.md`:

1. **Mandatory Test-Driven Development**: Write tests BEFORE implementation (RED -> GREEN -> REFACTOR)
2. **No Backwards Compatibility**: Clean breaks when improving code
3. **Fail-Fast Philosophy**: Early validation, immediate error reporting

## Import Standards

```python
# Standard library
import os
from pathlib import Path

# Third-party
import z3
from typing import Dict, List, Optional

# Local (prefer relative imports within packages)
from .models import Model
from ..utils import helpers
```

### Import Order

1. Standard library imports
2. Third-party imports
3. Local/package imports

Each group separated by blank line.

### TYPE_CHECKING Imports

Use TYPE_CHECKING for forward references to avoid circular imports:

```python
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .protocols import SemanticsProtocol
    from model_checker.syntactic import Sentence
```

## Naming Conventions

| Type | Convention | Example |
|------|------------|---------|
| Classes | PascalCase | `LogosSemantics` |
| Functions | snake_case | `get_operators` |
| Constants | UPPER_SNAKE | `DEFAULT_SETTINGS` |
| Private | leading underscore | `_helper_function` |
| Protected | single underscore | `_internal_state` |

## Docstrings

Use Google-style docstrings:

```python
def evaluate_sentence(sentence: str, settings: dict) -> bool:
    """
    Evaluate a logical sentence for validity.

    Args:
        sentence: The sentence to evaluate in standard notation.
        settings: Configuration dictionary with N, timeout, etc.

    Returns:
        True if the sentence is valid, False otherwise.

    Raises:
        ParseError: If the sentence cannot be parsed.
        SolverTimeout: If evaluation exceeds max_time.
    """
    pass
```

## Type Hints

Use type hints for all public functions:

```python
from typing import Dict, Any, Optional, List, Tuple

def process_model(
    model: "LogosModel",
    settings: Dict[str, Any],
    timeout: Optional[int] = None
) -> Tuple[bool, List[str]]:
    """Process model and return result with messages."""
    pass
```

## Class Structure

```python
class MySemantics(SemanticDefaults):
    """Brief description."""

    # Class constants first
    DEFAULT_SETTINGS = {'N': 16}

    # __init__ next
    def __init__(self, settings: Dict[str, Any]):
        super().__init__(settings)
        self._initialize()

    # Public methods
    def evaluate(self, sentence):
        """Public API method."""
        pass

    # Private/helper methods last
    def _initialize(self):
        """Private initialization helper."""
        pass
```

## Error Handling

Use custom exceptions from `theory_lib/errors.py`:

```python
from model_checker.theory_lib.errors import TheoryError

def validate_input(value):
    if not valid(value):
        raise TheoryError(f"Invalid input: {value}")
```

Prefer specific exceptions over generic ones.

## Test Structure

Tests mirror source structure:

```
theory_lib/logos/
├── semantic.py
└── tests/
    ├── unit/
    │   └── test_semantic_methods.py
    └── integration/
        └── test_iterate.py
```

Test file naming: `test_{module}.py`

```python
# test_semantic_methods.py
import pytest
from model_checker.theory_lib.logos.semantic import LogosSemantics


class TestLogosSemantics:
    """Test suite for LogosSemantics."""

    def test_initialization_with_defaults(self):
        """Test that semantics initializes with default settings."""
        semantics = LogosSemantics({}, "test")
        assert semantics.name == "test"

    def test_evaluation_simple_sentence(self):
        """Test evaluation of simple atomic sentence."""
        pass
```

## Running Tests

```bash
# All tests
PYTHONPATH=code/src pytest code/tests/ -v

# Specific theory
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v

# With coverage
pytest --cov=model_checker --cov-report=term-missing
```

## Line Length and Formatting

- Maximum line length: 100 characters
- Use 4 spaces for indentation (not tabs)
- Blank line between top-level definitions
- Two blank lines between classes

## Z3-Specific Patterns

```python
import z3

# Use explicit types
state = z3.BitVec('state', 16)  # Not just BitVec('state')

# Simplify before solving
constraint = z3.simplify(complex_constraint)

# Handle solver results explicitly
result = solver.check()
if result == z3.sat:
    model = solver.model()
elif result == z3.unsat:
    pass  # Handle unsatisfiable
else:
    pass  # Handle unknown (timeout)
```

## Documentation

- All public APIs must have docstrings
- Include usage examples for complex functions
- Reference related functions/classes

## Quality Targets

From `CLAUDE.md`:

- Type coverage: >90%
- Cyclomatic complexity: <10
- Test coverage: >85% overall
