# Theory Library Patterns

Standard file structure and conventions for semantic theories in ModelChecker.

## Directory Structure

Each theory in `theory_lib/` follows this structure:

```
theory_lib/{theory_name}/
├── __init__.py          # Package exports
├── semantic.py          # Main semantics class (or semantic/ directory)
├── operators.py         # Operator definitions
├── examples.py          # Example definitions (get_examples function)
├── iterate.py           # Model iteration logic (optional)
├── protocols.py         # Type protocols (optional)
└── tests/
    ├── __init__.py
    ├── conftest.py
    ├── unit/            # Unit tests
    └── integration/     # Integration tests
```

## Subtheory Structure

Complex theories like logos use subtheories:

```
theory_lib/logos/
├── semantic.py          # Shared LogosSemantics
├── operators.py         # Core operators
├── examples.py
└── subtheories/
    ├── __init__.py
    ├── modal/
    │   ├── __init__.py
    │   ├── operators.py
    │   └── examples.py
    ├── extensional/
    ├── constitutive/
    ├── counterfactual/
    └── relevance/
```

## semantic.py Pattern

The main semantics class inherits from SemanticDefaults:

```python
"""
Semantic framework for {theory_name} theory.
"""

from typing import Dict, Any, Optional, TYPE_CHECKING
import z3

from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults
from model_checker.utils import ForAll, Exists

if TYPE_CHECKING:
    from model_checker.syntactic import Sentence


class {Theory}Semantics(SemanticDefaults):
    """
    Semantic framework for {theory_name}.
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'max_time': 10,
        'iterate': False,
        'expectation': None,
    }

    def __init__(self, settings: Dict[str, Any], name: str = "{theory}"):
        super().__init__(settings, name)
        self._initialize_components()

    def _initialize_components(self):
        """Initialize theory-specific components."""
        pass


class {Theory}Proposition(PropositionDefaults):
    """Proposition handling for {theory_name}."""

    def __init__(self, semantics, sentence_letter, model, ...):
        super().__init__(semantics, sentence_letter, model, ...)


class {Theory}Model(ModelDefaults):
    """Model structure for {theory_name}."""

    def __init__(self, semantics, settings):
        super().__init__(semantics, settings)
```

## operators.py Pattern

Operators are registered via `get_operators()` function:

```python
"""
Operator definitions for {theory_name} theory.
"""

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .semantic import {Theory}Semantics


def get_operators(semantics: "{Theory}Semantics") -> dict:
    """
    Return operator definitions for this theory.

    Args:
        semantics: The semantics instance to bind operators to

    Returns:
        Dictionary mapping operator names to handler functions
    """
    return {
        'not': lambda s, args: _handle_not(semantics, s, args),
        'and': lambda s, args: _handle_and(semantics, s, args),
        'or': lambda s, args: _handle_or(semantics, s, args),
        # ... more operators
    }


def _handle_not(semantics, sentence, args):
    """Handle negation operator."""
    pass


def _handle_and(semantics, sentence, args):
    """Handle conjunction operator."""
    pass
```

## examples.py Pattern

Examples are defined via `get_examples()` function:

```python
"""
Example definitions for {theory_name} theory.
"""


def get_examples() -> list:
    """
    Return list of example dictionaries.

    Each example has:
    - 'name': Display name
    - 'premises': List of premise sentences
    - 'conclusions': List of conclusion sentences
    - 'settings': Optional override settings
    - 'expectation': Expected result (True/False)
    """
    return [
        {
            'name': "Modus Ponens",
            'premises': ["A", "A implies B"],
            'conclusions': ["B"],
            'settings': {'N': 8},
            'expectation': True,
        },
        {
            'name': "Affirming Consequent (Invalid)",
            'premises': ["B", "A implies B"],
            'conclusions': ["A"],
            'expectation': False,
        },
    ]
```

## __init__.py Pattern

Package init exports main components:

```python
"""
{Theory} theory package.
"""

from .semantic import {Theory}Semantics, {Theory}Model, {Theory}Proposition
from .operators import get_operators
from .examples import get_examples

__all__ = [
    '{Theory}Semantics',
    '{Theory}Model',
    '{Theory}Proposition',
    'get_operators',
    'get_examples',
]
```

## Subtheory Integration

Subtheories extend base operators and examples:

```python
# In logos/subtheories/modal/__init__.py
from .operators import get_operators
from .examples import get_examples

# In logos/__init__.py
from .subtheories import modal, extensional, constitutive
```

Subtheory operators are merged with base operators during initialization.

## Operator Registration

Operators are registered with the semantics registry:

```python
# During semantics initialization
from .operators import get_operators

operators = get_operators(self)
for name, handler in operators.items():
    self.registry.register(name, handler)
```

## Settings Dictionary

Standard settings keys:

| Key | Type | Description |
|-----|------|-------------|
| `N` | int | Number of states (bitvector width) |
| `contingent` | bool | Require contingent premises |
| `non_empty` | bool | No empty verifiers |
| `non_null` | bool | No null falsifiers |
| `disjoint` | bool | Verifiers/falsifiers disjoint |
| `max_time` | int | Solver timeout in seconds |
| `iterate` | bool | Enable model iteration |
| `expectation` | bool/None | Expected validity result |

## Type Checking

Use TYPE_CHECKING for forward references:

```python
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .semantic import {Theory}Semantics
    from model_checker.syntactic import Sentence
```

This avoids circular imports while maintaining type safety.
