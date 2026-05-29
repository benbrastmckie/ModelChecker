# ModelChecker API Reference

Package structure and key classes for the ModelChecker framework.

## Package Structure

```
code/src/model_checker/
├── __init__.py             # Main package entry point
├── theory_lib/             # Semantic theories (see theory-lib-patterns.md)
│   ├── logos/              # Core truthmaker semantics
│   ├── exclusion/          # Exclusion theory
│   ├── imposition/         # Imposition theory
│   └── bimodal/            # Bimodal theory
├── builder/                # Project generation utilities
├── iterate/                # Model iteration engine
├── models/                 # Core model structures
│   ├── model.py            # Model base class
│   ├── proposition.py      # PropositionDefaults
│   ├── semantic.py         # SemanticDefaults
│   └── structure.py        # ModelDefaults
├── syntactic/              # Formula parsing
│   ├── parser.py           # Expression parser
│   └── sentence.py         # Sentence class
├── output/                 # Result formatting
└── utils/                  # Z3 utilities and helpers
    ├── __init__.py         # Exports ForAll, Exists, bitvec_to_substates
    └── z3_helpers.py       # Z3 utility functions
```

## Key Classes

### SemanticDefaults (models/semantic.py)

Base class for semantic frameworks. All theory semantics inherit from this.

```python
from model_checker.models.semantic import SemanticDefaults

class MySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,              # Number of states
        'contingent': True,   # Require contingent sentences
        'non_empty': True,    # No empty verifiers
        'non_null': True,     # No null falsifiers
        'max_time': 10,       # Solver timeout
        'iterate': False,     # Model iteration mode
    }

    def __init__(self, settings, name):
        super().__init__(settings, name)
        # Initialize theory-specific components
```

### PropositionDefaults (models/proposition.py)

Base class for proposition handling. Defines verification and falsification.

```python
from model_checker.models.proposition import PropositionDefaults

class MyProposition(PropositionDefaults):
    def __init__(self, semantics, sentence_letter, model, ...):
        super().__init__(semantics, sentence_letter, model, ...)
        # Sentence letter is the atomic proposition identifier

    # Must implement verifier/falsifier methods
```

### ModelDefaults (models/structure.py)

Base class for model structures. Defines state space and evaluation.

```python
from model_checker.models.structure import ModelDefaults

class MyModel(ModelDefaults):
    def __init__(self, semantics, settings):
        super().__init__(semantics, settings)
        # Initialize model structure

    def evaluate(self, sentence, state):
        """Evaluate sentence at state."""
        pass
```

### Sentence (syntactic/sentence.py)

Parsed sentence representation.

```python
from model_checker import syntactic

# Parse a sentence
sentence = syntactic.parse("A and B")
# Returns Sentence object with operators and subsentences
```

## Import Patterns

Use relative imports within packages:

```python
# Within theory_lib/logos/
from .operators import get_operators
from .semantic import LogosSemantics
from ..errors import TheoryError  # Parent package

# From model_checker root
from model_checker.models.proposition import PropositionDefaults
from model_checker.utils import ForAll, Exists, bitvec_to_substates
```

## Z3 Utilities

Located in `model_checker.utils`:

```python
from model_checker.utils import (
    ForAll,              # Wrapper for z3.ForAll
    Exists,              # Wrapper for z3.Exists
    bitvec_to_substates, # Convert BitVec to state set
    pretty_set_print,    # Format state sets for display
    int_to_binary,       # Convert int to binary representation
)
```

## Testing Infrastructure

Tests live alongside packages in `tests/` subdirectories:

```
theory_lib/logos/
├── semantic.py
├── operators.py
└── tests/
    ├── __init__.py
    ├── conftest.py          # Pytest fixtures
    ├── unit/
    │   ├── test_semantic_methods.py
    │   └── test_operators.py
    └── integration/
        ├── test_injection.py
        └── test_iterate.py
```

Run tests:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v
```

## Type Hints

ModelChecker uses extensive type hints with TYPE_CHECKING imports:

```python
from typing import Dict, Any, Optional, Set, Tuple, Union, List, TYPE_CHECKING

if TYPE_CHECKING:
    from .protocols import SemanticsProtocol, StateType, Z3Constraint
    from model_checker.syntactic import Sentence
```

## Protocols

Type protocols for duck typing (in `theory_lib/logos/protocols.py`):

```python
from .protocols import (
    SemanticsProtocol,   # Interface for semantics classes
    RegistryProtocol,    # Interface for operator registries
    EvaluationPoint,     # Tuple[state, world] or similar
    StateType,           # State representation type
    Z3Constraint,        # z3.BoolRef type alias
    SettingsDict,        # Configuration dictionary
)
```
