---
paths: "**/*.py"
---

# Python/Z3 Development Rules

## Test-Driven Development

**MANDATORY**: All implementations follow TDD:

```
1. RED: Write failing test first
2. GREEN: Write minimal code to pass
3. REFACTOR: Improve while tests pass
```

### Test Commands

```bash
# Run all tests
PYTHONPATH=Code/src pytest Code/tests/ -v

# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v

# Run single file
PYTHONPATH=Code/src pytest path/to/test_file.py -v

# With coverage
PYTHONPATH=Code/src pytest --cov=model_checker --cov-report=term-missing
```

## Import Standards

```python
# 1. Standard library
import os
from pathlib import Path
from typing import Dict, List, Optional

# 2. Third-party
import z3
from z3 import And, Or, Not, Implies, ForAll, Exists

# 3. Local - prefer relative imports within package
from .models import Model
from ..utils import z3_helpers
from ...syntactic import Sentence
```

## Z3 Patterns

### Solver Usage
```python
# Create solver with timeout
solver = z3.Solver()
solver.set("timeout", 10000)  # 10 seconds

# Add constraints
solver.add(constraint1)
solver.add(constraint2)

# Check satisfiability
result = solver.check()
if result == z3.sat:
    model = solver.model()
elif result == z3.unsat:
    # No solution exists
    pass
else:  # z3.unknown
    # Timeout or inconclusive
    pass
```

### Constraint Generation
```python
# Boolean variables
p = z3.Bool('p')
q = z3.Bool('q')

# BitVector for worlds/states
world = z3.BitVec('w', 3)  # 3-bit state space

# Quantifiers
x = z3.BitVec('x', 3)
forall_constraint = z3.ForAll([x], condition(x))
exists_constraint = z3.Exists([x], condition(x))
```

### Model Extraction
```python
if solver.check() == z3.sat:
    model = solver.model()

    # Get Boolean value
    p_val = model.eval(p, model_completion=True)

    # Get BitVector value
    w_val = model.eval(world, model_completion=True)
    if isinstance(w_val, z3.BitVecNumRef):
        w_int = w_val.as_long()
```

## Theory Development

### SemanticDefaults Extension
```python
class MyTheorySemantics(SemanticDefaults):
    """Semantic framework for my theory."""

    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,              # State space size
        'contingent': False, # Force contingency
        'non_empty': False,  # Non-empty verifiers
        'max_time': 10,      # Solver timeout
    }

    def operator_verifier(self, sentence, eval_world):
        """Verifier clause for operator."""
        left = sentence.arguments[0]
        right = sentence.arguments[1]

        left_ver = self.true_at(left, eval_world)
        right_ver = self.true_at(right, eval_world)

        return z3.And(left_ver, right_ver)
```

### Operator Registration
```python
def get_operators():
    """Return operator collection for theory."""
    return OperatorCollection([
        Operator(
            name='my_op',
            symbol='◊',
            verifier=semantic.my_op_verifier,
            falsifier=semantic.my_op_falsifier,
            arity=2,
            precedence=5,
        ),
    ])
```

### Example Creation
```python
examples = [
    BuildExample(
        name='test_basic',
        premises=['A my_op B'],
        conclusions=['C'],
        settings={'N': 3},
        expectation=True,  # Expect valid
    ),
]
```

## Testing Patterns

### Theory Test Structure
```python
import pytest
from model_checker.theory_lib.logos import get_theory, get_examples

class TestOperator:
    """Tests for operator semantics."""

    @pytest.fixture
    def theory(self):
        """Get theory instance."""
        return get_theory()

    def test_verifier_basic(self, theory):
        """Test basic verifier case."""
        example = BuildExample(
            premises=['A op B'],
            conclusions=['C'],
            settings={'N': 3}
        )
        result = example.check(theory)
        assert result.valid is True

    def test_falsifier_counterexample(self, theory):
        """Test falsifier produces counterexample."""
        example = BuildExample(
            premises=['A op B'],
            conclusions=['D'],
            settings={'N': 3},
            expectation=False
        )
        result = example.check(theory)
        assert result.valid is False
        assert result.model is not None
```

### Pytest Fixtures
```python
@pytest.fixture(scope='module')
def theory():
    """Module-scoped theory fixture."""
    return get_theory()

@pytest.fixture
def solver():
    """Fresh solver for each test."""
    s = z3.Solver()
    s.set("timeout", 5000)
    return s
```

## Code Quality

### Type Hints
```python
from typing import List, Optional, Dict, Any

def process_sentence(
    sentence: Sentence,
    context: Dict[str, Any],
    timeout: Optional[int] = None
) -> z3.BoolRef:
    """Process sentence and return Z3 constraint."""
    ...
```

### Docstrings
```python
def my_function(arg1: str, arg2: int) -> bool:
    """
    Short description of function.

    Longer description if needed, explaining the purpose
    and any important behavior.

    Args:
        arg1: Description of first argument
        arg2: Description of second argument

    Returns:
        Description of return value

    Raises:
        ValueError: When arg2 is negative
    """
    ...
```

## Error Handling

### Common Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `ModuleNotFoundError` | PYTHONPATH not set | Set `PYTHONPATH=Code/src` |
| `z3.Z3Exception` | Invalid constraint | Check types match |
| `ImportError` | Wrong relative import | Check package structure |
| `TimeoutError` | Z3 solver timeout | Increase timeout or simplify |

### Error Patterns
```python
# Fail-fast with clear messages
def validate_input(value: int) -> None:
    if value < 0:
        raise ValueError(f"Expected non-negative value, got {value}")

# Z3 timeout handling
try:
    result = solver.check()
except z3.Z3Exception as e:
    logger.error(f"Z3 error: {e}")
    raise
```

## Project-Specific Patterns

### Theory Library Structure
```
theory_lib/{theory}/
├── semantic.py      # Core semantic framework
├── operators.py     # Operator registry
├── examples.py      # Test cases
├── iterate.py       # Iteration support
├── __init__.py      # Public API
└── tests/
    ├── unit/        # Unit tests
    └── integration/ # Integration tests
```

### Key Locations
- **Theories**: `Code/src/model_checker/theory_lib/`
- **Models**: `Code/src/model_checker/models/`
- **Builder**: `Code/src/model_checker/builder/`
- **Iterator**: `Code/src/model_checker/iterate/`
- **Utils**: `Code/src/model_checker/utils/`

## Development Commands

```bash
# Development CLI
cd Code && ./dev_cli.py examples/my_example.py

# Build package
cd Code && python -m build

# Check imports
PYTHONPATH=Code/src python -c "from model_checker import ..."

# Run model checker
model-checker examples.py --maximize
```
