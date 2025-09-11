# Plan 082: Utils Package Refactor (CORRECTED)

**Status:** Ready for Implementation  
**Priority:** P1 (Critical)  
**Timeline:** 1 week  
**Compliance Score:** 55/100 → 90/100  

## Executive Summary

The utils package provides shared utilities across the framework but critically lacks type hints (0% coverage for 30 functions across 8 modules). As utilities are used throughout the codebase, adding type safety here will improve reliability everywhere. This focused refactor adds comprehensive type hints to achieve full compliance.

## Current State Analysis

### Actual Package Structure
```
utils/
├── __init__.py          # Package exports
├── api.py              # API utilities (2 functions)
├── bitvector.py        # Bitvector operations (5 functions)
├── context.py          # Context management (1 function)
├── formatting.py       # Formatting utilities (3 functions)
├── parsing.py          # Parsing utilities (7 functions)
├── testing.py          # Testing helpers (5 functions)
├── version.py          # Version management (4 functions)
├── z3_helpers.py       # Z3 helper functions (3 functions)
└── tests/              # Test suite
    ├── unit/          # Unit tests for each module
    └── conftest.py    # Test fixtures
```

### Function Distribution (Verified)
- `api.py`: 2 functions
- `bitvector.py`: 5 functions  
- `context.py`: 1 function
- `formatting.py`: 3 functions
- `parsing.py`: 7 functions
- `testing.py`: 5 functions
- `version.py`: 4 functions
- `z3_helpers.py`: 3 functions
- **Total**: 30 functions

### Current Compliance
- **Type Hints:** 0/30 functions (0%) ❌
- **Error Handling:** Not critical for utilities ✓
- **Technical Debt:** 0 TODO/FIXME ✓
- **Test Coverage:** Good ✓
- **Documentation:** Good README ✓
- **Import Organization:** Clean ✓

## Implementation Strategy

Since utils has clean code and good tests, we focus solely on adding type hints systematically, file by file.

## Detailed Implementation Plan

### Day 1: Type Infrastructure and Small Modules

#### Create types.py for Shared Types
```python
# utils/types.py
from typing import TypeVar, Union, Any, Protocol, Optional
import z3

# Type variables
T = TypeVar('T')
Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.SeqRef]
Z3Sort = Union[z3.BoolSort, z3.ArithSort, z3.SeqSort]

# Common type aliases
PathLike = Union[str, 'Path']
ConfigDict = Dict[str, Any]
```

#### api.py (2 functions)
```python
from typing import Dict, Optional

def get_api_version() -> str:
    """Get API version string."""
    return "1.0.0"

def validate_api_key(key: str) -> bool:
    """Validate API key format."""
    return len(key) == 32 and key.isalnum()
```

#### context.py (1 function)
```python
from typing import Any, ContextManager
from contextlib import contextmanager

@contextmanager
def managed_context(resource: Any) -> ContextManager[Any]:
    """Create managed context for resource."""
    try:
        yield resource
    finally:
        # cleanup
        pass
```

### Day 2: Bitvector and Z3 Helpers

#### bitvector.py (5 functions)
```python
from typing import List, Tuple, Optional
import z3

def create_bitvector(
    name: str,
    size: int,
    ctx: Optional[z3.Context] = None
) -> z3.BitVecRef:
    """Create Z3 bitvector."""
    if ctx:
        return z3.BitVec(name, size, ctx=ctx)
    return z3.BitVec(name, size)

def bitvector_and(
    a: z3.BitVecRef,
    b: z3.BitVecRef
) -> z3.BitVecRef:
    """Bitwise AND of bitvectors."""
    return a & b

def bitvector_or(
    a: z3.BitVecRef,
    b: z3.BitVecRef
) -> z3.BitVecRef:
    """Bitwise OR of bitvectors."""
    return a | b

def extract_bits(
    bv: z3.BitVecRef,
    high: int,
    low: int
) -> z3.BitVecRef:
    """Extract bit range from bitvector."""
    return z3.Extract(high, low, bv)

def rotate_left(
    bv: z3.BitVecRef,
    count: int
) -> z3.BitVecRef:
    """Rotate bitvector left."""
    return z3.RotateLeft(bv, count)
```

#### z3_helpers.py (3 functions)
```python
from typing import List, Optional, Tuple, Any
import z3
from .types import Z3Expr

def create_solver(
    logic: Optional[str] = None,
    timeout: Optional[int] = None
) -> z3.Solver:
    """Create configured Z3 solver."""
    s = z3.Solver()
    if logic:
        s.set(logic=logic)
    if timeout:
        s.set(timeout=timeout)
    return s

def check_sat(
    constraints: List[Z3Expr],
    timeout: int = 5000
) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    """Check satisfiability of constraints."""
    s = create_solver(timeout=timeout)
    s.add(constraints)
    result = s.check()
    model = s.model() if result == z3.sat else None
    return result, model

def simplify_z3_expr(
    expr: Z3Expr,
    aggressive: bool = False
) -> Z3Expr:
    """Simplify Z3 expression."""
    if aggressive:
        return z3.simplify(expr, som=True, pull_cheap_ite=True)
    return z3.simplify(expr)
```

### Day 3: Formatting and Parsing

#### formatting.py (3 functions)
```python
from typing import Any, List, Optional

def format_table(
    headers: List[str],
    rows: List[List[Any]],
    padding: int = 2
) -> str:
    """Format data as ASCII table."""
    # implementation
    pass

def colorize(
    text: str,
    color: str,
    bold: bool = False
) -> str:
    """Add ANSI color codes to text."""
    # implementation
    pass

def indent_text(
    text: str,
    level: int,
    char: str = ' '
) -> str:
    """Indent text by specified level."""
    indent = char * (level * 2)
    return '\n'.join(indent + line for line in text.splitlines())
```

#### parsing.py (7 functions)
```python
from typing import List, Tuple, Optional, Dict, Any

def parse_operator(
    text: str
) -> Tuple[str, List[str]]:
    """Parse operator and arguments."""
    # implementation
    pass

def tokenize_formula(
    formula: str
) -> List[str]:
    """Tokenize logical formula."""
    # implementation
    pass

def parse_parentheses(
    text: str
) -> Tuple[bool, Optional[str]]:
    """Check parentheses balance."""
    # implementation
    pass

def extract_variables(
    formula: str
) -> List[str]:
    """Extract variable names from formula."""
    # implementation
    pass

def parse_config(
    config_str: str
) -> Dict[str, Any]:
    """Parse configuration string."""
    # implementation
    pass

def split_arguments(
    args_str: str,
    delimiter: str = ','
) -> List[str]:
    """Split argument string respecting nesting."""
    # implementation
    pass

def normalize_whitespace(
    text: str
) -> str:
    """Normalize whitespace in text."""
    return ' '.join(text.split())
```

### Day 4: Testing and Version

#### testing.py (5 functions)
```python
from typing import Any, Callable, Optional, TypeVar
import pytest

T = TypeVar('T')

def assert_equal_models(
    model1: Any,
    model2: Any,
    epsilon: float = 1e-6
) -> None:
    """Assert two models are equal."""
    # implementation
    pass

def create_mock_solver() -> Any:
    """Create mock Z3 solver for testing."""
    # implementation
    pass

def with_timeout(
    func: Callable[..., T],
    timeout: float,
    default: Optional[T] = None
) -> T:
    """Execute function with timeout."""
    # implementation
    pass

def capture_z3_output(
    func: Callable[..., T]
) -> Tuple[T, str]:
    """Capture Z3 output during function execution."""
    # implementation
    pass

def parametrize_theories(
    test_func: Callable
) -> Callable:
    """Parametrize test over all theories."""
    # decorator implementation
    pass
```

#### version.py (4 functions)
```python
from typing import Tuple, Optional

def get_version() -> str:
    """Get package version string."""
    return "1.0.0"

def parse_version(
    version_str: str
) -> Tuple[int, int, int]:
    """Parse version string to tuple."""
    parts = version_str.split('.')
    return tuple(int(p) for p in parts)

def compare_versions(
    v1: str,
    v2: str
) -> int:
    """Compare version strings."""
    # Returns -1, 0, or 1
    pass

def get_commit_hash() -> Optional[str]:
    """Get current git commit hash."""
    # implementation
    pass
```

### Day 5: Integration and Testing

#### Update __init__.py Exports
```python
# utils/__init__.py
from typing import TYPE_CHECKING

# Type-safe exports
if TYPE_CHECKING:
    from .api import get_api_version, validate_api_key
    from .bitvector import create_bitvector, bitvector_and
    from .context import managed_context
    # ... etc

__all__ = [
    'get_api_version',
    'validate_api_key',
    'create_bitvector',
    # ... etc
]
```

#### Run Type Checking
```bash
# Check all type hints
mypy src/model_checker/utils --strict

# Verify no Any types remain
grep -r ": Any" src/model_checker/utils | grep -v "typing import"
```

### Day 6: Documentation and Validation

- Update README with typed examples
- Run all tests to ensure compatibility
- Generate compliance report

## Testing Strategy

### Type Validation
```bash
# Run mypy on utils
mypy src/model_checker/utils --strict

# Run tests
./run_tests.py utils

# Check for remaining untyped functions
grep -r "def " src/model_checker/utils/*.py | grep -v "-> "
```

## Success Metrics

### Quantitative
- Type hint coverage: 0% → 100% (30/30 functions)
- mypy errors: Many → 0
- Test pass rate: 100% maintained
- Compliance score: 55/100 → 90/100

### Qualitative
- Full IDE autocomplete support
- Better error detection at development time
- Improved code documentation
- Easier maintenance and refactoring

## Migration Guide

### For Dependent Packages
```python
# Imports remain the same but now with type information
from model_checker.utils import create_bitvector, check_sat

# IDE now provides better autocomplete
solver = create_solver(logic="QF_BV", timeout=5000)
# Type checker knows solver is z3.Solver

result, model = check_sat(constraints)
# Type checker knows result is CheckSatResult, model is Optional[ModelRef]
```

## Risk Mitigation

### Identified Risks
1. **Import cycles** from type annotations
2. **Performance impact** from runtime type checking
3. **Compatibility** with existing code

### Mitigation Strategies
1. Use `TYPE_CHECKING` guard for import-only types
2. Avoid runtime type checking in performance-critical paths
3. Maintain backward compatibility by not changing signatures

## Definition of Done

- [ ] All 30 functions have type hints
- [ ] types.py created with common type definitions
- [ ] mypy --strict passes with no errors
- [ ] All existing tests pass
- [ ] Documentation updated with typed examples
- [ ] No decrease in test coverage
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Code Maintenance Standards](../../../Code/maintenance/README.md)