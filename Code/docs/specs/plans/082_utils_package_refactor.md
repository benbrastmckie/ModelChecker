# Plan 082: Utils Package Refactor

**Status:** Approved  
**Priority:** P1 (Critical)  
**Timeline:** 1 week  
**Compliance Score:** 55/100 → 90/100  

## Executive Summary

The utils package provides shared utilities across the framework but critically lacks type hints (0% coverage for 77 functions). As utilities are used throughout the codebase, adding type safety here will improve reliability everywhere. This focused refactor adds comprehensive type hints and optional error handling to achieve full compliance.

## Current State Analysis

### Package Structure
```
utils/
├── __init__.py          # Package exports (23 lines)
├── formula_utils.py     # Formula utilities (156 lines)
├── z3_utils.py         # Z3 helper functions (198 lines)
├── file_utils.py       # File operations (89 lines)
├── string_utils.py     # String manipulation (112 lines)
├── debug_utils.py      # Debugging helpers (147 lines)
├── common.py           # Common utilities (23 lines)
└── tests/              # Test suite (7 files, 776 lines)
```

### Current Compliance
- **Type Hints:** 0/77 functions (0%) ❌
- **Error Handling:** Not critical for utilities ✓
- **Technical Debt:** 0 TODO/FIXME ✓
- **Test Coverage:** Good (1.00 ratio) ✓
- **Documentation:** Good README ✓
- **Import Organization:** Clean ✓

## Implementation Strategy

Since utils has clean code and good tests, we focus solely on adding type hints systematically.

## Detailed Implementation Plan

### Day 1: Core Type Definitions and formula_utils.py

#### Create types.py for Shared Types
```python
# utils/types.py
from typing import TypeVar, Union, Any, Protocol, runtime_checkable
import z3

# Type variables
T = TypeVar('T')
Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.SeqRef]
Z3Sort = Union[z3.BoolSort, z3.ArithSort, z3.SeqSort]

@runtime_checkable
class Formattable(Protocol):
    """Protocol for objects that can be formatted."""
    def format(self, style: str = 'default') -> str: ...

@runtime_checkable  
class Serializable(Protocol):
    """Protocol for serializable objects."""
    def to_dict(self) -> dict: ...
    
FormulaType = Union[str, 'ASTNode', Z3Expr]
```

#### Type Hints for formula_utils.py (18 functions)
```python
# Before
def clean_formula(formula):
    return formula.strip().replace('  ', ' ')

def split_formula(formula, operator):
    parts = formula.split(operator)
    return [p.strip() for p in parts]

# After
from typing import List, Optional, Tuple, Set
from .types import FormulaType

def clean_formula(formula: str) -> str:
    """Clean whitespace from formula.
    
    Args:
        formula: Raw formula string
        
    Returns:
        Cleaned formula string
    """
    return formula.strip().replace('  ', ' ')

def split_formula(
    formula: str, 
    operator: str
) -> List[str]:
    """Split formula by operator.
    
    Args:
        formula: Formula to split
        operator: Operator to split on
        
    Returns:
        List of formula parts
    """
    parts: List[str] = formula.split(operator)
    return [p.strip() for p in parts]

def extract_atoms(formula: str) -> Set[str]:
    """Extract atomic propositions."""
    ...

def parenthesize(
    formula: str,
    force: bool = False
) -> str:
    """Add parentheses to formula."""
    ...
```

### Day 2: z3_utils.py Type Hints (23 functions)

```python
# Before
def create_bool_var(name, ctx=None):
    if ctx is None:
        return z3.Bool(name)
    return z3.Bool(name, ctx=ctx)

def get_model_values(model, variables):
    return {str(v): model.eval(v) for v in variables}

# After
from typing import Dict, List, Optional, Union, Any, cast
import z3
from .types import Z3Expr

def create_bool_var(
    name: str,
    ctx: Optional[z3.Context] = None
) -> z3.BoolRef:
    """Create a boolean Z3 variable.
    
    Args:
        name: Variable name
        ctx: Optional Z3 context
        
    Returns:
        Z3 boolean variable
    """
    if ctx is None:
        return z3.Bool(name)
    return z3.Bool(name, ctx=ctx)

def get_model_values(
    model: z3.ModelRef,
    variables: List[Z3Expr]
) -> Dict[str, Any]:
    """Extract variable values from model.
    
    Args:
        model: Z3 model
        variables: Variables to evaluate
        
    Returns:
        Dictionary of variable names to values
    """
    return {str(v): model.eval(v) for v in variables}

def simplify_expression(
    expr: Z3Expr,
    timeout: Optional[int] = None
) -> Z3Expr:
    """Simplify Z3 expression."""
    ...

def check_satisfiability(
    constraints: List[Z3Expr],
    timeout: int = 5000
) -> Tuple[bool, Optional[z3.ModelRef]]:
    """Check if constraints are satisfiable."""
    ...
```

### Day 3: file_utils.py and string_utils.py

#### file_utils.py Type Hints (12 functions)
```python
# Before
def read_json(filepath):
    with open(filepath) as f:
        return json.load(f)

def ensure_directory(path):
    os.makedirs(path, exist_ok=True)
    return path

# After
from typing import Any, Dict, Union, Optional
from pathlib import Path
import json

def read_json(filepath: Union[str, Path]) -> Dict[str, Any]:
    """Read JSON from file.
    
    Args:
        filepath: Path to JSON file
        
    Returns:
        Parsed JSON data
        
    Raises:
        FileNotFoundError: If file doesn't exist
        json.JSONDecodeError: If JSON is invalid
    """
    with open(filepath) as f:
        return json.load(f)

def ensure_directory(path: Union[str, Path]) -> Path:
    """Ensure directory exists.
    
    Args:
        path: Directory path
        
    Returns:
        Path object for directory
    """
    path_obj = Path(path)
    path_obj.mkdir(parents=True, exist_ok=True)
    return path_obj

def safe_write(
    filepath: Union[str, Path],
    content: str,
    backup: bool = True
) -> None:
    """Safely write to file with optional backup."""
    ...
```

#### string_utils.py Type Hints (14 functions)
```python
# Before  
def truncate(text, max_length=80):
    if len(text) <= max_length:
        return text
    return text[:max_length-3] + '...'

def indent(text, spaces=2):
    prefix = ' ' * spaces
    return '\n'.join(prefix + line for line in text.split('\n'))

# After
from typing import List, Optional, Pattern, Match
import re

def truncate(
    text: str,
    max_length: int = 80
) -> str:
    """Truncate text to maximum length.
    
    Args:
        text: Text to truncate
        max_length: Maximum length
        
    Returns:
        Truncated text with ellipsis if needed
    """
    if len(text) <= max_length:
        return text
    return text[:max_length-3] + '...'

def indent(
    text: str,
    spaces: int = 2
) -> str:
    """Indent text by specified spaces.
    
    Args:
        text: Text to indent
        spaces: Number of spaces
        
    Returns:
        Indented text
    """
    prefix: str = ' ' * spaces
    return '\n'.join(prefix + line for line in text.split('\n'))

def camel_to_snake(name: str) -> str:
    """Convert camelCase to snake_case."""
    ...

def extract_pattern(
    text: str,
    pattern: Union[str, Pattern[str]]
) -> List[str]:
    """Extract pattern matches from text."""
    ...
```

### Day 4: debug_utils.py and common.py

#### debug_utils.py Type Hints (19 functions)
```python
# Before
def print_ast(node, indent=0):
    print('  ' * indent + str(node))
    for child in node.children:
        print_ast(child, indent + 1)

def time_function(func):
    start = time.time()
    result = func()
    elapsed = time.time() - start
    return result, elapsed

# After
from typing import Any, Callable, TypeVar, Tuple, Optional
import time
from .types import T

def print_ast(
    node: Any,  # Should be ASTNode but avoid circular import
    indent: int = 0
) -> None:
    """Print AST structure for debugging.
    
    Args:
        node: AST node to print
        indent: Current indentation level
    """
    print('  ' * indent + str(node))
    for child in getattr(node, 'children', []):
        print_ast(child, indent + 1)

F = TypeVar('F', bound=Callable[..., Any])

def time_function(
    func: Callable[[], T]
) -> Tuple[T, float]:
    """Time function execution.
    
    Args:
        func: Function to time
        
    Returns:
        Tuple of (result, elapsed_seconds)
    """
    start: float = time.time()
    result: T = func()
    elapsed: float = time.time() - start
    return result, elapsed

def format_debug_output(
    title: str,
    data: Dict[str, Any],
    width: int = 80
) -> str:
    """Format debug output nicely."""
    ...
```

#### common.py Type Hints (3 functions)
```python
# Before
def flatten(nested_list):
    result = []
    for item in nested_list:
        if isinstance(item, list):
            result.extend(flatten(item))
        else:
            result.append(item)
    return result

# After
from typing import List, Any, Union, TypeVar, Sequence

T = TypeVar('T')

def flatten(nested_list: List[Union[T, List[Any]]]) -> List[T]:
    """Flatten nested list structure.
    
    Args:
        nested_list: Nested list to flatten
        
    Returns:
        Flattened list
    """
    result: List[T] = []
    for item in nested_list:
        if isinstance(item, list):
            result.extend(flatten(item))
        else:
            result.append(item)
    return result

def get_or_default(
    dictionary: Dict[str, T],
    key: str,
    default: T
) -> T:
    """Get value with default."""
    ...
```

### Day 5: Testing and Validation

#### Type Checking with mypy
```bash
# Run strict type checking
mypy src/model_checker/utils --strict

# Check for Any types
grep -r ": Any" src/model_checker/utils | grep -v "typing import"

# Verify all functions typed
python scripts/check_type_coverage.py utils
```

#### Update Tests for Type Safety
```python
# tests/test_type_safety.py
from typing import get_type_hints

def test_all_functions_have_type_hints():
    """Verify all functions are typed."""
    for module in [formula_utils, z3_utils, file_utils]:
        for name, func in inspect.getmembers(module, inspect.isfunction):
            if not name.startswith('_'):
                hints = get_type_hints(func)
                assert 'return' in hints, f"{name} missing return type"
```

## Error Handling Implementation (Day 5 continued)

To achieve 90/100 compliance, implement a minimal but comprehensive error hierarchy:

```python
# utils/errors.py
from typing import Optional, Dict, Any

class UtilityError(Exception):
    """Base class for utility errors."""
    def __init__(
        self,
        message: str,
        context: Optional[Dict[str, Any]] = None
    ):
        super().__init__(message)
        self.context = context or {}

class FileOperationError(UtilityError):
    """Raised for file operation failures."""
    pass

class FormulaProcessingError(UtilityError):
    """Raised for formula processing errors."""
    pass

class Z3UtilityError(UtilityError):
    """Raised for Z3-related utility errors."""
    pass

class StringProcessingError(UtilityError):
    """Raised for string manipulation errors."""
    pass

class DebugUtilityError(UtilityError):
    """Raised for debugging utility errors."""
    pass
```

This error hierarchy brings the package to full compliance by providing proper error handling infrastructure.

## Success Metrics

### Required Outcomes
- Type hints: 0/77 → 77/77 functions (100%)
- mypy validation: Pass with --strict
- Test coverage: Maintain 1.00 ratio
- Compliance score: 55/100 → 90/100

### Quality Indicators
- No use of `Any` except where necessary
- All public functions documented
- Type hints improve IDE autocomplete
- No regression in test coverage

## Risk Assessment

### Low Risk
- No functional changes, only type additions
- Excellent test coverage catches issues
- Small package with clear scope

### Potential Issues
1. **Z3 type complexity** - Use Union types as needed
2. **Circular imports** - Use string literals for forward refs
3. **Generic complexity** - Start simple, refine later

## Migration Impact

### For Dependent Packages
```python
# No breaking changes expected
# Type hints are additive only

# Benefits for dependents:
from model_checker.utils import clean_formula
# IDE now shows: clean_formula(formula: str) -> str
```

## Definition of Done

- [ ] All 77 functions have complete type hints
- [ ] types.py created with common type definitions
- [ ] errors.py created with 6 error classes
- [ ] mypy passes with --strict flag
- [ ] All existing tests still pass
- [ ] Type coverage report shows 100%
- [ ] No regression in test coverage
- [ ] README updated if needed
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Research 041: Framework Quality and Compliance Audit](../research/041_framework_quality_compliance_audit.md)
- [Code Maintenance Standards](../../../maintenance/README.md)