# Unified Code Quality Standards

[← Back to Maintenance](README.md) | [Code Organization →](CODE_ORGANIZATION.md) | [Testing Standards →](TESTING_STANDARDS.md)

## Overview

This document provides **unified code quality standards** for the ModelChecker framework, consolidating all coding conventions, patterns, and quality requirements into a single reference.

## Core Development Principles

### 1. No Backwards Compatibility

**NEVER** maintain backwards compatibility. This principle ensures:
- Clean architecture without legacy cruft
- Simplified interfaces without optional parameters
- Direct refactoring without compatibility layers

```python
# WRONG - Adding optional parameter for compatibility
def process(data, new_option=None):  # NO!
    if new_option is None:
        # Old behavior
    else:
        # New behavior

# CORRECT - Change interface directly
def process(data, new_option):  # Update all call sites
    # New behavior only
```

### 2. Test-Driven Development

Write tests BEFORE implementation:

```python
# 1. Write failing test first
def test_new_feature():
    result = new_feature(input_data)
    assert result == expected_output

# 2. Implement minimal code to pass
def new_feature(data):
    return process(data)

# 3. Refactor for quality
```

### 3. Fail-Fast Philosophy

Prefer deterministic failures with helpful messages:

```python
# WRONG - Silent failure
try:
    result = risky_operation()
except:
    result = None  # Hides problems

# CORRECT - Fail with context
if not validate_input(data):
    raise ValueError(f"Invalid input: {data} must be non-empty")
result = safe_operation(data)
```

## Code Style Requirements

### Python Version

- Target Python 3.8+ features
- Use type hints throughout
- Leverage modern Python idioms

### Import Organization

Follow strict import ordering (see [CODE_ORGANIZATION.md](CODE_ORGANIZATION.md)):

```python
# Standard library
import os
from typing import Dict, List, Optional

# Third-party
import z3

# Local application
from model_checker.defaults import SemanticDefaults

# Relative imports last
from .utils import helper_function
```

### Naming Conventions

```python
# Classes: PascalCase
class ModelVariable:
    pass

# Functions/methods: snake_case
def extract_constraints():
    pass

# Constants: UPPER_SNAKE_CASE
MAX_ITERATIONS = 1000

# Private: leading underscore
def _internal_helper():
    pass
```

### Type Annotations

Always use type hints:

```python
from typing import Dict, List, Optional, Union, Tuple

def process_formulas(
    formulas: List[str],
    settings: Dict[str, Any],
    timeout: Optional[int] = None
) -> Tuple[bool, List[str]]:
    """Process formulas with given settings."""
    pass
```

## Formula Standards

See [FORMULA_FORMATTING.md](FORMULA_FORMATTING.md) for complete details.

### Quick Reference

```python
# CORRECT - LaTeX notation, proper formatting
premises = [
    "\\Box (A \\rightarrow B)",  # Binary needs parentheses
    "\\neg C",                    # Unary no parentheses
    "((A \\wedge B) \\vee C)"    # Nested parentheses
]

# WRONG
bad = [
    "□(a→b)",      # Unicode and lowercase
    "(\\neg C)",   # Unnecessary parentheses
    "A \\wedge B"  # Missing outer parentheses
]
```

## Error Handling

See [ERROR_HANDLING.md](ERROR_HANDLING.md) for complete guidelines.

### User-Friendly Messages

```python
# WRONG - Technical jargon
raise ValueError("Z3 context mismatch in solver instance")

# CORRECT - Clear and actionable
raise ValueError(
    "Formula validation failed: 'A implies B' should be '(A \\rightarrow B)'. "
    "Binary operators require parentheses."
)
```

## Documentation Standards

### Docstring Format

```python
def complex_function(
    param1: str,
    param2: Optional[int] = None
) -> Dict[str, Any]:
    """
    Brief description of function purpose.
    
    Longer explanation if needed, including any important
    algorithmic details or usage notes.
    
    Args:
        param1: Description of first parameter
        param2: Description of optional parameter
        
    Returns:
        Description of return value
        
    Raises:
        ValueError: When validation fails
        TimeoutError: When Z3 solver times out
        
    Example:
        >>> result = complex_function("test", 42)
        >>> print(result['status'])
        'success'
    """
    pass
```

### Inline Comments

```python
# Use comments to explain WHY, not WHAT
# WRONG
x = x + 1  # Increment x

# CORRECT  
x = x + 1  # Compensate for 0-based indexing in user display
```

## Class Design

### Single Responsibility

Each class should have one clear purpose:

```python
# WRONG - Multiple responsibilities
class FormulaProcessor:
    def parse_formula(self): ...
    def validate_formula(self): ...
    def save_to_file(self): ...
    def send_email(self): ...

# CORRECT - Separated concerns
class FormulaParser:
    def parse(self): ...

class FormulaValidator:
    def validate(self): ...

class FormulaStorage:
    def save(self): ...
```

### Interface Segregation

```python
# Define clear, minimal interfaces
from abc import ABC, abstractmethod

class Validator(ABC):
    @abstractmethod
    def validate(self, item: Any) -> bool:
        """Validate an item."""
        pass

class FormulaValidator(Validator):
    def validate(self, formula: str) -> bool:
        """Validate a logical formula."""
        return check_syntax(formula)
```

## Testing Standards

See [TESTING_STANDARDS.md](TESTING_STANDARDS.md) for complete testing guide.

### Test Organization

```python
# tests/test_component.py
class TestComponent:
    """Test suite for Component."""
    
    def test_normal_case(self):
        """Test expected behavior."""
        pass
        
    def test_edge_case(self):
        """Test boundary conditions."""
        pass
        
    def test_error_handling(self):
        """Test error conditions."""
        pass
```

## Performance Guidelines

See [PERFORMANCE.md](PERFORMANCE.md) for optimization techniques.

### Quick Tips

```python
# Reuse Z3 contexts
ctx = z3.Context()
solver = z3.Solver(ctx=ctx)

# Batch operations
constraints = []
for item in items:
    constraints.append(create_constraint(item))
solver.add(*constraints)  # Add all at once
```

## Version Control Integration

Follow [VERSION_CONTROL.md](VERSION_CONTROL.md) for commit standards:

```bash
# Atomic commits with clear messages
git add src/component.py tests/test_component.py
git commit -m "Add validation for nested formulas

- Implement recursive validation logic
- Add comprehensive test coverage
- Update error messages for clarity"
```

## Security Considerations

### Input Validation

```python
def process_user_input(formula: str) -> str:
    """Safely process user-provided formula."""
    # Validate length
    if len(formula) > MAX_FORMULA_LENGTH:
        raise ValueError(f"Formula too long (max {MAX_FORMULA_LENGTH})")
    
    # Validate characters
    if not VALID_FORMULA_REGEX.match(formula):
        raise ValueError("Formula contains invalid characters")
    
    # Process safely
    return sanitize_formula(formula)
```

### No Dynamic Execution

```python
# NEVER do this
eval(user_input)  # Security risk!

# Use safe parsing instead
ast.parse(user_input, mode='eval')
```

## Code Review Checklist

Before submitting code:

- [ ] All tests passing
- [ ] Type hints added
- [ ] Docstrings complete
- [ ] No backwards compatibility code
- [ ] LaTeX notation in formulas
- [ ] Error messages user-friendly
- [ ] No commented-out code
- [ ] No debugging prints
- [ ] UTF-8 encoding verified
- [ ] Cross-references updated

---

[← Back to Maintenance](README.md) | [Code Organization →](CODE_ORGANIZATION.md) | [Testing Standards →](TESTING_STANDARDS.md)