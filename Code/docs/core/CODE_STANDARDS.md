# Unified Code Quality Standards

[← Back to Maintenance](../README.md) | [Testing Standards →](../TESTING_STANDARDS.md) | [Error Handling →](../ERROR_HANDLING.md)

## Overview

This document consolidates all code quality standards for the ModelChecker framework into a single, comprehensive reference. These standards ensure consistency, maintainability, and quality across the entire codebase.

**Philosophy:** These standards provide flexible guidance for gradual improvement rather than rigid rules requiring massive changes. Apply them opportunistically and practically as you work with the code, always prioritizing working software over perfect compliance.

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

### 2. No Decorators

**NEVER** use decorators in the codebase. This ensures:
- Explicit, traceable code flow
- Easier debugging and testing
- No hidden magic or side effects

```python
# WRONG - Using decorators
@property
def value(self):
    return self._value

@staticmethod
def helper():
    pass

# CORRECT - Use explicit methods
def get_value(self):
    return self._value

def helper():  # Just a regular function
    pass
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

### 4. Test-Driven Development

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

## Import Organization

Organize imports in strict order with blank lines between groups:

```python
# 1. Standard library
import os
import sys
from typing import Dict, List, Optional, Union, Tuple

# 2. Third-party
import z3
import numpy as np

# 3. Local framework
from model_checker.defaults import SemanticDefaults
from model_checker.operators import Operator

# 4. Relative imports (for portability)
from .utils import helper_function
from .semantic import TheorySemantics
```

### Why Relative Imports?

**ALWAYS use relative imports** for local modules within the same package:

```python
# CORRECT - Relative imports (portable)
from .semantic import TheorySemantics
from .operators import theory_operators
from ..base import BaseStructure

# INCORRECT - Absolute imports (fragile)
from model_checker.theory_lib.logos.semantic import LogosSemantics
```

## Naming Conventions

Follow these strict naming standards:

| Element       | Convention     | Example                |
|---------------|----------------|------------------------|
| **Classes**   | `PascalCase`   | `ModelVariable`        |
| **Functions** | `snake_case`   | `extract_constraints()` |
| **Constants** | `UPPER_SNAKE`  | `MAX_ITERATIONS`       |
| **Private**   | `_snake_case`  | `_internal_helper()`   |
| **Modules**   | `lowercase`    | `semantic.py`          |

```python
# Classes: PascalCase
class BimodalSemantics:
    pass

# Functions/methods: snake_case
def check_validity(premises, conclusions):
    pass

# Constants: UPPER_SNAKE_CASE
DEFAULT_SETTINGS = {
    'N': 3,
    'max_time': 10,
}

# Private: leading underscore
def _internal_helper():
    pass
```

## Type Annotations

**Always use type hints** for all public functions and methods:

```python
from typing import Dict, List, Optional, Union, Tuple, Any

def process_formulas(
    formulas: List[str],
    settings: Dict[str, Any],
    timeout: Optional[int] = None
) -> Tuple[bool, List[str]]:
    """Process formulas with given settings."""
    pass

def complex_function(
    param1: str,
    param2: Optional[int] = None
) -> Dict[str, Any]:
    """Complex function with proper type annotations."""
    pass
```

## Docstring Standards

Use comprehensive docstrings for all public interfaces:

### Function Docstrings

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
        param2: Description of optional parameter (default: None)
        
    Returns:
        Description of return value structure
        
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

### Class Docstrings

```python
class ExampleClass:
    """
    Brief one-line summary of class purpose.
    
    Longer description of the class behavior and responsibilities.
    
    Attributes:
        attribute1: Description of attribute1
        attribute2: Description of attribute2
    
    Example:
        >>> obj = ExampleClass()
        >>> result = obj.method()
    """
    pass
```

### Module Docstrings

```python
"""
Brief one-line summary of module purpose.

Longer description providing context and usage information.
This module implements logical reasoning components for...

Example:
    Basic usage example::
    
        >>> from module import function
        >>> result = function(arg)
"""
```

## Method Complexity Guidelines

These are **flexible guidelines** that respect domain complexity rather than rigid rules:

### Length Targets (Soft Guidelines)

- **Utility Methods:** 20-40 lines (focused, well-defined tasks)
- **Business Logic:** 40-75 lines (core functionality with moderate complexity)
- **Complex Domain Methods:** 75+ lines (legitimate algorithmic complexity)

### Complexity Assessment Criteria

Consider these factors beyond just line count:

#### Functional Cohesion
```python
# High cohesion - method does one clear thing
def generate_bitvector_constraints(self, n_atoms: int, state_vars: List) -> List:
    """Generate all necessary bitvector constraints for n atomic propositions."""
    # All code focuses on bitvector constraint generation

# Low cohesion - consider splitting
def process_and_save_and_validate(self, data):  # Multiple responsibilities
    # validation logic...
    # processing logic...  
    # file saving logic...
```

#### Nesting Depth
```python
# Reasonable nesting (2-3 levels)
def process_examples(self, examples):
    for example in examples:
        if self._should_process(example):
            result = self._process_single_example(example)

# Excessive nesting (4+ levels) - consider extraction
def complex_nested_processing(self, data):
    for item in data:
        if condition1:
            for sub_item in item.children:
                if condition2:
                    for detail in sub_item.details:  # Getting deep
                        if condition3:
                            # Consider extracting this logic
```

#### Cyclomatic Complexity
Rough guidelines for decision points (if/for/while/try/except):
- **Simple methods:** 1-5 decision points
- **Moderate methods:** 6-10 decision points
- **Complex methods:** 10+ decision points (may indicate need for decomposition)

### When to Extract Methods

#### Clear Extraction Opportunities
```python
# Before: Mixed responsibilities
def process_formula_validation(self, formula, theory):
    # Input parsing (could be extracted)
    # Semantic validation (could be extracted)  
    # Theory-specific checks (could be extracted)

# After: Clear responsibilities
def process_formula_validation(self, formula, theory):
    """Coordinate formula validation process."""
    tokens = self._parse_formula_tokens(formula)
    self._validate_semantic_structure(tokens)
    self._validate_theory_constraints(tokens, theory)
    return ValidationResult.success()
```

#### Repeated Patterns
```python
# Before: Repetitive validation
def validate_settings(self, settings):
    if 'N' in settings:
        if not isinstance(settings['N'], int) or settings['N'] < 1:
            raise ValueError("N must be positive integer")
    # More similar validation...

# After: Extracted common pattern  
def validate_settings(self, settings):
    self._validate_positive_int(settings, 'N', required=True)
    self._validate_positive_int(settings, 'max_time', required=False)
```

## Error Handling Standards

### User-Friendly Messages

Provide clear, actionable error messages that help users understand and fix problems:

```python
# WRONG - Technical jargon
raise ValueError("Z3 context mismatch in solver instance")

# CORRECT - Clear and actionable
raise ValueError(
    "Formula validation failed: 'A implies B' should be '(A \\rightarrow B)'. "
    "Binary operators require parentheses."
)

# WRONG - Generic error
if not os.path.exists(filepath):
    raise FileNotFoundError("File not found")

# CORRECT - Specific and helpful
if not os.path.exists(filepath):
    raise FileNotFoundError(
        f"Theory file '{filepath}' not found. "
        f"Check that the file exists and has correct permissions."
    )
```

### Exception Types

Use specific exception types with proper inheritance:

```python
# Define custom exceptions when needed
class ModelCheckerError(Exception):
    """Base exception for ModelChecker framework."""
    pass

class FormulaValidationError(ModelCheckerError):
    """Raised when formula validation fails."""
    pass

class TheoryLoadError(ModelCheckerError):
    """Raised when theory loading fails."""
    pass

# Use appropriate built-in exceptions
def validate_input(data: str) -> None:
    if not data.strip():
        raise ValueError("Input cannot be empty or whitespace only")
    
    if len(data) > MAX_LENGTH:
        raise ValueError(f"Input too long: {len(data)} > {MAX_LENGTH}")
```

## Formula Standards

### LaTeX Notation Requirements

**Always use LaTeX notation in code** with proper formatting:

```python
# CORRECT - LaTeX notation, proper formatting
premises = [
    "\\Box (A \\rightarrow B)",  # Binary needs parentheses
    "\\neg C",                    # Unary no parentheses
    "((A \\wedge B) \\vee C)"    # Nested parentheses
]

# WRONG
bad_formulas = [
    "□(a→b)",      # Unicode and lowercase
    "(\\neg C)",   # Unnecessary parentheses
    "A \\wedge B"  # Missing outer parentheses for binary
]
```

### Formatting Rules

- Use capital letters (`A`, `B`, `C`) for propositions
- Binary operators require outer parentheses: `(A \\rightarrow B)`
- Unary operators have no outer parentheses: `\\neg A`
- Always use double backslashes: `\\Box`, `\\wedge`, `\\rightarrow`
- Unicode symbols acceptable in comments and documentation

## Class Design Principles

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

Define clear, minimal interfaces:

```python
from abc import ABC, abstractmethod

class Validator(ABC):
    def validate(self, item: Any) -> bool:
        """Validate an item."""
        raise NotImplementedError("Subclasses must implement validate()")

class FormulaValidator(Validator):
    def validate(self, formula: str) -> bool:
        """Validate a logical formula."""
        return check_syntax(formula)
```

## Code Comments

Use comments sparingly and effectively:

```python
# Use comments to explain WHY, not WHAT
# WRONG
x = x + 1  # Increment x

# CORRECT  
x = x + 1  # Compensate for 0-based indexing in user display

# CORRECT - Explain complex logic
# Calculate bit vector size based on number of atomic propositions
# This ensures sufficient bits for all possible state combinations
bit_size = 2 ** N
```

## Security Considerations

### Input Validation

Always validate user input thoroughly:

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

## File Organization Standards

### Module Structure

Each module should follow this structure:

```python
"""
Module docstring describing purpose and usage.
"""

# Imports (organized as specified above)

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

### Theory Module Organization

Theory modules must follow this structure:

```
theory_name/
├── __init__.py         # Public API exports
├── semantic.py         # Core semantic classes
├── operators.py        # Operator definitions
├── examples.py         # Example formulas
├── iterate.py          # Model iteration (if applicable)
├── settings.py         # Default settings
└── utils.py            # Helper functions
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

## Testing Integration

### Test Organization

```python
# tests/test_component.py
class TestComponent:
    """Test suite for Component."""
    
    def test_normal_case(self):
        """Test expected behavior with valid input."""
        pass
        
    def test_edge_case(self):
        """Test boundary conditions and edge cases."""
        pass
        
    def test_error_handling(self):
        """Test error conditions and exception handling."""
        pass
```

### Test Naming

Use descriptive test names that explain what is being tested:

```python
# GOOD
def test_modus_ponens_valid_argument():
    """Test that modus ponens produces valid argument (no countermodel)."""
    pass

def test_invalid_formula_raises_validation_error():
    """Test that malformed formulas raise FormulaValidationError."""
    pass

# BAD
def test_1():
    pass

def test_formula():
    pass
```

## Performance Guidelines

### Z3 Optimization

```python
# Reuse Z3 contexts for efficiency
ctx = z3.Context()
solver = z3.Solver(ctx=ctx)

# Batch operations when possible
constraints = []
for item in items:
    constraints.append(create_constraint(item))
solver.add(*constraints)  # Add all at once

# Reset context between examples to prevent state leakage
def process_example(self, example):
    ctx = z3.Context()  # Fresh context
    solver = z3.Solver(ctx=ctx)
    # Process with clean state
```

### Memory Management

```python
# Clean up Z3 objects explicitly
solver = None
ctx = None

# Use appropriate timeouts
solver.set("timeout", 10000)  # 10 seconds
```

## Documentation Standards

### No Historical References

Documentation must describe the current state of the system without references to:
- Previous versions or implementations
- Refactoring phases or milestones  
- Past changes or improvements
- Migration notes from old systems
- "Recently added" or "newly refactored" annotations

**WRONG:**
```markdown
### Recent Improvements (Phase 1-4 Refactor)
- Test Organization: Clear separation (refactored in v2.0)
```

**RIGHT:**
```markdown
### Test Suite Features
- Test Organization: Clear separation by type
```

Documentation should be timeless and describe what IS, not what WAS or how it CHANGED.

## Code Review Checklist

Before submitting code, verify:

- [ ] All tests passing
- [ ] Type hints added to all public functions
- [ ] Docstrings complete and following standards
- [ ] No backwards compatibility code
- [ ] LaTeX notation used in formulas
- [ ] Error messages are user-friendly and actionable
- [ ] No commented-out code
- [ ] No debugging print statements
- [ ] UTF-8 encoding verified
- [ ] Imports organized correctly
- [ ] No decorators used
- [ ] Method complexity appropriate for domain
- [ ] Clear separation of concerns
- [ ] Consistent naming conventions followed
- [ ] No historical references in documentation

## Success Metrics

These standards should result in:

### Code Quality Metrics
- **Reduced debugging time:** Clear error messages and fail-fast design
- **Improved testability:** Single-responsibility methods are easier to test
- **Enhanced readability:** Consistent naming and organization
- **Better maintainability:** Clear interfaces and documentation

### Development Efficiency Metrics
- **Faster onboarding:** New developers can understand code structure quickly
- **Reduced merge conflicts:** Consistent formatting and organization
- **Improved code reviews:** Standards provide objective review criteria
- **Better refactoring confidence:** Comprehensive tests enable safe changes

### User Experience Metrics
- **Clearer error messages:** Users understand what went wrong and how to fix it
- **Consistent behavior:** Predictable interfaces across all components
- **Better documentation:** Complete docstrings and examples
- **Improved reliability:** Fail-fast design prevents silent failures

## Gradual Improvement Strategy

### Opportunistic Application

Apply these standards **opportunistically** rather than requiring massive rewrites:

1. **During bug fixes:** Improve the code you're already touching
2. **When adding features:** Ensure new code follows standards
3. **During refactoring:** Apply standards to the components being refactored
4. **In code reviews:** Suggest improvements aligned with standards

### Priority Order

When applying standards gradually, prioritize:

1. **Error handling:** Improve user-facing error messages first
2. **Type annotations:** Add type hints to new and modified functions
3. **Docstrings:** Document public interfaces as you work with them
4. **Import organization:** Fix imports when modifying files
5. **Method complexity:** Extract methods when adding functionality

### Integration with Existing Patterns

Work with established patterns in the codebase:

- Respect legitimate domain complexity in semantic algorithms
- Build on successful refactoring patterns from builder/ improvements
- Maintain compatibility with existing test structures
- Preserve working functionality while improving code quality

## Conclusion

These unified code quality standards provide a comprehensive framework for maintaining and improving the ModelChecker codebase. They emphasize:

- **Practical application** over theoretical perfection
- **Domain-appropriate complexity** over arbitrary metrics
- **User-friendly design** over developer convenience
- **Gradual improvement** over massive rewrites

Use these standards as guidance for writing clean, maintainable code that serves both developers and users effectively.

---

[← Back to Maintenance](../README.md) | [Testing Standards →](../TESTING_STANDARDS.md) | [Error Handling →](../ERROR_HANDLING.md)