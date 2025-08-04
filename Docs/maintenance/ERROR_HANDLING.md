# Error Handling Standards

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md) | [Performance Guidelines →](PERFORMANCE.md)

## Overview

This document defines error handling standards for the ModelChecker codebase, focusing on user-friendly messages and proper exception usage.

## Error Message Principles

### Be Specific and Helpful

```python
# GOOD - Provides context and guidance
if not os.path.exists(file_path):
    raise FileNotFoundError(
        f"Example file '{file_path}' not found. "
        f"Check that the file exists and the path is correct."
    )

# BAD - Too generic
if not os.path.exists(file_path):
    raise FileNotFoundError("File not found")
```

### Include Relevant Information

```python
# GOOD - Shows what was expected vs received
if operator_arity != len(arguments):
    raise ValueError(
        f"Operator '{operator_name}' expects {operator_arity} arguments "
        f"but received {len(arguments)}: {arguments}"
    )

# BAD - Missing context
if operator_arity != len(arguments):
    raise ValueError("Wrong number of arguments")
```

## Exception Types

### Use Appropriate Exception Classes

```python
# File operations
raise FileNotFoundError(f"Configuration file '{config_path}' not found")

# Value errors
raise ValueError(f"Invalid N value: {n}. Must be between 1 and 64")

# Type errors  
raise TypeError(f"Expected string formula, got {type(formula).__name__}")

# Not implemented
raise NotImplementedError(f"Operator '{op}' not yet implemented")

# Import errors
raise ImportError(f"Required module '{module}' not installed. Run: pip install {module}")
```

### Custom Exceptions

Define custom exceptions for domain-specific errors:

```python
class FormulaParseError(Exception):
    """Raised when a formula cannot be parsed."""
    pass

class ModelNotFoundError(Exception):
    """Raised when no model satisfies the constraints."""
    pass

class TheoryLoadError(Exception):
    """Raised when a theory cannot be loaded."""
    pass
```

## Error Handling Patterns

### Validation with Early Returns

```python
def process_formula(formula: str) -> Result:
    """Process a logical formula."""
    # Validate input first
    if not formula:
        raise ValueError("Formula cannot be empty")
    
    if not isinstance(formula, str):
        raise TypeError(f"Formula must be string, got {type(formula).__name__}")
    
    # Proceed with processing
    ...
```

### Context Managers for Cleanup

```python
class ModelBuilder:
    def __enter__(self):
        self.solver = z3.Solver()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        # Cleanup even if exception occurs
        self.solver.reset()
        return False  # Don't suppress exceptions
```

### Graceful Degradation

```python
try:
    # Try optimal approach
    result = optimize_model(constraints)
except z3.Z3Exception:
    # Fall back to basic approach
    logger.warning("Optimization failed, using basic solver")
    result = basic_solve(constraints)
```

## User-Facing Error Messages

### Formula Errors

```python
def validate_formula(formula: str) -> None:
    """Validate formula syntax."""
    if "∧" in formula or "∨" in formula:
        raise FormulaParseError(
            f"Unicode symbols not allowed in formulas. "
            f"Use LaTeX notation: '\\wedge' for ∧, '\\vee' for ∨"
        )
    
    if formula.count("(") != formula.count(")"):
        raise FormulaParseError(
            f"Unbalanced parentheses in formula: '{formula}'. "
            f"Found {formula.count('(')} '(' and {formula.count(')')} ')'"
        )
```

### Configuration Errors

```python
def validate_settings(settings: dict) -> None:
    """Validate settings dictionary."""
    if 'N' in settings:
        n = settings['N']
        if not isinstance(n, int) or n < 1 or n > 64:
            raise ValueError(
                f"Setting 'N' must be an integer between 1 and 64, got {n}. "
                f"This represents the number of atomic propositions."
            )
```

## Logging vs Exceptions

### When to Log

```python
import logging

logger = logging.getLogger(__name__)

# Log recoverable issues
if cache_miss:
    logger.debug(f"Cache miss for key: {key}")

# Log performance warnings
if execution_time > threshold:
    logger.warning(f"Slow execution: {execution_time}s for {operation}")
```

### When to Raise Exceptions

```python
# Raise for unrecoverable errors
if required_file_missing:
    raise FileNotFoundError(f"Required file '{file}' not found")

# Raise for programming errors
if not isinstance(argument, expected_type):
    raise TypeError(f"Expected {expected_type}, got {type(argument)}")
```

## Exception Documentation

### In Docstrings

```python
def parse_formula(formula: str) -> ParseTree:
    """
    Parse a logical formula into a parse tree.
    
    Args:
        formula: The formula string to parse
        
    Returns:
        ParseTree representation of the formula
        
    Raises:
        FormulaParseError: If formula syntax is invalid
        ValueError: If formula is empty
        
    Example:
        >>> parse_formula("(A \\wedge B)")
        ParseTree(...)
    """
```

### In Error Messages

Include examples of correct usage in error messages:

```python
raise FormulaParseError(
    f"Invalid operator '{op}' in formula. "
    f"Valid operators are: \\wedge, \\vee, \\neg, \\rightarrow, \\Box, \\Diamond. "
    f"Example: '(A \\wedge B)' or '\\Box (A \\rightarrow B)'"
)
```

---

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md) | [Performance Guidelines →](PERFORMANCE.md)