# Error Handling Standards

[← Code Organization](CODE_ORGANIZATION.md) | [Back to Maintenance](README.md) | [Performance Guidelines →](PERFORMANCE.md)

## Overview

This document defines **flexible error handling standards** for the ModelChecker codebase, focusing on helpful user experiences and maintainable error patterns. These standards build on the proven BuilderError hierarchy and provide guidance for creating consistent, actionable error handling across all packages.

**Philosophy:** Error handling should **help users understand and resolve problems** while providing developers with clear debugging information. Error patterns should be **consistent but not rigid**, adapting to the specific needs of each component.

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

## Proven Error Hierarchy Pattern

### BuilderError Model (Reference Standard)

The builder/ package demonstrates an effective error hierarchy that other packages should follow:

```python
# From builder/error_types.py - proven pattern to extend
class BuilderError(Exception):
    """Base exception for all builder package errors."""
    pass

class ModuleLoadError(BuilderError):
    """Raised when a module cannot be loaded or imported."""
    
    def __init__(self, module_name: str, path: str = None, suggestion: str = None):
        message = f"Failed to load module '{module_name}'"
        if path:
            message += f"\nPath: {path}"
        if suggestion:
            message += f"\nSuggestion: {suggestion}"
        super().__init__(message)

class ValidationError(BuilderError):
    """Raised when validation fails with helpful context."""
    
    def __init__(self, message: str, context: dict = None):
        if context:
            formatted_context = format_error_with_context(message, context)
            super().__init__(formatted_context)
        else:
            super().__init__(message)
```

### Extending the Pattern to New Packages

**For each package, follow this proven structure:**

```python
# Package-specific base error
class PackageNameError(Exception):
    """Base exception for package-specific errors."""
    pass

# Specific error types with helpful constructors
class ConfigurationError(PackageNameError):
    """Configuration-related errors with context."""
    
    def __init__(self, message: str, config_key: str = None, 
                 current_value: Any = None, suggestion: str = None):
        formatted_message = message
        if config_key:
            formatted_message += f"\nConfiguration key: '{config_key}'"
        if current_value is not None:
            formatted_message += f"\nCurrent value: {current_value}"
        if suggestion:
            formatted_message += f"\nSuggestion: {suggestion}"
        super().__init__(formatted_message)

class ProcessingError(PackageNameError):
    """Processing-related errors with context."""
    
    def __init__(self, operation: str, details: str = None, 
                 input_data: Any = None):
        message = f"Failed during {operation}"
        if details:
            message += f": {details}"
        if input_data is not None:
            message += f"\nInput data: {repr(input_data)[:100]}..."  # Truncate long data
        super().__init__(message)
```

### Mixed Exception Strategy

**Use both standard and custom exceptions appropriately:**

```python
# Standard exceptions for common cases
raise FileNotFoundError(f"Configuration file '{config_path}' not found")
raise ValueError(f"Invalid N value: {n}. Must be between 1 and 64")
raise TypeError(f"Expected string formula, got {type(formula).__name__}")

# Custom exceptions for domain-specific cases
raise ValidationError(
    f"Formula '{formula}' contains invalid operator sequence",
    context={"formula": formula, "position": error_position}
)

# Guideline: Use standard exceptions when the error type is clear,
# custom exceptions when you need domain-specific context or handling
```

### Context Formatting Helper

**Build on the proven context formatting pattern:**

```python
# From builder/error_types.py - reuse this pattern
def format_error_with_context(message: str, context: dict) -> str:
    """Format error message with structured context information."""
    if not context:
        return message
    
    formatted = message
    for key, value in context.items():
        formatted += f"\n{key}: {value}"
    return formatted

# Usage in custom exceptions
class TheoryLoadError(PackageNameError):
    def __init__(self, theory_name: str, error_details: str, 
                 search_paths: List[str] = None):
        context = {
            "theory_name": theory_name,
            "error_details": error_details
        }
        if search_paths:
            context["search_paths"] = ", ".join(search_paths)
        
        message = f"Failed to load theory '{theory_name}'"
        formatted_message = format_error_with_context(message, context)
        super().__init__(formatted_message)
```

## Gradual Error Handling Improvement

### Opportunistic Enhancement

**Improve error handling when making other changes, don't retrofit everything at once:**

```python
# When fixing a bug or adding a feature, consider improving the error handling

# Before: Generic error
def load_theory(theory_name):
    try:
        module = importlib.import_module(f"theory_lib.{theory_name}")
        return module
    except ImportError:
        raise ValueError(f"Theory not found: {theory_name}")  # Not very helpful

# After: Enhanced error during other changes
def load_theory(theory_name):
    try:
        module = importlib.import_module(f"theory_lib.{theory_name}")
        return module
    except ImportError as e:
        # More helpful error with context
        available_theories = self._get_available_theories()
        suggestion = f"Available theories: {', '.join(available_theories)}"
        raise TheoryLoadError(
            theory_name=theory_name,
            error_details=str(e),
            suggestion=suggestion
        )
```

### Backward Compatibility

**When enhancing existing error handling, maintain compatibility:**

```python
# Enhance existing exceptions without breaking catching code
class ExistingError(Exception):
    """Keep existing interface working."""
    
    def __init__(self, message: str, additional_context: dict = None):
        # Old code: ExistingError("simple message") still works
        # New code: can use additional context
        if additional_context:
            formatted = format_error_with_context(message, additional_context)
            super().__init__(formatted)
        else:
            super().__init__(message)  # Original behavior
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

### Domain-Specific Error Patterns

#### Formula Validation Errors
**Provide clear guidance for logical formula problems:**

```python
class FormulaValidationError(PackageNameError):
    """Errors in logical formula syntax or semantics."""
    
    def __init__(self, formula: str, issue: str, suggestion: str = None,
                 position: int = None):
        message = f"Invalid formula: '{formula}'"
        
        context = {"issue": issue}
        if position is not None:
            context["position"] = f"character {position}"
        if suggestion:
            context["suggestion"] = suggestion
            
        formatted = format_error_with_context(message, context)
        super().__init__(formatted)

# Usage
def validate_formula(formula: str) -> None:
    """Validate formula syntax with helpful feedback."""
    if "∧" in formula or "∨" in formula:
        raise FormulaValidationError(
            formula=formula,
            issue="Unicode symbols not allowed in code",
            suggestion="Use LaTeX notation: '\\wedge' for ∧, '\\vee' for ∨"
        )
    
    if formula.count("(") != formula.count(")"):
        raise FormulaValidationError(
            formula=formula,
            issue=f"Unbalanced parentheses: {formula.count('(')} '(' and {formula.count(')')} ')'",
            suggestion="Check that every opening parenthesis has a matching closing parenthesis"
        )
```

#### Configuration Validation Errors
**Handle configuration problems with clear guidance:**

```python
class ConfigurationError(PackageNameError):
    """Configuration-related errors with helpful context."""
    
    def __init__(self, setting_name: str, current_value: Any, 
                 issue: str, valid_range: str = None):
        message = f"Invalid configuration for '{setting_name}'"
        
        context = {
            "current_value": current_value,
            "issue": issue
        }
        if valid_range:
            context["valid_range"] = valid_range
            
        formatted = format_error_with_context(message, context)
        super().__init__(formatted)

# Usage
def validate_settings(settings: dict) -> None:
    """Validate settings with helpful feedback."""
    if 'N' in settings:
        n = settings['N']
        if not isinstance(n, int) or n < 1 or n > 64:
            raise ConfigurationError(
                setting_name='N',
                current_value=n,
                issue="Must be an integer representing the number of atomic propositions",
                valid_range="1 to 64"
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

## Integration with Existing Error Handling

### Working with Current Patterns

**The ModelChecker codebase already has good error handling in many places - build on these:**

```python
# Example from existing codebase - preserve what works
try:
    result = z3_solver.check()
    if result == z3.unsat:
        return ModelResult.no_model()
    elif result == z3.unknown:
        return ModelResult.timeout()
    else:
        return ModelResult.success(z3_solver.model())
except z3.Z3Exception as e:
    # Good existing pattern - preserve and enhance if needed
    raise ModelCheckError(f"Z3 solver error: {e}")
```

### Migration Strategy

**Don't rewrite working error handling - enhance gradually:**

1. **New code:** Use the enhanced error patterns from the start
2. **Bug fixes:** Improve error handling when fixing issues in that area  
3. **Feature additions:** Apply better error patterns in new functionality
4. **Opportunistic improvement:** Enhance when convenient, not as separate projects

## Error Handling Anti-Patterns

### Avoid Over-Engineering

```python
# Avoid: Too many error types without clear benefit
class InvalidFormulaLengthError(FormulaError): pass
class InvalidFormulaCharacterError(FormulaError): pass  
class InvalidFormulaSpacingError(FormulaError): pass  # Too specific

# Prefer: Flexible errors with good context
class FormulaValidationError(PackageError):
    """Handles various formula validation issues with context."""
    pass
```

### Don't Hide Useful Information

```python
# Avoid: Generic re-raising that loses context
try:
    complex_operation()
except Exception:
    raise ValueError("Operation failed")  # Lost all the useful details!

# Prefer: Preserve context while adding helpful information
try:
    complex_operation()
except SpecificError as e:
    raise ProcessingError(
        operation="complex_operation",
        details=str(e),
        input_data=input_data  # Add helpful context
    ) from e  # Preserve original exception chain
```

## Success Patterns from ModelChecker

The codebase demonstrates several effective error handling approaches:

### Theory Loading
Good error messages for missing or invalid theories with suggestions for available alternatives.

### Formula Validation  
Clear feedback about syntax errors with specific guidance on correct LaTeX notation.

### Z3 Integration
Proper handling of Z3-specific errors with translation to domain-meaningful messages.

### Configuration Management
Helpful validation of settings with clear explanations of valid ranges and meanings.

## Conclusion

Effective error handling in the ModelChecker framework should:

1. **Build on proven patterns** from the builder/ package error hierarchy
2. **Provide helpful context** that assists users in understanding and fixing problems
3. **Maintain consistency** across packages while allowing domain-specific adaptations  
4. **Improve incrementally** rather than requiring wholesale rewrites
5. **Balance detail with clarity** - enough information to be helpful, not so much as to be overwhelming

These standards provide **flexible guidance** for creating user-friendly error handling without imposing rigid structures that don't fit the domain. Apply them **gradually and practically** as you work with the code, always prioritizing helpful user experiences over perfect theoretical consistency.

**Remember:** Good error handling helps users solve their problems and helps developers debug issues efficiently. These patterns support both goals without requiring massive changes to working code.

---

[← Code Organization](CODE_ORGANIZATION.md) | [Back to Maintenance](README.md) | [Performance Guidelines →](PERFORMANCE.md)