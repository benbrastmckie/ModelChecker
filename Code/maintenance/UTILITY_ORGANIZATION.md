# Utility Organization Standards

[← Architectural Patterns](ARCHITECTURAL_PATTERNS.md) | [Back to Maintenance](README.md) | [Testing Standards →](TESTING_STANDARDS.md)

## Overview

This document describes **flexible standards for organizing utility functions** in the ModelChecker framework. These guidelines build on the successful patterns established in the `utils/` package and the package-specific utilities like `builder/runner_utils.py`, providing guidance for maintaining clean, discoverable utility organization.

**Philosophy:** Utility organization should **support code reuse and discoverability** without creating rigid hierarchies. Utilities should be **easy to find, understand, and maintain** while serving the practical needs of the codebase.

## Existing Utility Organization Patterns

### Shared Utilities Structure

The ModelChecker framework has a well-organized shared utilities structure in `src/model_checker/utils/`:

```
utils/
├── __init__.py          # Clean exports organized by category
├── api.py              # Theory and example access functions
├── bitvector.py        # Bit vector operations for Z3
├── context.py          # Z3 context management utilities
├── formatting.py       # Output formatting helpers
├── parsing.py          # Expression parsing utilities  
├── testing.py          # Test execution and validation
├── version.py          # Version management utilities
└── z3_helpers.py       # Z3 wrapper and helper functions
```

**Key characteristics of this successful pattern:**
- **Categorical organization:** Each module focuses on a specific domain
- **Clear naming:** Module names clearly indicate their purpose
- **Clean exports:** `__init__.py` provides organized public API
- **Cross-package utility:** Functions serve multiple components

### Package-Specific Utilities

The builder/ package demonstrates effective use of package-specific utilities:

```python
# builder/runner_utils.py - Specialized utilities for runner operations
def format_model_output(model_structure, example_name, theory_name):
    """Format model output for display - specific to builder needs."""

def calculate_model_statistics(model_structure):
    """Calculate statistics specific to builder model processing."""

def validate_runner_state(runner_instance):
    """Validate runner state - builder-specific logic."""
```

**This pattern works well for:**
- Utilities that are specific to one package's needs
- Functions that are too specialized for shared utilities
- Helper functions extracted during refactoring (like from runner.py)

## Utility Organization Guidelines

### Shared vs Package-Specific Decision Matrix

**Use shared utilities (`src/model_checker/utils/`) when:**
- Function is used by multiple packages
- Utility provides core framework functionality (Z3 operations, parsing, etc.)
- Function is general-purpose within the domain (bitvector operations, context management)
- Utility could benefit other future packages

**Use package-specific utilities (`package/package_utils.py`) when:**
- Function is specific to one package's internal operations
- Utility contains domain logic specific to that package
- Function was extracted during package refactoring
- Utility requires package-specific imports or knowledge

### Naming Conventions

#### Shared Utility Modules
```python
# Domain-focused naming for shared utilities
api.py           # External API access functions
bitvector.py     # Bit vector operations
context.py       # Context management
formatting.py    # Output formatting
parsing.py       # Expression parsing
testing.py       # Test utilities
z3_helpers.py    # Z3 wrapper functions
```

#### Package-Specific Utility Modules
```python
# Package name + 'utils' for package-specific utilities
builder_utils.py      # Builder package utilities
runner_utils.py       # Runner-specific utilities (already exists)
output_utils.py       # Output package utilities
settings_utils.py     # Settings package utilities
```

#### Function Naming
```python
# Clear, descriptive function names
def format_z3_model_output(model, include_metadata=True):
    """Format Z3 model for display output."""

def validate_formula_syntax(formula, allow_unicode=False):  
    """Validate logical formula syntax."""

def extract_bitvector_values(model, variable_names):
    """Extract bitvector values from Z3 model."""
```

## Utility Creation Guidelines

### When to Extract Utilities

**Consider extracting utilities when you find:**

#### Repeated Code Patterns
```python
# Before: Repeated formatting logic
class ComponentA:
    def display_result(self, result):
        formatted = f"Result: {result.status}"
        if result.metadata:
            formatted += f" (metadata: {result.metadata})"
        return formatted

class ComponentB:
    def show_output(self, result):
        formatted = f"Result: {result.status}"  # Same pattern
        if result.metadata:
            formatted += f" (metadata: {result.metadata})"
        return formatted

# After: Extracted to utility
def format_result_display(result, include_metadata=True):
    """Format result for consistent display across components."""
    formatted = f"Result: {result.status}"
    if include_metadata and result.metadata:
        formatted += f" (metadata: {result.metadata})"
    return formatted
```

#### Complex Helper Logic
```python
# Extracted from builder/runner.py - good example
def validate_runner_state(runner_instance):
    """Validate that runner instance is in correct state for processing.
    
    This was extracted because it's complex logic that was making
    the main runner methods harder to read and test.
    """
    if not runner_instance.module:
        raise RunnerError("Runner module not loaded")
    
    if not runner_instance.semantic_theories:
        raise RunnerError("No semantic theories available")
        
    # More validation logic...
    return True
```

#### Cross-Package Functionality
```python
# Good candidate for shared utilities
def load_theory_configuration(theory_name, config_overrides=None):
    """Load theory configuration with optional overrides.
    
    This is used by builder, settings, and theory_lib packages,
    so it belongs in shared utilities.
    """
    base_config = load_default_theory_config(theory_name)
    if config_overrides:
        base_config.update(config_overrides)
    return base_config
```

### Utility Module Organization

#### Clean Export Patterns
```python
# utils/__init__.py - Organized exports
"""ModelChecker utilities package."""

# Theory and configuration utilities
from .api import get_theory, list_theories, load_example_data
from .settings import load_theory_config, validate_settings

# Z3 and solver utilities  
from .z3_helpers import create_solver_context, format_z3_model
from .bitvector import create_bitvector, extract_bitvector_values
from .context import Z3ContextManager

# Output and formatting utilities
from .formatting import format_model_output, format_error_message
from .parsing import parse_formula, validate_syntax

# Test utilities
from .testing import run_theory_tests, validate_example_set

__all__ = [
    # Theory utilities
    'get_theory', 'list_theories', 'load_example_data',
    'load_theory_config', 'validate_settings',
    
    # Z3 utilities
    'create_solver_context', 'format_z3_model', 
    'create_bitvector', 'extract_bitvector_values',
    'Z3ContextManager',
    
    # Output utilities
    'format_model_output', 'format_error_message',
    'parse_formula', 'validate_syntax',
    
    # Test utilities  
    'run_theory_tests', 'validate_example_set'
]
```

#### Module Documentation
```python
# utils/formatting.py
"""Output formatting utilities for ModelChecker.

This module provides consistent formatting functions for model output,
error messages, and other display elements across the framework.

Functions:
    format_model_output: Format Z3 model results for display
    format_error_message: Format error messages with consistent style
    format_theory_summary: Format theory information for display
"""

def format_model_output(model_structure, include_metadata=True):
    """Format model structure for consistent display.
    
    Args:
        model_structure: The model structure to format
        include_metadata: Whether to include metadata in output
        
    Returns:
        Formatted string representation of the model
        
    Example:
        >>> model = get_example_model()
        >>> formatted = format_model_output(model)
        >>> print(formatted)
        Model: satisfiable
        Variables: A=True, B=False
    """
    # Implementation...
```

## Integration Patterns

### Shared Utility Integration

**For shared utilities, follow the established import patterns:**

```python
# In package files, import from utils
from model_checker.utils import format_model_output, Z3ContextManager
from model_checker.utils.api import get_theory, list_theories

# Usage in package code
class ModelProcessor:
    def __init__(self):
        self.context_manager = Z3ContextManager()
    
    def format_result(self, result):
        return format_model_output(result, include_metadata=True)
```

### Package-Specific Utility Integration

**For package utilities, use relative imports:**

```python
# In package files
from .package_utils import specialized_function, PackageHelper

# Usage
class PackageComponent:
    def process_data(self, data):
        if not specialized_function(data):
            raise ValidationError("Data validation failed")
        return PackageHelper.process(data)
```

## Migration and Gradual Improvement

### Opportunistic Utility Extraction

**Extract utilities when making other changes:**

```python
# When refactoring a method, consider extracting reusable parts

# Before refactoring
def complex_processing_method(self, data):
    # 80 lines including some reusable formatting logic
    ...
    # Complex formatting that might be useful elsewhere
    formatted = f"Processing {data.type}: {data.status}"
    if data.metadata:
        for key, value in data.metadata.items():
            formatted += f"\n  {key}: {value}"
    ...

# After refactoring with utility extraction
def complex_processing_method(self, data):
    # Main processing logic remains here
    ...
    # Extracted formatting for reuse
    formatted = format_processing_status(data)
    ...

# New utility function (in appropriate utils module)
def format_processing_status(data, include_metadata=True):
    """Format processing status for consistent display."""
    formatted = f"Processing {data.type}: {data.status}"
    if include_metadata and data.metadata:
        for key, value in data.metadata.items():
            formatted += f"\n  {key}: {value}"
    return formatted
```

### Utility Migration Strategy

**Don't reorganize everything at once - improve gradually:**

1. **New utilities:** Follow these patterns from the start
2. **Extracted utilities:** Place appropriately based on scope (shared vs package-specific)
3. **Existing utilities:** Leave working utilities alone unless making related changes
4. **Consolidation:** Combine similar utilities only when convenient

## Testing Utility Functions

### Utility Testing Patterns

```python
# Test utilities separately for clarity
def test_format_model_output_basic():
    """Test basic model output formatting."""
    model = create_test_model(status="satisfiable", variables={"A": True})
    result = format_model_output(model)
    
    assert "satisfiable" in result
    assert "A=True" in result

def test_format_model_output_with_metadata():
    """Test model output formatting with metadata."""
    model = create_test_model(
        status="satisfiable", 
        variables={"A": True},
        metadata={"solver_time": "0.1s"}
    )
    result = format_model_output(model, include_metadata=True)
    
    assert "solver_time: 0.1s" in result
```

### Utility Documentation Testing

```python
def test_utility_documentation_examples():
    """Ensure that utility documentation examples work correctly."""
    # Test the examples from docstrings to keep them accurate
    model = get_example_model()  # From docstring example
    formatted = format_model_output(model)
    
    # Verify the example output structure
    assert "Model:" in formatted
    assert "Variables:" in formatted
```

## Anti-Patterns to Avoid

### Over-Abstraction
```python
# Avoid: Generic utilities that don't add value
def generic_processor(data, processor_type, config):
    """Too generic - doesn't help with understanding."""
    if processor_type == "type1":
        return process_type1(data, config)
    elif processor_type == "type2": 
        return process_type2(data, config)
    # Better to just call the specific functions directly
```

### Utility Sprawl
```python
# Avoid: Too many tiny utility functions
def add_one(x): return x + 1
def add_two(x): return x + 2  
def add_three(x): return x + 3  # Not helpful

# Prefer: Meaningful utility functions
def increment_model_counter(current_count, increment=1):
    """Increment model counter with bounds checking."""
    return max(0, current_count + increment)
```

### Circular Dependencies
```python
# Avoid: Utilities that import from packages that use them
# utils/helper.py
from model_checker.builder import SomeClass  # Creates circular dependency

# Prefer: Keep utilities independent or use dependency injection
def process_with_handler(data, handler=None):
    """Process data with optional handler injection."""
    handler = handler or default_handler
    return handler.process(data)
```

## Success Examples from ModelChecker

The current utility organization demonstrates several successful patterns:

### Domain-Focused Modules
- `z3_helpers.py` - Focused on Z3 integration utilities
- `bitvector.py` - Specialized bitvector operations
- `api.py` - Theory access and discovery functions

### Clean Package Integration
- Utilities are imported cleanly without circular dependencies
- Functions have clear, documented interfaces
- Shared utilities serve multiple packages effectively

### Practical Extraction
- `runner_utils.py` was created during refactoring to reduce method complexity
- Functions were extracted based on actual reuse needs, not theoretical organization

## Conclusion

Effective utility organization in the ModelChecker framework should:

1. **Build on the successful `utils/` package structure** for shared functionality
2. **Use package-specific utilities** for specialized needs that don't belong in shared utilities  
3. **Extract utilities opportunistically** during refactoring and development
4. **Maintain clean imports and exports** for discoverability
5. **Focus on practical reuse** rather than theoretical organization

These guidelines provide **flexible standards** that support code reuse and maintainability without requiring massive reorganization of working code. Apply them **gradually and practically** as you develop and refactor components.

**Remember:** Good utility organization makes code easier to find, understand, and reuse. These patterns support those goals while working with the existing, successful utility structures in the codebase.

---

[← Architectural Patterns](ARCHITECTURAL_PATTERNS.md) | [Back to Maintenance](README.md) | [Testing Standards →](TESTING_STANDARDS.md)