# Utility Organization and Management Standards

[← Back to Maintenance](../README.md) | [Packages →](PACKAGES.md) | [Iterator →](ITERATOR.md)

## Overview

This document provides **comprehensive standards for organizing and maintaining utility code** in the ModelChecker framework. These standards build on the successful patterns established in the `utils/` package and package-specific utilities, providing clear guidance for creating, organizing, and maintaining utility functions that support code reuse and discoverability.

**Philosophy:** Utility organization should **maximize code reuse and discoverability** while maintaining clear separation of concerns. Utilities should be **easy to find, understand, test, and maintain** with clear decision criteria for placement and organization.

## Shared Utility Standards

### Core Shared Utilities Structure

The ModelChecker framework maintains a well-organized shared utilities structure in `src/model_checker/utils/`:

```
utils/
├── __init__.py          # Clean exports organized by category
├── api.py               # Theory and example access functions
├── bitvector.py         # Bit vector operations for Z3
├── context.py           # Z3 context management utilities
├── formatting.py        # Output formatting helpers
├── parsing.py           # Expression parsing utilities  
├── testing.py           # Test execution and validation
├── version.py           # Version management utilities
└── z3_helpers.py        # Z3 wrapper and helper functions
```

### Shared Utility Standards

#### Domain Organization
```python
# Each module focuses on a specific domain with clear boundaries
api.py           # External API access and theory management
bitvector.py     # Bit vector operations and transformations
context.py       # Z3 context management and lifecycle
formatting.py    # Output formatting and display utilities
parsing.py       # Expression parsing and syntax validation
testing.py       # Test execution utilities and validation
z3_helpers.py    # Z3 wrapper functions and solver operations
```

#### Quality Standards for Shared Utilities
```python
# Example: High-quality shared utility function
def format_z3_model_output(model, include_metadata=True, format_style="standard"):
    """Format Z3 model for consistent display across the framework.
    
    This utility provides standardized model formatting used by multiple
    packages including builder, output, and interactive components.
    
    Args:
        model: Z3 model object to format
        include_metadata (bool): Whether to include solver metadata
        format_style (str): Format style - 'standard', 'compact', or 'verbose'
        
    Returns:
        str: Formatted model representation
        
    Raises:
        ValueError: If format_style is not recognized
        TypeError: If model is not a valid Z3 model
        
    Examples:
        >>> model = get_satisfiable_model()
        >>> formatted = format_z3_model_output(model)
        >>> print(formatted)
        Model: satisfiable
        Variables: A=True, B=False
        
        >>> compact = format_z3_model_output(model, format_style="compact")
        >>> print(compact)
        sat: A=T, B=F
    """
    if not is_valid_z3_model(model):
        raise TypeError("Expected valid Z3 model object")
    
    if format_style not in ["standard", "compact", "verbose"]:
        raise ValueError(f"Unknown format_style: {format_style}")
    
    # Implementation with clear error handling and edge cases
    return _format_model_by_style(model, include_metadata, format_style)
```

#### Export Organization Standards
```python
# utils/__init__.py - Organized exports with clear categories
"""ModelChecker utilities package.

This package provides shared utilities for common framework operations
including Z3 integration, formatting, parsing, and testing support.
"""

# Theory and configuration utilities
from .api import (
    get_theory, 
    list_theories, 
    load_example_data,
    discover_theory_modules
)

# Z3 and solver utilities  
from .z3_helpers import (
    create_solver_context, 
    format_z3_model,
    validate_z3_formula,
    extract_z3_statistics
)
from .bitvector import (
    create_bitvector, 
    extract_bitvector_values,
    convert_bitvector_format
)
from .context import Z3ContextManager, create_scoped_context

# Output and formatting utilities
from .formatting import (
    format_model_output, 
    format_error_message,
    format_theory_summary,
    format_performance_metrics
)
from .parsing import (
    parse_formula, 
    validate_syntax,
    extract_formula_variables,
    normalize_formula_representation
)

# Test utilities
from .testing import (
    run_theory_tests, 
    validate_example_set,
    create_test_context,
    assert_model_equivalence
)

__all__ = [
    # Theory utilities
    'get_theory', 'list_theories', 'load_example_data', 'discover_theory_modules',
    
    # Z3 utilities
    'create_solver_context', 'format_z3_model', 'validate_z3_formula', 'extract_z3_statistics',
    'create_bitvector', 'extract_bitvector_values', 'convert_bitvector_format',
    'Z3ContextManager', 'create_scoped_context',
    
    # Output utilities
    'format_model_output', 'format_error_message', 'format_theory_summary', 'format_performance_metrics',
    'parse_formula', 'validate_syntax', 'extract_formula_variables', 'normalize_formula_representation',
    
    # Test utilities  
    'run_theory_tests', 'validate_example_set', 'create_test_context', 'assert_model_equivalence'
]
```

## Package-Specific Utilities Guidance

### When to Use Package-Specific Utilities

**Use package-specific utilities (`package/package_utils.py`) when:**

1. **Domain-Specific Logic:** Function contains business logic specific to one package
2. **Internal Operations:** Utility supports internal package operations only
3. **Specialized Dependencies:** Function requires package-specific imports or knowledge
4. **Refactoring Extraction:** Utility was extracted during package refactoring to reduce complexity
5. **Performance Optimization:** Function needs package-specific optimization or caching

### Package-Specific Utility Standards

#### Naming and Organization
```python
# Package-specific utility module naming
builder_utils.py      # Builder package utilities
runner_utils.py       # Runner-specific utilities (existing)
output_utils.py       # Output package utilities  
settings_utils.py     # Settings package utilities
models_utils.py       # Models package utilities
iterate_utils.py      # Iterate package utilities
jupyter_utils.py      # Jupyter package utilities
```

#### Quality Standards for Package Utilities
```python
# Example: Well-structured package-specific utility
# builder/builder_utils.py

"""Builder package utilities.

This module provides utilities specific to model building operations,
including runner state validation, model statistics, and output formatting
optimized for builder workflows.
"""

from typing import Dict, Any, Optional, List
from ..models.base import ModelStructure
from ..utils.formatting import format_error_message  # Use shared when appropriate


def validate_runner_state(runner_instance) -> bool:
    """Validate that runner instance is in correct state for building.
    
    This utility performs builder-specific validation that includes
    checking semantic theories, module loading, and builder-specific
    configuration requirements.
    
    Args:
        runner_instance: Runner instance to validate
        
    Returns:
        bool: True if runner is ready for building operations
        
    Raises:
        RunnerError: If runner is in invalid state for building
        
    Note:
        This is package-specific because it includes builder workflow
        requirements that don't apply to other runner usage patterns.
    """
    if not runner_instance.module:
        raise RunnerError("Runner module not loaded for building")
    
    if not runner_instance.semantic_theories:
        raise RunnerError("No semantic theories available for model building")
    
    # Builder-specific validations
    if not hasattr(runner_instance, 'build_config'):
        raise RunnerError("Builder configuration not initialized")
        
    return True


def calculate_model_statistics(model_structure: ModelStructure) -> Dict[str, Any]:
    """Calculate statistics specific to builder model processing.
    
    Computes metrics that are relevant for builder operations including
    model complexity, satisfiability patterns, and building performance
    indicators.
    
    Args:
        model_structure: The model structure to analyze
        
    Returns:
        Dict containing builder-relevant statistics
        
    Examples:
        >>> model = create_test_model_structure()
        >>> stats = calculate_model_statistics(model)
        >>> print(stats['complexity_score'])
        7.5
    """
    stats = {
        'variable_count': len(model_structure.variables),
        'constraint_count': len(model_structure.constraints),
        'complexity_score': _calculate_builder_complexity(model_structure),
        'build_time_estimate': _estimate_build_time(model_structure),
        'memory_requirements': _estimate_memory_usage(model_structure)
    }
    
    return stats


def format_model_output(model_structure: ModelStructure, 
                       example_name: str, 
                       theory_name: str) -> str:
    """Format model output for builder-specific display needs.
    
    This formatting includes builder workflow context and is optimized
    for builder output requirements, which differ from general model
    formatting in the shared utilities.
    
    Args:
        model_structure: Model to format
        example_name: Name of the example being built
        theory_name: Name of the theory being used
        
    Returns:
        Formatted string optimized for builder workflows
    """
    # Builder-specific formatting that includes workflow context
    header = f"Building: {example_name} with {theory_name}"
    model_info = _format_builder_model_info(model_structure)
    progress_info = _format_builder_progress(model_structure)
    
    return f"{header}\n{model_info}\n{progress_info}"


# Private helper functions for internal package use
def _calculate_builder_complexity(model_structure: ModelStructure) -> float:
    """Calculate complexity score for builder operations."""
    # Implementation specific to builder needs
    pass


def _estimate_build_time(model_structure: ModelStructure) -> str:
    """Estimate build time based on model characteristics."""
    # Builder-specific estimation logic
    pass
```

## Utility Discovery Patterns

### Discoverability Standards

#### Clear Module Documentation
```python
# Each utility module must have comprehensive module docstring
"""Bitvector utilities for Z3 operations.

This module provides utilities for working with Z3 bitvector operations
including creation, manipulation, and extraction of bitvector values
from Z3 models.

Key Functions:
    create_bitvector: Create Z3 bitvector with specified width
    extract_bitvector_values: Extract values from Z3 model
    convert_bitvector_format: Convert between bitvector representations
    
Usage Patterns:
    # Basic bitvector creation
    bv = create_bitvector("var", 8, value=42)
    
    # Extract from model
    values = extract_bitvector_values(model, ["var1", "var2"])

Dependencies:
    - z3-solver: Core Z3 functionality
    - model_checker.utils.context: Context management
    
See Also:
    - z3_helpers.py: General Z3 wrapper functions
    - context.py: Z3 context management utilities
"""
```

#### Function Discovery Standards
```python
def discover_available_utilities(category: Optional[str] = None) -> Dict[str, List[str]]:
    """Discover available utility functions by category.
    
    Provides programmatic discovery of utility functions for development
    and documentation purposes.
    
    Args:
        category: Optional category filter ('z3', 'formatting', 'testing', etc.)
        
    Returns:
        Dict mapping categories to lists of available functions
        
    Examples:
        >>> utils = discover_available_utilities('formatting')
        >>> print(utils['formatting'])
        ['format_model_output', 'format_error_message', 'format_theory_summary']
    """
    utility_map = {
        'z3': _discover_z3_utilities(),
        'formatting': _discover_formatting_utilities(),
        'testing': _discover_testing_utilities(),
        'parsing': _discover_parsing_utilities(),
        'api': _discover_api_utilities()
    }
    
    if category:
        return {category: utility_map.get(category, [])}
    
    return utility_map
```

#### IDE Support Standards
```python
# Type hints for better IDE discovery
from typing import Union, Optional, Dict, List, Any, TypeVar, Generic
from z3 import ModelRef, ExprRef, SolverRef

ModelType = TypeVar('ModelType', bound=ModelRef)
ExprType = TypeVar('ExprType', bound=ExprRef)

def format_z3_expression(expr: ExprType, 
                        style: str = "standard",
                        unicode_symbols: bool = False) -> str:
    """Format Z3 expression with type safety and IDE support."""
    pass
```

## Dependency Management

### Dependency Standards for Utilities

#### Shared Utility Dependencies
```python
# Minimal external dependencies in shared utilities
# utils/z3_helpers.py

"""Z3 helper utilities with managed dependencies."""

import z3
from typing import Optional, Dict, Any, List
from contextlib import contextmanager

# Import from other utils modules is allowed
from .context import Z3ContextManager
from .formatting import format_error_message

# NO imports from package modules to avoid circular dependencies
# AVOID: from model_checker.builder import SomeClass


def create_solver_context(timeout: Optional[int] = None,
                         memory_limit: Optional[int] = None) -> z3.Solver:
    """Create Z3 solver with standard configuration.
    
    Dependencies:
        - z3-solver (external)
        - model_checker.utils.context (internal)
    """
    solver = z3.Solver()
    
    if timeout:
        solver.set("timeout", timeout)
    if memory_limit:
        solver.set("memory_max_mb", memory_limit)
    
    return solver
```

#### Package Utility Dependencies
```python
# Package utilities can import from their package and shared utils
# builder/builder_utils.py

"""Builder utilities with managed dependencies."""

# Package internal imports are allowed
from .base import BuilderBase
from .exceptions import BuilderError
from .config import BuilderConfig

# Shared utilities imports are encouraged
from model_checker.utils import format_error_message, Z3ContextManager
from model_checker.utils.z3_helpers import create_solver_context

# Cross-package imports should be minimal and well-justified
from model_checker.models.base import ModelStructure  # Core model interface


def create_builder_context(config: BuilderConfig) -> Z3ContextManager:
    """Create context manager optimized for builder operations."""
    base_context = Z3ContextManager()
    base_context.configure_for_building(config.solver_settings)
    return base_context
```

#### Dependency Injection Patterns
```python
# Support dependency injection for testing and flexibility
def process_model_with_solver(model_structure: ModelStructure,
                             solver_factory=None,
                             formatter=None) -> str:
    """Process model with injected dependencies for flexibility.
    
    Args:
        model_structure: Model to process
        solver_factory: Optional solver factory (default: create_solver_context)
        formatter: Optional formatter (default: format_model_output)
    """
    solver_factory = solver_factory or create_solver_context
    formatter = formatter or format_model_output
    
    solver = solver_factory()
    result = solver.check()
    return formatter(result)
```

## Utility Testing Requirements

### Testing Standards for Shared Utilities

#### Comprehensive Test Coverage
```python
# tests/utils/test_formatting.py

"""Comprehensive tests for formatting utilities."""

import pytest
from model_checker.utils.formatting import (
    format_model_output, 
    format_error_message,
    format_theory_summary
)
from tests.fixtures.models import create_test_model


class TestFormatModelOutput:
    """Test suite for model output formatting."""
    
    def test_format_satisfiable_model(self):
        """Test formatting of satisfiable model."""
        model = create_test_model(status="satisfiable", variables={"A": True, "B": False})
        result = format_model_output(model)
        
        assert "satisfiable" in result
        assert "A=True" in result
        assert "B=False" in result
    
    def test_format_unsatisfiable_model(self):
        """Test formatting of unsatisfiable model."""
        model = create_test_model(status="unsatisfiable")
        result = format_model_output(model)
        
        assert "unsatisfiable" in result
        assert "No solution found" in result
    
    def test_format_with_metadata(self):
        """Test formatting with metadata inclusion."""
        model = create_test_model(
            status="satisfiable",
            variables={"A": True},
            metadata={"solver_time": "0.1s", "memory_used": "2MB"}
        )
        result = format_model_output(model, include_metadata=True)
        
        assert "solver_time: 0.1s" in result
        assert "memory_used: 2MB" in result
    
    def test_format_without_metadata(self):
        """Test formatting without metadata."""
        model = create_test_model(
            status="satisfiable",
            variables={"A": True},
            metadata={"solver_time": "0.1s"}
        )
        result = format_model_output(model, include_metadata=False)
        
        assert "solver_time" not in result
    
    @pytest.mark.parametrize("style,expected", [
        ("standard", "Model: satisfiable"),
        ("compact", "sat"),
        ("verbose", "Model Status: satisfiable")
    ])
    def test_format_styles(self, style, expected):
        """Test different formatting styles."""
        model = create_test_model(status="satisfiable")
        result = format_model_output(model, format_style=style)
        assert expected in result
    
    def test_invalid_format_style(self):
        """Test error handling for invalid format style."""
        model = create_test_model(status="satisfiable")
        with pytest.raises(ValueError, match="Unknown format_style"):
            format_model_output(model, format_style="invalid")
    
    def test_invalid_model_type(self):
        """Test error handling for invalid model type."""
        with pytest.raises(TypeError, match="Expected valid Z3 model"):
            format_model_output("not a model")


class TestErrorHandling:
    """Test error handling in formatting utilities."""
    
    def test_format_error_message_with_context(self):
        """Test error message formatting with context."""
        error = ValueError("Test error")
        context = {"operation": "model_building", "theory": "test_theory"}
        
        result = format_error_message(error, context=context)
        
        assert "ValueError" in result
        assert "Test error" in result
        assert "operation: model_building" in result
        assert "theory: test_theory" in result
    
    def test_format_error_message_without_context(self):
        """Test error message formatting without context."""
        error = ValueError("Test error")
        result = format_error_message(error)
        
        assert "ValueError: Test error" in result


class TestPerformance:
    """Test performance characteristics of formatting utilities."""
    
    def test_large_model_formatting_performance(self):
        """Test formatting performance with large models."""
        import time
        
        large_model = create_test_model(
            status="satisfiable",
            variables={f"var_{i}": i % 2 == 0 for i in range(1000)}
        )
        
        start_time = time.time()
        result = format_model_output(large_model)
        end_time = time.time()
        
        # Should format large model in reasonable time
        assert (end_time - start_time) < 1.0  # Less than 1 second
        assert len(result) > 0


class TestDocumentationExamples:
    """Test that documentation examples work correctly."""
    
    def test_docstring_examples(self):
        """Test examples from function docstrings."""
        # Example from format_model_output docstring
        model = create_test_model(status="satisfiable", variables={"A": True, "B": False})
        formatted = format_model_output(model)
        
        # Verify the example output structure
        assert "Model:" in formatted
        assert "Variables:" in formatted
        assert "A=True" in formatted
        assert "B=False" in formatted
```

#### Testing Package-Specific Utilities
```python
# tests/builder/test_builder_utils.py

"""Tests for builder-specific utilities."""

import pytest
from unittest.mock import Mock, patch
from model_checker.builder.builder_utils import (
    validate_runner_state,
    calculate_model_statistics,
    format_model_output
)
from model_checker.builder.exceptions import RunnerError


class TestValidateRunnerState:
    """Test runner state validation."""
    
    def test_valid_runner_state(self):
        """Test validation with valid runner state."""
        runner = Mock()
        runner.module = Mock()
        runner.semantic_theories = [Mock()]
        runner.build_config = Mock()
        
        result = validate_runner_state(runner)
        assert result is True
    
    def test_missing_module(self):
        """Test validation with missing module."""
        runner = Mock()
        runner.module = None
        
        with pytest.raises(RunnerError, match="Runner module not loaded"):
            validate_runner_state(runner)
    
    def test_missing_semantic_theories(self):
        """Test validation with missing semantic theories."""
        runner = Mock()
        runner.module = Mock()
        runner.semantic_theories = []
        
        with pytest.raises(RunnerError, match="No semantic theories available"):
            validate_runner_state(runner)


class TestModelStatistics:
    """Test model statistics calculation."""
    
    def test_basic_statistics(self):
        """Test basic statistics calculation."""
        model_structure = Mock()
        model_structure.variables = ["A", "B", "C"]
        model_structure.constraints = ["A -> B", "B -> C"]
        
        with patch('model_checker.builder.builder_utils._calculate_builder_complexity', return_value=5.0):
            stats = calculate_model_statistics(model_structure)
        
        assert stats['variable_count'] == 3
        assert stats['constraint_count'] == 2
        assert stats['complexity_score'] == 5.0
        assert 'build_time_estimate' in stats
        assert 'memory_requirements' in stats


class TestIntegrationWithSharedUtils:
    """Test integration with shared utilities."""
    
    @patch('model_checker.utils.format_error_message')
    def test_uses_shared_error_formatting(self, mock_format_error):
        """Test that package utilities use shared formatting when appropriate."""
        mock_format_error.return_value = "Formatted error"
        
        # Test that package utilities call shared utilities correctly
        # Implementation depends on specific package utility usage
        pass
```

## Performance Considerations

### Performance Standards for Utilities

#### Lazy Loading and Caching
```python
# Implement lazy loading for expensive utilities
from functools import lru_cache
from typing import Optional
import threading


class UtilityCache:
    """Thread-safe caching for utility operations."""
    
    def __init__(self):
        self._cache = {}
        self._lock = threading.RLock()
    
    def get_or_compute(self, key: str, compute_func, *args, **kwargs):
        """Get cached result or compute and cache."""
        with self._lock:
            if key not in self._cache:
                self._cache[key] = compute_func(*args, **kwargs)
            return self._cache[key]


# Global cache instance
_utility_cache = UtilityCache()


@lru_cache(maxsize=128)
def parse_formula_cached(formula: str, allow_unicode: bool = False) -> 'ParsedFormula':
    """Parse formula with caching for repeated parsing operations.
    
    Performance: Caches parsed formulas to avoid re-parsing identical
    formulas across multiple operations.
    """
    return _parse_formula_implementation(formula, allow_unicode)


def load_theory_configuration(theory_name: str) -> Dict[str, Any]:
    """Load theory configuration with caching.
    
    Performance: Theory configurations are cached since they're frequently
    accessed but rarely change during execution.
    """
    cache_key = f"theory_config_{theory_name}"
    return _utility_cache.get_or_compute(
        cache_key, 
        _load_theory_config_implementation, 
        theory_name
    )
```

#### Memory Management
```python
def process_large_model_efficiently(model_structure: 'ModelStructure',
                                  chunk_size: int = 1000) -> Iterator[str]:
    """Process large models in chunks to manage memory usage.
    
    Performance: Yields formatted chunks instead of building large
    strings in memory.
    """
    variables = model_structure.variables
    
    for i in range(0, len(variables), chunk_size):
        chunk = variables[i:i + chunk_size]
        yield format_variable_chunk(chunk)


def format_model_output_streaming(model_structure: 'ModelStructure') -> Iterator[str]:
    """Stream model output formatting for large models.
    
    Performance: Generates output incrementally to avoid memory pressure
    with very large models.
    """
    yield format_model_header(model_structure)
    
    for variable_chunk in process_large_model_efficiently(model_structure):
        yield variable_chunk
    
    yield format_model_footer(model_structure)
```

#### Performance Monitoring
```python
import time
import functools
from typing import Callable, Any


def monitor_performance(threshold_seconds: float = 1.0):
    """Decorator to monitor utility function performance.
    
    Args:
        threshold_seconds: Log warning if execution exceeds this time
    """
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args, **kwargs) -> Any:
            start_time = time.time()
            try:
                result = func(*args, **kwargs)
                return result
            finally:
                execution_time = time.time() - start_time
                if execution_time > threshold_seconds:
                    import logging
                    logging.warning(
                        f"Utility function {func.__name__} took {execution_time:.2f}s "
                        f"(threshold: {threshold_seconds}s)"
                    )
        return wrapper
    return decorator


@monitor_performance(threshold_seconds=0.5)
def format_complex_model_output(model_structure: 'ModelStructure') -> str:
    """Format complex model with performance monitoring."""
    # Implementation with automatic performance monitoring
    pass
```

## Documentation Requirements for Utilities

### Documentation Standards

#### Function Documentation Template
```python
def utility_function_template(param1: Type1, 
                            param2: Type2 = default_value,
                            optional_param: Optional[Type3] = None) -> ReturnType:
    """One-line summary of what the function does.
    
    More detailed description explaining the purpose, use cases, and
    any important behaviors or constraints. Include information about
    when to use this utility vs alternatives.
    
    Args:
        param1: Description of first parameter including valid values
        param2: Description with default behavior explanation
        optional_param: Description of optional parameter and None behavior
        
    Returns:
        Description of return value including type and format details
        
    Raises:
        ExceptionType1: When this exception occurs
        ExceptionType2: When this other exception occurs
        
    Examples:
        Basic usage:
        >>> result = utility_function_template("value1", "value2")
        >>> print(result)
        Expected output
        
        Advanced usage:
        >>> result = utility_function_template("value1", optional_param="custom")
        >>> print(result)
        Different output
        
    Performance:
        O(n) time complexity where n is the number of items
        Uses caching for repeated calls with same parameters
        
    See Also:
        related_utility_function: Similar functionality for different use case
        AlternativeClass.method: Alternative approach using class method
        
    Notes:
        Any special considerations, limitations, or warnings
        Cross-package usage notes if applicable
    """
    # Implementation with clear error handling
    if param1 is None:
        raise ValueError("param1 cannot be None")
    
    # Clear implementation with comments for complex logic
    result = _process_param1(param1)
    
    if optional_param:
        result = _apply_optional_processing(result, optional_param)
    
    return result
```

#### Module Documentation Standards
```python
"""Module name and purpose.

This module provides [category] utilities for [specific domain] operations
within the ModelChecker framework. The utilities in this module are designed
for [use case description] and follow [relevant patterns or standards].

Key Features:
    - Feature 1: Brief description
    - Feature 2: Brief description
    - Feature 3: Brief description

Common Usage Patterns:
    Basic pattern:
        from model_checker.utils.module_name import main_function
        result = main_function(data)
    
    Advanced pattern:
        from model_checker.utils.module_name import AdvancedClass
        processor = AdvancedClass(config)
        result = processor.process(data)

Performance Characteristics:
    - Time complexity: O(n) for most operations
    - Memory usage: Linear with input size
    - Caching: Automatic caching for expensive operations

Dependencies:
    External:
        - z3-solver: Core solver functionality
        - typing: Type annotations
    
    Internal:
        - model_checker.utils.context: Context management
        - model_checker.models.base: Base model interfaces

Thread Safety:
    - All functions are thread-safe unless noted
    - UtilityClass instances are NOT thread-safe
    - Use separate instances for concurrent access

Examples:
    See individual function documentation for detailed examples.
    
See Also:
    - related_module.py: Related functionality
    - ../package/module.py: Package-specific alternatives
    
Notes:
    Any module-level warnings, limitations, or special considerations.
"""
```

## Decision Criteria for Utility Placement

### Clear Decision Framework

#### Shared vs Package-Specific Decision Tree
```
Is the utility function used by multiple packages?
├── YES: Is it core framework functionality?
│   ├── YES: Place in shared utils/ with appropriate module
│   └── NO: Evaluate reuse potential
│       ├── HIGH potential: Place in shared utils/
│       └── LOW potential: Keep package-specific, document for potential promotion
└── NO: Is it specific to package domain logic?
    ├── YES: Place in package-specific utils
    └── NO: Evaluate if it should be shared
        ├── General-purpose: Consider for shared utils/
        └── Specialized: Keep package-specific
```

#### Detailed Decision Criteria

**Place in Shared Utils (`src/model_checker/utils/`) when:**

1. **Multi-Package Usage:** Function is currently used by 2+ packages
2. **Core Framework:** Provides core functionality (Z3 operations, parsing, etc.)
3. **General Purpose:** Function is general-purpose within the domain
4. **API Stability:** Function interface is stable and unlikely to change frequently
5. **Independence:** Function doesn't require package-specific knowledge
6. **Future Utility:** Clear potential for future cross-package usage

**Place in Package-Specific Utils (`package/package_utils.py`) when:**

1. **Single Package:** Function is used only within one package
2. **Domain-Specific:** Contains business logic specific to package domain
3. **Specialized Dependencies:** Requires package-specific imports or configuration
4. **Rapid Evolution:** Function interface may change as package evolves
5. **Internal Operations:** Supports internal package operations only
6. **Performance Optimization:** Optimized for specific package usage patterns

**Decision Examples:**
```python
# SHARED UTILITY: Used by multiple packages for Z3 operations
def create_solver_context(timeout=None) -> z3.Solver:
    """Used by builder, models, iterate packages."""

# SHARED UTILITY: General-purpose parsing used across framework  
def parse_formula(formula_str: str) -> ParsedFormula:
    """Used by syntactic, builder, jupyter packages."""

# PACKAGE-SPECIFIC: Builder workflow optimization
def format_model_output(model, example_name, theory_name) -> str:
    """Specific to builder package display needs."""

# PACKAGE-SPECIFIC: Iterator-specific state management
def validate_iteration_state(iterator_instance) -> bool:
    """Specific to iterate package operations."""
```

## Naming Conventions

### Comprehensive Naming Standards

#### Module Naming
```python
# Shared utility modules: domain-focused names
api.py               # External API and theory access
bitvector.py         # Bit vector operations  
context.py           # Context management
formatting.py        # Output formatting
parsing.py           # Expression parsing
testing.py           # Test utilities
z3_helpers.py        # Z3 wrapper functions
performance.py       # Performance monitoring utilities
validation.py        # General validation utilities

# Package-specific modules: package_name + utils
builder_utils.py     # Builder package utilities
runner_utils.py      # Runner utilities (existing)
output_utils.py      # Output package utilities
settings_utils.py    # Settings package utilities
models_utils.py      # Models package utilities
iterate_utils.py     # Iterate package utilities
jupyter_utils.py     # Jupyter package utilities
```

#### Function Naming Patterns
```python
# Action-oriented naming with clear intent
def create_solver_context() -> z3.Solver:
    """Create: Instantiate new objects."""

def format_model_output(model) -> str:
    """Format: Transform for display."""

def validate_formula_syntax(formula) -> bool:
    """Validate: Check correctness/validity."""

def extract_bitvector_values(model, variables) -> Dict:
    """Extract: Get specific data from complex structures."""

def calculate_model_statistics(model) -> Dict:
    """Calculate: Compute derived metrics."""

def parse_logical_expression(expr_str) -> ParsedExpression:
    """Parse: Convert string representation to structured data."""

def load_theory_configuration(theory_name) -> Dict:
    """Load: Read and initialize from external sources."""

def discover_available_theories() -> List[str]:
    """Discover: Find and list available items."""
```

#### Class Naming for Utility Classes
```python
# Utility classes: descriptive names ending in appropriate suffixes
class Z3ContextManager:
    """Manager: Handles lifecycle and state."""

class FormulaParser:
    """Parser: Converts between representations."""

class ModelStatisticsCalculator:
    """Calculator: Computes derived values."""

class PerformanceMonitor:
    """Monitor: Tracks and reports metrics."""

class ConfigurationLoader:
    """Loader: Reads and initializes data."""

class ValidationRunner:
    """Runner: Executes operations or processes."""
```

#### Constant and Configuration Naming
```python
# Constants: ALL_CAPS with descriptive names
DEFAULT_SOLVER_TIMEOUT = 30000  # milliseconds
MAX_MODEL_VARIABLES = 10000
SUPPORTED_Z3_VERSIONS = ["4.8.0", "4.8.1", "4.9.0"]
CACHE_SIZE_LIMIT = 128
PERFORMANCE_WARNING_THRESHOLD = 1.0  # seconds

# Configuration keys: descriptive strings
CONFIG_KEYS = {
    'solver_timeout': 'solver_timeout_ms',
    'memory_limit': 'memory_limit_mb', 
    'unicode_support': 'allow_unicode_symbols',
    'cache_enabled': 'enable_result_caching'
}
```

## Success Metrics for Utility Reuse

### Quantitative Metrics

#### Usage Metrics
```python
# Track utility usage across the codebase
def measure_utility_usage():
    """Measure how frequently utilities are used."""
    return {
        'function_call_frequency': {
            'format_model_output': 45,  # calls per week
            'create_solver_context': 78,
            'parse_formula': 23,
            'validate_syntax': 34
        },
        'cross_package_usage': {
            'format_model_output': ['builder', 'output', 'jupyter'],
            'create_solver_context': ['builder', 'models', 'iterate'],
            'parse_formula': ['syntactic', 'builder', 'jupyter']
        },
        'reuse_ratio': 0.73  # Percentage of utilities used by 2+ packages
    }
```

#### Code Quality Metrics
```python
def measure_code_quality_improvement():
    """Measure code quality improvements from utility usage."""
    return {
        'duplicate_code_reduction': {
            'before_utilities': 234,  # lines of duplicate code
            'after_utilities': 67,   # lines of remaining duplicates
            'improvement': 71.4      # percentage reduction
        },
        'function_complexity_reduction': {
            'average_complexity_before': 8.5,
            'average_complexity_after': 5.2,
            'improvement': 38.8  # percentage reduction
        },
        'test_coverage': {
            'utility_functions': 94.2,  # percentage covered
            'utility_integration': 87.6  # integration test coverage
        }
    }
```

### Qualitative Success Indicators

#### Developer Experience Metrics
```python
def assess_developer_experience():
    """Assess impact on developer experience."""
    return {
        'discoverability': {
            'time_to_find_utility': 2.3,  # minutes average
            'ide_autocomplete_success': 0.89,  # success rate
            'documentation_completeness': 0.92  # percentage complete
        },
        'ease_of_use': {
            'api_consistency_score': 0.87,  # 0-1 scale
            'parameter_clarity': 0.91,
            'error_message_quality': 0.84
        },
        'maintenance_burden': {
            'breaking_changes_per_month': 0.2,
            'bug_reports_per_utility': 0.15,
            'documentation_update_frequency': 0.95  # percentage up-to-date
        }
    }
```

#### Success Thresholds
```python
SUCCESS_THRESHOLDS = {
    'minimum_reuse_ratio': 0.60,        # 60% of utilities used by 2+ packages
    'maximum_duplicate_lines': 100,      # Less than 100 lines of duplicates
    'minimum_test_coverage': 0.85,       # 85% test coverage for utilities
    'maximum_discovery_time': 5.0,       # 5 minutes to find needed utility
    'minimum_documentation_score': 0.80, # 80% documentation completeness
    'maximum_bug_rate': 0.25             # Less than 0.25 bugs per utility
}

def evaluate_utility_success(metrics: Dict) -> Dict[str, bool]:
    """Evaluate whether utility organization meets success criteria."""
    return {
        'reuse_success': metrics['reuse_ratio'] >= SUCCESS_THRESHOLDS['minimum_reuse_ratio'],
        'quality_success': metrics['duplicate_lines'] <= SUCCESS_THRESHOLDS['maximum_duplicate_lines'],
        'testing_success': metrics['test_coverage'] >= SUCCESS_THRESHOLDS['minimum_test_coverage'],
        'discoverability_success': metrics['discovery_time'] <= SUCCESS_THRESHOLDS['maximum_discovery_time'],
        'documentation_success': metrics['doc_score'] >= SUCCESS_THRESHOLDS['minimum_documentation_score'],
        'reliability_success': metrics['bug_rate'] <= SUCCESS_THRESHOLDS['maximum_bug_rate']
    }
```

## Refactoring Guidance

### Utility Extraction Refactoring

#### Systematic Extraction Process
```python
# Step 1: Identify extraction candidates during code review
def identify_extraction_candidates(file_path: str) -> List[Dict]:
    """Identify potential utility extraction opportunities."""
    candidates = []
    
    # Look for repeated code patterns
    repeated_patterns = find_repeated_code_patterns(file_path)
    for pattern in repeated_patterns:
        if pattern['frequency'] >= 3 and pattern['complexity'] >= 5:
            candidates.append({
                'type': 'repeated_pattern',
                'pattern': pattern,
                'priority': calculate_extraction_priority(pattern)
            })
    
    # Look for complex helper methods
    complex_helpers = find_complex_private_methods(file_path)
    for helper in complex_helpers:
        if helper['lines'] >= 20 or helper['complexity'] >= 7:
            candidates.append({
                'type': 'complex_helper',
                'method': helper,
                'priority': calculate_extraction_priority(helper)
            })
    
    return sorted(candidates, key=lambda x: x['priority'], reverse=True)


# Step 2: Extract utilities with proper placement
def extract_utility_function(original_code: str, 
                           function_name: str,
                           target_location: str) -> Dict:
    """Extract utility function to appropriate location."""
    extraction_result = {
        'extracted_function': generate_utility_function(original_code, function_name),
        'updated_original': replace_with_utility_call(original_code, function_name),
        'import_statement': generate_import_statement(target_location, function_name),
        'tests_needed': generate_test_requirements(function_name),
        'documentation_needed': generate_doc_requirements(function_name)
    }
    
    return extraction_result
```

#### Refactoring Examples

**Before: Repeated formatting logic**
```python
# Multiple files with similar code
# builder/runner.py
class ModelRunner:
    def display_result(self, result):
        formatted = f"Result: {result.status}"
        if result.metadata:
            formatted += f" | Time: {result.metadata.get('time', 'unknown')}"
            formatted += f" | Memory: {result.metadata.get('memory', 'unknown')}"
        return formatted

# output/formatter.py  
class OutputFormatter:
    def format_model_result(self, result):
        output = f"Result: {result.status}"  # Same pattern!
        if result.metadata:
            output += f" | Time: {result.metadata.get('time', 'unknown')}"
            output += f" | Memory: {result.metadata.get('memory', 'unknown')}"
        return output
```

**After: Extracted shared utility**
```python
# utils/formatting.py - NEW SHARED UTILITY
def format_result_with_metadata(result, include_metadata=True):
    """Format result with optional metadata display.
    
    Provides consistent result formatting across packages including
    status display and optional performance metadata.
    """
    formatted = f"Result: {result.status}"
    
    if include_metadata and result.metadata:
        time_info = result.metadata.get('time', 'unknown')
        memory_info = result.metadata.get('memory', 'unknown')
        formatted += f" | Time: {time_info} | Memory: {memory_info}"
    
    return formatted

# builder/runner.py - UPDATED TO USE UTILITY
from model_checker.utils.formatting import format_result_with_metadata

class ModelRunner:
    def display_result(self, result):
        return format_result_with_metadata(result, include_metadata=True)

# output/formatter.py - UPDATED TO USE UTILITY  
from model_checker.utils.formatting import format_result_with_metadata

class OutputFormatter:
    def format_model_result(self, result):
        return format_result_with_metadata(result, include_metadata=True)
```

### Migration Strategy for Existing Code

#### Gradual Migration Approach
```python
# Phase 1: New code uses utility standards immediately
def implement_new_feature_with_utilities():
    """New features follow utility standards from the start."""
    # Use existing shared utilities
    from model_checker.utils import format_model_output, create_solver_context
    
    # Create new package-specific utilities as needed
    from .feature_utils import validate_feature_state, process_feature_data
    
    # Implementation using proper utility patterns
    pass

# Phase 2: Opportunistic refactoring during maintenance
def refactor_during_maintenance(existing_method):
    """Refactor existing code when making other changes."""
    # When touching existing code, look for extraction opportunities
    candidates = identify_extraction_candidates(existing_method)
    
    if candidates and any(c['priority'] > 7 for c in candidates):
        # Extract high-priority utilities while making other changes
        extract_utilities(candidates)
    
    # Continue with original maintenance task
    return updated_method

# Phase 3: Systematic refactoring of utility-heavy areas
def systematic_utility_refactoring():
    """Systematic refactoring of areas with high utility potential."""
    high_utility_areas = [
        'model_processing',  # Lots of formatting and validation
        'error_handling',    # Repeated error formatting patterns  
        'test_helpers',      # Common test setup and validation
        'configuration'      # Configuration loading and validation
    ]
    
    for area in high_utility_areas:
        analyze_and_extract_utilities(area)
```

#### Backward Compatibility During Migration
```python
# Maintain backward compatibility during utility migration
# old_module.py - DEPRECATED BUT MAINTAINED
"""DEPRECATED: Use model_checker.utils.formatting instead.

This module is maintained for backward compatibility but will be
removed in version 2.0. Please migrate to the new utilities.
"""

import warnings
from model_checker.utils.formatting import format_model_output as _new_format_model_output

def format_model_output(*args, **kwargs):
    """DEPRECATED: Use model_checker.utils.formatting.format_model_output."""
    warnings.warn(
        "old_module.format_model_output is deprecated. "
        "Use model_checker.utils.formatting.format_model_output instead.",
        DeprecationWarning,
        stacklevel=2
    )
    return _new_format_model_output(*args, **kwargs)
```

## Shared vs Package-Specific Decision Framework

### Detailed Decision Matrix

| Factor | Shared Utils | Package-Specific | Decision Weight |
|--------|-------------|------------------|-----------------|
| **Current Usage** | 2+ packages | 1 package | High |
| **Future Potential** | High reuse likely | Low reuse likely | Medium |
| **Domain Specificity** | General purpose | Domain specific | High |
| **Dependencies** | Framework only | Package specific | Medium |
| **Stability** | Stable interface | Evolving interface | Medium |
| **Complexity** | Simple/moderate | Any complexity | Low |

### Decision Algorithm
```python
def decide_utility_placement(utility_info: Dict) -> str:
    """Algorithmic decision for utility placement.
    
    Args:
        utility_info: Dictionary with utility characteristics
        
    Returns:
        'shared' or 'package_specific'
    """
    score = 0
    
    # Current usage (high weight)
    if utility_info['current_packages'] >= 2:
        score += 3
    
    # Future potential (medium weight)  
    if utility_info['reuse_potential'] == 'high':
        score += 2
    elif utility_info['reuse_potential'] == 'medium':
        score += 1
    
    # Domain specificity (high weight, negative)
    if utility_info['domain_specific']:
        score -= 3
    
    # Dependencies (medium weight, negative)
    if utility_info['package_dependencies']:
        score -= 2
    
    # Interface stability (medium weight)
    if utility_info['stable_interface']:
        score += 2
    
    # Decision threshold
    return 'shared' if score >= 2 else 'package_specific'

# Example usage
utility_characteristics = {
    'current_packages': 3,           # Used by 3 packages
    'reuse_potential': 'high',       # High future reuse potential
    'domain_specific': False,        # General purpose
    'package_dependencies': False,   # No package-specific dependencies
    'stable_interface': True         # Stable API
}

placement = decide_utility_placement(utility_characteristics)
# Result: 'shared' (score = 3 + 2 - 0 - 0 + 2 = 7)
```

## Examples of Good Utility Design

### Exemplary Shared Utility Design
```python
# utils/z3_helpers.py - Excellent shared utility example
"""Z3 helper utilities providing clean abstractions over Z3 operations.

This module demonstrates excellent utility design with clear interfaces,
comprehensive error handling, and broad applicability across packages.
"""

from typing import Optional, Dict, Any, List, Union
import z3
from contextlib import contextmanager

from .context import Z3ContextManager
from .formatting import format_error_message


def create_solver_context(timeout: Optional[int] = None,
                         memory_limit: Optional[int] = None,
                         logic: str = "ALL") -> z3.Solver:
    """Create Z3 solver with standardized configuration.
    
    This utility provides a consistent way to create Z3 solvers across
    all packages, ensuring proper configuration and resource limits.
    
    Args:
        timeout: Solver timeout in milliseconds (default: 30000)
        memory_limit: Memory limit in MB (default: 512) 
        logic: Z3 logic to use (default: "ALL")
        
    Returns:
        Configured Z3 solver instance
        
    Raises:
        ValueError: If timeout or memory_limit are invalid
        Z3Exception: If logic is not supported
        
    Examples:
        Basic usage:
        >>> solver = create_solver_context()
        >>> solver.add(z3.Bool('A'))
        >>> result = solver.check()
        
        With custom configuration:
        >>> solver = create_solver_context(timeout=60000, memory_limit=1024)
        >>> # Use for complex problems requiring more resources
        
    Performance:
        - Creation time: O(1)
        - Memory overhead: ~10MB base + configured limit
        - Thread-safe: Yes (creates independent instances)
    """
    if timeout is not None and timeout <= 0:
        raise ValueError("Timeout must be positive")
    if memory_limit is not None and memory_limit <= 0:
        raise ValueError("Memory limit must be positive")
    
    try:
        solver = z3.Solver()
        solver.set("timeout", timeout or 30000)
        solver.set("memory_max_mb", memory_limit or 512)
        
        if logic != "ALL":
            solver.set("logic", logic)
            
        return solver
        
    except z3.Z3Exception as e:
        raise z3.Z3Exception(f"Failed to create solver with logic '{logic}': {e}")


@contextmanager
def scoped_solver_context(**solver_kwargs):
    """Context manager for scoped Z3 solver usage.
    
    Provides automatic cleanup and resource management for Z3 solvers,
    ensuring proper disposal even when exceptions occur.
    
    Args:
        **solver_kwargs: Arguments passed to create_solver_context
        
    Yields:
        Configured Z3 solver instance
        
    Examples:
        >>> with scoped_solver_context(timeout=10000) as solver:
        ...     solver.add(some_constraint)
        ...     result = solver.check()
        # Solver automatically cleaned up here
    """
    solver = create_solver_context(**solver_kwargs)
    try:
        yield solver
    finally:
        # Explicit cleanup for resource management
        solver.reset()


def extract_model_values(model: z3.ModelRef, 
                        variables: List[Union[str, z3.ExprRef]]) -> Dict[str, Any]:
    """Extract variable values from Z3 model with type conversion.
    
    Provides standardized value extraction with proper type conversion
    and error handling for different Z3 data types.
    
    Args:
        model: Z3 model to extract values from
        variables: List of variable names or Z3 expressions
        
    Returns:
        Dictionary mapping variable names to Python values
        
    Raises:
        TypeError: If model is not a valid Z3 model
        ValueError: If variable is not found in model
        
    Examples:
        >>> variables = ['A', 'B', 'count']
        >>> values = extract_model_values(model, variables)
        >>> print(values)
        {'A': True, 'B': False, 'count': 42}
    """
    if not isinstance(model, z3.ModelRef):
        raise TypeError("Expected Z3 ModelRef")
    
    result = {}
    
    for var in variables:
        try:
            if isinstance(var, str):
                # Find variable by name in model
                z3_var = _find_variable_by_name(model, var)
            else:
                z3_var = var
                
            if z3_var is None:
                raise ValueError(f"Variable '{var}' not found in model")
                
            # Extract and convert value
            z3_value = model[z3_var]
            python_value = _convert_z3_value_to_python(z3_value)
            
            var_name = str(var) if isinstance(var, str) else str(z3_var)
            result[var_name] = python_value
            
        except Exception as e:
            error_msg = f"Failed to extract value for variable '{var}': {e}"
            raise ValueError(error_msg) from e
    
    return result


# Private helper functions - clear separation of concerns
def _find_variable_by_name(model: z3.ModelRef, name: str) -> Optional[z3.ExprRef]:
    """Find Z3 variable by name in model."""
    for decl in model.decls():
        if decl.name() == name:
            return decl()
    return None


def _convert_z3_value_to_python(z3_value) -> Any:
    """Convert Z3 value to appropriate Python type."""
    if z3.is_bool(z3_value):
        return z3.is_true(z3_value)
    elif z3.is_int_value(z3_value):
        return z3_value.as_long()
    elif z3.is_real_value(z3_value):
        return float(z3_value.as_decimal(10))
    elif z3.is_bv_value(z3_value):
        return z3_value.as_long()
    else:
        return str(z3_value)
```

### Exemplary Package-Specific Utility Design
```python
# builder/builder_utils.py - Excellent package-specific utility example
"""Builder-specific utilities for model construction workflows.

This module provides utilities specialized for builder package operations,
including runner state validation, build optimization, and builder-specific
output formatting that integrates with the builder workflow.
"""

from typing import Dict, Any, List, Optional, Tuple
import time
from functools import lru_cache

from .exceptions import BuilderError, RunnerError
from .config import BuilderConfig
from ..models.base import ModelStructure
from ..utils.formatting import format_error_message  # Use shared where appropriate
from ..utils.performance import monitor_performance


@monitor_performance(threshold_seconds=0.1)
def validate_runner_state(runner_instance, strict_mode: bool = False) -> bool:
    """Validate runner state for builder operations.
    
    Performs builder-specific validation that ensures runner is properly
    configured for model building workflows. This includes checks that
    are specific to builder requirements and may differ from general
    runner validation.
    
    Args:
        runner_instance: Runner instance to validate
        strict_mode: Enable additional validation checks
        
    Returns:
        True if runner is ready for building operations
        
    Raises:
        RunnerError: If runner is in invalid state for building
        BuilderError: If builder-specific requirements are not met
        
    Examples:
        >>> runner = create_test_runner()
        >>> is_valid = validate_runner_state(runner)
        >>> assert is_valid == True
        
        >>> validate_runner_state(runner, strict_mode=True)
        # Performs additional validations
    """
    # Basic runner validation
    if not runner_instance.module:
        raise RunnerError("Runner module not loaded for building operations")
    
    if not runner_instance.semantic_theories:
        raise RunnerError("No semantic theories available for model building")
    
    # Builder-specific validations
    if not hasattr(runner_instance, 'build_config'):
        raise BuilderError("Builder configuration not initialized on runner")
    
    if strict_mode:
        _validate_runner_state_strict(runner_instance)
    
    return True


def calculate_build_complexity(model_structure: ModelStructure,
                             theory_name: str) -> Dict[str, Any]:
    """Calculate complexity metrics for build optimization.
    
    Computes builder-specific complexity metrics used for optimizing
    build strategies, resource allocation, and performance estimation.
    
    Args:
        model_structure: Model structure to analyze
        theory_name: Theory being used for building
        
    Returns:
        Dictionary with complexity metrics and build recommendations
        
    Examples:
        >>> model = create_test_model()
        >>> complexity = calculate_build_complexity(model, "classical_logic")
        >>> print(complexity['estimated_build_time'])
        3.2  # seconds
    """
    base_complexity = _calculate_base_complexity(model_structure)
    theory_complexity = _get_theory_complexity_multiplier(theory_name)
    
    # Builder-specific complexity factors
    builder_factors = _calculate_builder_specific_factors(model_structure)
    
    total_complexity = base_complexity * theory_complexity * builder_factors
    
    return {
        'base_complexity': base_complexity,
        'theory_multiplier': theory_complexity,
        'builder_factors': builder_factors,
        'total_complexity': total_complexity,
        'estimated_build_time': _estimate_build_time(total_complexity),
        'memory_requirements': _estimate_memory_requirements(model_structure),
        'recommended_strategy': _recommend_build_strategy(total_complexity),
        'parallelization_potential': _assess_parallelization(model_structure)
    }


def optimize_build_sequence(models: List[ModelStructure],
                          available_resources: Dict[str, Any]) -> List[Tuple[ModelStructure, Dict]]:
    """Optimize build sequence for multiple models.
    
    Determines optimal build order and resource allocation for multiple
    models to maximize throughput and minimize total build time.
    
    Args:
        models: List of model structures to build
        available_resources: Available computational resources
        
    Returns:
        List of (model, build_config) tuples in optimal build order
    """
    # Calculate complexity for each model
    model_complexities = []
    for model in models:
        complexity = calculate_build_complexity(model, "default_theory")
        model_complexities.append((model, complexity))
    
    # Optimize build sequence based on complexity and dependencies
    optimized_sequence = _optimize_sequence_algorithm(model_complexities, available_resources)
    
    return optimized_sequence


@lru_cache(maxsize=64)
def get_build_strategy_for_theory(theory_name: str, 
                                 complexity_level: str) -> Dict[str, Any]:
    """Get optimized build strategy for theory and complexity combination.
    
    Returns cached build strategies optimized for specific theory and
    complexity combinations. Caching improves performance for repeated
    builds with similar characteristics.
    
    Args:
        theory_name: Name of the theory
        complexity_level: 'low', 'medium', 'high', or 'extreme'
        
    Returns:
        Dictionary with build strategy configuration
    """
    strategy_config = {
        'solver_timeout': _get_timeout_for_complexity(complexity_level),
        'memory_limit': _get_memory_for_complexity(complexity_level),
        'parallelization': _should_parallelize(complexity_level),
        'optimization_level': _get_optimization_level(theory_name, complexity_level),
        'caching_strategy': _get_caching_strategy(complexity_level)
    }
    
    return strategy_config


def format_build_progress(current_step: int,
                         total_steps: int,
                         current_model: str,
                         elapsed_time: float,
                         estimated_remaining: float) -> str:
    """Format build progress for builder-specific display.
    
    Provides progress formatting optimized for builder workflows,
    including build-specific metrics and estimated completion times.
    
    Args:
        current_step: Current build step number
        total_steps: Total number of build steps
        current_model: Name of model currently being built
        elapsed_time: Time elapsed since build start
        estimated_remaining: Estimated time remaining
        
    Returns:
        Formatted progress string for builder display
    """
    progress_percent = (current_step / total_steps) * 100
    
    progress_bar = _create_progress_bar(progress_percent, width=30)
    time_info = _format_time_info(elapsed_time, estimated_remaining)
    
    return f"""Build Progress: {progress_bar} {progress_percent:.1f}%
Step {current_step}/{total_steps}: Building {current_model}
{time_info}"""


# Private helper functions specific to builder operations
def _validate_runner_state_strict(runner_instance) -> None:
    """Perform strict validation checks for builder operations."""
    # Additional validations for strict mode
    if not runner_instance.build_config.is_valid():
        raise BuilderError("Builder configuration validation failed")
    
    if not _check_resource_availability(runner_instance):
        raise BuilderError("Insufficient resources for building operations")


def _calculate_base_complexity(model_structure: ModelStructure) -> float:
    """Calculate base complexity score for model structure."""
    variable_complexity = len(model_structure.variables) * 0.1
    constraint_complexity = len(model_structure.constraints) * 0.5
    depth_complexity = _calculate_nesting_depth(model_structure) * 2.0
    
    return variable_complexity + constraint_complexity + depth_complexity


def _get_theory_complexity_multiplier(theory_name: str) -> float:
    """Get complexity multiplier for specific theory."""
    complexity_multipliers = {
        'classical_logic': 1.0,
        'modal_logic': 1.5,
        'temporal_logic': 2.0,
        'higher_order_logic': 3.0
    }
    
    return complexity_multipliers.get(theory_name, 1.0)


def _recommend_build_strategy(complexity_score: float) -> str:
    """Recommend build strategy based on complexity score."""
    if complexity_score < 5.0:
        return 'fast_build'
    elif complexity_score < 15.0:
        return 'balanced_build'
    elif complexity_score < 50.0:
        return 'thorough_build'
    else:
        return 'intensive_build'
```

## Conclusion

This comprehensive utility organization and management standard provides **clear guidance for creating, organizing, and maintaining utility code** in the ModelChecker framework. The standards build on successful existing patterns while providing detailed criteria for:

### Key Achievements

1. **Clear Decision Framework:** Algorithmic approach to shared vs package-specific placement
2. **Quality Standards:** Comprehensive requirements for documentation, testing, and performance
3. **Discovery Patterns:** Multiple mechanisms for finding and understanding utilities
4. **Migration Strategy:** Gradual improvement approach that doesn't disrupt working code
5. **Success Metrics:** Quantifiable measures for utility organization effectiveness
6. **Examples:** Concrete demonstrations of excellent utility design

### Implementation Approach

- **Build on Success:** Leverage existing successful patterns in `utils/` package
- **Gradual Improvement:** Apply standards to new code immediately, improve existing code opportunistically
- **Practical Focus:** Prioritize actual reuse needs over theoretical organization
- **Quality Emphasis:** Maintain high standards for shared utilities while allowing flexibility for package-specific needs

### Long-term Benefits

These standards will result in:
- **Reduced Code Duplication:** Clear extraction patterns and shared utilities
- **Improved Discoverability:** Better organization and documentation
- **Enhanced Maintainability:** Consistent patterns and quality requirements
- **Developer Productivity:** Easier utility discovery and reliable utility interfaces
- **Code Quality:** Higher-quality implementations with comprehensive testing

**Remember:** Good utility organization makes code easier to find, understand, and reuse. These standards support those goals while working with the existing, successful utility structures in the codebase.

---

[← Back to Maintenance](../README.md) | [Packages →](PACKAGES.md) | [Iterator →](ITERATOR.md)