# Plan 065: Iterate Package Refactor Implementation

**Status:** Phase 2 Completed  
**Created:** 2025-01-09  
**Updated:** 2025-01-10  
**Priority:** MEDIUM  
**Current Compliance:** 76% → 88% (Phase 1 & 2)  
**Target Compliance:** 95%+  
**Estimated Effort:** 16 hours  

## Executive Summary

The iterate/ package has appropriate domain complexity but needs error handling improvements and import standardization. The 330-line `iterate_generator()` method is legitimately complex for the iteration algorithm.

## Critical Issues (Based on Current Analysis)

1. **Weak Error Handling** (45% compliance)
   - Generic `Exception` catches throughout (core.py, models.py)
   - No custom error hierarchy
   - Minimal error context in messages
   - Silent failures with only logging

2. **Import Organization** 
   - Absolute imports used (e.g., `from model_checker.iterate.iterator import`)
   - Should use relative imports for internal references
   - No clear import grouping

3. **Missing Type Hints**
   - Many methods lack return type hints
   - Parameters often missing type annotations
   - Complex types (e.g., Z3 objects) not properly typed

4. **Test Coverage Gaps**
   - Need to verify current test coverage
   - Complex iteration logic needs comprehensive edge case testing

## Implementation Plan

### Phase 1: Foundation Cleanup (4 hours) ✅ COMPLETED
- **Import Standardization**
  - Convert all internal imports to relative (e.g., `from .iterator import`)
  - Group imports: stdlib, third-party (z3), local
  - Remove unused imports
- **Create Error Hierarchy** in `errors.py`
  - Base `IterateError` class
  - Specific exceptions for different failure modes
- **Add Type Hints**
  - Return types for all methods
  - Parameter types including Z3 objects
  - Use `typing` module appropriately

### Phase 2: Error Handling Enhancement (5 hours) ✅ COMPLETED
- **Replace Generic Exceptions**
  - Convert all `Exception` catches to specific types
  - Add proper error context and suggestions
  - Implement error recovery where possible
- **Enhance Error Messages**
  - Include iteration state in errors
  - Add actionable suggestions
  - Preserve stack traces for debugging
- **Add Validation Methods**
  - Input validation for build_example
  - State validation during iteration
  - Constraint validation before application

### Phase 3: Test Coverage Enhancement (4 hours)
- **Measure Current Coverage**
  - Run coverage analysis on iterate package
  - Identify untested code paths
- **Add Missing Tests**
  - Error handling paths
  - Edge cases in iteration logic
  - Isomorphism detection scenarios
- **Improve Test Organization**
  - Ensure proper unit/integration/e2e separation
  - Add parameterized tests for variations

### Phase 4: Documentation and Cleanup (3 hours)
- **Update Module Docstrings**
  - Explain complex algorithms clearly
  - Add usage examples in docstrings
- **Create/Update README.md**
  - Package overview and architecture
  - Usage patterns and examples
  - API reference
- **Code Cleanup**
  - Remove dead code
  - Consolidate duplicate logic
  - Ensure consistent style

## Key Refactoring Tasks

### Error Hierarchy Creation (errors.py)
```python
"""Error hierarchy for iterate package."""

from typing import Dict, Any, Optional


class IterateError(Exception):
    """Base exception for iteration errors."""
    
    def __init__(self, message: str, context: Optional[Dict[str, Any]] = None):
        """Initialize with message and optional context."""
        super().__init__(message)
        self.context = context or {}


class IterationLimitError(IterateError):
    """Raised when iteration limit exceeded."""
    
    def __init__(self, limit: int, found: int):
        """Initialize with limit and models found."""
        message = f"Iteration limit of {limit} models reached (found {found})"
        super().__init__(message, {'limit': limit, 'found': found})


class IterationStateError(IterateError):
    """Raised when iteration state is invalid."""
    
    def __init__(self, state: str, reason: str):
        """Initialize with state and reason."""
        message = f"Invalid iteration state '{state}': {reason}"
        super().__init__(message, {'state': state, 'reason': reason})


class ModelExtractionError(IterateError):
    """Raised when model extraction fails."""
    
    def __init__(self, model_num: int, reason: str):
        """Initialize with model number and failure reason."""
        message = f"Failed to extract model {model_num}: {reason}"
        super().__init__(message, {'model_num': model_num, 'reason': reason})


class ConstraintGenerationError(IterateError):
    """Raised when constraint generation fails."""
    
    def __init__(self, constraint_type: str, reason: str):
        """Initialize with constraint type and reason."""
        message = f"Failed to generate {constraint_type} constraint: {reason}"
        super().__init__(message, {'type': constraint_type, 'reason': reason})


class IsomorphismCheckError(IterateError):
    """Raised when isomorphism checking fails."""
    
    def __init__(self, model1: int, model2: int, reason: str):
        """Initialize with model numbers and reason."""
        message = f"Isomorphism check failed between models {model1} and {model2}: {reason}"
        super().__init__(message, {'model1': model1, 'model2': model2, 'reason': reason})
```

### Import Standardization Example
```python
# Before (absolute imports)
from model_checker.iterate.iterator import IteratorCore
from model_checker.iterate.constraints import ConstraintGenerator
from model_checker.iterate.models import ModelBuilder, DifferenceCalculator

# After (relative imports)
from .iterator import IteratorCore
from .constraints import ConstraintGenerator
from .models import ModelBuilder, DifferenceCalculator
```

### Type Hints Enhancement Example
```python
# Before
def iterate_models(self, build_example, max_iterations=None):
    """Find multiple models."""
    # ...

# After
from typing import Optional, List, Dict, Any
import z3

def iterate_models(
    self, 
    build_example: 'BuildExample',
    max_iterations: Optional[int] = None
) -> List[Dict[str, Any]]:
    """Find multiple models.
    
    Args:
        build_example: The BuildExample instance to iterate
        max_iterations: Maximum number of models to find
        
    Returns:
        List of model dictionaries with structure and metadata
        
    Raises:
        IterationLimitError: If max_iterations reached
        ModelExtractionError: If model extraction fails
    """
    # ...
```

## Success Metrics

### Quantitative Targets
- **Error Handling Compliance**: 45% → 95%+
  - All generic exceptions replaced
  - Custom error hierarchy in use
  - Actionable error messages
- **Import Organization**: 100% relative imports for internal refs
- **Type Coverage**: 90%+ of public methods with type hints
- **Test Coverage**: Target 85%+ line coverage
- **Documentation**: All modules with comprehensive docstrings

### Validation Checklist
- [ ] All tests passing before and after refactor
- [ ] No new linting errors introduced
- [ ] Error messages include context and suggestions
- [ ] README.md created/updated with examples
- [ ] Type hints added for all public APIs

## Implementation Priority

Given that the output/ package is now complete with 97% test coverage, the iterate/ package is next in line for refactoring. The refactor should maintain the package's current functionality while significantly improving its maintainability and error handling.

## Files to Modify

### Core Files (Must Update)
1. **Create** `errors.py` - New error hierarchy
2. **Update** `core.py` - Main refactor target
3. **Update** `iterator.py` - Error handling and types
4. **Update** `models.py` - Error handling and validation
5. **Update** `constraints.py` - Error handling
6. **Update** `__init__.py` - Export error classes

### Test Files (Add/Update)
1. **Create** `tests/unit/test_errors.py` - Test error hierarchy
2. **Update** existing tests for new error types
3. **Add** tests for uncovered code paths

### Documentation
1. **Create/Update** `README.md` - Package documentation
2. **Update** module docstrings throughout

---

## Implementation Progress

### Phase 1 Completion (2025-01-10)
- ✅ Created `errors.py` with comprehensive error hierarchy (8 exception classes)
- ✅ Standardized all imports to relative (core.py, iterator.py, __init__.py)
- ✅ Added type hints to all main methods in core.py and iterator.py
- ✅ All 106 tests passing after changes
- **Compliance Improvement**: 76% → 82% (6% increase from Phase 1)

### Phase 2 Completion (2025-01-10)
- ✅ Replaced all generic `Exception` catches with custom error types
- ✅ Replaced all `ValueError` with `IterationStateError` where appropriate
- ✅ Added actionable error messages with suggestions
- ✅ Updated tests to expect new error types
- ✅ All 106 tests passing after changes
- **Compliance Improvement**: 82% → 88% (6% increase from Phase 2)

**Note**: The 330-line `iterate_generator()` method in iterator.py is appropriately complex for the domain algorithm and should NOT be broken down. This is a legitimate case of necessary complexity for the iteration algorithm.

**Next Action**: Begin Phase 3 implementation - Test Coverage Enhancement