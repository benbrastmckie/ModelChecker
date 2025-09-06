# Plan 061: Models Package Refactor Implementation

**Status:** Ready for Implementation  
**Created:** 2025-01-09  
**Priority:** CRITICAL - Highest Urgency  
**Current Compliance:** 63%  
**Target Compliance:** 85%+  
**Estimated Effort:** 30 hours  
**Dependencies:** Plan 060 (Framework Refactoring Overview)  

## Executive Summary

The models/ package requires immediate refactoring due to incomplete extraction work and critical missing functionality. This plan addresses a missing method causing runtime errors, inconsistent documentation, and methods exceeding complexity guidelines. The refactor will bring compliance from 63% to 85%+ through systematic improvements.

## Current State Analysis

### Package Structure
```
models/
├── __init__.py          (33 lines)  - Inconsistent exports
├── README.md           (165 lines)  - Good documentation
├── constraints.py      (231 lines)  - Well-structured
├── proposition.py      (110 lines)  - Compliant
├── semantic.py         (312 lines)  - Moderate complexity
├── structure.py        (788 lines)  - CRITICAL ISSUES
└── tests/              (1,158 lines) - Good coverage
```

### Critical Issues Identified

#### 🔴 CRITICAL: Missing Method
- **File**: `structure.py:474`
- **Issue**: `print_all()` method called but not defined
- **Impact**: Runtime errors in `build_test_file()`
- **Priority**: IMMEDIATE

#### 🟡 HIGH: Method Complexity
Four methods exceed 60+ lines in `structure.py`:
- `__init__` (lines 41-101): 60 lines
- `print_grouped_constraints` (lines 330-395): 65 lines
- `build_test_file` (lines 421-485): 65 lines  
- `print_model_differences` (lines 608-673): 65 lines

#### 🟡 MEDIUM: Documentation Issues
- `__init__.py` references non-existent files
- Missing `ModelDefaults` export
- Inconsistent module structure documentation

#### 🟢 LOW: Error Handling
- Inconsistent exception types
- Missing f-string formatting in error messages
- Lack of context in error messages

## Implementation Plan

### Phase 1: Foundation Cleanup (Day 1 - 8 hours)

#### Task 1.1: Fix Missing print_all Method
**Priority:** CRITICAL  
**File:** `structure.py`  
**Location:** Add after line 788  
**Effort:** 2 hours  

```python
def print_all(self, output=sys.stdout):
    """Print complete model information.
    
    Combines all printing methods for comprehensive output:
    - Input sentences
    - Grouped constraints
    - Model interpretation
    - Model differences (if available)
    """
    self.print_input_sentences(output)
    print(file=output)  # Separator
    self.print_grouped_constraints(output)
    print(file=output)  # Separator
    self.print_model(output)
    
    if hasattr(self, 'model_differences') and self.model_differences:
        print(file=output)  # Separator
        self.print_model_differences(output)
```

**Validation:**
```bash
# Test the new method works
python -c "from model_checker.models.structure import ModelStructure"
pytest src/model_checker/models/tests/test_structure.py::test_print_all -v
```

#### Task 1.2: Fix __init__.py Exports
**Priority:** HIGH  
**File:** `__init__.py`  
**Effort:** 1 hour  

**Changes:**
1. Remove lines 11-12 (non-existent file references)
2. Uncomment and fix lines 25-28:
```python
from .structure import ModelDefaults, ModelStructure
```
3. Update `__all__` list:
```python
__all__ = [
    'ModelConstraints',
    'ModelDefaults',
    'ModelProposition', 
    'ModelSemantic',
    'ModelStructure',
]
```

#### Task 1.3: Fix Error Message Formatting
**Priority:** LOW  
**File:** `constraints.py:126`  
**Effort:** 0.5 hours  

**Change:**
```python
# Before
raise TypeError("The sentence letter {letter} is not of type z3.ExprRef")

# After  
raise TypeError(f"The sentence letter {letter} is not of type z3.ExprRef")
```

#### Task 1.4: Create Tests for Fixed Issues
**Priority:** MEDIUM  
**File:** `tests/test_structure.py`  
**Effort:** 1.5 hours  

**Add tests:**
```python
def test_print_all_method_exists():
    """Verify print_all method is properly implemented."""
    # Test implementation
    
def test_model_defaults_import():
    """Verify ModelDefaults can be imported from package."""
    from model_checker.models import ModelDefaults
    assert ModelDefaults is not None
```

#### Phase 1 Validation
```bash
# Run all tests to ensure no regression
pytest src/model_checker/models/tests/ -v
# Verify imports work
python -c "from model_checker.models import ModelDefaults, ModelStructure"
```

### Phase 2: Method Refinement (Day 2-3 - 12 hours)

#### Task 2.1: Refactor __init__ Method
**Priority:** HIGH  
**File:** `structure.py:41-101`  
**Effort:** 3 hours  

**Extract into focused methods:**
```python
def __init__(self, model_constraints, settings):
    """Initialize model structure with constraints and settings."""
    self._initialize_colors()
    self._initialize_attributes(model_constraints, settings)
    self._setup_z3_solver()
    self._solve_and_process()

def _initialize_colors(self):
    """Set up ANSI color codes for terminal output."""
    # Lines 42-51 - color initialization
    
def _initialize_attributes(self, model_constraints, settings):
    """Initialize instance attributes from constraints and settings."""
    # Lines 53-77 - attribute setup
    
def _setup_z3_solver(self):
    """Initialize Z3 solver with constraints."""
    # Lines 78-93 - Z3 setup
    
def _solve_and_process(self):
    """Solve constraints and process results."""
    # Lines 94-101 - solving logic
```

#### Task 2.2: Refactor print_grouped_constraints
**Priority:** MEDIUM  
**File:** `structure.py:330-395`  
**Effort:** 3 hours  

**Extract helper methods:**
```python
def print_grouped_constraints(self, output=sys.__stdout__):
    """Print constraints organized by type."""
    constraints = self._get_filtered_constraints()
    
    if not constraints:
        print("No constraints to display", file=output)
        return
        
    self._print_constraint_header(len(constraints), output)
    groups = self._group_constraints_by_type(constraints)
    self._print_constraint_groups(groups, output)

def _get_filtered_constraints(self):
    """Get constraints excluding print settings."""
    # Filter logic from lines 356-366
    
def _print_constraint_header(self, count, output):
    """Print header with constraint count."""
    # Header printing from lines 367-377
    
def _group_constraints_by_type(self, constraints):
    """Organize constraints into type-based groups."""
    # Grouping logic from lines 378-388
    
def _print_constraint_groups(self, groups, output):
    """Print each group of constraints."""
    # Group printing from lines 389-395
```

#### Task 2.3: Refactor build_test_file
**Priority:** MEDIUM  
**File:** `structure.py:421-485`  
**Effort:** 2.5 hours  

**Simplify with extraction:**
```python
def build_test_file(self, output=sys.stdout):
    """Generate test file from current model."""
    if not self.z3_model:
        raise ValueError("Cannot build test file without solved model")
        
    template_data = self._prepare_test_template_data()
    test_content = self._generate_test_content(template_data)
    print(test_content, file=output)

def _prepare_test_template_data(self):
    """Prepare data dictionary for test template."""
    return {
        'premises': self._format_premises_for_test(),
        'conclusions': self._format_conclusions_for_test(),
        'N': self.N,
        'model_output': self._capture_model_output()
    }
    
def _capture_model_output(self):
    """Capture print_all output as string."""
    from io import StringIO
    buffer = StringIO()
    self.print_all(buffer)  # Now uses the fixed method
    return buffer.getvalue()
```

#### Task 2.4: Refactor print_model_differences  
**Priority:** HIGH  
**File:** `structure.py:608-673`  
**Effort:** 3.5 hours  

**Extract difference printing:**
```python
def print_model_differences(self, output=sys.stdout):
    """Print differences from previous model."""
    if not self._has_model_differences():
        return
        
    print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
    
    difference_printers = [
        self._print_sentence_letter_differences,
        self._print_semantic_function_differences,
        self._print_model_structure_differences,
        self._print_structural_metrics
    ]
    
    for printer in difference_printers:
        try:
            printer(output)
        except (KeyError, TypeError) as e:
            print(f"Error printing differences: {e}", file=output)

def _has_model_differences(self):
    """Check if model differences exist."""
    return hasattr(self, 'model_differences') and self.model_differences

def _print_sentence_letter_differences(self, output):
    """Print differences in sentence letters."""
    # Extract lines 622-635 with improved error handling
    
def _print_semantic_function_differences(self, output):
    """Print differences in semantic functions."""
    # Extract lines 636-651 with improved error handling
```

#### Phase 2 Validation
```bash
# Run tests after each extraction
pytest src/model_checker/models/tests/test_structure.py -v

# Verify behavior unchanged
python -m model_checker.models.tests.test_integration
```

### Phase 3: Error Handling Enhancement (Day 4 - 6 hours)

#### Task 3.1: Create Error Hierarchy
**Priority:** HIGH  
**File:** New file `models/error_types.py`  
**Effort:** 2 hours  

```python
"""Error types for models package."""

class ModelsError(Exception):
    """Base exception for models package errors."""
    pass

class ModelStructureError(ModelsError):
    """Errors in model structure operations."""
    
    def __init__(self, message: str, context: dict = None):
        super().__init__(message)
        self.context = context or {}

class ModelConstraintError(ModelsError):
    """Errors in constraint handling."""
    pass

class ModelSolvingError(ModelsError):
    """Errors during Z3 solving."""
    
    def __init__(self, message: str, solver_status: str = None):
        super().__init__(message)
        self.solver_status = solver_status
```

#### Task 3.2: Apply Error Hierarchy
**Priority:** MEDIUM  
**Files:** All model files  
**Effort:** 2 hours  

**Replace generic errors:**
```python
# Before
raise RuntimeError("Solver failed")

# After
from .error_types import ModelSolvingError
raise ModelSolvingError(
    "Z3 solver failed to find model",
    solver_status=str(solver.check())
)
```

#### Task 3.3: Enhance Error Context
**Priority:** LOW  
**Files:** All model files  
**Effort:** 2 hours  

**Add helpful context:**
```python
# Before
raise ValueError("Invalid N value")

# After
raise ValueError(
    f"Invalid N value: {n}. "
    f"N must be a positive integer between 1 and 64, "
    f"representing the number of atomic propositions."
)
```

#### Phase 3 Validation
```bash
# Test error handling
pytest src/model_checker/models/tests/ -v -k "error"

# Verify error messages are helpful
python -c "
from model_checker.models import ModelStructure
try:
    ms = ModelStructure(None, {'N': -1})
except Exception as e:
    print(f'Error message: {e}')
"
```

### Phase 4: Architectural Improvements (Day 5 - 4 hours)

#### Task 4.1: Add Type Hints
**Priority:** LOW  
**Files:** All model files  
**Effort:** 2 hours  

**Add comprehensive type hints:**
```python
from typing import Dict, List, Optional, Any, Union, TextIO
import z3

def __init__(
    self, 
    model_constraints: 'ModelConstraints',
    settings: Dict[str, Any]
) -> None:
    """Initialize with type hints."""
    
def print_model(
    self, 
    output: TextIO = sys.stdout
) -> None:
    """Print with proper TextIO type."""
```

#### Task 4.2: Extract Constants
**Priority:** LOW  
**File:** `structure.py`  
**Effort:** 1 hour  

```python
# At module level
DEFAULT_COLORS = {
    "default": "\033[37m",  # WHITE
    "world": "\033[34m",    # BLUE
    "true": "\033[32m",     # GREEN
    "false": "\033[31m",    # RED
    "relation": "\033[36m", # CYAN
    "frame": "\033[33m",    # YELLOW
}
ANSI_RESET = "\033[0m"

# Maximum values
MAX_N_VALUE = 64
MAX_PRINT_WIDTH = 120
```

#### Task 4.3: Update Documentation
**Priority:** LOW  
**File:** `models/README.md`  
**Effort:** 1 hour  

**Add sections:**
- Refactoring status
- Error handling patterns
- Type hint coverage
- Testing strategy

#### Phase 4 Validation
```bash
# Type checking
mypy src/model_checker/models/ --ignore-missing-imports

# Final comprehensive test
pytest src/model_checker/models/tests/ -v --cov=model_checker.models

# Import validation
python -c "from model_checker.models import *; print('All imports successful')"
```

## Testing Strategy

### Test Coverage Requirements
- Maintain existing coverage (currently good)
- Add tests for all extracted methods
- Test error handling improvements
- Validate type hints

### Critical Test Cases
1. `test_print_all` - Verify new method works correctly
2. `test_model_defaults_import` - Verify export fixes
3. `test_extracted_methods` - Each extracted method tested
4. `test_error_hierarchy` - New error types work correctly

### Regression Testing
Run full test suite after each phase:
```bash
# Full package tests
pytest src/model_checker/models/tests/ -v

# Integration with other packages  
pytest tests/ -k "model" -v
```

## Risk Mitigation

### High Risk Items
1. **Missing print_all method** - Test extensively after implementation
2. **Large method extractions** - Preserve exact behavior first, optimize later

### Mitigation Strategies
1. **Incremental commits** - Commit after each successful task
2. **Parallel implementation** - Keep old code commented during refactor
3. **Comprehensive testing** - Run tests after every change
4. **Rollback plan** - Git branches for each phase

## Success Metrics

### Quantitative Metrics
- **Compliance Score**: 63% → 85%+
- **Method Size**: All methods ≤20 lines (except legitimate complexity)
- **Test Coverage**: Maintain or improve current level
- **Type Coverage**: 100% of public methods

### Qualitative Metrics
- All imports work correctly
- No runtime errors from missing methods
- Error messages are helpful and contextual
- Code is more maintainable and testable

## Implementation Schedule

| Day | Phase | Tasks | Hours |
|-----|-------|-------|-------|
| 1 | Phase 1 | Fix critical issues, missing methods | 8 |
| 2-3 | Phase 2 | Method extraction and refinement | 12 |
| 4 | Phase 3 | Error handling enhancement | 6 |
| 5 | Phase 4 | Type hints, constants, documentation | 4 |

**Total: 30 hours over 5 days**

## Validation Checklist

### Phase 1 Complete
- [ ] print_all method implemented and tested
- [ ] __init__.py exports fixed
- [ ] Error message formatting corrected
- [ ] All tests passing

### Phase 2 Complete  
- [ ] __init__ method refactored
- [ ] print_grouped_constraints refactored
- [ ] build_test_file refactored
- [ ] print_model_differences refactored
- [ ] All tests still passing

### Phase 3 Complete
- [ ] Error hierarchy created
- [ ] Error types applied throughout
- [ ] Error messages enhanced
- [ ] Error handling tests passing

### Phase 4 Complete
- [ ] Type hints added
- [ ] Constants extracted
- [ ] Documentation updated
- [ ] Type checking passing

### Final Validation
- [ ] Compliance score ≥85%
- [ ] All tests passing
- [ ] No regression in functionality
- [ ] Documentation reflects changes

## Next Steps

1. **Immediate**: Begin Phase 1 implementation (fix critical issues)
2. **After Phase 1**: Update progress in Plan 060
3. **After completion**: Proceed to next priority package (tests/)

---

**Status**: Ready for immediate implementation
**Next Action**: Begin Phase 1, Task 1.1 (implement print_all method)