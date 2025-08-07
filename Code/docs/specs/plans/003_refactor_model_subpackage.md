# Implementation Plan: Refactor model.py into Subpackage

## Overview

This plan details the refactoring of the monolithic `model.py` (1,352 lines) into a well-organized `model/` subpackage with clear separation of concerns.

## Test-Driven Development Strategy

### Test Categories
1. **Import Compatibility Tests** - Ensure backward compatibility
2. **Unit Tests** - Test each module independently
3. **Integration Tests** - Verify components work together
4. **Theory Tests** - Ensure all theories still function

### Success Criteria
- All tests pass after updating imports
- Each new module under 500 lines
- Clean separation of concerns achieved
- All imports updated throughout codebase

## Implementation Phases

### Phase 1: Setup and Update All Imports

**Tests to Write First**:
```python
# test_model_refactoring.py
def test_subpackage_imports():
    """Ensure new subpackage imports work."""
    from model_checker.model.semantic import SemanticDefaults
    from model_checker.model.proposition import PropositionDefaults
    from model_checker.model.constraints import ModelConstraints
    from model_checker.model.structure import ModelDefaults
    
    # Verify they are classes
    assert isinstance(SemanticDefaults, type)
    assert isinstance(PropositionDefaults, type)
    assert isinstance(ModelConstraints, type)
    assert isinstance(ModelDefaults, type)
```

**Implementation Tasks**:
1. Create `model/` directory structure
2. Create `__init__.py` with proper exports
3. Create empty module files
4. Set up test infrastructure

### Phase 2: Move SemanticDefaults

**Tests to Wriunit_testste First**:
- Test all semantic operations (fusion, part_of, etc.)
- Test bit vector operations
- Test set operations

**Implementation Tasks**:
1. Extract SemanticDefaults class to `semantic.py`
2. Move related imports and helper functions
3. Update docstrings and comments
4. Verify all methods work correctly

### Phase 3: Move PropositionDefaults

**Tests to Write First**:
- Test proposition creation
- Test evaluation methods
- Test string representation

**Implementation Tasks**:
1. Extract PropositionDefaults to `proposition.py`
2. Ensure proper imports
3. Add module docstring
4. Test with existing proposition tests

### Phase 4: Move ModelConstraints

**Tests to Write First**:
- Test constraint generation
- Test operator integration
- Test premise/conclusion handling

**Implementation Tasks**:
1. Extract ModelConstraints to `constraints.py`
2. Move constraint generation logic
3. Ensure semantic integration works
4. Verify Z3 constraint generation

### Phase 5: Split ModelDefaults

**Tests to Write First**:
- Test solver functionality
- Test printing functionality separately
- Test analysis methods

**Implementation Tasks**:
1. Create `structure.py` with core ModelDefaults logic:
   - `__init__` method
   - `solve` method
   - Core model analysis
   - Z3 interaction

2. Create `printing.py` with output functionality:
   - `print_info` method
   - `print_model` method
   - `print_propositions` method
   - Formatting utilities

3. Create `analysis.py` with analysis utilities:
   - State analysis methods
   - Model interpretation
   - Helper functions

### Phase 6: Update All Imports and Delete Old File

**Implementation Tasks**:
1. Update all imports in dependent files:
   - Theory implementations: `logos/semantic.py`, `bimodal/semantic.py`, etc.
   - Builder components: `builder/module.py`, `builder/example.py`
   - Tests and other dependencies

2. Delete the original `model.py` file completely

3. Run all tests to ensure everything still works

### Phase 7: Documentation

**Implementation Tasks**:
1. Create comprehensive `model/README.md`
2. Add docstrings to all new modules
3. Update cross-references in documentation
4. Document the new structure

## Validation

### Test Execution Plan
1. Run unit tests for each new module
2. Run all existing model_checker tests
3. Run theory-specific tests
4. Run integration tests

### Performance Validation
- Ensure no performance regression
- Verify import time is not significantly increased

## Timeline

- Phase 1: 2 hours
- Phase 2: 3 hours  
- Phase 3: 2 hours
- Phase 4: 2 hours
- Phase 5: 4 hours
- Phase 6: 1 hour
- Phase 7: 2 hours

**Total: ~16 hours (2 days)**
