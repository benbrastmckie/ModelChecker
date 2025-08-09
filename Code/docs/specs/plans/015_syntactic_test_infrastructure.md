# Syntactic Refactoring Test Infrastructure

**Plan ID**: 015  
**Created**: 2025-08-07  
**Status**: Phase 3.1 Complete
**Purpose**: Test infrastructure for syntactic.py refactoring

## Overview

This document defines the test infrastructure for the syntactic refactoring (Phase 3).
Following the NO BACKWARDS COMPATIBILITY principle from CLAUDE.md, all imports will
be updated when components move.

## Test Structure

### Location
All tests will be in `src/model_checker/syntactic/tests/` when the package is created.

### Test Files Created (Phase 3.1)

1. **test_atoms.py** - Tests for AtomSort and AtomVal functionality
   - Z3 sort creation
   - Z3 constant creation
   - Solver integration
   - Isolation testing

2. **test_sentence.py** - Tests for Sentence class
   - Creation and initialization
   - Infix/prefix notation handling
   - String representation
   - Equality comparison
   - Subsentence operations

3. **test_operators.py** - Tests for operator classes
   - Operator creation and properties
   - DefinedOperator functionality
   - OperatorCollection management
   - Lookup operations
   - Theory-specific inheritance

4. **test_syntax.py** - Tests for Syntax class
   - Basic instantiation
   - Formula parsing
   - Sentence letter extraction
   - Operator integration

5. **test_refactoring_validation.py** - Phase validation tests
   - Baseline validation (all examples work)
   - Phase-specific validation
   - Import update verification

## Testing Protocol

### For Each Refactoring Phase:

1. **Pre-refactoring baseline**:
   ```bash
   # Capture current behavior
   ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > baseline.txt
   ```

2. **Create component with tests**:
   ```bash
   # Create new component file
   touch src/model_checker/syntactic/$component.py
   
   # Run component tests
   pytest src/model_checker/syntactic/tests/test_$component.py -v
   ```

3. **Update imports (NO BACKWARDS COMPATIBILITY)**:
   ```bash
   # Update all imports to new location
   # No compatibility layers or optional imports
   ```

4. **Validate behavior**:
   ```bash
   # All examples must still work
   ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > after.txt
   diff baseline.txt after.txt
   ```

## Import Update Strategy

When a component moves, ALL imports must be updated immediately:

### Example: Moving AtomSort and AtomVal (Phase 3.2)

Before:
```python
from model_checker.syntactic import AtomSort, AtomVal
```

After:
```python
from model_checker.syntactic.atoms import AtomSort, AtomVal
```

No transition period, no compatibility imports.

## Validation Commands

### Quick validation:
```bash
# Test all theories still work
for theory in logos exclusion imposition bimodal; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py || echo "$theory FAILED"
done
```

### Full validation:
```bash
# Run all tests
./run_tests.py --unit --package
```

### Component validation:
```bash
# Test specific component
pytest src/model_checker/syntactic/tests/test_$component.py -v
```

## Risk Mitigation

1. **Atomic commits** - One component move per commit
2. **Immediate testing** - Run validation after each change
3. **Update all imports** - No partial updates
4. **Clear error messages** - Import errors should be obvious

## Next Steps

Phase 3.1 is complete with test infrastructure in place.
Phase 3.2 can begin with moving AtomSort and AtomVal to atoms.py.