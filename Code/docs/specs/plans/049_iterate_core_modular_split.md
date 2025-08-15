# Iterate Core Modular Split Implementation Plan

**Date**: 2025-08-15  
**Author**: AI Assistant  
**Status**: Approved  
**Priority**: HIGHEST  
**Focus**: Complete the iterate/core.py refactoring to achieve true modularity

## Executive Summary

The iterate/core.py file remains at 729 lines despite claims of successful refactoring. This plan details the completion of the modularization to achieve the target of ~350-400 lines by properly delegating responsibilities to existing and new modules.

## Specification Validation

**Verification Checklist**:
- ✅ Clear phase breakdown (5 phases with specific tasks)
- ✅ Test requirements for each phase (dual testing methodology)
- ✅ Success criteria (line count targets, test passing)
- ✅ Implementation tasks (detailed per phase)

## Current State Analysis

### File Sizes
- `core.py`: 729 lines (target: ~350-400)
- `iterator.py`: 381 lines
- `constraints.py`: 279 lines  
- `models.py`: 607 lines
- `graph.py`: 539 lines
- `metrics.py`: 277 lines

### Core.py Current Responsibilities
1. BaseModelIterator orchestration (appropriate)
2. Theory-specific abstract methods (180+ lines)
3. Validation logic embedded in methods
4. Progress tracking logic
5. Error handling and recovery
6. Direct Z3 manipulation
7. Model difference calculation coordination

## Research and Design Phase (Before Implementation)

Per IMPLEMENT.md requirements, this phase must be completed first:

1. **Current Structure Analysis**:
   - Review actual methods in core.py that are theory-specific
   - Map dependencies between iterator and theory implementations
   - Identify exact lines that can be extracted

2. **Impact Assessment**:
   - Which theory implementations will need updates
   - How composition will replace inheritance
   - Migration path for existing code

3. **Design Decisions**:
   - Interface design for TheoryInterface
   - Delegation pattern implementation
   - Backward compatibility approach

## Implementation Phases

### Phase 1: Extract Theory Interface Module

**Goal**: Move all abstract methods and theory-specific logic to dedicated module

**Tasks**:
1. Create `theory_interface.py` module
2. Define `TheoryInterface` abstract base class
3. Move theory-specific methods from BaseModelIterator (after identifying them in research phase)
4. Update BaseModelIterator to use composition instead of inheritance
5. Update all theory implementations to inherit from TheoryInterface

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Create tests for new interface
src/model_checker/iterate/tests/test_theory_interface.py

# Run iterate package tests
./run_tests.py --package --components iterate -v

# Run full test suite
./run_tests.py --all
```

**Method 2 - Direct CLI Testing**:
```bash
# Test each theory with iterations
./dev_cli.py -i 1 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i 2 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py

# Test all theories systematically
for theory in logos bimodal exclusion imposition; do
    echo "Testing $theory..."
    ./dev_cli.py -i 3 src/model_checker/theory_lib/$theory/examples.py
done
```

**Success Criteria**:
- ✅ All unit tests passing (Method 1)
- ✅ No warnings or AttributeErrors (Method 2)
- ✅ No Z3 casting errors
- ✅ core.py reduced by identified line count
- ✅ Clean separation of theory concerns

### Phase 2: Extract Validation Module

**Goal**: Centralize all validation logic in dedicated module

**Tasks**:
1. Create `validation.py` module
2. Extract validation methods:
   - Settings validation
   - Model validation
   - Constraint validation
   - State consistency checks
3. Create `ModelValidator` class
4. Update core.py to use validator
5. Add comprehensive validation tests

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Create validation tests first
src/model_checker/iterate/tests/test_validation.py

# Test edge cases
# - Empty models
# - Invalid settings
# - Error message formatting

./run_tests.py --package --components iterate -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Test invalid inputs to verify fail-fast behavior
./dev_cli.py -i 0 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i -1 src/model_checker/theory_lib/logos/examples.py
```

**Success Criteria**:
- ✅ All validation tests passing
- ✅ Fail-fast with helpful errors
- ✅ core.py reduced by ~100 lines
- ✅ All validation centralized

### Phase 3: Refactor Model Building Flow

**Goal**: Simplify model building orchestration in core.py

**Tasks**:
1. Enhance `models.py` ModelBuilder to handle more orchestration
2. Move model reconstruction logic to ModelBuilder
3. Extract model state management to dedicated class
4. Simplify BaseModelIterator's role to pure coordination
5. Remove direct Z3 manipulation from core.py

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Test model building scenarios
./run_tests.py --package --components iterate -v

# Focus on MODEL 1, 2, 3+ tests
./run_tests.py iterate.test_models -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Test different model counts to verify state preservation
./dev_cli.py -i 1 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i 2 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i 5 src/model_checker/theory_lib/logos/examples.py

# Monitor memory usage during large iterations
./dev_cli.py -i 10 src/model_checker/theory_lib/logos/examples.py
```

**Success Criteria**:
- ✅ All model building tests pass
- ✅ State correctly preserved across models
- ✅ No memory leaks or excessive usage
- ✅ core.py reduced by ~150 lines
- ✅ No Z3 imports in core.py

### Phase 4: Enhance Progress and Metrics Integration

**Goal**: Delegate all progress tracking to metrics module

**Tasks**:
1. Move progress calculation logic to metrics.py
2. Create unified progress interface
3. Remove progress logic from core.py
4. Integrate with TerminationManager
5. Simplify iteration loop

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Test progress tracking
./run_tests.py iterate.test_metrics -v

# Test termination conditions
./run_tests.py iterate.test_iteration_control -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Test progress bar display
./dev_cli.py -i 5 src/model_checker/theory_lib/logos/examples.py

# Test timeout handling
./dev_cli.py -i 100 --timeout 5 src/model_checker/theory_lib/logos/examples.py
```

**Success Criteria**:
- ✅ Progress displays correctly
- ✅ Termination conditions work
- ✅ Timeout properly handled
- ✅ core.py reduced by ~50 lines

### Phase 5: Final Cleanup and Optimization

**Goal**: Achieve target line count and optimize structure

**Tasks**:
1. Review remaining core.py code
2. Extract any remaining non-orchestration logic
3. Optimize imports and structure
4. Add comprehensive docstrings
5. Update all cross-references

**Dual Testing Protocol**:

**Method 1 - Full Regression Testing**:
```bash
# Run complete test suite
./run_tests.py --all --verbose

# Check character encoding
grep -n '[^[:print:][:space:]]' src/model_checker/iterate/

# Verify UTF-8
file -i src/model_checker/iterate/*.py
```

**Method 2 - Comprehensive Theory Testing**:
```bash
# Test all theories with multiple iterations
for theory in logos bimodal exclusion imposition; do
    echo "=== Testing $theory ==="
    ./dev_cli.py -i 1 src/model_checker/theory_lib/$theory/examples.py
    ./dev_cli.py -i 3 src/model_checker/theory_lib/$theory/examples.py
    ./dev_cli.py -i 5 src/model_checker/theory_lib/$theory/examples.py
done

# Performance check
time ./dev_cli.py -i 10 src/model_checker/theory_lib/logos/examples.py
```

**Success Criteria**:
- ✅ All tests passing (no regressions)
- ✅ No performance degradation
- ✅ core.py at ~350-400 lines
- ✅ Clean orchestration focus
- ✅ Documentation updated

## Module Responsibilities After Refactoring

### core.py (~350-400 lines)
- BaseModelIterator orchestration
- Component initialization
- High-level iteration flow
- Result coordination

### theory_interface.py (NEW ~200 lines)
- TheoryInterface abstract base class
- All theory-specific abstract methods
- Theory validation helpers

### validation.py (NEW ~150 lines)
- ModelValidator class
- All validation logic
- Error message formatting

### iterator.py (existing)
- Main iteration loop
- Already well-structured

### models.py (enhanced)
- Extended model building orchestration
- Model state management
- Z3 model manipulation

### Other modules (unchanged)
- constraints.py
- graph.py  
- metrics.py
- statistics.py

## Phase Completion Protocol

Per IMPLEMENT.md section 4, after completing each phase:

```bash
# 1. Run comprehensive validation
./run_tests.py --all
grep -n '[^[:print:][:space:]]' src/  # Character validation

# 2. Commit phase with descriptive message
git add -A
git commit -m "Phase X Complete: [Brief description]

- [List key achievements]
- All tests passing
- No regressions detected

Next: Phase Y - [Next phase description]"

# 3. Push to remote
git push origin feature/iterate-core-split
```

## Risk Mitigation

### Iterator Fragility
- Test after each extraction
- Use both test methods (run_tests.py and dev_cli.py)
- Keep backup of working state

### Z3 Context Issues
- Maintain solver ownership clarity
- Test constraint preservation
- Verify MODEL 2+ reconstruction
- Watch for "Symbolic expressions cannot be cast to concrete Boolean values" errors

### Theory Compatibility
- Update one theory at a time
- Comprehensive theory testing
- Maintain backwards compatibility during transition

### Debugging Philosophy (per IMPLEMENT.md)
- **Fail-Fast Strategy**: Prefer deterministic failures with helpful error messages
- **Deep Root Cause Analysis**: Trace to fundamental cause when errors occur
- **Uniform High-Quality Solutions**: Avoid cheap patches and band-aid fixes

## Documentation Updates

Per IMPLEMENT.md section 5, throughout implementation:
- Update iterate/README.md with new module descriptions
- Update theory_lib READMEs if interface changes
- Maintain cross-references between modules
- Update examples if API changes

## Final Validation

Before marking implementation complete:

```bash
# Full test suite
./run_tests.py --all --verbose

# Performance check (no degradation allowed)
# Document any performance improvements

# Documentation validation
# Verify all examples in docs still work
# Check cross-references are intact
```

## Implementation Timeline

- **Research Phase**: Complete analysis before starting
- **Phase 1**: Extract Theory Interface
- **Phase 2**: Extract Validation  
- **Phase 3**: Refactor Model Building
- **Phase 4**: Enhance Progress/Metrics
- **Phase 5**: Final Cleanup

Phases should be completed sequentially with validation after each.

## Success Criteria (per IMPLEMENT.md)

Implementation is complete when:
- [ ] All phases in spec marked complete
- [ ] All tests passing (both test methods)
- [ ] No performance regressions
- [ ] Documentation updated
- [ ] Spec file updated with completion status

## Success Metrics

1. **Line Count**: core.py reduced from 729 to ~350-400 lines
2. **Test Coverage**: All tests passing, no regressions
3. **Performance**: No degradation in iteration speed
4. **Maintainability**: Clear module boundaries and responsibilities
5. **Documentation**: Updated module docs and cross-references

## Common Issues and Solutions (per IMPLEMENT.md)

### Z3 Boolean Evaluation Errors
```python
# WRONG - Causes "cannot cast to concrete Boolean"
if z3_expr:
    ...

# CORRECT - Explicit Z3 evaluation
if not z3.is_false(z3_expr):
    ...
```

### Import Circularity
- Move shared dependencies to separate modules
- Use proper import ordering (see CODE_ORGANIZATION.md)
- Consider interface segregation

### Test Failures After Refactoring
- Run baseline comparison before changes
- Use both testing methods to catch different issues
- Check for implicit dependencies

## Notes

- This plan completes the partial refactoring already started
- Focus on extraction without changing behavior
- Maintain all existing functionality
- Follow CLAUDE.md guidelines (no decorators, break compatibility if needed)
- Research phase must be completed before implementation begins