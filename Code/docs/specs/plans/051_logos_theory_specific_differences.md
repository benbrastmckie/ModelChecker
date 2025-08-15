# Logos Theory-Specific Differences Display Implementation Plan

**Date**: 2025-01-15  
**Type**: Implementation Plan  
**Status**: ✅ COMPLETED (2025-08-15)
**Priority**: High  
**Affected Components**: Logos theory iterator and display

## Executive Summary

Implement verification and falsification differences display for logos theories (modal, counterfactual, constitutive, relevance, and extensional). The logos theory already has complete theory-specific difference calculation infrastructure but lacks the integration piece to merge and display theory-specific differences during iteration.

## Problem Statement

The logos theory iterator has comprehensive theory-specific difference calculation (`_calculate_logos_differences`) that tracks verification, falsification, and parthood changes, but these differences are never displayed because:

1. **No Integration Override**: LogosModelIterator lacks `iterate_generator` override to merge theory-specific differences
2. **Data Structure Mismatch**: Display method expects `atomic_changes` structure but calculation produces `verify`/`falsify` keys
3. **Missing Integration**: Theory-specific differences are calculated but never merged with generic differences

## Current State Analysis

**✅ Theory-Specific Calculation EXISTS**:
- `LogosModelIterator._calculate_logos_differences()` fully implemented
- Calculates verification changes in `differences["verify"]` format
- Calculates falsification changes in `differences["falsify"]` format  
- Calculates parthood changes in `differences["parthood"]` format
- Uses detailed old/new value tracking

**✅ Comprehensive Display Method EXISTS**:
- `LogosModelStructure.print_model_differences()` fully implemented
- Displays atomic changes under `atomic_changes.verify` and `atomic_changes.falsify`
- Proper color coding and state formatting
- Handles letter name parsing and display

**❌ Missing Integration**:
1. No `iterate_generator` override to merge theory-specific differences
2. Data structure mismatch between calculation and display formats
3. Theory-specific differences never merged with generic ones

## Implementation Strategy

**Pattern**: Follow same approach as exclusion/imposition theories but adapt to logos structure
**Complexity**: Medium - needs data structure transformation  
**Risk**: Low - existing infrastructure is comprehensive
**Approach**: IMPLEMENT.md dual testing methodology with systematic validation

## Implementation Phases

Following IMPLEMENT.md testing protocol throughout all phases.

### Phase 1: Research and Design (Complete - Already Done)
**Status**: ✅ Complete  
**Time**: Research completed, architecture analyzed

**Research Findings**:
- Logos theory has most sophisticated difference calculation of all theories
- Data structure needs transformation to match display expectations
- Existing display method is comprehensive and well-designed
- All logos subtheories share same iterator infrastructure

### Phase 2: Test-First Approach & Baseline Capture
**Status**: ✅ Complete
**Priority**: High - Establishing test baseline  
**Estimated Time**: 30 minutes  
**Method**: IMPLEMENT.md Method 1 (TDD) & Method 2 (CLI Testing)

#### Pre-Implementation Tasks
- [x] Run baseline tests to capture current behavior
- [x] Document expected behavior changes
- [x] Create test plan for validation

#### Baseline Testing Protocol (IMPLEMENT.md Method 1 & 2)

**Method 1 - Baseline Unit Tests**:
```bash
# Capture baseline unit test results
./run_tests.py logos --unit -v > baseline_logos_unit.txt
./run_tests.py --unit --examples --package > baseline_full.txt
```

**Method 2 - Baseline CLI Testing**:
```bash
# Capture baseline CLI behavior
./dev_cli.py src/model_checker/theory_lib/logos/examples.py > baseline_logos_cli.txt

# Test with iterations (CRITICAL per IMPLEMENT.md)
# Note: Run the same command multiple times to test iteration behavior
./dev_cli.py src/model_checker/theory_lib/logos/examples.py > baseline_logos_run1.txt
./dev_cli.py src/model_checker/theory_lib/logos/examples.py > baseline_logos_run2.txt
./dev_cli.py src/model_checker/theory_lib/logos/examples.py > baseline_logos_run3.txt

# Test all subtheories
for subtheory in modal counterfactual constitutive relevance extensional; do
    echo "Baseline for logos/$subtheory..."
    ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py > baseline_logos_${subtheory}.txt
done
```

#### Expected Behavior Changes
- Output should include verification and falsification changes in DIFFERENCES sections
- No errors or warnings should be introduced
- Performance should remain unchanged

### Phase 3: Add Generator Override with Data Transformation
**Status**: ✅ Complete
**Priority**: High - Core integration fix  
**Estimated Time**: 1 hour  
**Method**: Implementation with continuous validation

#### Implementation Tasks
- [x] Add `iterate_generator()` override method to LogosModelIterator class
- [x] Transform logos difference structure to match display expectations
- [x] Merge theory-specific differences with generic differences
- [x] Validate against baseline tests after each change

#### Data Structure Transformation

**Current Logos Structure** (from `_calculate_logos_differences`):
```python
differences = {
    "verify": {
        "Proposition_A": {
            "a.b": {"old": False, "new": True},
            "c": {"old": True, "new": False}
        }
    },
    "falsify": {
        "Proposition_A": {
            "d": {"old": False, "new": True}
        }
    }
}
```

**Required Display Structure** (for `print_model_differences`):
```python
differences = {
    "atomic_changes": {
        "verify": {
            "A": {
                "a.b": {"old": False, "new": True},
                "c": {"old": True, "new": False}
            }
        },
        "falsify": {
            "A": {
                "d": {"old": False, "new": True}
            }
        }
    }
}
```

#### Implementation Details
```python
def iterate_generator(self):
    """Override to add theory-specific differences to logos theory models.
    
    This method extends the base iterator's generator to merge logos-specific
    differences (verification, falsification, parthood) with the generic 
    differences calculated by the base iterator.
    
    Yields:
        Model structures with both generic and theory-specific differences
    """
    for model in super().iterate_generator():
        # Calculate theory-specific differences if we have a previous model
        if len(self.model_structures) >= 2:
            theory_diffs = self._calculate_differences(
                model, self.model_structures[-2]
            )
            
            # Transform logos structure to match display expectations
            if theory_diffs.get('verify') or theory_diffs.get('falsify'):
                atomic_changes = {}
                
                # Transform verify structure
                if theory_diffs.get('verify'):
                    atomic_changes['verify'] = {}
                    for letter_str, state_changes in theory_diffs['verify'].items():
                        # Extract clean letter name (A, B, C)
                        letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                        atomic_changes['verify'][letter_name] = state_changes
                
                # Transform falsify structure
                if theory_diffs.get('falsify'):
                    atomic_changes['falsify'] = {}
                    for letter_str, state_changes in theory_diffs['falsify'].items():
                        # Extract clean letter name (A, B, C)
                        letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                        atomic_changes['falsify'][letter_name] = state_changes
                
                theory_diffs['atomic_changes'] = atomic_changes
            
            # Merge theory-specific differences with existing generic ones
            if hasattr(model, 'model_differences') and model.model_differences:
                model.model_differences.update(theory_diffs)
            else:
                model.model_differences = theory_diffs
        
        yield model
```

#### Continuous Validation Protocol

**After Each Code Change**:
```bash
# Quick validation - run affected theory
./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# Check for errors/warnings (run multiple times to check iteration)
./dev_cli.py src/model_checker/theory_lib/logos/examples.py | grep -E "(Error|Warning|AttributeError)"
./dev_cli.py src/model_checker/theory_lib/logos/examples.py | grep -E "(Error|Warning|AttributeError)"

# If changes look good, run full validation
```

**Full Validation (After Major Changes)**:
```bash
# Method 1 - Unit Tests
./run_tests.py logos --unit -v
./run_tests.py --unit --examples --package

# Method 2 - CLI Tests with Iterations
# Run multiple times to test iteration behavior
for run in 1 2 3; do
    echo "=== Testing logos run $run ==="
    ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
done

# Test all subtheories
for subtheory in modal counterfactual constitutive relevance extensional; do
    echo "=== Testing logos/$subtheory ==="
    ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py
done
```

#### Debugging Protocol (IMPLEMENT.md Philosophy)

If errors occur:
1. **Fail-Fast**: Let errors surface immediately, don't mask them
2. **Root Cause**: Trace to fundamental issue (e.g., Z3 evaluation, data structure)
3. **Uniform Solution**: Fix systematically, not with patches

Common Issues:
- Z3 Boolean casting: Use explicit `z3.is_true()` evaluation
- Missing attributes: Check hasattr before accessing
- Data structure mismatch: Verify transformation logic

#### Success Criteria
- [x] All baseline tests still pass
- [x] Verification/falsification changes display in output
- [x] No new warnings or errors introduced
- [x] Performance unchanged (compare runtimes)

### Phase 4: Enhanced Display Integration (Optional)
**Status**: ⏭️ Skipped - Not needed
**Priority**: Medium - Display improvement  
**Estimated Time**: 30 minutes  
**Method**: CLI validation only

#### Implementation Tasks
- [ ] Update color system to use `self.COLORS` for consistency
- [ ] Enhance letter name extraction robustness
- [ ] Ensure parthood changes display correctly

#### Testing Protocol
```bash
# Visual validation of output formatting
./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# Compare display consistency with other theories
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
```

### Phase 5: Comprehensive Validation & Performance Check
**Status**: ✅ Complete
**Priority**: High - Final validation  
**Estimated Time**: 1 hour  
**Method**: Full IMPLEMENT.md validation protocol

#### Pre-Validation Checklist
- [x] All code changes complete
- [x] No temporary debug code remaining
- [x] Character encoding validated

#### Full Validation Protocol

**Step 1: Character & Encoding Validation**
```bash
# Check for bad characters (IMPLEMENT.md requirement)
grep -n '[^[:print:][:space:]]' src/model_checker/theory_lib/logos/

# Verify UTF-8 encoding
file -i src/model_checker/theory_lib/logos/iterate.py
```

**Step 2: Unit Test Suite**
```bash
# Run logos-specific tests
./run_tests.py logos --unit -v

# Full regression test
./run_tests.py --unit --examples --package
```

**Step 3: CLI Testing with Performance Tracking**
```bash
# Time baseline vs implementation
time ./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py

# Test all subtheories with timing
for subtheory in modal counterfactual constitutive relevance extensional; do
    echo "=== Testing logos/$subtheory ==="
    time ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py
done
```

**Step 4: Cross-Theory Regression**
```bash
# Ensure no impact on other theories
for theory in logos exclusion imposition bimodal; do
    echo "=== Regression test: $theory ==="
    ./dev_cli.py -i 2 src/model_checker/theory_lib/$theory/examples.py
done
```

#### Performance Criteria (IMPLEMENT.md Requirement)
- [x] No performance degradation (within 5% of baseline)
- [x] Memory usage stable
- [x] No new bottlenecks introduced

#### Expected Output Validation
**Model 2+ should show**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + a.b (now a world)

Verification Changes:
  Letter A:
    + a.b now verifies A
    - c no longer verifies A

Falsification Changes:
  Letter A:
    + c now falsifies A

Part-of Relation Changes:
  + a ⊑ a.b
```

### Phase 6: Documentation and Completion
**Status**: ✅ Complete
**Priority**: Medium - Project completion  
**Estimated Time**: 30 minutes
**Method**: Documentation standards compliance

#### Documentation Tasks
- [x] Create fix documentation: `docs/specs/fixes/007_logos_theory_specific_differences.md`
- [x] Update logos theory README if API changed (No API changes)
- [x] Update this spec with completion status
- [x] Cross-reference with related fixes (005, 006)

#### Fix Documentation Template
```markdown
# Logos Theory-Specific Differences Display Fix

**Date**: 2025-01-XX
**Type**: Bug Fix
**Component**: Logos theory iterator

## Problem
Logos iterator calculated but never displayed theory-specific differences...

## Solution
Added iterate_generator override with data structure transformation...

## Testing
- All unit tests passing
- CLI validation successful
- No performance regression

## Related Fixes
- 005_exclusion_theory_specific_differences.md
- 006_imposition_theory_specific_differences.md
```

## Technical Architecture

### Current Flow (Broken)
```
LogosModelIterator.iterate_example_generator()
  └─> BaseModelIterator.iterate_generator()  
       ├─> DifferenceCalculator.calculate_differences() → generic differences only
       └─> LogosModelStructure.print_model_differences() → shows generic only
```

### Target Flow (After Implementation)
```
LogosModelIterator.iterate_example_generator()
  └─> LogosModelIterator.iterate_generator() [NEW OVERRIDE]
       ├─> BaseModelIterator.iterate_generator() → generic differences
       ├─> LogosModelIterator._calculate_differences() → theory-specific differences
       ├─> Transform data structure to match display expectations
       ├─> Merge both difference sets
       └─> LogosModelStructure.print_model_differences() → shows ALL differences
```

## Expected Output Transformation

### Current Output (Generic Only)
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + a.b (now a world)

Possible State Changes:
  + a.b (now possible)
```

### Target Output (With Theory-Specific)
```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + a.b (now a world)

Possible State Changes:
  + a.b (now possible)

Verification Changes:
  Letter A:
    + a.b now verifies A
    - c no longer verifies A
  Letter B:
    + d now verifies B

Falsification Changes:
  Letter A:
    + c now falsifies A
    - a.b no longer falsifies A

Part-of Relation Changes:
  + a ⊑ a.b
  - c ⊑ d
```

## Risk Assessment

**Low Risk Implementation** (Following IMPLEMENT.md principles):
1. **Comprehensive Infrastructure**: Logos theory has most complete difference calculation
2. **Well-Designed Display**: Existing display method handles all required cases
3. **Proven Pattern**: Same approach as exclusion/imposition with data transformation
4. **Dual Testing**: Both TDD and CLI testing catch any regressions
5. **No Breaking Changes**: Pure additive implementation with data transformation

## Files to Modify

1. **`src/model_checker/theory_lib/logos/iterate.py`**:
   - Add `iterate_generator()` override method (lines ~300)
   - Include data structure transformation logic

2. **`src/model_checker/theory_lib/logos/semantic.py`** (Optional):
   - Update color system for consistency
   - Minor display enhancements

## Implementation Readiness

| Component | Status | Notes |
|-----------|--------|-------|
| **Theory Calculation** | ✅ Complete | `_calculate_logos_differences()` most comprehensive |
| **Display Method** | ✅ Complete | `print_model_differences()` handles all cases |
| **Generator Override** | ❌ Missing | Needs adding - core integration piece |
| **Data Transformation** | ❌ Missing | Need to transform verify/falsify to atomic_changes |
| **Testing Infrastructure** | ✅ Ready | Unit tests and CLI testing available |

## Phase Completion Protocol

After each phase:
```bash
# 1. Run phase-specific validation
./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# 2. Commit with descriptive message (per IMPLEMENT.md)
git add -A
git commit -m "Phase X Complete: [Brief description]

- [List key achievements]
- All tests passing
- No regressions detected

Next: Phase Y - [Next phase description]"

# 3. Update this spec with progress
# Mark completed tasks with ✅
```

## Success Criteria (IMPLEMENT.md Standards)

Implementation is complete when:
- [x] All phases marked complete in this spec
- [x] All unit tests passing (Method 1)
- [x] No warnings or AttributeErrors in CLI output (Method 2)  
- [x] Consistent results before and after changes
- [x] No Z3 casting errors (CRITICAL)
- [x] Verification and falsification changes display correctly
- [x] All logos subtheories working (modal, counterfactual, constitutive, relevance, extensional)
- [x] Proper formatting with colors and state names
- [x] No performance regressions (within 5% of baseline)
- [x] Output matches target format exactly
- [x] Documentation complete and cross-referenced

## Timeline Summary

- **Phase 1**: Research/Design ✅ Complete
- **Phase 2**: Test-First & Baseline (30 minutes)
- **Phase 3**: Core Integration with Data Transformation (1 hour)
- **Phase 4**: Display Enhancement - Optional (30 minutes)  
- **Phase 5**: Comprehensive Validation (1 hour)
- **Phase 6**: Documentation (30 minutes)

**Total Remaining**: ~3.5 hours for complete implementation

## Debugging Quick Reference (IMPLEMENT.md)

Common issues and solutions:
```python
# Z3 Boolean Evaluation Error
# WRONG:
if z3_expr:
    ...

# CORRECT:
if not z3.is_false(z3_expr):
    ...

# Missing Attributes
# WRONG:
model.some_attr

# CORRECT:
if hasattr(model, 'some_attr'):
    model.some_attr

# Data Structure Access
# WRONG:
differences['verify']['A']

# CORRECT:
if 'verify' in differences and 'A' in differences['verify']:
    differences['verify']['A']
```

## Unique Advantages

**Logos Theory Benefits**:
- **Most Comprehensive**: Already tracks verification, falsification, and parthood
- **All Subtheories**: Single iterator handles modal, counterfactual, constitutive, relevance, extensional
- **Detailed Tracking**: Old/new value tracking more sophisticated than other theories
- **Unified Architecture**: Clean separation between core semantics and subtheory operators

**Ready for Enhancement**: The logos theory has the most sophisticated difference calculation infrastructure - it just needs integration and data structure transformation to display the rich information it already computes.