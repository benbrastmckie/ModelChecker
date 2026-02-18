# Plan 013: Iterator Constraint Extraction Fix

**Date**: 2025-01-08  
**Status**: DRAFT  
**Priority**: CRITICAL  
**Target**: v1.0 Release Blocker  

## Overview

Fix the critical iterator framework bug where MODEL 2+ are created without original semantic constraints, causing semantically invalid models with empty verifier/falsifier sets.

## Problem Statement

### Root Cause Identified
The iterator framework's `_create_extended_constraints()` method extracts 0 original constraints from the build_example.model_structure.solver because:

1. `build_example.model_structure.solver` is `None`
2. `build_example.model_structure.stored_solver` is `[]` (empty array)

This causes MODEL 2+ to be solved with **only difference constraints** and **no semantic framework constraints**, resulting in Z3 models that don't satisfy basic `possible(state)` relations.

### Evidence
```
[ITERATOR-DEBUG] WARNING: No original constraints found! This will cause invalid models.
[ITERATOR-DEBUG] Build example solver: None  
[ITERATOR-DEBUG] Stored solver: []
[ITERATOR-DEBUG] Returning 0 original + 2 difference = 2 total constraints
```

### Impact
- **All theories** using `iterate > 1` produce invalid models
- MODEL 2+ show empty verifier/falsifier sets: `< ∅, ∅ >`
- Semantically meaningless results that compromise research validity
- Intermittent failures (MODEL 3+ sometimes work due to different constraint patterns)

## Solution Strategy

### Approach: Fix Constraint Preservation
Instead of relying on solver.assertions() (which gets cleared), preserve the original constraints from ModelConstraints.all_constraints during iterator setup.

### Design Principles
1. **Preserve Original Constraints**: Maintain access to complete constraint set throughout iteration
2. **Theory Agnostic**: Fix works for all semantic theories  
3. **Minimal Changes**: Focused fix without architectural disruption
4. **Robust Error Handling**: Clear diagnostics when constraint extraction fails
5. **Backward Compatibility**: Existing single-model cases continue working

## Implementation Plan

### Phase 1: Constraint Preservation (HIGH PRIORITY)

#### 1.1 Modify BaseModelIterator Initialization
**File**: `src/model_checker/iterate/core.py`

```python
def __init__(self, build_example):
    # ... existing initialization ...
    
    # CRITICAL FIX: Preserve original constraints for iteration
    self.original_constraints = list(build_example.model_constraints.all_constraints)
    print(f"[ITERATOR] Preserved {len(self.original_constraints)} original constraints")
    
    # Validate constraint preservation
    if len(self.original_constraints) == 0:
        raise RuntimeError("No constraints available for iteration - this will produce invalid models")
```

#### 1.2 Update _create_extended_constraints Method
**File**: `src/model_checker/iterate/core.py`

```python
def _create_extended_constraints(self):
    """Create extended constraints using preserved original constraints."""
    print(f"[ITERATOR-DEBUG] Using {len(self.original_constraints)} preserved original constraints")
    
    # Use preserved constraints instead of solver.assertions()
    original_constraints = self.original_constraints
    
    # Create difference constraints for all previous models
    difference_constraints = []
    for model in self.found_models:
        diff_constraint = self._create_difference_constraint([model])
        difference_constraints.append(diff_constraint)
    
    # Add isomorphism constraints if available
    if HAS_NETWORKX:
        for model in self.found_models:
            iso_constraint = self._create_non_isomorphic_constraint(model)
            if iso_constraint is not None:
                difference_constraints.append(iso_constraint)
    
    print(f"[ITERATOR-DEBUG] Combining {len(original_constraints)} original + {len(difference_constraints)} difference constraints")
    return original_constraints + difference_constraints
```

### Phase 2: Enhanced Error Handling (MEDIUM PRIORITY)

#### 2.1 Add Model Validation
**File**: `src/model_checker/iterate/core.py`

```python
def _validate_model_structure(self, model_structure):
    """Validate that a model structure has valid semantic properties."""
    
    # Check for basic semantic validity
    if not hasattr(model_structure, 'z3_possible_states'):
        raise ValueError("Model structure missing z3_possible_states")
    
    if len(getattr(model_structure, 'z3_possible_states', [])) == 0:
        raise ValueError("Model structure has no possible states - invalid semantic model")
    
    if len(getattr(model_structure, 'z3_world_states', [])) == 0:
        raise ValueError("Model structure has no world states - invalid semantic model")
    
    print(f"[ITERATOR] Model validation passed: {len(model_structure.z3_possible_states)} possible states, {len(model_structure.z3_world_states)} world states")
    return True
```

#### 2.2 Integrate Validation into Model Building
**File**: `src/model_checker/iterate/core.py`

```python
def _build_new_model_structure(self, z3_model):
    """Build a completely new model structure with validation."""
    try:
        # ... existing model building code ...
        
        # CRITICAL: Validate model structure before returning
        self._validate_model_structure(new_structure)
        
        return new_structure
        
    except ValueError as e:
        logger.error(f"Model structure validation failed: {str(e)}")
        logger.error("This indicates the iterator constraints are not preserving semantic framework")
        return None
    except Exception as e:
        # ... existing exception handling ...
```

### Phase 3: Comprehensive Testing (HIGH PRIORITY)

#### 3.1 Multi-Theory Testing Script
**File**: `scripts/test_iterator_fix.py`

```python
#!/usr/bin/env python3
"""Test iterator fix across all theories"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

def test_theory_iteration(theory_name, theory_components, test_case):
    """Test iteration for a specific theory."""
    try:
        from model_checker.builder.example import BuildExample
        
        settings = test_case['settings']
        settings['iterate'] = 3  # Test multiple iterations
        
        example = BuildExample(...)
        models = example.build_and_check()
        
        print(f"✓ {theory_name}: Found {len(models)} models")
        
        # Validate each model has proper propositions
        for i, model in enumerate(models):
            if hasattr(model, 'syntax') and hasattr(model.syntax, 'sentence_letters'):
                empty_props = 0
                for letter in model.syntax.sentence_letters:
                    if hasattr(letter, 'proposition') and letter.proposition:
                        prop = letter.proposition
                        if len(prop.verifiers) == 0 and len(prop.falsifiers) == 0:
                            empty_props += 1
                
                if empty_props > 0:
                    print(f"✗ {theory_name} MODEL {i+1}: {empty_props} empty propositions")
                else:
                    print(f"✓ {theory_name} MODEL {i+1}: All propositions valid")
        
        return True
        
    except Exception as e:
        print(f"✗ {theory_name}: {e}")
        return False

# Test all theories
theories = [
    ('Imposition', ...),
    ('Exclusion', ...),
    ('Logos', ...),
    ('Bimodal', ...),
]

for theory_name, theory_components in theories:
    test_theory_iteration(theory_name, theory_components, test_cases[theory_name])
```

#### 3.2 Regression Testing
- Test all existing examples with `iterate=1` (should continue working)
- Test all theories with `iterate=2` and `iterate=3`
- Validate no performance regression
- Ensure constraint counts are reasonable

### Phase 4: Documentation and Cleanup (LOW PRIORITY)

#### 4.1 Update Iterator Documentation
**File**: `src/model_checker/iterate/README.md`

- Document the constraint preservation approach
- Explain validation checks
- Add troubleshooting guide for constraint issues

#### 4.2 Remove Debug Output
Once fix is confirmed working:
- Remove `[ITERATOR-DEBUG]` print statements
- Clean up temporary debugging code in LogosProposition
- Restore clean production output

## Risk Assessment

### HIGH RISK: Constraint Compatibility
- **Risk**: Preserved constraints might conflict with difference constraints
- **Mitigation**: Extensive testing across all theories
- **Contingency**: Fallback to improved solver.assertions() extraction

### MEDIUM RISK: Performance Impact
- **Risk**: Larger constraint sets might slow solving
- **Mitigation**: Monitor solve times during testing
- **Contingency**: Optimize constraint generation if needed

### LOW RISK: Theory-Specific Issues
- **Risk**: Some theories might have unique constraint requirements
- **Mitigation**: Theory-by-theory validation testing
- **Contingency**: Theory-specific constraint preservation if needed

## Success Criteria

### Must Have (Release Blockers)
- [ ] All theories produce valid models with `iterate > 1`
- [ ] No empty verifier/falsifier sets in any MODEL 2+
- [ ] Proper state space evaluation (possible states > 0, world states > 0)
- [ ] No regression in single-model cases (`iterate = 1`)

### Should Have (Quality)
- [ ] Clear error messages when constraint extraction fails
- [ ] Model validation catches invalid structures before proposition creation
- [ ] Performance remains acceptable (< 2x slowdown)
- [ ] Comprehensive test coverage

### Nice to Have (Polish)
- [ ] Improved debugging output for constraint analysis
- [ ] Documentation updated with troubleshooting guide
- [ ] Automated regression testing in CI/CD

## Implementation Timeline

### Sprint 1 (Critical - 1-2 days)
- Implement constraint preservation in BaseModelIterator.__init__
- Update _create_extended_constraints to use preserved constraints
- Basic testing with imposition theory

### Sprint 2 (High Priority - 1 day)  
- Add model structure validation
- Test all theories with iterate=2
- Fix any theory-specific issues discovered

### Sprint 3 (Quality - 1 day)
- Comprehensive regression testing
- Performance validation
- Clean up debug output

### Sprint 4 (Polish - 0.5 days)
- Documentation updates
- Final validation
- Prepare for v1.0 release

## References

- **Finding 015**: MODEL 2 Impossible States Issue  
- **Root Cause**: Iterator constraint extraction failure
- **Debug Evidence**: 0 original constraints extracted from solver
- **Framework**: BaseModelIterator in iterate/core.py
- **Impact**: All theories using iterate > 1

---

**CRITICAL**: This is a v1.0 release blocker. The iterator framework currently produces invalid models that compromise research validity.