# Research 020: Bimodal Iterator Isomorphism Detection Issue

**Date**: 2025-01-15  
**Type**: Research Report  
**Component**: Bimodal Theory Iterator  
**Status**: Investigation Complete  

## Executive Summary

The bimodal theory iterator cannot find non-isomorphic models because it has stub implementations for critical isomorphism-related methods. It skips 100+ models as "isomorphic" without actually implementing proper isomorphism detection or constraint generation, leading to an infinite search that always times out.

## Problem Description

When running bimodal examples with `iterate: 2`, the iterator:
1. Finds the first model successfully
2. Attempts to find a second model
3. Skips 100-163+ models as "isomorphic" 
4. Times out after max_time without finding a second model

Example output:
```
Finding non-isomorphic models: [████████████████████] 2/2 (143 skipped) 10.0s
ITERATION REPORT
    Model 1: Initial model (0.06s)
    Model 2: Not found - timeout after 10s after checking 144 models (10.00s)
```

## Root Cause Analysis

### 1. Stub Implementations in BimodalModelIterator

The bimodal iterator has placeholder implementations that always return `True`:

```python
# In bimodal/iterate.py lines 545-553:
def _create_non_isomorphic_constraint(self, z3_model):
    """Create constraint preventing isomorphic models."""
    # For now, simple implementation
    return z3.BoolVal(True)
    
def _create_stronger_constraint(self, isomorphic_model):
    """Create constraint for finding stronger models."""
    # For now, simple implementation
    return z3.BoolVal(True)
```

These methods should create constraints to:
- Prevent finding models that are structurally identical (isomorphic)
- Guide the search toward genuinely different models

### 2. How Isomorphism Detection Works

The base iterator (in `iterate/core.py`) expects theories to implement:
1. **Isomorphism detection**: Check if two models are structurally equivalent
2. **Non-isomorphic constraints**: Create Z3 constraints to exclude isomorphic models

Without proper implementation, the iterator:
- Cannot distinguish between genuinely different models
- Keeps finding the same model structure with minor variations
- Marks all subsequent models as "isomorphic" and skips them

### 3. Comparison with Working Theories

**Logos Theory** (`logos/iterate.py`):
- Implements proper `_create_non_isomorphic_constraint`
- Creates constraints based on state permutations
- Successfully finds multiple distinct models

**Exclusion Theory** (inherits from Logos):
- Uses Logos' isomorphism detection
- Adds exclusion-specific constraints
- Works correctly for finding multiple models

**Bimodal Theory**:
- Returns `True` (no constraint)
- Effectively tells Z3 "any model is fine"
- Z3 keeps returning variations of the same model

## Technical Analysis

### What Makes Models Isomorphic in Bimodal Theory?

Two bimodal models are isomorphic if there exists a bijection between their components that preserves:

1. **World histories**: Time-to-state mappings
2. **Task relations**: Transitions between states
3. **Truth conditions**: Which propositions are true at which states
4. **Time intervals**: Valid time ranges for each world
5. **Time-shift relations**: How worlds relate across time shifts

### Why the Iterator Skips So Many Models

Without proper constraints, the iterator's workflow is:

1. Find first model ✓
2. Add constraint: "next model must differ from first" 
3. Z3 finds a model (likely very similar)
4. Check if isomorphic: Always returns true (due to missing implementation)
5. Mark as skipped, add another constraint
6. Repeat until timeout

Each "skipped" model is actually a valid model, but the iterator doesn't know how to distinguish them.

## Implications

### Current Behavior
- Bimodal theory can only find one model per example
- Iteration always times out searching for additional models
- Users cannot explore the model space for bimodal formulas
- The `iterate` setting is effectively ignored

### Expected Behavior
- Should find genuinely different models when they exist
- Should terminate quickly when no more models exist
- Should properly identify and skip only truly isomorphic models

## Recommended Solution

The bimodal theory needs proper implementations of:

### 1. Isomorphism Detection
```python
def _check_models_isomorphic(self, model1, model2):
    """Check if two bimodal models are isomorphic."""
    # Check for bijection preserving:
    # - World history mappings
    # - Task transitions
    # - Truth conditions
    # - Time structures
```

### 2. Non-Isomorphic Constraint Generation
```python
def _create_non_isomorphic_constraint(self, z3_model):
    """Create constraints to exclude isomorphic models."""
    # Generate constraints that force at least one of:
    # - Different world history structure
    # - Different task relations
    # - Different truth assignments
    # - Different time intervals
```

### 3. Proper Integration
- Study how logos theory implements these methods
- Adapt the approach for bimodal's unique features
- Test with examples known to have multiple models

## Workarounds

Until properly implemented:
1. Set `iterate: 1` for bimodal examples
2. Use manual constraint modification to find different models
3. Increase `max_time` if searching for edge cases

## Test Cases

To verify a fix works:
1. **Simple disjunction**: `(A ∨ B)` with `iterate: 3` should find models where:
   - Only A is true
   - Only B is true
   - Both A and B are true

2. **Modal example**: `◇A` with multiple worlds should find models with different accessibility patterns

3. **Temporal example**: `⏵A` should find models with A true at different future times

## Conclusion

The bimodal iterator's inability to find non-isomorphic models is due to missing implementation of isomorphism detection and constraint generation. This is not a bug but an incomplete feature that needs proper implementation for the bimodal theory to support model iteration effectively.

## References

- Base iterator implementation: `/src/model_checker/iterate/core.py`
- Logos implementation (working example): `/src/model_checker/theory_lib/logos/iterate.py`
- Bimodal iterator (needs work): `/src/model_checker/theory_lib/bimodal/iterate.py`