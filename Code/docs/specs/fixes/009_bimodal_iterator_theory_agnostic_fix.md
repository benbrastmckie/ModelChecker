# Fix 009: Bimodal Iterator Theory-Agnostic Compatibility

**Date**: 2025-01-15  
**Type**: Bug Fix  
**Component**: Iterator Models Builder  
**Status**: Complete  

## Problem

The bimodal theory iterator failed during model building with:
- `'BimodalSemantics' object has no attribute 'possible'`
- `'BimodalSemantics' object has no attribute 'verify'`

The iterator's model builder assumed all theories have the same semantic predicates (possible, verify, falsify), but theories have different approaches:
- **Logos/Exclusion/Imposition**: Use `possible()`, `verify()`, and `falsify()` predicates
- **Bimodal**: Uses `truth_condition()` for atomic propositions and doesn't have a concept of "possible states"

## Root Cause

The `iterate/models.py` `_rebuild_model_from_structure()` method unconditionally called:
1. `semantics.possible(state)` without checking if it exists
2. `semantics.verify(state, atom)` without checking if it exists

This violated the Theory Agnostic Principle by assuming all theories share the same interface.

## Solution

Added proper attribute checks before using theory-specific predicates:

### 1. Fixed `possible` predicate usage (line 93):
```python
# Is this state possible in the iterator model?
# Note: Not all theories have a 'possible' predicate (e.g., bimodal theory)
if hasattr(semantics, 'possible'):
    is_possible_val = z3_model.eval(semantics.possible(state), model_completion=True)
    if z3.is_true(is_possible_val):
        temp_solver.add(semantics.possible(state))
    else:
        temp_solver.add(z3.Not(semantics.possible(state)))
```

### 2. Fixed `verify` predicate usage (line 102):
```python
# Constrain verify/falsify for sentence letters
# Note: Some theories (e.g., bimodal) use truth_condition instead of verify/falsify
if hasattr(semantics, 'verify'):
    for letter_obj in syntax.sentence_letters:
        if hasattr(letter_obj, 'sentence_letter'):
            atom = letter_obj.sentence_letter
            for state in range(2**semantics.N):
                # Verify value
                verify_val = z3_model.eval(semantics.verify(state, atom), model_completion=True)
                # ... rest of verify/falsify logic
```

## Impact

- Bimodal theory iterator now works correctly
- Iterator is now theory-agnostic and compatible with different semantic approaches
- No impact on theories that do have these predicates (logos, exclusion, imposition)
- Follows defensive programming practices per CLAUDE.md

## Testing

Verified the fix works:
1. Bimodal iterator runs without errors
2. Successfully finds initial model
3. Properly searches for additional models (times out as expected when none exist)
4. All iterator unit tests pass

## Files Modified

1. `/src/model_checker/iterate/models.py` - Added attribute checks for theory-specific predicates

## Related Issues

This fix complements the previous fixes:
- Fix 008: Added iterate_generator to bimodal theory
- Fix for "brast-mckie" module error (changed semantic theory name)