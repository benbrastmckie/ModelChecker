# Findings 009: Iterator Constraint Preservation Issue

[← Back to Findings](README.md) | [Implementation Plan →](../plans/009_fresh_modelconstraints_implementation.md)

## Summary

Investigation into the iterator constraint preservation issue revealed that MODEL 2+ can violate fundamental countermodel requirements (false premises or true conclusions at evaluation world). The root cause is that the iterator reuses ModelConstraints from MODEL 1 when building MODEL 2+, but these constraints were generated using MODEL 1's verify/falsify functions.

## Problem Details

### Observed Behavior

When running iterator tests with simple premises like `['A']`:
- MODEL 1: Premise A is true at evaluation world (correct)
- MODEL 2: Premise A is false at evaluation world (incorrect)

This violates the fundamental requirement that all countermodels must have true premises at the evaluation world.

### Root Cause Analysis

1. **Constraint Generation**: ModelConstraints generates Z3 constraints based on the semantics' verify/falsify functions
2. **Model-Specific Functions**: Each model has its own verify/falsify function values 
3. **Constraint Reuse**: Iterator reuses MODEL 1's constraints for MODEL 2+
4. **Mismatch**: MODEL 2's verify/falsify functions differ from MODEL 1's, causing constraint violations

### Initial Implementation Attempt

Implemented the fresh ModelConstraints approach:
1. Added `extract_verify_falsify_state()` to ModelDefaults
2. Added `initialize_with_state()` to SemanticDefaults
3. Modified `_build_new_model_structure()` to create fresh constraints

However, the issue persists in testing.

## Current Status

The implementation is complete but the issue persists. Investigation revealed:

1. **Constructor Issue**: ModelDefaults constructor automatically solves constraints, overwriting the Z3 model
2. **Manual Construction**: Fixed by manually constructing model structure without auto-solving
3. **Issue Persists**: Even with fresh constraints, MODEL 2 still has false premises

### Key Discovery

The fresh ModelConstraints approach may be fundamentally flawed because:
- The Z3 model was found using MODEL 1's constraints
- Creating fresh constraints and then evaluating the same Z3 model against them may be inconsistent
- The verify/falsify values in the Z3 model were determined by MODEL 1's semantics

## Alternative Approaches

1. **Constraint Projection**: Instead of fresh constraints, project MODEL 1's constraints onto MODEL 2's verify/falsify space
2. **Evaluation Override**: Override proposition evaluation rather than constraint generation
3. **Solver Integration**: Integrate constraint freshness into the Z3 solving process itself

## Next Steps

1. Consider abandoning the fresh ModelConstraints approach
2. Implement evaluation-level fixes instead of constraint-level fixes
3. Research how other model checkers handle iteration with changing semantics
4. Document the fundamental challenge for future reference

## Lessons Learned

1. **Theory Agnostic**: Core framework changes must work with all semantic theories
2. **Z3 Types Matter**: Boolean values vs Z3 BoolVal expressions are not interchangeable
3. **Complex Dependencies**: The interaction between ModelConstraints, Semantics, and Z3 solving is intricate
4. **Test Early**: Simple test cases like `['A']` are crucial for catching fundamental issues

---

[← Back to Findings](README.md) | [Implementation Plan →](../plans/009_fresh_modelconstraints_implementation.md)