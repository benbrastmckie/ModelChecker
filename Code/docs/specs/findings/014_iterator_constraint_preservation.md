# Finding 019: Iterator Constraint Preservation Issue

## Summary

The iterator produces MODEL 2+ with false premises and true conclusions despite preserving all constraints. The root cause is that ModelConstraints are built with the original model's verify/falsify functions, but subsequent models reassign these functions, creating a mismatch between constraint expectations and actual model evaluation.

## Problem Description

### Symptoms
- MODEL 1 always correct (premises true, conclusions false)
- MODEL 2+ often have false premises and/or true conclusions
- Z3 reports constraints are satisfied
- But semantic evaluation shows constraint violations

### Impact
- Iterator produces invalid countermodels
- Violates fundamental requirement that premises stay true and conclusions stay false
- Affects all hyperintensional theories (logos, exclusion, imposition)

### Reproduction
Run any example with iteration:
```bash
./dev_cli.py test_minimal_iterator.py -z -p
```

## Root Cause

The issue stems from a fundamental mismatch between how constraints are created and how models are evaluated:

1. **Constraint Creation**: ModelConstraints builds premise constraints using the original model's verify/falsify functions
2. **Model Iteration**: Z3 finds new models that satisfy the constraints symbolically
3. **Function Reassignment**: New models have different verify/falsify function assignments
4. **Evaluation Mismatch**: Constraints expect original functions, but evaluation uses new functions

### Technical Details

For premise 'A' with evaluation world 1:
- Constraint: `Or(And(0 | 1 == 1, verify(0, A)), And(1 | 1 == 1, verify(1, A)), ...)`
- Simplifies to: `Or(verify(0, A), verify(1, A))`
- MODEL 1: verify(1, A) = True → A is true at world 1 ✓
- MODEL 2: verify(0, A) = False, verify(1, A) = False → A is false at world 1 ✗

Z3 satisfies the constraint with MODEL 1's verify function but evaluates with MODEL 2's verify function.

## Solution

### Approach 1: Fresh ModelConstraints (Recommended)
Build new ModelConstraints for each iteration with the current model's functions:
- Ensures constraints match the model being evaluated
- Requires refactoring _build_new_model_structure
- Most correct but higher complexity

### Approach 2: Pin Verify/Falsify Functions
Add constraints that preserve verify/falsify assignments across models:
- For each sentence letter, add: verify_new(s, A) == verify_old(s, A)
- Simpler to implement but restricts model diversity
- May lead to fewer distinct models

### Approach 3: Constraint Regeneration
Regenerate premise/conclusion constraints in each iteration:
- Keep frame and model constraints
- Rebuild premise/conclusion constraints with new functions
- Middle ground between correctness and complexity

## Verification

Before fix:
```
MODEL 2: Premise 'A' false at evaluation world (should be true)
MODEL 2: Conclusion 'C' true at evaluation world (should be false)
```

After fix:
```
All MODEL 2+ maintain:
- Premises true at evaluation world
- Conclusions false at evaluation world
```

## Lessons Learned

1. **Constraint Context**: Constraints must be evaluated in the same context they were created
2. **Function Identity**: In hyperintensional semantics, verify/falsify functions are part of model identity
3. **Symbolic vs Semantic**: Z3's symbolic satisfaction doesn't guarantee semantic correctness
4. **Model Independence**: Each model should have independent constraint generation

## Related Issues
- Finding 017: MODEL 2 Empty Verifiers/Falsifiers (fixed sentence letter inclusion)
- Finding 018: Iterator Model vs Countermodel Behavior (clarified iterator intent)

## Implementation Notes

The current iterator implementation uses:
- `self.original_constraints` to preserve constraints
- `_create_persistent_solver()` to maintain constraints across iterations
- `_build_new_model_structure()` to create new models

The fix requires modifying how ModelConstraints interact with iterated models to ensure constraint consistency.