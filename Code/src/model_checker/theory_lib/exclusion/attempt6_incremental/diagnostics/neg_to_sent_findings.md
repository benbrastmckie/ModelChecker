# NEG_TO_SENT Analysis Findings

## Summary
The NEG_TO_SENT example (premise: `\exclude A`, conclusion: `A`) has no countermodel, but it should. The manual constraint analysis proves that a countermodel exists where:
- World = 0b000 (A is false)
- `\exclude A` is true via the three-condition semantics

## Root Cause
The issue is in the `extended_verify` method of `ExclusionOperator` (line 474-499 in operators.py):

```python
def extended_verify(self, state, argument, eval_point):
    # State verifies ¬φ if there's NO part of state that verifies φ
    return ForAll([v], 
        z3.Implies(
            self.semantics.is_part_of(v, state),
            z3.Not(self.semantics.extended_verify(v, argument, eval_point))
        )
    )
```

This creates a **circular dependency**:
1. To check if a state verifies `\exclude A`, it needs to know what verifies `A`
2. But checking what verifies `A` requires checking `extended_verify` 
3. If `\exclude A` appears in the formula, this creates an infinite loop

## Why Manual Analysis Works
The manual analysis in `analyze_neg_to_sent_simple.py` shows the three-condition semantics correctly allows:
- World 0b000 where A is false
- All h_sk functions map verifiers of A to 0b000
- The fusion equals the world, satisfying minimality
- Therefore `\exclude A` is true at a world where A is false

## The Implementation Gap
The current implementation:
1. Uses a "simplified approach that avoids circular reference" (line 485 comment)
2. But actually creates a circular reference via `self.semantics.extended_verify`
3. This prevents `\exclude A` from having any verifiers
4. Which explains why no countermodel is found

## Solution Path
The original refactor plan proposed a VerifierRegistry to break circular dependencies through two-phase computation:
1. Phase 1: Compute atomic verifiers
2. Phase 2: Compute complex verifiers using Phase 1 results

However, this wasn't fully implemented. The current code still has the circular dependency issue that prevents proper exclusion semantics.

## Verification
Running `analyze_neg_to_sent_simple.py` proves that the three-condition semantics itself is sound and should produce the expected countermodel. The issue is purely in the implementation's handling of the circular dependency.