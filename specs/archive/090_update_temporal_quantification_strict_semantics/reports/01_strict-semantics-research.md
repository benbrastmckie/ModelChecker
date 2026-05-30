# Task 90: Strict Temporal Semantics Research Report

## Executive Summary

The ModelChecker's temporal operators (G, H, F, P) **already use strict semantics** (`<` ordering). The Until/Since operators from Task 89 also correctly implement strict witness with open guard intervals. **No changes are needed to the temporal ordering** in operators.py.

However, the **temporal quantification scope** differs between ProofChecker and ModelChecker:
- **ProofChecker**: Quantifies over ALL times in domain D (atoms outside domain are false)
- **ModelChecker**: Quantifies over times within world's interval via `is_valid_time_for_world`

This scope difference affects how formulas are evaluated at boundary times and requires changes to `ForAllTime`/`ExistsTime` in semantic.py.

## 1. Current vs Target Semantics Comparison

### ProofChecker (Lean) - Target Semantics

From Truth.lean lines 122-131:
```lean
def truth_at (M : TaskModel F) (Omega : Set (WorldHistory F))
    (τ : WorldHistory F) (t : D) : Formula -> Prop
  | Formula.untl phi psi => exists s : D, t < s ...
  | Formula.snce phi psi => exists s : D, s < t ...
```

Key characteristics:
1. **Strict ordering**: `t < s` (not `t <= s`) for Until; `s < t` for Since
2. **All-D quantification**: Temporal operators quantify over `s : D` (all times in domain), not restricted to world's interval
3. **Atoms outside domain are FALSE**: `atom_false_of_not_domain` theorem (lines 186-195)

From future_iff/past_iff theorems (lines 252-286):
- G(phi) true at t iff `forall s, t < s -> truth_at ... s phi`
- H(phi) true at t iff `forall s, s < t -> truth_at ... s phi`

### ModelChecker (Python) - Current Semantics

From operators.py FutureOperator.true_at (lines 531-549):
```python
return semantics.ForAllTime(
    eval_world,
    future_time,
    z3.Implies(
        eval_time < future_time,  # STRICT ordering (correct!)
        semantics.true_at(argument, {"world": eval_world, "time": future_time})
    )
)
```

The operators **already use strict ordering** (`<`). The issue is in `ForAllTime` which restricts quantification to the world's interval.

From semantic.py ForAllTime (lines 209-226):
```python
def ForAllTime(self, world, time_var, body):
    return z3.ForAll(
        time_var,
        z3.Implies(
            self.is_valid_time_for_world(world, time_var),  # Restricts to world interval!
            body
        )
    )
```

## 2. Code Audit - Ordering Analysis

| Operator | Current Ordering | Target Ordering | Status |
|----------|-----------------|-----------------|--------|
| FutureOperator (G) | `eval_time < future_time` | `t < s` | CORRECT |
| PastOperator (H) | `past_time < eval_time` | `s < t` | CORRECT |
| UntilOperator (U) | `eval_time < witness_time` | `t < s` | CORRECT |
| SinceOperator (S) | `witness_time < eval_time` | `s < t` | CORRECT |
| DefFutureOperator (F) | Via FutureOperator | Via Until | CORRECT |
| DefPastOperator (P) | Via PastOperator | Via Since | CORRECT |

**Conclusion**: All operators use strict ordering. No changes needed to operators.py for ordering.

## 3. Required Changes - Quantification Scope

### Current Problem

`ForAllTime` and `ExistsTime` restrict quantification to `is_valid_time_for_world(world, time_var)`, which checks:
```python
def is_valid_time_for_world(self, given_world, given_time):
    return z3.And(
        given_time >= self.world_interval_start(given_world),
        given_time <= self.world_interval_end(given_world)
    )
```

This means G/H only check times within the world's finite interval, not all times in D.

### Required Changes to semantic.py

**Option A: Remove world-interval restriction from ForAllTime/ExistsTime**

Change ForAllTime to quantify over all valid times in D:
```python
def ForAllTime(self, world, time_var, body):
    return z3.ForAll(
        time_var,
        z3.Implies(
            self.is_valid_time(time_var),  # All times in D, not world-specific
            body
        )
    )
```

**Option B: Remove ForAllTime wrapper entirely**

Have operators quantify directly over integers with is_valid_time bound:
```python
# In FutureOperator.true_at:
future_time = z3.Int('future_true_time')
return z3.ForAll(
    future_time,
    z3.Implies(
        z3.And(
            semantics.is_valid_time(future_time),  # Global bound
            eval_time < future_time
        ),
        semantics.true_at(argument, {"world": eval_world, "time": future_time})
    )
)
```

**Recommendation**: Option A is cleaner - modify ForAllTime/ExistsTime to use `is_valid_time` instead of `is_valid_time_for_world`.

### Atom Semantics Change

The ProofChecker makes atoms FALSE at times outside the history's domain. Current ModelChecker behavior needs verification.

In semantic.py true_at (lines 887-916):
```python
def true_at(self, sentence, eval_point):
    if sentence_letter is not None:
        eval_world_state = z3.Select(world_array, eval_time)
        return self.truth_condition(eval_world_state, sentence_letter)
```

This evaluates atoms at ANY time, even outside the world's interval. For ProofChecker alignment, atoms should be false at times outside the world's domain.

**Required change**: Add domain check to atom evaluation:
```python
if sentence_letter is not None:
    # Atoms false outside world's domain
    in_domain = self.is_valid_time_for_world(eval_world, eval_time)
    eval_world_state = z3.Select(world_array, eval_time)
    return z3.And(
        in_domain,
        self.truth_condition(eval_world_state, sentence_letter)
    )
```

## 4. Axiom Implications

Under strict semantics:

| Axiom | Formula | Validity |
|-------|---------|----------|
| T (reflexivity) | G(phi) -> phi | NOT VALID |
| T' (reflexivity) | H(phi) -> phi | NOT VALID |
| BX1 (seriality) | T -> F(T) | VALID |
| BX1' (seriality) | T -> P(T) | VALID |
| K (distribution) | G(phi -> psi) -> (G(phi) -> G(psi)) | VALID |
| 4 (transitivity) | G(phi) -> G(G(phi)) | VALID |

The T-axioms fail because at time t:
- G(phi) requires phi at all s > t (strictly future)
- But phi at t itself is NOT checked
- So G(phi) -> phi can fail

The seriality axioms (BX1/BX1') hold because in a dense or discrete linear order, there always exists a strictly future/past time.

## 5. Test Impacts

### Tests That May Break

1. **T-axiom tests**: Any test expecting `G(p) -> p` or `H(p) -> p` to be valid will fail.

2. **Boundary time tests**: Tests evaluating formulas at world interval boundaries may behave differently when atoms become false outside domain.

3. **find_truth_condition tests**: The `find_truth_condition` methods in operators.py also need to be updated to reflect all-D quantification.

### find_truth_condition Changes Needed

In FutureOperator.find_truth_condition (lines 578-643), the current logic:
```python
for time_point in time_interval:  # Only checks world's interval
    future_false_times = [
        any_time for any_time in false_times
        if any_time > time_point
        and any_time in time_interval  # Restricts to interval
    ]
```

Should become:
```python
for time_point in time_interval:
    # Check ALL times in D that are > time_point
    future_false_times = [
        any_time for any_time in all_D_times  # All times in D
        if any_time > time_point
    ]
    # Also consider: atoms at times outside world domain are false
```

This is a significant change to the extension computation logic.

## 6. Implementation Plan

### Phase 1: Semantic Changes (semantic.py)
1. Modify `ForAllTime` to use `is_valid_time` instead of `is_valid_time_for_world`
2. Modify `ExistsTime` similarly
3. Add domain check to atom evaluation in `true_at`

### Phase 2: Extension Computation (operators.py)
1. Update `find_truth_condition` in FutureOperator to consider all times in D
2. Update `find_truth_condition` in PastOperator similarly
3. Until/Since find_truth_condition already uses world interval - verify alignment

### Phase 3: Test Updates
1. Remove or update T-axiom validity tests
2. Add seriality axiom tests (BX1, BX1')
3. Add boundary time behavior tests

## Summary

**Strict ordering**: Already implemented correctly in all temporal operators.

**Quantification scope**: Needs change from world-interval to all-D quantification.

**Atom semantics**: Needs domain check (atoms false outside world's domain).

**Axiom changes**: T-axioms no longer valid; seriality axioms become the replacement.
