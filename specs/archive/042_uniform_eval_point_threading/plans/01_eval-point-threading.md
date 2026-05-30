# Implementation Plan: Task #42

- **Task**: 42 - Uniform eval_point threading across all logos subtheory operators
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/042_uniform_eval_point_threading/reports/01_team-research.md
- **Artifacts**: plans/01_eval-point-threading.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Several intensional operators (NecessityOperator, CounterfactualOperator) construct bare `{"world": u}` dictionaries when shifting to new worlds, dropping the `"assignment"` key that carries first-order variable bindings. This breaks compositionality for formulas like `Box(forall x. phi(x))`. The fix is to add a `with_world` helper to LogosSemantics (analogous to the existing `with_assignment` helper) and update all world-shifting operators to use it.

### Research Integration

The team research confirmed:
- NecessityOperator has 2 sites (lines 46, 58) that need fixing
- CounterfactualOperator has 2 sites (lines 50, 65) that need fixing
- PossibilityOperator has vestigial bimodal code (lines 118, 131) that references non-existent `eval_point["time"]`
- First-order operators already use the correct pattern via `with_assignment`
- Constitutive and extensional operators are correct and need no changes

## Goals & Non-Goals

**Goals**:
- Preserve variable bindings when modal/counterfactual operators shift worlds
- Add `with_world` helper following the `with_assignment` pattern
- Enable compositional semantics for modal + first-order formulas
- Clean up vestigial bimodal code in PossibilityOperator

**Non-Goals**:
- Changing extensional or constitutive operators (already correct)
- Adding new test infrastructure (existing test framework sufficient)
- Performance optimization

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking existing modal examples | H | L | Run existing test suite before/after |
| PossibilityOperator removal too aggressive | M | L | Review defined operator pattern first |
| Missing additional sites | M | L | Grep for `{"world":` pattern across codebase |

## Implementation Phases

### Phase 1: Add with_world helper [COMPLETED]

**Goal**: Add the `with_world` helper method to LogosSemantics, following the established `with_assignment` pattern.

**Tasks**:
- [ ] Add `with_world` method to LogosSemantics class in semantic.py
- [ ] Add docstring following `with_assignment` style
- [ ] Verify method signature: `with_world(self, eval_point, world) -> EvaluationPoint`

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Add `with_world` method after `with_assignment` (around line 673)

**Implementation**:
```python
def with_world(self, eval_point: 'EvaluationPoint', world: 'StateType') -> 'EvaluationPoint':
    """Create a new evaluation point with the given world.

    Creates a copy of the evaluation point with the world field set
    to the provided value, preserving all other keys (including assignment).
    Used by intensional operators to thread variable bindings through
    world-shifting evaluation.

    Args:
        eval_point: The base evaluation point to extend
        world: The world to evaluate in

    Returns:
        A new evaluation point dictionary with the world
    """
    return {**eval_point, "world": world}
```

**Verification**:
- Method exists and returns dict with spread operator
- Unit test: `with_world({"world": w, "assignment": a}, u)` returns `{"world": u, "assignment": a}`

---

### Phase 2: Fix NecessityOperator [COMPLETED]

**Goal**: Update NecessityOperator.true_at and NecessityOperator.false_at to use `with_world` instead of bare dict construction.

**Tasks**:
- [ ] Update `true_at` (line 46): `{"world": u}` -> `sem.with_world(eval_point, u)`
- [ ] Update `false_at` (line 58): `{"world": u}` -> `sem.with_world(eval_point, u)`

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py` - NecessityOperator methods

**Verification**:
- Grep confirms no bare `{"world":` in NecessityOperator
- Existing modal tests pass

---

### Phase 3: Fix CounterfactualOperator [COMPLETED]

**Goal**: Update CounterfactualOperator.true_at and CounterfactualOperator.false_at to use `with_world` instead of bare dict construction.

**Tasks**:
- [ ] Update `true_at` (line 50): `{"world": u}` -> `semantics.with_world(eval_point, u)`
- [ ] Update `false_at` (line 65): `{"world": u}` -> `semantics.with_world(eval_point, u)`

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` - CounterfactualOperator methods

**Verification**:
- Grep confirms no bare `{"world":` in CounterfactualOperator
- Existing counterfactual tests pass

---

### Phase 4: Clean up PossibilityOperator vestigial code [COMPLETED]

**Goal**: Review and fix or remove the vestigial bimodal code in PossibilityOperator that references `eval_point["time"]` which doesn't exist.

**Tasks**:
- [ ] Analyze PossibilityOperator (lines 109-168) - it's a DefinedOperator with explicit true_at/false_at
- [ ] The true_at/false_at methods use `sem.accessibility_relation` and `eval_point["time"]` - this is dead code since PossibilityOperator is defined via `derived_definition`
- [ ] Option A: Remove the explicit true_at/false_at methods (rely on derived_definition)
- [ ] Option B: Fix to use `with_world` if the methods are actually called
- [ ] Verify which path is taken by checking if DefinedOperator.true_at delegates to derived_definition

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py` - PossibilityOperator methods

**Verification**:
- Either methods removed or fixed to use `with_world`
- Modal tests pass (confirms no regression)

---

### Phase 5: Verify unchanged subtheories [COMPLETED]

**Goal**: Confirm that extensional, constitutive, and first-order operators remain correct and don't need changes.

**Tasks**:
- [ ] Grep for `{"world":` pattern across all subtheories
- [ ] Verify extensional operators pass eval_point unchanged
- [ ] Verify constitutive operators use correct patterns
- [ ] Verify first-order operators use `with_assignment` correctly

**Timing**: 15 minutes

**Files to review**:
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/operators.py`

**Verification**:
- No bare `{"world":` construction in these files (or if present, documented as intentional)
- All existing tests pass

---

### Phase 6: Test compositionality [COMPLETED]

**Goal**: Add tests that verify modal + first-order formula composition works correctly.

**Tasks**:
- [ ] Create test case for `Box(forall x. P[x])` - necessity with universal quantification
- [ ] Create test case for `(A boxright B) \\and forall x. C[x]` - counterfactual with first-order
- [ ] Verify variable bindings are preserved across world shifts

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/modal/examples.py` - Add compositionality test cases
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py` - Add compositionality test cases

**Verification**:
- New tests pass demonstrating correct variable binding preservation
- `pytest code/src/model_checker/theory_lib/logos/subtheories/modal/tests/`
- `pytest code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/`

## Testing & Validation

- [ ] All existing modal tests pass: `pytest code/src/model_checker/theory_lib/logos/subtheories/modal/tests/`
- [ ] All existing counterfactual tests pass: `pytest code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/`
- [ ] All existing first-order tests pass: `pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/`
- [ ] New compositionality tests pass
- [ ] No regressions in full test suite: `pytest code/src/model_checker/`

## Artifacts & Outputs

- Modified `code/src/model_checker/theory_lib/logos/semantic.py` with `with_world` helper
- Modified `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py`
- Modified `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`
- New test cases in `examples.py` files

## Rollback/Contingency

The changes are localized to operator implementations. If issues arise:
1. Revert the `with_world` usage back to `{"world": u}` patterns
2. Keep the `with_world` helper for future use
3. Investigate specific failure cases

Git provides easy rollback via `git checkout -- <file>` for individual files.
