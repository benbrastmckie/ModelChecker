# Implementation Plan: Fix Temporal Operator Display Truth Outside Interval

- **Task**: 95 - fix_temporal_display_truth_outside_interval
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/095_fix_temporal_display_truth_outside_interval/reports/02_refined-temporal-analysis.md
- **Artifacts**: plans/02_temporal-display-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Four temporal operators (`FutureOperator`, `PastOperator`, `UntilOperator`, `SinceOperator`) in `operators.py` hardcode the assumption that arguments are FALSE at times outside the world's time interval. This is correct for atoms but wrong for negated or complex arguments (e.g., `\neg A` is TRUE when atoms are FALSE). The fix replaces each hardcoded FALSE assumption with a call to `semantics.true_at()`, which already handles both atoms (FALSE outside interval via `is_valid_time_for_world`) and complex formulas (recursive evaluation through operator `true_at` methods). This is the same evaluation pattern used in `BimodalProposition.find_extension()` at semantic.py:1720-1726. Definition of done: BM_CM_4's countermodel displays `\past A` as False (matching the solver's correct result), and all four operators handle complex arguments correctly at out-of-interval times.

### Research Integration

Research report `02_refined-temporal-analysis.md` confirmed:
- The bug exists in all four temporal operators at identical code patterns (Finding 1)
- `semantics.true_at()` is the correct and minimal fix approach (Finding 3, Option A)
- Extensions only cover in-interval times; out-of-interval evaluation requires Z3 model evaluation (Finding 2)
- Concrete trace of BM_CM_4 demonstrates the bug producing True instead of False for `\past A` (Finding 5)
- `argument.proposition.z3_model` and `argument.proposition.model_structure.semantics` are already accessible in all four operators (Finding 6)
- `is_true` from `model_checker.solver` is needed for safe Z3 boolean evaluation (Finding 4/Priority 4)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Replace hardcoded FALSE assumption in all 4 temporal operators with `semantics.true_at()` evaluation
- Add `is_true` import to `operators.py` for safe Z3 boolean comparison
- Re-enable BM_CM_4 in the test suite and verify it passes
- Ensure no regression in existing temporal operator tests

**Non-Goals**:
- Modifying the Z3 constraint generation (`true_at`/`false_at` methods) -- those are already correct
- Building a separate local evaluator or mini-evaluator (Option B from research)
- Changing the extension computation architecture
- Fixing any other unrelated display bugs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Z3 model evaluation returns unexpected types | M | L | Use `is_true()` from `model_checker.solver` which already handles Z3 expression types safely |
| Performance regression from Z3 evaluation at out-of-interval times | L | L | Only triggers for times outside interval; number of such times is bounded by domain size (2M-1); existing `find_extension` already uses this pattern |
| UntilOperator/SinceOperator event witness search also affected | M | L | Research confirms event witness search is limited to in-interval times (lines 1012-1013, 1231-1232); only the guard check has the bug |
| BM_CM_4 excluded for Z3 state reasons, not just this bug | M | M | Run BM_CM_4 in isolation first; if it still times out, keep in KNOWN_TIMEOUT but note bug is fixed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Import and Fix All Four Temporal Operators [COMPLETED]

**Goal**: Replace the hardcoded FALSE assumption in FutureOperator, PastOperator, UntilOperator, and SinceOperator with `semantics.true_at()` evaluation, and add the required `is_true` import.

**Tasks**:
- [ ] Add `from model_checker.solver import is_true` to the imports section of `operators.py` (after line 38)
- [ ] Fix `FutureOperator.find_truth_condition()` (lines 640-644): Replace the `else` block with `semantics.true_at()` evaluation using `argument.proposition.sentence`, `current_world`, `future_time`, and `argument.proposition.z3_model`
- [ ] Fix `PastOperator.find_truth_condition()` (lines 807-811): Same pattern using `past_time` instead of `future_time`
- [ ] Fix `UntilOperator.find_truth_condition()` (lines 1025-1028): Same pattern using `guard_arg.proposition` for sentence/z3_model, `world_id` for world, and `r` for time; set `guard_ok = False` when argument evaluates to false
- [ ] Fix `SinceOperator.find_truth_condition()` (lines 1244-1247): Same pattern as UntilOperator

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Add `is_true` import; replace 4 hardcoded FALSE blocks with `semantics.true_at()` calls

**Fix pattern for FutureOperator/PastOperator** (the `argument` variable holds the formula):
```python
else:
    # Time is outside world's interval: evaluate argument using
    # semantics.true_at() which handles atoms (FALSE via
    # is_valid_time_for_world) and complex formulas (recursive eval)
    truth_expr = semantics.true_at(
        argument.proposition.sentence,
        {"world": current_world, "time": future_time}  # or past_time
    )
    if not is_true(argument.proposition.z3_model.evaluate(truth_expr)):
        future_false = True  # or past_false
        break
```

**Fix pattern for UntilOperator/SinceOperator** (the `guard_arg` variable holds the guard formula):
```python
else:
    # Time is outside world's interval: evaluate guard using
    # semantics.true_at() which handles atoms (FALSE via
    # is_valid_time_for_world) and complex formulas (recursive eval)
    truth_expr = semantics.true_at(
        guard_arg.proposition.sentence,
        {"world": world_id, "time": r}
    )
    if not is_true(guard_arg.proposition.z3_model.evaluate(truth_expr)):
        guard_ok = False
        break
```

**Verification**:
- File parses without syntax errors (`python -c "import ast; ast.parse(open('operators.py').read())"`)
- All existing tests in `test_bimodal.py` still pass (excluding KNOWN_TIMEOUT_EXAMPLES)

---

### Phase 2: Re-enable BM_CM_4 Test and Validate [COMPLETED]

**Goal**: Remove BM_CM_4 from the excluded test list and verify it produces the correct countermodel display.

**Tasks**:
- [ ] Remove `"BM_CM_4"` from `KNOWN_TIMEOUT_EXAMPLES` set in `test_bimodal.py` (line 43)
- [ ] Run `BM_CM_4` test in isolation to verify it passes: `\past A` should display as False in the countermodel
- [ ] Run the full bimodal test suite to check for regressions
- [ ] If BM_CM_4 times out in the full suite (Z3 state issue, not the display bug), add it back to KNOWN_TIMEOUT_EXAMPLES with an updated comment noting the display bug is fixed

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - Remove BM_CM_4 from KNOWN_TIMEOUT_EXAMPLES (line 43)

**Verification**:
- BM_CM_4 test passes in isolation
- No regressions in other bimodal tests
- Countermodel output shows `\past A` as False (not True)

---

### Phase 3: Update Docstrings and Run Full Verification [COMPLETED]

**Goal**: Update the docstrings in all four operators to reflect the corrected behavior, and perform comprehensive verification.

**Tasks**:
- [ ] Update the docstring comment in `FutureOperator.find_truth_condition()` (near line 631): Change "Times outside the world's interval have atoms FALSE" to reflect that arguments are now properly evaluated
- [ ] Update the docstring comment in `PastOperator.find_truth_condition()` (near line 798): Same update
- [ ] Update the docstring comment in `UntilOperator.find_truth_condition()` (near line 972 and line 1012): Change "Atoms at times outside the world's domain are FALSE" and "Witnesses can only be in world's interval since atoms outside are FALSE" to reflect corrected evaluation
- [ ] Update the docstring comment in `SinceOperator.find_truth_condition()` (near line 1190 and line 1231): Same updates
- [ ] Run `pytest` on the full test suite to confirm no regressions
- [ ] Manually verify BM_CM_4 output if possible (run example and inspect countermodel display)

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Update 6 docstring/comment lines across 4 operators

**Verification**:
- Full test suite passes
- All modified comments accurately describe the corrected behavior
- No remaining references to the incorrect "atoms are FALSE" assumption in temporal operator comments

## Testing & Validation

- [ ] `python -c "import ast; ast.parse(open('code/src/model_checker/theory_lib/bimodal/operators.py').read())"` passes (syntax check)
- [ ] Existing bimodal tests pass (excluding other KNOWN_TIMEOUT_EXAMPLES): `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -v`
- [ ] BM_CM_4 passes in isolation: `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -k "BM_CM_4" -v`
- [ ] BM_CM_4 countermodel shows `\past A` as False (not True)
- [ ] No import errors when loading the modified `operators.py`

## Artifacts & Outputs

- `specs/095_fix_temporal_display_truth_outside_interval/plans/02_temporal-display-fix.md` (this plan)
- `code/src/model_checker/theory_lib/bimodal/operators.py` (modified: import + 4 bug fixes + docstring updates)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (modified: BM_CM_4 re-enabled)

## Rollback/Contingency

If the fix causes unexpected regressions:
1. Revert `operators.py` changes with `git checkout -- code/src/model_checker/theory_lib/bimodal/operators.py`
2. Revert `test_bimodal.py` changes with `git checkout -- code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`
3. If only BM_CM_4 fails (Z3 state issue), keep the operator fixes but add BM_CM_4 back to KNOWN_TIMEOUT_EXAMPLES with an updated comment
4. If `is_true` import causes circular dependency issues, use `z3.is_true()` from the existing `z3_shim` import instead
