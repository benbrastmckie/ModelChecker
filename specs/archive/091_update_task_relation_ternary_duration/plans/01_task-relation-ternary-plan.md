# Implementation Plan: Task #91

- **Task**: 91 - Update task relation to ternary with duration parameter
- **Status**: [NOT STARTED]
- **Effort**: 4.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_task-relation-ternary-research.md
- **Artifacts**: plans/01_task-relation-ternary-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

Refactor the bimodal task relation from binary `task(w, u)` to ternary `task_rel(w, d, u)` where `d` represents duration. This aligns the ModelChecker with the ProofChecker (Lean) semantics which supports arbitrary duration tasks. The implementation maintains backward compatibility via a wrapper function while expanding the semantic foundation to support multi-step temporal transitions.

### Research Integration

Key findings from `reports/01_task-relation-ternary-research.md`:
- Current binary relation at `semantic.py:153-158` only supports unit transitions
- 6 update sites identified: task function definition, lawful constraint, task restriction, model injection, iterate.py difference tracking
- Lean ProofChecker uses `taskRel : S -> Q -> S -> Prop` with duration type Q as ordered commutative group
- Main risk: constraint space expansion from O(N^2) to O(N^2*D)

## Goals & Non-Goals

**Goals**:
- Define ternary `task_rel(w, d, u)` function with integer duration parameter
- Update frame constraints to use explicit duration=1 for consecutive states
- Update task restriction constraint to support arbitrary durations
- Maintain backward compatibility with existing `task(w, u)` calls via wrapper
- Update model injection to iterate over duration range
- Update iterate.py difference tracking for ternary relations
- Prepare foundation for task 92 frame axioms (nullity, compositionality, converse)

**Non-Goals**:
- Implementing compositionality axiom (deferred to task 92)
- Implementing nullity identity axiom (deferred to task 92)
- Implementing converse axiom (deferred to task 92)
- Supporting non-integer duration types (e.g., Real)
- Performance optimization for large duration ranges (future work)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Constraint space expansion | High | High | Bound duration range to world interval size M, lazy enumeration in injection |
| Quantifier complexity increase | Medium | Medium | Use bounded quantification over integer duration range |
| Model extraction slowdown | Medium | Medium | Only extract task relations for durations appearing in world histories |
| Test regression | Medium | Low | Run full test suite after each phase; preserve backward-compatible wrapper |
| Z3 performance degradation | High | Low | Profile after implementation; add constraint pruning if needed |

## Implementation Phases

### Phase 1: Define Ternary Task Relation [NOT STARTED]

**Goal**: Add the new `task_rel` function alongside existing `task` function

**Tasks**:
- [ ] Add `task_rel` as Z3 Function with signature `(BitVec[N], Int, BitVec[N]) -> Bool`
- [ ] Add `max_duration` property based on world interval size M
- [ ] Add backward-compatible `task` wrapper method that calls `task_rel(w, 1, u)`
- [ ] Verify existing code continues to work with wrapper

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 152-158)

**Verification**:
- Existing tests pass with wrapper in place
- New `task_rel` function is callable with 3 arguments

---

### Phase 2: Update Lawful Constraint [NOT STARTED]

**Goal**: Modify lawful constraint to use explicit duration=1

**Tasks**:
- [ ] Update lawful constraint at lines 356-381 to call `task_rel(state_t, 1, state_t+1)`
- [ ] Ensure IntVal(1) is used for the duration parameter
- [ ] Add comment documenting unit duration assumption

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 373-379)

**Verification**:
- Frame constraints build without error
- Existing bimodal test cases pass

---

### Phase 3: Update Task Restriction Constraint [NOT STARTED]

**Goal**: Generalize task restriction to support arbitrary durations

**Tasks**:
- [ ] Add duration quantification variable `some_duration` as z3.Int
- [ ] Modify ForAll to quantify over `(some_state, some_duration, next_state)`
- [ ] Update implication antecedent to `task_rel(some_state, some_duration, next_state)`
- [ ] Update existential body to check `time_shifted + some_duration` for target state
- [ ] Add time validity guard: `some_duration >= 1` and `some_duration <= max_duration`
- [ ] Add validity check for `time_shifted + some_duration` being in world interval

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 416-445)

**Verification**:
- Frame constraints build without error
- Task relations properly restricted to states appearing in world histories

---

### Phase 4: Update Model Injection [NOT STARTED]

**Goal**: Inject ternary task relations during model transfer

**Tasks**:
- [ ] Modify injection loop to iterate over duration range `[1, max_duration]`
- [ ] Update evaluation call to use `task_rel(state1, duration, state2)`
- [ ] Update constraint addition to use ternary relation
- [ ] Consider lazy enumeration: only inject for durations that could appear in model
- [ ] Add performance guard: skip if duration exceeds world interval size

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 990-999)

**Verification**:
- Model injection completes within timeout
- Injected constraints properly constrain ternary relation

---

### Phase 5: Update Iterate.py Difference Tracking [NOT STARTED]

**Goal**: Update difference extraction to track ternary task relations

**Tasks**:
- [ ] Modify `task_relations` structure to use `"{state1}->{duration}->{state2}"` keys
- [ ] Update difference extraction loop to iterate over duration range
- [ ] Update comparison logic to handle ternary relation values
- [ ] Ensure backward compatibility with existing difference reports

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` (lines 92-98, 245-257)

**Verification**:
- Difference tracking captures duration information
- Iteration output includes duration in task relation changes

---

### Phase 6: Add Duration Helpers [NOT STARTED]

**Goal**: Add utility methods for duration-related operations

**Tasks**:
- [ ] Add `is_valid_duration(d)` method returning `And(d >= 1, d <= max_duration)`
- [ ] Add `get_state_at_offset(world, time, duration)` helper for time + duration lookup
- [ ] Add documentation for duration semantics (integer, positive, bounded by M)

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py`

**Verification**:
- Helper methods return correct Z3 expressions
- Documentation accurately describes duration semantics

---

### Phase 7: Run Full Test Suite [NOT STARTED]

**Goal**: Verify complete implementation against existing tests

**Tasks**:
- [ ] Run unit tests: `pytest code/tests/unit/`
- [ ] Run integration tests: `pytest code/tests/integration/`
- [ ] Run e2e tests: `pytest code/tests/e2e/`
- [ ] Check for any bimodal-specific test failures
- [ ] Fix any regressions discovered

**Timing**: 30 minutes

**Files to modify**:
- Any test files requiring updates for new signature

**Verification**:
- All existing tests pass
- No performance regressions in test execution time

---

### Phase 8: Documentation and Cleanup [NOT STARTED]

**Goal**: Document changes and prepare for downstream task 92

**Tasks**:
- [ ] Update docstrings for `task_rel`, `task`, and modified methods
- [ ] Add inline comments explaining duration semantics
- [ ] Document relationship to Lean ProofChecker's TaskFrame structure
- [ ] Note that task 92 will add frame axioms (nullity, compositionality, converse)
- [ ] Verify code formatting and style consistency

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py`
- `code/src/model_checker/theory_lib/bimodal/iterate.py`

**Verification**:
- Docstrings complete and accurate
- Code passes linting checks

## Testing & Validation

- [ ] Existing bimodal theory tests pass with backward-compatible wrapper
- [ ] New `task_rel` function accepts 3 arguments correctly
- [ ] Lawful constraint uses duration=1 for consecutive states
- [ ] Task restriction properly generalizes to arbitrary durations
- [ ] Model injection completes without timeout for typical model sizes
- [ ] Difference tracking reports duration in task relation changes
- [ ] Performance remains acceptable (no more than 2x slowdown on typical cases)
- [ ] Foundation ready for task 92 frame axioms

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Updated with ternary task_rel
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - Updated difference tracking
- `plans/01_task-relation-ternary-plan.md` - This plan
- `summaries/01_task-relation-ternary-summary.md` - Execution summary (after completion)

## Rollback/Contingency

If implementation causes critical issues:
1. The backward-compatible `task` wrapper ensures existing code continues to work
2. Git revert to pre-implementation commit if needed
3. Task restriction can be temporarily disabled if causing solver issues
4. Duration range can be restricted to `[1, 1]` to match binary semantics
5. Full rollback: restore original `task` function definition, remove `task_rel`
