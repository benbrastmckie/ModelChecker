# Implementation Plan: Add Frame Constraints (nullity, compositionality, converse)

- **Task**: 92 - Add frame constraints for bimodal task relation
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: 91 (ternary task relation refactor, completed)
- **Research Inputs**: reports/01_frame-constraints-research.md
- **Artifacts**: plans/01_frame-constraints-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: true

## Overview

This plan implements three frame constraints for the bimodal task relation in `semantic.py`: (1) `nullity_identity` -- zero duration implies state identity, (2) `converse` -- time reversal symmetry, and (3) `forward_comp` -- compositionality of sequential tasks. These constraints align with the Lean ProofChecker's `TaskFrame` axioms and `Compositional` typeclass from `Frame.lean`. The implementation adds three builder methods to `BimodalSemantics`, integrates them into `build_frame_constraints()`, and includes targeted tests to verify correctness and constraint interactions.

### Research Integration

Key findings from the research report (01_frame-constraints-research.md):
- Z3 encodings for all three constraints use quantified formulas over BitVec states and Int durations
- `forward_comp` has the highest quantifier complexity (5 variables) and may benefit from Z3 multi-patterns to guide instantiation
- `task_restriction` (currently commented out at line 539) may conflict with `forward_comp` since composition derives task_rel values not directly witnessed by world histories; the research recommends leaving it disabled
- Duration validity guards (`is_valid_duration`) are already implemented (line 236-251) and should be used in guards
- Recommended implementation order: nullity_identity (lowest risk) -> converse (medium) -> forward_comp (highest risk)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add `build_nullity_identity_constraint()` method implementing `task_rel(w, 0, u) <-> w = u`
- Add `build_converse_constraint()` method implementing `task_rel(w, d, u) <-> task_rel(u, -d, w)` under duration validity guards
- Add `build_forward_comp_constraint()` method implementing compositionality with Z3 multi-patterns for performance
- Integrate all three constraints into `build_frame_constraints()` return list
- Add unit tests verifying each constraint individually and in combination with the existing `lawful` constraint
- Ensure all existing tests continue to pass (136 tests)

**Non-Goals**:
- Adding a `frame_class` settings option for conditional constraint loading (deferred to future task)
- Modifying `task_restriction` (currently commented out, leave as-is)
- Implementing the full evolution constraint from Frame.lean:299-301
- Performance benchmarking or optimization beyond multi-patterns on `forward_comp`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| forward_comp causes solver timeout due to 5 quantified variables | H | M | Use Z3 MultiPattern hints; add duration validity guards to narrow instantiation scope |
| New constraints make existing satisfiable examples unsatisfiable | M | L | Run full test suite after each constraint addition; constraints are mathematically consistent with lawful |
| Converse + nullity interaction creates unintended equality forcing | M | L | Test with concrete states that should remain distinct; biconditional is scoped to specific duration values |
| Performance regression on existing tests | M | M | Monitor test execution times; constraints add quantifiers but do not increase N/M search space |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add nullity_identity and converse constraints [COMPLETED]

**Goal**: Implement the two simpler frame constraint builder methods and integrate them into the constraint list.

**Tasks**:
- [x] Add `build_nullity_identity_constraint()` method to `BimodalSemantics` class after `build_task_rel_at()` (around line 273) *(completed)*
  - Quantify over two BitVec variables `w, u`
  - Return `ForAll([w, u], task_rel(w, IntVal(0), u) == (w == u))`
  - Include docstring referencing ProofChecker alignment
- [x] Add `build_converse_constraint()` method immediately after `build_nullity_identity_constraint()` *(completed)*
  - Quantify over two BitVec variables `w, u` and one Int variable `d`
  - Guard with `is_valid_duration(d)` and `is_valid_duration(-d)`
  - Return `ForAll([w, u, d], Implies(guard, task_rel(w, d, u) == task_rel(u, -d, w)))`
  - Include docstring referencing group converse property
- [x] Add both constraints to `build_frame_constraints()` return list (after `lawful`, before `skolem_abundance`) *(completed)*
  - Add builder calls: `nullity_identity = self.build_nullity_identity_constraint()`
  - Add builder calls: `converse = self.build_converse_constraint()`
  - Add comment block explaining the new frame axioms
- [x] Run existing test suite to verify no regressions *(completed: 136 passed)*

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add two builder methods and integrate into constraint list

**Verification**:
- All 136 existing tests pass
- New methods are callable and return Z3 ForAll expressions

---

### Phase 2: Add forward_comp constraint with multi-patterns [NOT STARTED]

**Goal**: Implement the compositionality constraint with Z3 multi-pattern hints for solver efficiency.

**Tasks**:
- [ ] Add `build_forward_comp_constraint()` method after `build_converse_constraint()`
  - Quantify over three BitVec variables `w, v, u` and two Int variables `d1, d2`
  - Guard premises with `is_valid_duration(d1)`, `is_valid_duration(d2)`, `is_valid_duration(d1 + d2)`
  - Body: `Implies(And(task_rel(w, d1, v), task_rel(v, d2, u), guards), task_rel(w, d1+d2, u))`
  - Add Z3 `MultiPattern(task_rel(w, d1, v), task_rel(v, d2, u))` to guide quantifier instantiation
  - Include docstring referencing Compositional.compose from Frame.lean:112-114
- [ ] Add `forward_comp` to `build_frame_constraints()` return list (after converse)
- [ ] Run existing test suite to verify no regressions
- [ ] Check for any significant test time increase (rough comparison)

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add builder method and integrate into constraint list

**Verification**:
- All existing tests pass
- No individual test takes more than 2x its previous execution time
- `build_forward_comp_constraint()` returns a ForAll with patterns attribute

---

### Phase 3: Add frame constraint tests [NOT STARTED]

**Goal**: Create dedicated tests verifying each constraint individually and their interactions with the existing lawful constraint.

**Tasks**:
- [ ] Create test file `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py`
- [ ] Implement `TestNullityIdentity` class:
  - `test_zero_duration_self_task` -- task_rel(s, 0, s) is satisfiable given frame constraints
  - `test_zero_duration_different_states_unsat` -- task_rel(s1, 0, s2) with s1 != s2 is unsatisfiable
- [ ] Implement `TestConverse` class:
  - `test_converse_symmetry` -- task_rel(w, d, u) implies task_rel(u, -d, w) is satisfiable
  - `test_converse_exclusion` -- task_rel(w, d, u) AND NOT task_rel(u, -d, w) is unsatisfiable
- [ ] Implement `TestForwardComp` class:
  - `test_composition_exists` -- given task_rel(w, d1, v) and task_rel(v, d2, u), task_rel(w, d1+d2, u) is satisfiable
  - `test_composition_chain` -- derive task_rel(s0, 2, s2) from two unit-duration tasks via lawful
- [ ] Implement `TestConstraintInteractions` class:
  - `test_lawful_plus_nullity` -- lawful + nullity_identity are jointly satisfiable
  - `test_all_constraints_consistent` -- all three new constraints + lawful are jointly satisfiable
- [ ] Run full test suite including new tests

**Timing**: 1 hour 15 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py` - New test file

**Verification**:
- All new tests pass
- Full test suite (existing + new) passes
- Each test class exercises the intended constraint behavior

## Testing & Validation

- [ ] All 136 existing bimodal tests pass after Phase 1
- [ ] All existing tests pass after Phase 2 (with forward_comp added)
- [ ] New frame constraint unit tests pass (8 tests across 4 test classes)
- [ ] No test execution time regression beyond 2x for any individual test
- [ ] Spot-check: `nullity_identity` correctly forces `task_rel(s, 0, t)` to require `s == t`
- [ ] Spot-check: `converse` correctly forces symmetry between `task_rel(w, d, u)` and `task_rel(u, -d, w)`
- [ ] Spot-check: `forward_comp` correctly derives composed task relations from unit tasks

## Artifacts & Outputs

- `plans/01_frame-constraints-plan.md` (this file)
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (modified -- 3 new builder methods + constraint list update)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py` (new -- dedicated constraint tests)

## Rollback/Contingency

- If `forward_comp` causes solver timeouts: remove it from the constraint list in `build_frame_constraints()` and add a code comment noting it is deferred pending performance optimization. The `nullity_identity` and `converse` constraints are independent and can remain active.
- If any existing test fails: `git stash` to revert changes and investigate the constraint interaction causing the failure before re-applying.
- All changes are confined to `semantic.py` (method additions + list modification) and a new test file, making targeted rollback straightforward.
