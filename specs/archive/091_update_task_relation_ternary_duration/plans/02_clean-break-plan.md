# Implementation Plan: Clean-Break Ternary Task Relation

- **Task**: 91 - Update task relation to ternary with duration parameter
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/02_clean-break-research.md
- **Artifacts**: plans/02_clean-break-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This plan implements a clean-break refactoring of the task relation from binary `task(w, u)` to ternary `task_rel(w, d, u)` where `d` is an explicit duration parameter. The refactoring removes all backward compatibility concerns, directly replacing the old API throughout the codebase to align with the Lean ProofChecker's `taskRel : S -> Q -> S -> Prop` signature.

### Research Integration

Key findings from `reports/02_clean-break-research.md`:
- Use `z3.IntSort()` for duration type (matches TimeSort)
- Duration range: `(-M + 1, M)` based on time domain
- Constraint count increases 3x but remains manageable
- Frame constraints require explicit duration=1 for consecutive states
- Iteration module needs duration enumeration loop

## Goals & Non-Goals

**Goals**:
- Remove the binary `task(w, u)` function entirely
- Add ternary `task_rel(w, d, u)` with explicit duration parameter
- Update all frame constraints to use explicit duration
- Extend model injection and iteration to enumerate durations
- Align naming and semantics with ProofChecker's `taskRel`
- Provide comprehensive documentation

**Non-Goals**:
- Backward compatibility wrappers (explicitly rejected)
- Duration generalized lawful constraint (deferred to Task 92)
- Additional task relation axioms (nullity_identity, forward_comp, converse - Task 92)
- Performance optimization beyond basic implementation

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Constraint explosion with large M | Medium | Low | Typical M=2 gives only 3x increase; acceptable |
| Missed usage sites | High | Medium | Grep for `\.task\(` and `hasattr.*'task'` to find all |
| Subtle semantic drift from ProofChecker | Medium | Low | Document alignment explicitly in docstrings |
| Test failures due to API change | Low | High | Expected; update tests in dedicated phase |

## Implementation Phases

### Phase 1: Core Primitive Refactoring [COMPLETED]

**Goal**: Replace the binary task relation with ternary task_rel in define_primitives()

**Tasks**:
- [ ] Remove `self.task` Z3 function definition (semantic.py line 153-158)
- [ ] Add `self.task_rel` with ternary signature `(WorldStateSort, IntSort, WorldStateSort) -> BoolSort`
- [ ] Add duration validation helper `is_valid_duration(self, duration)`
- [ ] Add task relation builder helper `build_task_rel_at(self, world, time, duration)`
- [ ] Update docstring for `define_primitives()` to document new signature

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 136-200)

**Verification**:
- `task_rel` function exists with correct signature
- Old `task` function no longer exists
- Helper methods are accessible

---

### Phase 2: Frame Constraint Updates [COMPLETED]

**Goal**: Update lawful and task restriction constraints to use task_rel with explicit duration

**Tasks**:
- [ ] Update lawful constraint to use `self.task_rel(..., z3.IntVal(1), ...)` (lines 359-381)
- [ ] Add `some_duration` variable to task restriction constraint
- [ ] Update task restriction ForAll to include duration in quantification
- [ ] Update task restriction body to use `task_rel(some_state, some_duration, next_state)`
- [ ] Add duration bounds checks in task restriction (`some_duration > -M`, `some_duration < M`)
- [ ] Update state matching to use `time_shifted + some_duration` for target state

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 356-446)

**Verification**:
- Frame constraints compile without Z3 errors
- Lawful constraint uses duration=1 explicitly
- Task restriction quantifies over duration dimension

---

### Phase 3: Model Injection Refactoring [COMPLETED]

**Goal**: Update inject_z3_model_values to enumerate over duration dimension

**Tasks**:
- [ ] Calculate duration range from M setting: `range(-M + 1, M)`
- [ ] Add duration enumeration loop inside state iteration
- [ ] Update task evaluation to use `task_rel(state1, duration, state2)`
- [ ] Update constraint appending to use `self.task_rel(state1, duration, state2)`
- [ ] Update Not constraint for false task relations

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 990-999)

**Verification**:
- Injection loop includes duration enumeration
- Constraint count matches expected O(N^2 * D)

---

### Phase 4: Iteration Module Updates [COMPLETED]

**Goal**: Update iterate.py to track task relation differences with duration parameter

**Tasks**:
- [ ] Change `hasattr(semantics, 'task')` to `hasattr(semantics, 'task_rel')` (line 218)
- [ ] Add duration range calculation
- [ ] Add inner duration loop in state pair iteration
- [ ] Update task relation evaluation to use `task_rel(state1, duration, state2)`
- [ ] Update difference key format from `"state1->state2"` to `"state1--[duration]-->state2"`
- [ ] Update print_model_differences to parse new format (if applicable)

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` (lines 217-257, 433-437 if present)

**Verification**:
- Difference tracking includes duration dimension
- Key format matches research specification

---

### Phase 5: Test Suite Updates [COMPLETED]

**Goal**: Update bimodal tests to use new task_rel API

**Tasks**:
- [ ] Search codebase for all `\.task\(` references in test files
- [ ] Update test assertions from `hasattr(self.semantics, 'task')` to `task_rel`
- [ ] Update test constraints from `self.semantics.task(0, 1)` to `self.semantics.task_rel(0, 1, 1)`
- [ ] Add assertions for explicit duration handling
- [ ] Add test for duration boundary conditions (d=0, d=negative)
- [ ] Run full bimodal test suite and fix any failures

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py`
- Any other test files found via grep

**Verification**:
- All existing tests pass (with updated API)
- New duration-specific tests pass
- No references to old `task` function remain

---

### Phase 6: Documentation and Migration Notes [COMPLETED]

**Goal**: Add comprehensive documentation and migration notes

**Tasks**:
- [ ] Add module-level migration note to semantic.py header explaining the refactoring
- [ ] Update define_primitives() docstring with full task_rel documentation
- [ ] Document ProofChecker alignment (reference Frame.lean:72)
- [ ] Update any inline comments referencing old task function
- [ ] Add docstring to new helper methods (is_valid_duration, build_task_rel_at)

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (module header, docstrings)

**Verification**:
- Module docstring includes migration note with date
- All new methods have docstrings
- ProofChecker alignment is explicitly documented

## Testing & Validation

- [ ] Z3 solver accepts new frame constraints without type errors
- [ ] Bimodal test suite passes completely
- [ ] Model iteration generates correct task_rel differences
- [ ] Model injection enumerates correct number of constraints
- [ ] No grep results for `\.task\(` in bimodal source files (only `task_rel`)
- [ ] No grep results for `hasattr.*'task'` (should be `task_rel`)

## Artifacts & Outputs

- plans/02_clean-break-plan.md (this file)
- Modified: code/src/model_checker/theory_lib/bimodal/semantic.py
- Modified: code/src/model_checker/theory_lib/bimodal/iterate.py
- Modified: test files with task relation references

## Rollback/Contingency

If implementation reveals unexpected issues:
1. Git stash or revert uncommitted changes
2. The binary task relation can be restored from git history
3. Task 92 (frame constraint axioms) may need scope adjustment based on findings
4. Consider hybrid approach only if clean-break proves unworkable (unlikely given research findings)
