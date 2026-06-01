# Implementation Plan: Task #110 - Frame Class Validation for Base Frame

- **Task**: 110 - Frame class validation for Base frame
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: 100 (completed)
- **Research Inputs**: specs/110_frame_class_validation/reports/01_frame-class-validation.md
- **Artifacts**: plans/01_frame-class-validation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

This task validates and documents the correspondence between the Z3 oracle's "Base" frame class and BimodalLogic's TaskFrame structure. Research found that the Z3 oracle's three active frame axioms (nullity_identity, forward_comp, converse) map exactly to BimodalLogic's `TaskFrame` structure fields, but the term "Base" in `supported_frame_classes` conflates two distinct concepts: the proof-system `FrameClass.Base` (37 axioms) and the semantic `TaskFrame` axiom satisfaction. The implementation documents this mapping in provider.py, analyzes the disabled task_restriction constraint's soundness implications, and creates a test suite that post-hoc validates extracted countermodels against the documented frame axioms.

### Research Integration

The research report (01_frame-class-validation.md) provided:
- Complete axiom mapping table (Z3 oracle constraints to BimodalLogic TaskFrame.lean fields)
- Analysis of 8 additional model-building constraints beyond the 3 TaskFrame axioms
- Soundness analysis of disabled task_restriction (not a soundness issue for countermodel generation)
- Terminology mismatch identification ("Base" in oracle vs "Base" in FrameClass)
- Test plan with 5 test classes for post-hoc countermodel validation

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Document the exact mapping between Z3 frame axioms and BimodalLogic's TaskFrame Lean axioms in provider.py
- Document the soundness analysis of the disabled task_restriction constraint
- Document the Z3 frame hierarchy and what "Base" means in the oracle context
- Write test_frame_class_mapping.py with post-hoc validation of extracted countermodels against frame axioms

**Non-Goals**:
- Enable or modify the task_restriction constraint (future work)
- Rename "Base" in supported_frame_classes (that is a task 103 concern when OracleProvider is implemented)
- Modify the Z3 frame axiom implementation in semantic.py
- Add seriality or density constraints to the oracle

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Countermodel extraction API changes before task 103 | M | L | Tests use existing BimodalStructure extraction methods which are stable |
| Test examples take too long under full solver | M | M | Use small N=2, M=3 settings; select fast-solving examples |
| Provider.py is a placeholder stub that task 103 will overwrite | M | H | Place frame hierarchy documentation in a docstring module-level comment that task 103 will preserve; also add documentation in semantic.py near the frame axiom builders |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Document Frame Axiom Mapping and Hierarchy [COMPLETED]

**Goal**: Add comprehensive documentation of the Z3-to-BimodalLogic frame axiom correspondence in both provider.py and semantic.py.

**Tasks**:
- [x] Add module-level docstring to `code/src/bimodal_logic/provider.py` documenting:
  - The three TaskFrame axioms (nullity_identity, forward_comp, converse) and their Z3 implementations
  - The mapping table: Z3 constraint builder -> BimodalLogic TaskFrame.lean field -> semantic type (TaskFrame axiom vs model-building)
  - The terminology distinction: "Base" in `supported_frame_classes` means TaskFrame axiom satisfaction, NOT BimodalLogic's proof-system `FrameClass.Base`
  - The bounded domain approximation: Z3 uses `(-M, M)` integer time; Lean uses unbounded `Int`
  - The converse guard discrepancy: Z3 uses `is_valid_duration(d)` guard; Lean is unconditional
  - The forward_comp asymmetry: Z3 uses general duration guards; Lean restricts to `0 <= x, 0 <= y` (equivalent via converse)
- [x] Add frame hierarchy docstring to `build_frame_constraints()` in `code/src/model_checker/theory_lib/bimodal/semantic.py` summarizing:
  - Which constraints are TaskFrame axioms (items 7-9) vs model-building constraints (items 1-6, 8-9)
  - What the oracle guarantees about task_rel structure
  - What the oracle does NOT guarantee (task_restriction disabled, bounded domain)
- [x] Document task_restriction soundness analysis as a detailed comment block in `semantic.py` near the disabled constraint (lines 636-696), covering:
  - Why disabling task_restriction is sound for countermodel generation (UNSAT results are conservative in the larger domain)
  - The phantom task-pair gap: task_rel pairs not grounded in world histories may exist
  - The mitigation: post-hoc frame axiom checking via StructuredCountermodel.validate()

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/bimodal_logic/provider.py` - Module-level frame hierarchy docstring
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Enhanced docstrings on build_frame_constraints() and task_restriction block

**Verification**:
- `grep -c "TaskFrame" code/src/bimodal_logic/provider.py` returns nonzero (docstring present)
- `grep -c "soundness" code/src/model_checker/theory_lib/bimodal/semantic.py` returns nonzero
- No existing tests broken: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py -v`

---

### Phase 2: Create Test Infrastructure and Fixtures [NOT STARTED]

**Goal**: Set up the test_frame_class_mapping.py file with fixtures that produce solved BimodalStructure instances from known-countermodel examples.

**Tasks**:
- [ ] Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` with module docstring explaining its purpose (post-hoc frame axiom validation of extracted countermodels)
- [ ] Implement a pytest fixture that:
  - Creates a BimodalSemantics instance with small settings (N=2, M=3)
  - Constructs a formula known to have countermodels (select 2-3 from examples.py with `expectation=True`)
  - Runs the Z3 solver to obtain a satisfying model
  - Extracts model elements (world_histories, task_rel pairs) from the Z3 model
  - Returns the extracted data for post-hoc checking
- [ ] Implement helper functions for task_rel extraction:
  - `extract_task_rel_pairs(semantics, z3_model)` -> set of (source_state, duration, target_state) tuples
  - `extract_world_histories(semantics, z3_model)` -> dict mapping world_id to {time: state} dicts
- [ ] Write a smoke test that verifies the fixture produces non-empty countermodel data

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - New file

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v -k "smoke"` passes
- Fixture produces at least 1 world history and at least 1 task_rel pair

---

### Phase 3: Write Post-Hoc Frame Axiom Validation Tests [NOT STARTED]

**Goal**: Implement test classes that assert extracted countermodels satisfy the three TaskFrame axioms and lawful history property.

**Tasks**:
- [ ] `TestNullityIdentityPostHoc`: For every extracted task_rel pair with duration=0, assert source == target. For every distinct state in the countermodel, assert task_rel(s, 0, s) holds.
- [ ] `TestConversePostHoc`: For every extracted task_rel pair (s, d, u), assert (u, -d, s) is also present (within valid duration bounds).
- [ ] `TestForwardCompPostHoc`: For extracted task_rel pairs (s, d1, v) and (v, d2, u), assert (s, d1+d2, u) is present (within valid duration bounds).
- [ ] `TestLawfulHistoryPostHoc`: For every world history, assert that consecutive time points (t, t+1) have a corresponding task_rel pair (state_at_t, 1, state_at_t+1).
- [ ] `TestFrameClassDeclarationConsistency`: Assert that the oracle's "Base" frame class claim is justified by documenting what "Base" means and verifying the three TaskFrame axioms hold in the extracted model.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - Add test classes

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v` -- all tests pass
- Test count is at least 5 (one per test class)
- No existing tests broken: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

---

### Phase 4: Integration Verification and Cleanup [NOT STARTED]

**Goal**: Run full test suite to verify no regressions, and confirm all task deliverables are met.

**Tasks**:
- [ ] Run full bimodal test suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] Verify all 4 deliverables are addressed:
  1. Frame axiom mapping documented in provider.py (check docstring present)
  2. task_restriction soundness analysis documented in semantic.py (check comment block)
  3. Z3 frame hierarchy documented in provider.py (check hierarchy section)
  4. test_frame_class_mapping.py passes with post-hoc validation (check test results)
- [ ] Verify documentation consistency: ensure the axiom mapping in provider.py matches the actual constraint builders in semantic.py (cross-reference line numbers)
- [ ] Verify test coverage: each of the three TaskFrame axioms + lawful property has at least one dedicated test

**Timing**: 0.5 hours

**Depends on**: 2, 3

**Files to modify**:
- None (verification only, minor fixes if needed)

**Verification**:
- Full test suite passes with zero regressions
- All 4 task deliverables confirmed present
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v` reports 5+ tests passing

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v` -- all new tests pass
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py -v` -- existing frame constraint tests still pass
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` -- full bimodal test suite passes
- [ ] provider.py contains frame hierarchy documentation (grep for "TaskFrame")
- [ ] semantic.py contains task_restriction soundness analysis (grep for "soundness")

## Artifacts & Outputs

- `specs/110_frame_class_validation/plans/01_frame-class-validation.md` (this file)
- `code/src/bimodal_logic/provider.py` - Enhanced with frame hierarchy documentation
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Enhanced docstrings and soundness analysis
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - New test file

## Rollback/Contingency

All changes are additive (docstrings and a new test file). To revert:
- Remove the new test file: `test_frame_class_mapping.py`
- Revert docstring additions to provider.py and semantic.py via `git checkout` on those files
- No production code is modified, so rollback has zero risk of breaking existing functionality
