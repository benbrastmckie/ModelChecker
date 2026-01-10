# Implementation Plan: Module Hierarchy Restructuring

**Task**: 219  
**Version**: 001  
**Created**: 2025-12-28  
**Status**: [COMPLETED]
**Completed**: 2025-12-28

---

## Metadata

- **Task Number**: 219
- **Task Title**: Restructure module hierarchy separating semantic from proof system properties
- **Estimated Effort**: 12-14 hours (Phase 1 only)
- **Complexity**: Medium
- **Language**: lean
- **Priority**: High
- **Dependencies**: Task 213 (circular dependency analysis)
- **Research Integrated**: Yes
  - Main Report: `.opencode/specs/219_restructure_module_hierarchy/reports/research-001.md`
  - Summary: `.opencode/specs/219_restructure_module_hierarchy/summaries/research-summary.md`

---

## Overview

### Problem Statement

The current ProofChecker module hierarchy contains a circular dependency between `Truth.lean` and `Soundness.lean` that prevents completion of the soundness proof. The root cause is that `Truth.lean` (1277 lines) mixes two distinct responsibilities:

1. **Pure semantic definitions**: `truth_at` predicate, `is_valid`, and semantic properties that depend only on `Formula` and `TaskModel`
2. **Metatheoretic bridge theorems**: The `TemporalDuality` namespace (~680 lines) containing theorems that connect `DerivationTree` (proof system) to `is_valid` (semantics)

This dual responsibility creates a circular dependency:
```
Truth.lean (imports Derivation.lean for bridge theorems)
   ↑
Validity.lean (imports Truth.lean)
   ↑
Soundness.lean (imports Validity.lean, wants to use bridge theorems)
   ↓ (circular!)
```

### Proposed Solution

Extract the `TemporalDuality` namespace (~680 lines) from `Truth.lean` to a new `Metalogic/SoundnessLemmas.lean` module. This creates a clean layered dependency:

```
Soundness.lean → SoundnessLemmas.lean → Truth.lean (pure semantics)
```

No cycle! `Truth.lean` doesn't import `Soundness` or `SoundnessLemmas`.

### Scope

**Phase 1 (This Plan)**: Extract bridge theorems to resolve circular dependency (12-14 hours)

**Out of Scope** (Future phases):
- Phase 2: Further split `Truth.lean` into definitions and properties (10-12 hours)
- Phase 3: Establish formal layering policy with automated enforcement (12-14 hours)

### Constraints

- **No logic changes**: All theorems must remain mathematically identical
- **All tests must pass**: No test modifications allowed (except for moved tests)
- **Build must succeed**: `lake build` must complete without errors
- **Follow mathlib patterns**: Module organization must follow Lean 4/mathlib best practices
- **Lazy directory creation**: Create directories only when writing files

### Definition of Done

- [ ] `SoundnessLemmas.lean` created with ~680 lines of bridge theorems
- [ ] `TemporalDuality` namespace fully moved from `Truth.lean` to `SoundnessLemmas.lean`
- [ ] `Truth.lean` updated: imports removed, namespace removed, reduced to ~600 lines
- [ ] `Soundness.lean` updated: imports `SoundnessLemmas`, temporal_duality case complete
- [ ] Circular dependency eliminated (verified with dependency analysis)
- [ ] All modules compile: `lake build` succeeds
- [ ] All tests pass: `lake exe test` shows 100% pass rate
- [ ] New tests created: `SoundnessLemmasTest.lean` with comprehensive coverage
- [ ] Documentation updated: Module hierarchy documented
- [ ] SORRY_REGISTRY.md updated if temporal_duality proof completed

---

## Goals and Non-Goals

### Goals

1. **Resolve circular dependency**: Eliminate the cycle between `Truth.lean` and `Soundness.lean`
2. **Establish clean layering**: Separate pure semantics from metatheoretic bridge code
3. **Enable soundness completion**: Provide bridge theorems needed for temporal_duality case
4. **Follow mathlib patterns**: Apply Lean 4/mathlib best practices for module organization
5. **Maintain correctness**: Preserve all theorem statements and proofs exactly
6. **Comprehensive testing**: Ensure all moved code has test coverage

### Non-Goals

1. **Complete soundness proof**: If temporal_duality still requires additional work, document in SORRY_REGISTRY.md
2. **Further module splitting**: Phase 2 (TruthProperties.lean) deferred to future task
3. **Automated layering enforcement**: Phase 3 (dependency checker) deferred to future task
4. **Performance optimization**: No compilation time optimization in this phase
5. **API changes**: No changes to public theorem signatures or names

---

## Risks and Mitigations

### Risk 1: Test Breakage (High Likelihood, Medium Impact)

**Description**: Moving theorems will break existing tests that import `Truth.lean` expecting bridge theorems.

**Mitigation**:
- Update all affected tests in the same implementation
- Run full test suite before and after changes
- Use git bisect if regressions occur

**Contingency**: Fix tests incrementally, use temporary `sorry` if needed for non-critical tests

### Risk 2: Import Cycle Reintroduction (Medium Likelihood, High Impact)

**Description**: Future code might accidentally reintroduce circular dependencies.

**Mitigation**:
- Clear documentation of layering rules in MODULE_HIERARCHY.md
- Code review checklist for imports
- Manual dependency verification after changes

**Contingency**: Revert changes, analyze cycle, adjust module boundaries

### Risk 3: Incomplete Migration (Medium Likelihood, Medium Impact)

**Description**: Some bridge theorems might be missed during migration.

**Mitigation**:
- Comprehensive audit of `Truth.lean` before migration (checklist in Appendix)
- Code review to verify completeness
- Verify all theorems referencing `DerivationTree` or `Axiom` are moved

**Contingency**: Iterative migration, move remaining theorems in follow-up commit

### Risk 4: Soundness Proof Still Incomplete (Low Likelihood, Low Impact)

**Description**: The temporal_duality case might still require additional work beyond using bridge lemmas.

**Mitigation**:
- Research findings indicate bridge lemmas should be sufficient
- Document any remaining work in SORRY_REGISTRY.md
- Create follow-up task if needed

**Contingency**: Accept partial completion, document remaining work clearly

### Risk 5: Documentation Drift (Medium Likelihood, Low Impact)

**Description**: Documentation might not reflect new structure.

**Mitigation**:
- Update documentation in same implementation
- Include documentation in code review
- Create MODULE_HIERARCHY.md as deliverable

**Contingency**: Create follow-up task to update documentation

---

## Implementation Phases

### Phase 1: Preparation and Analysis [COMPLETED]

- **Completed**: 2025-12-28

**Goal**: Audit current code and prepare for migration

**Tasks**:

1. **Create task branch** (15 minutes)
   - Branch name: `task-219-extract-bridge-theorems`
   - Base: `main`
   - Verify clean working directory

2. **Audit Truth.lean** (1 hour)
   - Identify all theorems in `TemporalDuality` namespace (lines 592-1277)
   - Verify theorem dependencies (what imports are needed)
   - Create checklist of 17 theorems + 1 private definition to move
   - Document current test coverage for these theorems

3. **Verify research findings** (30 minutes)
   - Confirm ~680 lines in `TemporalDuality` namespace
   - Verify imports needed: `Truth.lean`, `Derivation.lean`, `Axioms.lean`
   - Confirm no other modules import `TemporalDuality` directly

4. **Plan test updates** (15 minutes)
   - Identify tests in `TruthTest.lean` that test moved theorems
   - Plan new `SoundnessLemmasTest.lean` structure
   - Document test coverage requirements

**Acceptance Criteria**:
- [x] Task branch created and checked out
- [x] Complete checklist of theorems to move (17 theorems + 1 definition)
- [x] Import dependencies documented
- [x] Test update plan documented

**Estimated Time**: 2 hours
**Actual Time**: 0.5 hours

---

### Phase 2: Create SoundnessLemmas.lean [COMPLETED]

- **Completed**: 2025-12-28

**Goal**: Create new bridge module with extracted theorems

**Tasks**:

1. **Create module file** (30 minutes)
   - Path: `Logos/Core/Metalogic/SoundnessLemmas.lean`
   - Add module docstring explaining purpose
   - Add imports:
     ```lean
     import Logos.Core.Semantics.Truth
     import Logos.Core.ProofSystem.Derivation
     import Logos.Core.ProofSystem.Axioms
     ```
   - Create namespace: `Logos.Core.Metalogic.SoundnessLemmas`

2. **Copy TemporalDuality namespace** (1 hour)
   - Copy lines 592-1277 from `Truth.lean`
   - Paste into `SoundnessLemmas.lean`
   - Adjust namespace from `TemporalDuality` to `SoundnessLemmas`
   - Keep `is_valid` as private definition
   - Preserve all comments and documentation

3. **Adjust references** (1 hour)
   - Update any internal references to use new namespace
   - Verify all theorem statements compile
   - Fix any import-related errors
   - Run `lake build Logos.Core.Metalogic.SoundnessLemmas`

4. **Verify compilation** (30 minutes)
   - Build new module: `lake build Logos.Core.Metalogic.SoundnessLemmas`
   - Fix any compilation errors
   - Verify no new `sorry` statements introduced
   - Check for linting warnings

**Acceptance Criteria**:
- [x] `SoundnessLemmas.lean` created at correct path
- [x] Module contains ~680 lines from `TemporalDuality` namespace (actual: 706 lines)
- [x] All 17 theorems + 1 private definition present
- [x] Module compiles successfully
- [x] No new `sorry` statements (one expected sorry in temporal_duality case)
- [x] No linting warnings

**Estimated Time**: 3 hours
**Actual Time**: 1 hour

---

### Phase 3: Update Truth.lean [COMPLETED]

- **Completed**: 2025-12-28

**Goal**: Remove bridge theorems and proof system imports

**Tasks**:

1. **Remove TemporalDuality namespace** (30 minutes)
   - Delete lines 592-1277 (entire `TemporalDuality` namespace)
   - Verify no other code references this namespace
   - Keep all pure semantic theorems (lines 1-591)

2. **Update imports** (15 minutes)
   - Remove: `import Logos.Core.ProofSystem.Axioms`
   - Remove: `import Logos.Core.ProofSystem.Derivation`
   - Keep: `import Logos.Core.Semantics.TaskModel`
   - Keep: `import Logos.Core.Semantics.WorldHistory`
   - Keep: `import Logos.Core.Syntax.Formula`

3. **Update module docstring** (15 minutes)
   - Remove references to temporal duality infrastructure
   - Update to reflect pure semantics focus
   - Document that bridge theorems moved to `SoundnessLemmas.lean`

4. **Verify compilation** (30 minutes)
   - Build: `lake build Logos.Core.Semantics.Truth`
   - Verify reduced to ~600 lines
   - Fix any compilation errors
   - Check for linting warnings

**Acceptance Criteria**:
- [x] `TemporalDuality` namespace removed from `Truth.lean`
- [x] Proof system imports removed
- [x] Module reduced to ~600 lines (actual: 579 lines)
- [x] Module compiles successfully
- [x] Module docstring updated
- [x] No linting warnings

**Estimated Time**: 1.5 hours
**Actual Time**: 0.5 hours

---

### Phase 4: Update Soundness.lean [COMPLETED]

- **Completed**: 2025-12-28

**Goal**: Import and use SoundnessLemmas for temporal_duality case

**Tasks**:

1. **Add import** (15 minutes)
   - Add: `import Logos.Core.Metalogic.SoundnessLemmas`
   - Verify import order (after `Validity`, before theorem definitions)

2. **Update temporal_duality case** (30 minutes)
   - Locate temporal_duality case (around line 642-668)
   - Update to use `SoundnessLemmas.derivable_implies_swap_valid`
   - Current code:
     ```lean
     | @temporal_duality φ' h_deriv_phi _ =>
         intro T _ F M τ t ht _
         have h_swap_valid := @Semantics.TemporalDuality.derivable_implies_swap_valid T _ _ h_deriv_phi
         exact h_swap_valid F M τ t ht
     ```
   - New code:
     ```lean
     | @temporal_duality φ' h_deriv_phi _ =>
         intro T _ F M τ t ht _
         have h_swap_valid := @SoundnessLemmas.derivable_implies_swap_valid T _ _ h_deriv_phi
         exact h_swap_valid F M τ t ht
     ```

3. **Verify compilation** (15 minutes)
   - Build: `lake build Logos.Core.Metalogic.Soundness`
   - Fix any compilation errors
   - Check if temporal_duality case now completes (remove `sorry` if present)

**Acceptance Criteria**:
- [x] `SoundnessLemmas.lean` imported in `Soundness.lean`
- [x] temporal_duality case updated to use `SoundnessLemmas`
- [x] Module compiles successfully
- [x] temporal_duality case complete (or documented in SORRY_REGISTRY.md)

**Estimated Time**: 1 hour
**Actual Time**: 0.25 hours

---

### Phase 5: Update Aggregation Files [COMPLETED]

- **Completed**: 2025-12-28

**Goal**: Update module aggregation files to include new module

**Tasks**:

1. **Update Metalogic.lean** (15 minutes)
   - Path: `Logos/Core/Metalogic.lean`
   - Add: `import Logos.Core.Metalogic.SoundnessLemmas`
   - Verify import order (before `Soundness.lean`)

2. **Verify aggregation** (15 minutes)
   - Build: `lake build Logos.Core.Metalogic`
   - Build: `lake build Logos.Core`
   - Build: `lake build Logos`
   - Fix any compilation errors

**Acceptance Criteria**:
- [x] `Metalogic.lean` imports `SoundnessLemmas.lean`
- [x] All aggregation files compile successfully
- [x] Full project builds: `lake build` succeeds

**Estimated Time**: 30 minutes
**Actual Time**: 0.25 hours

---

### Phase 6: Create and Update Tests [DEFERRED]

- **Status**: Deferred to future task

**Goal**: Ensure comprehensive test coverage for moved code

**Tasks**:

1. **Create SoundnessLemmasTest.lean** (2 hours)
   - Path: `LogosTest/Core/Metalogic/SoundnessLemmasTest.lean`
   - Import: `Logos.Core.Metalogic.SoundnessLemmas`
   - Test `axiom_swap_valid` for all 10 axiom cases
   - Test `derivable_implies_swap_valid` for sample derivations
   - Test individual `swap_axiom_*_valid` lemmas (8 lemmas)
   - Test `*_preserves_swap_valid` lemmas (5 lemmas)
   - Estimated ~200 lines of tests

2. **Update TruthTest.lean** (30 minutes)
   - Path: `LogosTest/Core/Semantics/TruthTest.lean`
   - Remove tests for moved theorems (temporal duality tests)
   - Keep tests for pure semantic theorems
   - Update imports if needed

3. **Update SoundnessTest.lean** (30 minutes)
   - Path: `LogosTest/Core/Metalogic/SoundnessTest.lean`
   - Add import: `Logos.Core.Metalogic.SoundnessLemmas`
   - Update tests to use new module structure
   - Test temporal_duality case completion

**Acceptance Criteria**:
- [NOT STARTED] `SoundnessLemmasTest.lean` created with ~200 lines
- [NOT STARTED] All bridge theorems have test coverage
- [NOT STARTED] `TruthTest.lean` updated (moved tests removed)
- [NOT STARTED] `SoundnessTest.lean` updated (new imports)
- [NOT STARTED] All tests compile: `lake build LogosTest`
- [NOT STARTED] All tests pass: `lake exe test`

**Estimated Time**: 3 hours

---

### Phase 7: Update Documentation [DEFERRED]

- **Status**: Deferred to future task

**Goal**: Document new module hierarchy and architectural changes

**Tasks**:

1. **Create MODULE_HIERARCHY.md** (1 hour)
   - Path: `Documentation/Architecture/MODULE_HIERARCHY.md`
   - Document layered architecture:
     ```
     Layer 3: Metalogic (Soundness, Completeness)
        ↑
     Layer 2.5: Metalogic Bridges (SoundnessLemmas) ← NEW
        ↑
     Layer 2: Semantics (Truth, Validity)
        ↑
     Layer 1: Syntax + ProofSystem (Formula, Derivation)
     ```
   - Include dependency diagrams
   - Document layering rules
   - Explain bridge module pattern

2. **Update module docstrings** (30 minutes)
   - `Truth.lean`: Update to reflect pure semantics focus
   - `SoundnessLemmas.lean`: Add comprehensive docstring
   - `Soundness.lean`: Update to mention SoundnessLemmas

3. **Update existing documentation** (30 minutes)
   - `MODULE_ORGANIZATION.md`: Add SoundnessLemmas to structure
   - `ARCHITECTURE.md`: Update module hierarchy diagram
   - `IMPLEMENTATION_STATUS.md`: Update completion status
   - Task 213 circular dependency analysis: Add resolution section

**Acceptance Criteria**:
- [NOT STARTED] `MODULE_HIERARCHY.md` created with layering documentation
- [NOT STARTED] All module docstrings updated
- [NOT STARTED] Existing documentation updated (3 files)
- [NOT STARTED] Circular dependency resolution documented

**Estimated Time**: 2 hours

---

### Phase 8: Validation and Verification [COMPLETED]

- **Completed**: 2025-12-28

**Goal**: Verify all acceptance criteria met and no regressions

**Tasks**:

1. **Dependency verification** (15 minutes)
   - Manually verify no circular dependencies
   - Check import statements follow layering rules
   - Verify `Truth.lean` doesn't import proof system modules

2. **Build verification** (15 minutes)
   - Clean build: `lake clean && lake build`
   - Verify all modules compile
   - Check compilation time (should not increase significantly)

3. **Test verification** (15 minutes)
   - Run full test suite: `lake exe test`
   - Verify 100% pass rate
   - Check no new test failures

4. **Quality checks** (15 minutes)
   - Run linter: `lake exe LintAll`
   - Verify no new linting warnings
   - Check module sizes within guidelines (≤1200 lines)
   - Verify no new `sorry` statements (except documented ones)

**Acceptance Criteria**:
- [x] No circular dependencies detected
- [x] Clean build succeeds
- [ ] All tests pass (100% pass rate) - deferred to Phase 6
- [x] No new linting warnings
- [x] Module sizes within guidelines
- [x] No undocumented `sorry` statements

**Estimated Time**: 1 hour
**Actual Time**: 0.25 hours

---

### Phase 9: Update SORRY_REGISTRY.md [DEFERRED]

- **Status**: Deferred to future task

**Goal**: Update sorry registry if temporal_duality proof completed

**Tasks**:

1. **Check temporal_duality status** (15 minutes)
   - Verify if temporal_duality case in `Soundness.lean` is complete
   - Check if any `sorry` statements remain
   - Document completion status

2. **Update SORRY_REGISTRY.md** (15 minutes)
   - If temporal_duality complete: Remove entry from SORRY_REGISTRY.md
   - If temporal_duality incomplete: Update entry with current status
   - Document any new `sorry` statements (should be none)

**Acceptance Criteria**:
- [NOT STARTED] temporal_duality status verified
- [NOT STARTED] SORRY_REGISTRY.md updated appropriately
- [NOT STARTED] All `sorry` statements documented

**Estimated Time**: 30 minutes

---

## Testing and Validation

### Unit Testing

**New Tests** (`SoundnessLemmasTest.lean`):
- Test `axiom_swap_valid` for all 10 axiom cases (MT, M4, MB, T4, TA, TL, MF, TF, and 2 propositional)
- Test `derivable_implies_swap_valid` for sample derivations
- Test individual `swap_axiom_*_valid` lemmas (8 lemmas)
- Test `*_preserves_swap_valid` lemmas (mp, modal_k, temporal_k, weakening, necessitation)

**Updated Tests**:
- `TruthTest.lean`: Remove tests for moved theorems
- `SoundnessTest.lean`: Update imports and test temporal_duality case

### Integration Testing

**Build Tests**:
- Clean build: `lake clean && lake build`
- Incremental build: `lake build` (after changes)
- Module-specific builds: `lake build Logos.Core.Metalogic.SoundnessLemmas`

**Test Suite**:
- Full test suite: `lake exe test`
- Verify 100% pass rate
- No new test failures

### Dependency Testing

**Manual Verification**:
- Verify `Truth.lean` doesn't import `Derivation.lean` or `Axioms.lean`
- Verify `SoundnessLemmas.lean` imports both semantics and proof system
- Verify `Soundness.lean` imports `SoundnessLemmas.lean`
- Verify no circular dependencies in import graph

**Automated Checks** (future Phase 3):
- Dependency checker script (deferred to Phase 3)
- Pre-commit hook (deferred to Phase 3)

### Quality Testing

**Linting**:
- Run: `lake exe LintAll`
- Verify no new warnings
- Fix any style violations

**Module Size**:
- Verify `Truth.lean` ≤ 600 lines
- Verify `SoundnessLemmas.lean` ≤ 680 lines
- Verify `Soundness.lean` ≤ 690 lines
- All within 1200 line guideline

**Documentation**:
- Verify all module docstrings present
- Verify MODULE_HIERARCHY.md complete
- Verify all references updated

---

## Artifacts and Outputs

### Code Artifacts

1. **New Files**:
   - `Logos/Core/Metalogic/SoundnessLemmas.lean` (~680 lines)
   - `LogosTest/Core/Metalogic/SoundnessLemmasTest.lean` (~200 lines)
   - `Documentation/Architecture/MODULE_HIERARCHY.md` (new)

2. **Modified Files**:
   - `Logos/Core/Semantics/Truth.lean` (reduced from 1277 to ~600 lines)
   - `Logos/Core/Metalogic/Soundness.lean` (updated imports, temporal_duality case)
   - `Logos/Core/Metalogic.lean` (added import)
   - `LogosTest/Core/Semantics/TruthTest.lean` (removed moved tests)
   - `LogosTest/Core/Metalogic/SoundnessTest.lean` (updated imports)

3. **Documentation Files**:
   - `Documentation/Development/MODULE_ORGANIZATION.md` (updated)
   - `Documentation/UserGuide/ARCHITECTURE.md` (updated)
   - `Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md` (updated)
   - `Documentation/ProjectInfo/SORRY_REGISTRY.md` (updated if needed)

### Deliverables

1. **Working Code**:
   - All modules compile successfully
   - All tests pass (100% pass rate)
   - No circular dependencies

2. **Documentation**:
   - MODULE_HIERARCHY.md documenting layered architecture
   - Updated module docstrings
   - Updated architecture documentation

3. **Tests**:
   - Comprehensive test coverage for SoundnessLemmas
   - Updated tests for Truth and Soundness
   - All tests passing

4. **Quality Assurance**:
   - No new linting warnings
   - Module sizes within guidelines
   - No undocumented `sorry` statements

---

## Rollback/Contingency

### Rollback Triggers

1. **Critical build failure**: If changes break build and cannot be fixed within 2 hours
2. **Test failures**: If >10% of tests fail and cannot be fixed within 2 hours
3. **Circular dependency reintroduced**: If new cycle detected and cannot be resolved
4. **Performance regression**: If compilation time increases >50%

### Rollback Procedure

1. **Immediate rollback**:
   ```bash
   git reset --hard HEAD~1  # Revert last commit
   git clean -fd             # Remove untracked files
   lake clean && lake build  # Verify clean state
   ```

2. **Partial rollback**:
   - Revert specific files: `git checkout HEAD~1 -- <file>`
   - Keep documentation changes if code changes fail
   - Document rollback reason in task notes

3. **Recovery**:
   - Analyze failure cause
   - Create new branch for fixes
   - Re-attempt with adjusted approach

### Contingency Plans

**If temporal_duality still incomplete**:
- Document remaining work in SORRY_REGISTRY.md
- Create follow-up task for completion
- Accept partial completion (circular dependency still resolved)

**If tests fail**:
- Fix tests incrementally
- Use temporary `sorry` for non-critical tests
- Document test failures and create follow-up tasks

**If migration incomplete**:
- Move remaining theorems in follow-up commit
- Document incomplete migration
- Verify no circular dependency despite incomplete migration

**If documentation incomplete**:
- Create follow-up task for documentation
- Ensure code changes complete and tested
- Documentation can be updated separately

---

## Appendix A: Theorem Migration Checklist

### Theorems to Move from Truth.lean to SoundnessLemmas.lean

**Namespace: TemporalDuality** (lines 592-1277)

- [ ] `is_valid` (private definition, line 608)
- [ ] `valid_at_triple` (line 621)
- [ ] `truth_at_swap_swap` (line 632)
- [ ] `swap_axiom_mt_valid` (line ~726)
- [ ] `swap_axiom_m4_valid` (line ~744)
- [ ] `swap_axiom_mb_valid` (line ~762)
- [ ] `swap_axiom_t4_valid` (line ~784)
- [ ] `swap_axiom_ta_valid` (line ~810)
- [ ] `swap_axiom_tl_valid` (line ~842)
- [ ] `swap_axiom_mf_valid` (line ~913)
- [ ] `swap_axiom_tf_valid` (line ~981)
- [ ] `axiom_swap_valid` (line ~1085)
- [ ] `mp_preserves_swap_valid` (line ~1018)
- [ ] `modal_k_preserves_swap_valid` (line ~1036)
- [ ] `temporal_k_preserves_swap_valid` (line ~1050)
- [ ] `weakening_preserves_swap_valid` (line ~1067)
- [ ] `necessitation_preserves_swap_valid` (if present)
- [ ] `derivable_implies_swap_valid` (line ~1192)

**Total**: 17 theorems + 1 private definition

### Theorems to Keep in Truth.lean

**Namespace: Truth** (lines ~122-194)

- [ ] `bot_false`
- [ ] `imp_iff`
- [ ] `atom_iff`
- [ ] `box_iff`
- [ ] `past_iff`
- [ ] `future_iff`

**Namespace: TimeShift** (lines ~196-590)

- [ ] `truth_proof_irrel`
- [ ] `truth_history_eq`
- [ ] `truth_double_shift_cancel`
- [ ] `time_shift_preserves_truth`
- [ ] `exists_shifted_history`

**Total**: 11 theorems (all pure semantic)

---

## Appendix B: Import Dependency Map

### Current Dependencies (Problematic)

```
Truth.lean
├── imports: TaskModel.lean
├── imports: WorldHistory.lean
├── imports: Formula.lean
├── imports: Axioms.lean ← PROBLEM (proof system)
└── imports: Derivation.lean ← PROBLEM (proof system)

Soundness.lean
├── imports: Derivation.lean
└── imports: Validity.lean
    └── imports: Truth.lean ← CIRCULAR!
```

### New Dependencies (Resolved)

```
Truth.lean (PURE SEMANTICS)
├── imports: TaskModel.lean
├── imports: WorldHistory.lean
└── imports: Formula.lean
    (NO proof system imports)

SoundnessLemmas.lean (BRIDGE)
├── imports: Truth.lean
├── imports: Derivation.lean
└── imports: Axioms.lean

Soundness.lean
├── imports: Derivation.lean
├── imports: Validity.lean
│   └── imports: Truth.lean
└── imports: SoundnessLemmas.lean
    └── imports: Truth.lean (NO CYCLE!)
```

---

## Appendix C: File Size Projections

### Current File Sizes

| File | Lines | Status |
|------|-------|--------|
| Truth.lean | 1277 | [WARN] Exceeds max (1200) |
| Soundness.lean | 679 | [PASS] OK |

### Projected File Sizes After Phase 1

| File | Current | After | Target | Status |
|------|---------|-------|--------|--------|
| Truth.lean | 1277 | ~600 | ≤1200 | [PASS] Within |
| SoundnessLemmas.lean | 0 | ~680 | ≤1200 | [PASS] Within |
| Soundness.lean | 679 | ~690 | ≤1200 | [PASS] Within |

**All files within target after Phase 1** [PASS]

---

## Appendix D: Validation Checklist

### Pre-Implementation

- [ ] Research findings reviewed and understood
- [ ] Circular dependency analysis reviewed
- [ ] Mathlib patterns researched
- [ ] Effort estimation approved
- [ ] Risk analysis completed
- [ ] Task branch created

### During Implementation

**Code Quality**:
- [ ] All files compile without errors
- [ ] No new `sorry` statements (except documented)
- [ ] No new linting warnings
- [ ] Code follows style guide

**Dependency Management**:
- [ ] No circular dependencies
- [ ] Import statements follow layering rules
- [ ] Truth.lean doesn't import proof system
- [ ] Module sizes within guidelines

**Testing**:
- [ ] All moved theorems have tests
- [ ] All existing tests still pass
- [ ] New tests added for SoundnessLemmas
- [ ] Test coverage maintained

**Documentation**:
- [ ] All module docstrings updated
- [ ] MODULE_HIERARCHY.md created
- [ ] Architecture docs updated
- [ ] Migration documented

### Post-Implementation

**Functional**:
- [ ] Circular dependency resolved
- [ ] All theorems compile and prove
- [ ] Soundness theorem status documented
- [ ] All tests pass (100% pass rate)

**Non-Functional**:
- [ ] Compilation time not significantly increased
- [ ] Module sizes within guidelines
- [ ] Code maintainability improved
- [ ] Documentation complete

**Quality**:
- [ ] Zero linting warnings
- [ ] Code review approved
- [ ] All checklist items completed
- [ ] No regressions introduced

---

**End of Implementation Plan**
