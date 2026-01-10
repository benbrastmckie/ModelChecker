# Implementation Plan: Fix Truth.lean Build Error (swap_past_future proof)

- **Task**: 184 - Fix Truth.lean build error (swap_past_future proof)
- **Status**: [IN PROGRESS]
- **Started**: 2025-12-26
- **Effort**: 1 hour
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: 
  - .opencode/specs/184_truth_lean_build_error/reports/research-001.md
- **Artifacts**: 
  - plans/implementation-001.md (this file)
  - summaries/implementation-summary-YYYYMMDD.md (created upon completion)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: lean
- **Lean Intent**: true

## Overview

Fix the build error in `Logos/Core/Semantics/Truth.lean` at line 636. The current code uses a helper lemma `swap_preserves_truth_backward` that has a tactic ordering bug: it rewrites the goal before introducing the hypothesis, causing a type mismatch. The research report recommended a direct fix using `rw [← Formula.swap_past_future_involution φ]` followed by `exact h F M τ t ht`, which is simpler and correct. This is a critical blocker for task 173 (integration tests) as it prevents compilation of all test files.

## Goals & Non-Goals

**Goals:**
- Fix the type mismatch error at Truth.lean:636
- Ensure Truth.lean compiles successfully
- Verify no regressions in downstream modules
- Unblock task 173 integration test compilation

**Non-Goals:**
- Refactor other parts of Truth.lean
- Add new functionality
- Modify theorem signatures or APIs
- Update documentation (no API changes)

## Risks & Mitigations

**Risk:** The fix might break downstream code that depends on `swap_preserves_truth_backward` helper lemma.
**Mitigation:** Very low risk - the helper lemma was just added and is only used once in the same file. We can remove it entirely and use the direct fix from the research report.

**Risk:** The recommended fix might not work as expected.
**Mitigation:** Very low risk - the research report provides detailed proof analysis and the fix follows standard Lean proof patterns. Alternative approaches are documented if needed.

**Risk:** Downstream modules might fail to build after the fix.
**Mitigation:** Low risk - this is an internal proof change with no API modifications. We'll verify downstream builds in Phase 2.

## Implementation Phases

### Phase 1: Verification [IN PROGRESS]

- **Goal:** Verify current build error and understand the exact failure mode
- **Tasks:**
  - [ ] Build Truth.lean and capture exact error message
  - [ ] Confirm error is at line 636 in `swap_preserves_truth_backward`
  - [ ] Verify error matches research report description (type mismatch)
  - [ ] Document current error state for comparison
- **Timing:** 5 minutes
- **Expected Outcome:** Clear understanding of current error and confirmation that research analysis is accurate

### Phase 2: Apply Fix [NOT STARTED]

- **Goal:** Fix the `is_valid_swap_involution` theorem using research-recommended approach
- **Tasks:**
  - [ ] Remove the `swap_preserves_truth_backward` helper lemma (lines 625-636)
  - [ ] Replace `is_valid_swap_involution` proof with direct fix:
    ```lean
    theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
        is_valid T φ := by
      intro F M τ t ht
      rw [← Formula.swap_past_future_involution φ]
      exact h F M τ t ht
    ```
  - [ ] Verify the fix compiles locally
  - [ ] Check for any warnings introduced
- **Timing:** 10 minutes
- **Expected Outcome:** Truth.lean compiles successfully with no errors or warnings

### Phase 3: Downstream Verification [NOT STARTED]

- **Goal:** Verify no regressions in modules that import Truth.lean
- **Tasks:**
  - [ ] Build `Logos.Core.Semantics.Validity` (direct dependent)
  - [ ] Build `Logos.Core.Metalogic.Soundness` (uses Truth.lean)
  - [ ] Build `Logos.Core.Semantics` (parent module)
  - [ ] Build `LogosTest.Core.Semantics` (test module)
  - [ ] Build `LogosTest.Core.Metalogic.SoundnessTest` (metalogic tests)
  - [ ] Verify all builds succeed with no new errors
- **Timing:** 15 minutes
- **Expected Outcome:** All downstream modules compile successfully

### Phase 4: Integration Test Verification [NOT STARTED]

- **Goal:** Verify that task 173 integration tests can now compile (blocked by this error)
- **Tasks:**
  - [ ] Build `LogosTest.Core.Integration` module
  - [ ] Verify integration test files compile (may still have other errors from task 185)
  - [ ] Document any remaining errors (expected: task 185 API mismatches)
  - [ ] Confirm this specific blocker is resolved
- **Timing:** 10 minutes
- **Expected Outcome:** Integration tests compile or fail with different errors (task 185), confirming this blocker is resolved

### Phase 5: Testing & Completion [NOT STARTED]

- **Goal:** Run existing tests and mark task complete
- **Tasks:**
  - [ ] Run `lake exe test` for Semantics tests
  - [ ] Run `lake exe test` for Metalogic tests
  - [ ] Verify no test regressions
  - [ ] Create implementation summary in summaries/
  - [ ] Update TODO.md status to [COMPLETED]
  - [ ] Update state.json with completion timestamp
  - [ ] Commit changes with descriptive message
- **Timing:** 15 minutes
- **Expected Outcome:** All tests pass, task marked complete, changes committed

## Testing & Validation

**Build Tests:**
- [ ] `lake build Logos.Core.Semantics.Truth` succeeds
- [ ] `lake build Logos.Core.Semantics.Validity` succeeds
- [ ] `lake build Logos.Core.Metalogic.Soundness` succeeds
- [ ] `lake build LogosTest.Core.Semantics` succeeds
- [ ] `lake build LogosTest.Core.Metalogic.SoundnessTest` succeeds
- [ ] `lake build LogosTest.Core.Integration` succeeds or fails with different errors

**Test Execution:**
- [ ] `lake exe test` for Semantics module passes
- [ ] `lake exe test` for Metalogic module passes
- [ ] No test regressions compared to baseline

**Quality Checks:**
- [ ] No new compiler warnings introduced
- [ ] Proof remains readable and maintainable
- [ ] Code follows Lean style guide

## Artifacts & Outputs

**Primary Artifacts:**
- `.opencode/specs/184_truth_lean_build_error/plans/implementation-001.md` (this file)
- `.opencode/specs/184_truth_lean_build_error/summaries/implementation-summary-YYYYMMDD.md` (created upon completion)

**Modified Files:**
- `Logos/Core/Semantics/Truth.lean` (lines 625-645, remove helper lemma and fix proof)

**State Updates:**
- `.opencode/specs/TODO.md` (status: [IN PROGRESS] → [COMPLETED])
- `.opencode/specs/state.json` (completion timestamp, activity log)

## Rollback/Contingency

**If the recommended fix fails:**
1. Try Alternative Approach B from research report (using `convert` tactic):
   ```lean
   theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
       is_valid T φ := by
     intro F M τ t ht
     convert h F M τ t ht
     exact Formula.swap_past_future_involution φ
   ```

2. If both approaches fail, restore original code and escalate for further research

**If downstream builds fail:**
1. Investigate specific failure
2. Verify no API changes were made
3. Check if failure is pre-existing (from other tasks)
4. Document findings and update plan

**Rollback procedure:**
- Revert changes to Truth.lean using git
- Restore original error state
- Update task status to [BLOCKED] with reason
- Create new research task if needed

## Success Criteria

**Primary:**
- [ ] Truth.lean compiles successfully with no errors
- [ ] Line 636 type mismatch error is resolved
- [ ] All downstream modules compile successfully
- [ ] No test regressions

**Secondary:**
- [ ] Integration tests from task 173 can compile (may have other errors from task 185)
- [ ] Proof is clean, readable, and follows Lean conventions
- [ ] Implementation summary documents the fix and verification results

**Completion Criteria:**
- [ ] All acceptance criteria from TODO.md task 184 are met
- [ ] Task status updated to [COMPLETED] in TODO.md and state.json
- [ ] Changes committed with descriptive message
- [ ] Task 173 unblocked (can proceed to task 185 for remaining errors)

## Notes

**Current Code Status:**
The code has already been modified from the broken version described in the research report. The current implementation uses a helper lemma `swap_preserves_truth_backward` instead of the broken `simpa` tactic. However, this helper lemma has its own bug: it rewrites the goal before introducing the hypothesis, causing a type mismatch.

**Research Recommendation:**
The research report recommends a simpler, direct fix that doesn't require a helper lemma. This approach is cleaner, more maintainable, and follows standard Lean proof patterns.

**Impact on Task 173:**
This fix is critical for task 173 (integration tests). The integration test implementation is complete with 106 new tests achieving 82% coverage, but the tests cannot compile due to this error (and errors in task 183 and task 185). Fixing this error is one of three blockers that must be resolved before task 173 can be verified as complete.

**Estimated Total Time:**
- Phase 1: 5 minutes
- Phase 2: 10 minutes
- Phase 3: 15 minutes
- Phase 4: 10 minutes
- Phase 5: 15 minutes
- **Total: 55 minutes** (well within 1 hour estimate)

**Risk Assessment:** Very Low
- Simple proof fix with no API changes
- Research provides detailed analysis and proven solution
- Helper lemma is only used once and can be safely removed
- Standard Lean proof pattern with low chance of failure
