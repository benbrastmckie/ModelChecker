# Implementation Plan: Complete is_valid_swap_involution Proof (Revised)

**Project Number**: 193  
**Project Name**: prove_is_valid_swap_involution  
**Type**: bugfix  
**Priority**: High  
**Complexity**: Low (revised from Medium)  
**Estimated Total Hours**: 0.5  
**Total Phases**: 1  
**Language**: lean  
**Plan Version**: 2 (Revised 2025-12-28)

---

## Revision Context

**Previous Plan**: implementation-001.md (2 hours, single-phase)  
**Previous Status**: 85% complete (helper lemma done, main theorem blocked)  
**Reason for Revision**: Implementation revealed simpler solution than originally planned. Helper lemma `truth_at_swap_swap` already complete and proven. Only remaining work is adding involution helper and updating main theorem (30 minutes).

**Implementation Findings** (from implementation-001.md report):
- Helper lemma `truth_at_swap_swap` completed successfully (lines 632-671)
- All 6 structural induction cases proven correctly
- Main theorem blocked by type theory issue: cannot convert `truth_at ... φ.swap` to `truth_at ... φ.swap.swap` using propositional equality
- Clear solution identified: Add `truth_at_involution` helper that applies existing helper to `φ.swap`

---

## Overview

Complete the remaining 15% of task 193 by adding a simple involution helper lemma and updating the main theorem to use it. The bulk of the work (helper lemma with structural induction) is already complete. This revision focuses solely on the blocker resolution.

**What's Already Done** (from previous implementation):
- [PASS] Helper lemma `truth_at_swap_swap` with full structural induction (6 cases)
- [PASS] Build verification (compiles successfully)
- [PASS] Test verification (all tests pass)
- [PASS] Comprehensive inline documentation

**What Remains** (this revision):
- [FAIL] Add `truth_at_involution` helper (5 lines)
- [FAIL] Update main theorem to compose helpers (3 lines)
- [FAIL] Remove `sorry` from line 691

---

## Research Inputs

**Research Report**: `.opencode/specs/193_prove_is_valid_swap_involution/reports/research-001.md`  
**Implementation Report**: `.opencode/specs/193_prove_is_valid_swap_involution/reports/implementation-001.md`  
**Implementation Summary**: `.opencode/specs/193_prove_is_valid_swap_involution/summaries/implementation-summary.md`

**Key Implementation Findings**:
- Type theory issue: Cannot transport `truth_at M τ t ht φ.swap` to `truth_at M τ t ht φ.swap.swap` via propositional equality `φ.swap.swap = φ.swap`
- Root cause: `truth_at` is pattern-matched (structural recursion), preventing automatic equality transport
- Solution: Apply existing helper to `φ.swap` instead of `φ`, then compose
- Precedent: This pattern is well-established in Lean 4 for handling involutions with pattern-matched definitions

**From Implementation Report (Solution B)**:
```lean
-- New helper (applies existing helper to φ.swap)
theorem truth_at_involution : 
    truth_at M τ t ht φ.swap ↔ truth_at M τ t ht φ.swap.swap :=
  (truth_at_swap_swap M τ t ht φ.swap).symm

-- Updated main theorem (compose both helpers)
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h1 := (truth_at_involution M τ t ht φ).mpr (h F M τ t ht)
  exact (truth_at_swap_swap M τ t ht φ).mp h1
```

---

## Phase 1: Add Involution Helper and Complete Main Theorem [NOT STARTED]

**Estimated Effort**: 0.5 hours (30 minutes)

**Objective**: Add involution helper lemma and update main theorem to use helper composition.

### Tasks

#### 1.1: Add truth_at_involution Helper Lemma (10 minutes)

**Location**: `Logos/Core/Semantics/Truth.lean` (after line 671, before line 673)

**Implementation**:

```lean
/--
Involution helper: Converts truth_at for φ.swap to φ.swap.swap.

This helper applies the double-swap helper to φ.swap instead of φ,
providing the missing conversion needed in is_valid_swap_involution.
The symmetry provides: truth_at ... φ.swap ↔ truth_at ... φ.swap.swap
-/
theorem truth_at_involution {F : TaskFrame T} (M : TaskModel F)
    (τ : WorldHistory F) (t : T) (ht : τ.domain t) (φ : Formula) :
    truth_at M τ t ht φ.swap_past_future ↔ 
    truth_at M τ t ht φ.swap_past_future.swap_past_future := by
  exact (truth_at_swap_swap M τ t ht φ.swap_past_future).symm
```

**Explanation**:
- Takes the proven `truth_at_swap_swap` helper
- Applies it to `φ.swap` instead of `φ`
- Uses `.symm` to reverse the direction: `(φ.swap.swap ↔ φ.swap)` becomes `(φ.swap ↔ φ.swap.swap)`
- Provides the exact conversion needed by main theorem

**Why This Works**:
1. `truth_at_swap_swap` proves: `truth_at ... ψ.swap.swap ↔ truth_at ... ψ` for any formula `ψ`
2. Instantiate with `ψ = φ.swap`: `truth_at ... φ.swap.swap.swap ↔ truth_at ... φ.swap.swap`
3. Use involution `φ.swap.swap = φ`: simplifies to `truth_at ... φ.swap.swap ↔ truth_at ... φ.swap`
4. Reverse with `.symm`: `truth_at ... φ.swap ↔ truth_at ... φ.swap.swap`

#### 1.2: Update is_valid_swap_involution Theorem (10 minutes)

**Location**: `Logos/Core/Semantics/Truth.lean` (line 688-691)

**Current Code**:
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  sorry
```

**Updated Code**:
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h1 := (truth_at_involution M τ t ht φ).mpr (h F M τ t ht)
  exact (truth_at_swap_swap M τ t ht φ).mp h1
```

**Proof Flow**:
```
Goal: truth_at M τ t ht φ

Given:
  h : is_valid T φ.swap
  → provides: truth_at M τ t ht φ.swap

Step 1 (h1): Convert φ.swap to φ.swap.swap
  truth_at_involution.mpr : truth_at ... φ.swap → truth_at ... φ.swap.swap
  h1 : truth_at M τ t ht φ.swap.swap

Step 2 (exact): Convert φ.swap.swap to φ
  truth_at_swap_swap.mp : truth_at ... φ.swap.swap → truth_at ... φ
  Closes goal [YES]
```

**Why This Works**:
- `truth_at_involution` converts the hypothesis from `φ.swap` to `φ.swap.swap`
- `truth_at_swap_swap` converts from `φ.swap.swap` to `φ`
- Composition gives: `φ.swap → φ.swap.swap → φ` [YES]

#### 1.3: Update Docstring (5 minutes)

**Location**: `Logos/Core/Semantics/Truth.lean` (lines 673-687)

**Current Docstring**:
```lean
/--
Validity is invariant under the temporal swap involution.
If `φ.swap` is valid, then so is `φ` (since swap is involutive).

NOTE: This theorem currently admits `sorry`. The helper lemma `truth_at_swap_swap`
is fully proven by structural induction. The remaining step requires using the
helper with the involution property φ.swap.swap = φ, but this interaction between
propositional equality and pattern-matched definitions requires further investigation.

TODO (task 193): Complete this proof by applying truth_at_swap_swap correctly.
The proof strategy should be:
  - Apply helper at φ to reduce goal truth_at ... φ to truth_at ... φ.swap.swap
  - Convert truth_at ... φ.swap (from h) to truth_at ... φ.swap.swap using a second
    application of the helper or by leveraging the involution property
-/
```

**Updated Docstring**:
```lean
/--
Validity is invariant under the temporal swap involution.
If `φ.swap` is valid, then so is `φ` (since swap is involutive).

Proof strategy: Compose two applications of the `truth_at_swap_swap` helper:
  1. `truth_at_involution` converts hypothesis from φ.swap to φ.swap.swap
  2. `truth_at_swap_swap` converts goal from φ to φ.swap.swap
  3. Composition closes the goal

This approach avoids direct use of the involution property φ.swap.swap = φ
because `truth_at` is pattern-matched (structurally recursive), preventing
automatic transport across propositional equality.
-/
```

#### 1.4: Build and Test (5 minutes)

**Build Verification**:
```bash
lake build Logos.Core.Semantics.Truth
```

**Expected**: No errors, no `sorry` warning for `is_valid_swap_involution`

**Full Build**:
```bash
lake build
```

**Expected**: No new errors, all modules compile

**Test Suite**:
```bash
lake exe test
```

**Expected**: All existing tests pass

**Verification Steps**:
1. Verify no `sorry` at line 691
2. Verify Truth.lean compiles without errors
3. Verify downstream usage at line 1171 compiles correctly
4. Confirm no new build errors
5. Confirm all tests pass

### Acceptance Criteria

- [x] Helper lemma `truth_at_swap_swap` complete (from previous implementation)
- [ ] Helper lemma `truth_at_involution` added (5 lines)
- [ ] Main theorem `is_valid_swap_involution` updated with helper composition (3 lines)
- [ ] `sorry` removed from line 691
- [ ] Docstring updated to explain proof strategy
- [ ] Truth.lean compiles successfully with `lake build Logos.Core.Semantics.Truth`
- [ ] Full codebase builds with `lake build` (no new errors)
- [ ] All tests pass with `lake exe test`
- [ ] Line 1171 downstream usage compiles correctly
- [ ] Proof is mathematically sound and type-checks

### Risks and Mitigations

**Risk**: Type mismatch in helper composition
- **Likelihood**: Low (solution verified in implementation report)
- **Mitigation**: Follow exact pattern from implementation report Solution B
- **Verification**: Incremental compilation after each step

**Risk**: Docstring update introduces errors
- **Likelihood**: Very low (documentation only)
- **Mitigation**: Use careful copy-paste from proven examples
- **Verification**: Build check after docstring update

### Dependencies

**Already Satisfied**:
- `truth_at_swap_swap` helper lemma (lines 632-671, COMPLETE)
- `Formula.swap_past_future_involution` theorem (involution property)
- `Logos/Core/Syntax/Formula.lean` (swap definition)
- `Logos/Core/Semantics/TaskModel.lean` (model definitions)

**No New Dependencies**: All required components already in place.

### Success Metrics

- Zero `sorry` in Truth.lean for this theorem
- Zero build errors in Truth.lean
- Zero new build errors in codebase
- All existing tests pass
- Proof verified by Lean type checker
- Implementation time ≤ 30 minutes (well under 0.5h estimate)

---

## Comparison to Original Plan

| Aspect | Original Plan (v1) | Revised Plan (v2) |
|--------|-------------------|-------------------|
| **Total Effort** | 2.0 hours | 0.5 hours (30 min) |
| **Phases** | 1 (with 4 tasks) | 1 (with 4 tasks) |
| **Completion** | 85% (blocked) | 15% remaining |
| **Helper Lemma** | Planned (1h) | [PASS] Complete |
| **Main Theorem** | Planned (15min) | Blocked → Clear path |
| **Testing** | Planned (30min) | [PASS] Complete |
| **Documentation** | Planned (15min) | [PASS] Partial, needs docstring update |
| **Blocker** | None anticipated | Type theory issue → Resolved with involution helper |
| **Risk Level** | Low | Very Low |

**Key Insights from Implementation**:
1. Structural induction helper worked perfectly (no issues)
2. Type theory blocker was not anticipated in original plan
3. Solution simpler than expected: just apply existing helper to `φ.swap`
4. Most work (85%) already complete and proven correct

---

## Implementation Notes

### Why the Original Approach Failed

**Original Plan (line 134-141 of implementation-001.md)**:
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  rw [← truth_at_swap_swap M τ t ht φ]
  exact h F M τ t ht
```

**Error**:
```
type mismatch
  h F M τ t ht
has type
  truth_at M τ t ht φ.swap_past_future : Prop
but is expected to have type
  truth_at M τ t ht φ.swap_past_future.swap_past_future : Prop
```

**Problem**: After rewrite, goal is `truth_at ... φ.swap.swap` but hypothesis `h` provides `truth_at ... φ.swap`. The rewrite creates a gap that propositional equality cannot bridge.

### Why the Revised Approach Works

**Revised Approach** (this plan):
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h1 := (truth_at_involution M τ t ht φ).mpr (h F M τ t ht)
  exact (truth_at_swap_swap M τ t ht φ).mp h1
```

**Success**: 
- `truth_at_involution` explicitly converts hypothesis to match rewritten goal
- No reliance on propositional equality transport
- Uses only proven helpers with structural induction
- Composition is straightforward: `φ.swap → φ.swap.swap → φ`

**Type Theory Insight**: Pattern-matched definitions like `truth_at` require explicit lemmas for equality transport. Propositional equality (`φ.swap.swap = φ.swap`) is not enough; we need definitional equivalence or explicit conversion lemmas.

---

## Time Breakdown

| Task | Estimated | Notes |
|------|-----------|-------|
| Add truth_at_involution | 10 min | Simple symmetry application |
| Update main theorem | 10 min | Two-line proof |
| Update docstring | 5 min | Documentation only |
| Build and test | 5 min | Verification |
| **Total** | **30 min** | Comfortable within 0.5h |

**Buffer**: 30 minutes allocated vs 30 minutes estimated = 0 minutes buffer  
**Confidence**: High (solution already verified in implementation report)

---

## Summary

This revised plan completes the remaining 15% of task 193 by adding a simple involution helper and updating the main theorem. The bulk of the work (structural induction helper with 6 cases) is already complete and proven correct.

**Key Changes from Original Plan**:
1. Reduced scope: Focus only on remaining blocker resolution
2. Reduced effort: 0.5 hours vs 2.0 hours (85% already done)
3. Simpler solution: Apply existing helper to `φ.swap` instead of complex transport
4. Higher confidence: Solution already verified in implementation report

**Deliverables**:
- Complete proof for `is_valid_swap_involution` (no `sorry`)
- Updated documentation explaining proof strategy
- Full build verification with all tests passing
- Task 193 moved from [PARTIAL] to [COMPLETED]

The proof is straightforward because we leverage the already-proven `truth_at_swap_swap` helper twice: once for `φ.swap` and once for `φ`. The composition naturally bridges the gap between hypothesis and goal without relying on propositional equality transport.
