# Implementation Plan: Prove is_valid_swap_involution Theorem

**Project Number**: 193  
**Project Name**: prove_is_valid_swap_involution  
**Type**: bugfix  
**Priority**: High  
**Complexity**: Medium  
**Estimated Total Hours**: 2.0  
**Total Phases**: 1  
**Language**: lean

---

## Overview

Replace the `sorry` placeholder in the `is_valid_swap_involution` theorem (Truth.lean, line 629) with a complete proof using structural induction. The current `simpa` proof fails because `truth_at` is defined by structural recursion, preventing direct formula substitution. The solution requires a helper lemma that proves equivalence case-by-case for each formula constructor.

---

## Research Inputs

**Research Report**: `.opencode/specs/193_prove_is_valid_swap_involution/reports/research-001.md`  
**Research Summary**: `.opencode/specs/193_prove_is_valid_swap_involution/summaries/research-summary.md`

**Key Findings**:
- Current proof uses `simpa [Formula.swap_past_future_involution φ]` which fails with type mismatch
- Root cause: `truth_at` is pattern-matched (structurally recursive), so propositional equality doesn't imply definitional equality
- Solution: Add helper lemma `truth_at_swap_swap` using structural induction
- Standard Lean 4 pattern used throughout codebase
- Low risk: minimal changes, well-understood proof technique

---

## Phase 1: Implement Helper Lemma and Update Main Theorem [PARTIAL]
(Started: 2025-12-28T16:00:00Z)

**Estimated Effort**: 2.0 hours  
**Actual Effort**: 1.7 hours  
**Completion**: 85%

**Partial Completion Notes**:
- Task 1.1 (Helper Lemma): COMPLETED (lines 632-671, all 6 cases proven)
- Task 1.2 (Main Theorem): BLOCKED (line 691 still admits sorry)
- Task 1.3 (Build and Test): COMPLETED (builds successfully, all tests pass)
- Task 1.4 (Documentation): COMPLETED (comprehensive inline docs added)

**Blocker**: Type theory issue with equality transport. Main theorem blocked by inability to convert `truth_at M τ t ht φ.swap` to `truth_at M τ t ht φ.swap.swap` using propositional equality `φ.swap.swap = φ.swap`. Pattern-matched `truth_at` definition prevents automatic transport.

**Solution**: Add involution helper lemma `truth_at_involution` to explicitly perform conversion, then compose with existing `truth_at_swap_swap` helper.

**Remaining Effort**: 0.5 hours (30 minutes to add helper and complete proof)

**Objective**: Add `truth_at_swap_swap` helper lemma with structural induction and update `is_valid_swap_involution` to use it.

### Tasks

#### 1.1: Add truth_at_swap_swap Helper Lemma (1 hour)

**Location**: `Logos/Core/Semantics/Truth.lean` (before line 629)

**Implementation**:

```lean
/--
Helper lemma: truth_at is invariant under double swap.

This lemma proves that applying swap twice to a formula preserves truth evaluation.
Required because truth_at is defined by structural recursion, preventing direct use
of the involution property φ.swap.swap = φ via substitution.
-/
theorem truth_at_swap_swap {F : TaskFrame T} (M : TaskModel F)
    (τ : WorldHistory F) (t : T) (ht : τ.domain t) (φ : Formula) :
    truth_at M τ t ht φ.swap_past_future.swap_past_future ↔ truth_at M τ t ht φ := by
  induction φ with
  | atom p => 
    -- Atom case: swap doesn't change atoms
    simp only [Formula.swap_past_future, truth_at]
    
  | bot => 
    -- Bot case: swap doesn't change bot
    simp only [Formula.swap_past_future, truth_at]
    
  | imp φ ψ ih_φ ih_ψ => 
    -- Implication case: (φ.swap.swap → ψ.swap.swap) ↔ (φ → ψ)
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h <;> intro h_φ
    · exact ih_ψ.mp (h (ih_φ.mpr h_φ))
    · exact ih_ψ.mpr (h (ih_φ.mp h_φ))
    
  | box φ ih => 
    -- Box case: □(φ.swap.swap) ↔ □φ
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h σ hs
    · exact ih.mp (h σ hs)
    · exact ih.mpr (h σ hs)
    
  | all_past φ ih => 
    -- All_past case: all_past φ → all_future φ.swap → all_past φ.swap.swap
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h s hs h_ord
    · exact ih.mp (h s hs h_ord)
    · exact ih.mpr (h s hs h_ord)
    
  | all_future φ ih => 
    -- All_future case: all_future φ → all_past φ.swap → all_future φ.swap.swap
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h s hs h_ord
    · exact ih.mp (h s hs h_ord)
    · exact ih.mpr (h s hs h_ord)
```

**Validation**:
- Each case follows the structure of `truth_at` definition (lines 109-116)
- Induction hypotheses applied correctly in recursive cases
- Temporal cases handle double-swap correctly (all_past ↔ all_future ↔ all_past)

#### 1.2: Update is_valid_swap_involution Theorem (15 minutes)

**Location**: `Logos/Core/Semantics/Truth.lean` (line 629-632)

**Current Code**:
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  simpa [Formula.swap_past_future_involution φ] using h F M τ t ht
```

**Updated Code**:
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  rw [← truth_at_swap_swap M τ t ht φ]
  exact h F M τ t ht
```

**Explanation**:
- `rw [← truth_at_swap_swap]` rewrites goal from `truth_at ... φ` to `truth_at ... φ.swap.swap`
- `exact h F M τ t ht` provides exactly `truth_at M τ t ht φ.swap_past_future`
- Since `φ.swap_past_future = φ.swap` (definitional), this closes the goal

#### 1.3: Build and Test (30 minutes)

**Build Verification**:
```bash
lake build Logos.Core.Semantics.Truth
```

**Expected**: No errors, successful compilation

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
1. Verify Truth.lean compiles without errors
2. Verify downstream usage at line 1171 compiles correctly
3. Check no new build errors introduced
4. Confirm existing test suite passes
5. Verify no `sorry` remains in Truth.lean for this theorem

#### 1.4: Documentation Update (15 minutes)

**Check SORRY_REGISTRY.md**:
- If `is_valid_swap_involution` is tracked, remove it
- Update sorry count in documentation

**Update Theorem Documentation**:
- Verify docstring accurately describes the proof approach
- Add reference to helper lemma in comments if helpful

### Acceptance Criteria

- [ ] Helper lemma `truth_at_swap_swap` added with complete structural induction proof
- [ ] All 6 cases (atom, bot, imp, box, all_past, all_future) proven correctly
- [ ] Main theorem `is_valid_swap_involution` updated to use helper lemma
- [ ] `sorry` placeholder removed from line 632
- [ ] Truth.lean compiles successfully with `lake build Logos.Core.Semantics.Truth`
- [ ] Full codebase builds with `lake build` (no new errors)
- [ ] All tests pass with `lake exe test`
- [ ] Line 1171 usage of theorem compiles correctly
- [ ] SORRY_REGISTRY.md updated if applicable
- [ ] Proof is mathematically sound and type-checks

### Risks and Mitigations

**Risk**: Temporal cases (all_past/all_future) may have subtle issues with double-swap
- **Mitigation**: Follow exact pattern from `truth_at` definition, use IH directly
- **Verification**: Test with `lake build` after each case completion

**Risk**: Type mismatch in quantifier handling
- **Mitigation**: Use `simp only` to expand definitions carefully
- **Verification**: Incremental compilation during implementation

**Risk**: Regression in downstream usage (line 1171)
- **Mitigation**: Verify full build after changes
- **Verification**: Run full test suite

### Dependencies

- `Logos/Core/Syntax/Formula.lean` (swap definition, lines 204-213)
- `Logos/Core/Semantics/TaskModel.lean` (model definitions)
- `Formula.swap_past_future_involution` theorem (involution property)

### Success Metrics

- Zero build errors in Truth.lean
- Zero new build errors in codebase
- All existing tests pass
- Proof verified by Lean type checker
- No `sorry` remains for this theorem

---

## Summary

This single-phase plan implements the proof for `is_valid_swap_involution` using a standard structural induction pattern. The helper lemma approach is well-understood, low-risk, and follows existing codebase patterns. Total implementation time: 2 hours (1h helper lemma, 30min testing, 30min documentation/verification).

The proof is straightforward because `swap_past_future` is an involution and each case follows directly from the induction hypothesis. The only subtlety is in the temporal cases where `all_past` swaps to `all_future` and back, but the IH handles this correctly.
