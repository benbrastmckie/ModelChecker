# Research Report: Prove is_valid_swap_involution theorem (Task 193)

**Date**: 2025-12-28  
**Researcher**: Research Agent  
**Task**: 193 - Prove is_valid_swap_involution theorem in Truth.lean (currently sorry)

---

## Executive Summary

Task 193 requires proving the `is_valid_swap_involution` theorem in Truth.lean (line 629), which currently uses `sorry` and fails to compile with a type mismatch error. The theorem states that if `φ.swap_past_future` is valid, then `φ` is also valid, leveraging the involution property of the swap operation.

**Current Status**: Build error at line 632 - type mismatch after `simpa` application.

**Root Cause**: The `simpa` tactic attempts to simplify using the involution property `φ.swap_past_future.swap_past_future = φ`, but `truth_at` is defined by pattern matching (structural recursion), preventing direct formula substitution via definitional equality.

**Solution**: Replace the failed `simpa` proof with a structural induction proof that establishes the equivalence `truth_at M τ t ht φ.swap_past_future.swap_past_future ↔ truth_at M τ t ht φ` case-by-case.

**Estimated Effort**: 2 hours (consistent with TODO.md estimate).

---

## Problem Analysis

### Current Code (Line 629-632)

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  simpa [Formula.swap_past_future_involution φ] using h F M τ t ht
```

### Build Error

```
error: type mismatch, term
  h F M τ t ht
after simplification has type
  truth_at M τ t ht φ.swap_past_future : Prop
but is expected to have type
  truth_at M τ t ht φ : Prop
```

### Why It Fails

1. **Goal**: Prove `truth_at M τ t ht φ`
2. **Given**: `h : is_valid T φ.swap_past_future`, which when instantiated gives `truth_at M τ t ht φ.swap_past_future`
3. **Involution Property**: `Formula.swap_past_future_involution φ` states `φ.swap_past_future.swap_past_future = φ`
4. **The Issue**: `truth_at` is defined by pattern matching on formulas (lines 109-116):
   ```lean
   def truth_at (M : TaskModel F) (τ : WorldHistory F) (t : T) (ht : τ.domain t) :
       Formula → Prop
     | Formula.atom p => M.valuation (τ.states t ht) p
     | Formula.bot => False
     | Formula.imp φ ψ => truth_at M τ t ht φ → truth_at M τ t ht ψ
     | Formula.box φ => ∀ (σ : WorldHistory F) (hs : σ.domain t), truth_at M σ t hs φ
     | Formula.all_past φ => ∀ (s : T) (hs : τ.domain s), s < t → truth_at M τ s hs φ
     | Formula.all_future φ => ∀ (s : T) (hs : τ.domain s), t < s → truth_at M τ s hs φ
   ```

   This structural recursion means `truth_at M τ t ht φ` and `truth_at M τ t ht φ.swap.swap` are not definitionally equal even though `φ = φ.swap.swap` propositionally. The tactic `simpa` cannot rewrite inside the recursively-defined function.

---

## Solution Strategy

### Approach: Helper Lemma with Structural Induction

Create a helper lemma `truth_at_swap_swap` that proves the equivalence by structural induction on formulas:

```lean
theorem truth_at_swap_swap {F : TaskFrame T} (M : TaskModel F)
    (τ : WorldHistory F) (t : T) (ht : τ.domain t) (φ : Formula) :
    truth_at M τ t ht φ.swap_past_future.swap_past_future ↔ truth_at M τ t ht φ
```

Then use this lemma in `is_valid_swap_involution`:

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  rw [← truth_at_swap_swap M τ t ht φ]
  exact h F M τ t ht
```

### Why This Works

1. **Structural Induction**: The helper lemma uses `induction φ` to handle each formula constructor separately
2. **Case-by-Case Equivalence**: For each constructor (atom, bot, imp, box, all_past, all_future), we prove the equivalence directly
3. **Swap Definition**: `swap_past_future` (lines 204-210 in Formula.lean):
   - Atoms: `atom s → atom s` (identity)
   - Bot: `bot → bot` (identity)
   - Imp: `imp φ ψ → imp φ.swap ψ.swap` (recursive)
   - Box: `box φ → box φ.swap` (recursive)
   - All_past: `all_past φ → all_future φ.swap` (swap)
   - All_future: `all_future φ → all_past φ.swap` (swap)

4. **Double Swap Behavior**:
   - `atom s → atom s → atom s` (identity)
   - `bot → bot → bot` (identity)
   - `imp φ ψ → imp φ.swap ψ.swap → imp φ.swap.swap ψ.swap.swap` (by IH: equals `imp φ ψ`)
   - `box φ → box φ.swap → box φ.swap.swap` (by IH: equals `box φ`)
   - `all_past φ → all_future φ.swap → all_past φ.swap.swap` (by IH: equals `all_past φ`)
   - `all_future φ → all_past φ.swap → all_future φ.swap.swap` (by IH: equals `all_future φ`)

---

## Detailed Implementation Plan

### Step 1: Helper Lemma (1 hour)

```lean
theorem truth_at_swap_swap {F : TaskFrame T} (M : TaskModel F)
    (τ : WorldHistory F) (t : T) (ht : τ.domain t) (φ : Formula) :
    truth_at M τ t ht φ.swap_past_future.swap_past_future ↔ truth_at M τ t ht φ := by
  induction φ with
  | atom p => 
    -- atom case: swap doesn't change atoms
    simp only [Formula.swap_past_future, truth_at]
    
  | bot => 
    -- bot case: swap doesn't change bot
    simp only [Formula.swap_past_future, truth_at]
    
  | imp φ ψ ih_φ ih_ψ => 
    -- imp case: (φ.swap.swap → ψ.swap.swap) ↔ (φ → ψ)
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h <;> intro h_φ
    · exact ih_ψ.mp (h (ih_φ.mpr h_φ))
    · exact ih_ψ.mpr (h (ih_φ.mp h_φ))
    
  | box φ ih => 
    -- box case: □(φ.swap.swap) ↔ □φ
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h σ hs
    · exact ih.mp (h σ hs)
    · exact ih.mpr (h σ hs)
    
  | all_past φ ih => 
    -- all_past case: all_past φ → all_future φ.swap → all_past φ.swap.swap
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h s hs h_ord
    · exact ih.mp (h s hs h_ord)
    · exact ih.mpr (h s hs h_ord)
    
  | all_future φ ih => 
    -- all_future case: all_future φ → all_past φ.swap → all_future φ.swap.swap
    simp only [Formula.swap_past_future, truth_at]
    constructor <;> intro h s hs h_ord
    · exact ih.mp (h s hs h_ord)
    · exact ih.mpr (h s hs h_ord)
```

**Notes**:
- Each case follows the structure of `truth_at` definition
- Temporal cases (all_past, all_future) require careful handling of the double swap
- Induction hypotheses provide the equivalence for subformulas

### Step 2: Update Main Theorem (15 minutes)

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  rw [← truth_at_swap_swap M τ t ht φ]
  exact h F M τ t ht
```

**Notes**:
- Simple rewrite using the helper lemma
- `rw [← ...]` rewrites from right to left: `truth_at ... φ` becomes `truth_at ... φ.swap.swap`
- Then `h F M τ t ht` provides exactly `truth_at M τ t ht φ.swap_past_future`
- Since `φ.swap_past_future = φ.swap` (by definition), this closes the goal

### Step 3: Verify Downstream Usage (15 minutes)

Check line 1171 where `is_valid_swap_involution` is used:

```lean
have h_original : is_valid T ψ' := is_valid_swap_involution ψ' h_swap_valid
```

This usage should work correctly once the theorem is proven.

### Step 4: Build and Test (30 minutes)

1. Run `lake build Logos.Core.Semantics.Truth` to verify compilation
2. Run `lake build` to ensure no downstream breakage
3. Run `lake exe test` to verify existing tests pass
4. Review SORRY_REGISTRY.md - this theorem should be removed from it once proven

---

## Alternative Approaches Considered

### Alternative 1: Use `rw` with Involution Directly

**Idea**: Try `rw [Formula.swap_past_future_involution φ]` to rewrite `φ.swap.swap` to `φ`.

**Problem**: Same issue - `truth_at` is structurally recursive, so rewrites inside it require congruence lemmas or manual case analysis.

**Verdict**: Not viable without the helper lemma.

### Alternative 2: Generalize `truth_at` Definition

**Idea**: Define `truth_at` in a way that's more amenable to substitution.

**Problem**: Would require refactoring the entire truth evaluation system, affecting all downstream theorems.

**Verdict**: Too invasive for this focused task.

### Alternative 3: Use `cast` or Type-Level Equality

**Idea**: Use dependent type casting to transport the proof across the equality.

**Problem**: `truth_at` returns `Prop`, so casting doesn't help. We need logical equivalence, not type equality.

**Verdict**: Not applicable.

---

## Risk Assessment

### Low Risk
- **Proof Pattern**: Structural induction on formulas is well-understood and used extensively in the codebase
- **Minimal Changes**: Only adding one helper lemma and updating one theorem
- **No API Changes**: `is_valid_swap_involution` signature remains unchanged
- **Isolated Impact**: Only affects Truth.lean, no downstream API changes

### Potential Issues
1. **Temporal Cases Complexity**: The all_past/all_future cases involve double negation of temporal direction, but the IH handles this
2. **Quantifier Handling**: Need to ensure quantifiers in temporal cases are handled correctly, but the pattern from `truth_at` definition makes this straightforward

### Mitigation
- Follow the exact structure of `truth_at` definition in each case
- Use the induction hypotheses directly without complex manipulations
- Test compilation after each case to catch errors early

---

## Dependencies and Prerequisites

### Knowledge Required
- Understanding of structural induction in Lean 4
- Familiarity with `truth_at` definition (lines 109-116)
- Understanding of `swap_past_future` definition (lines 204-210 in Formula.lean)
- Basic tactic knowledge: `simp`, `constructor`, `intro`, `exact`, `rw`

### Files to Modify
- `Logos/Core/Semantics/Truth.lean` (lines 629-632)

### Files to Reference
- `Logos/Core/Syntax/Formula.lean` (swap definition and involution theorem)
- `Logos/Core/Semantics/TaskModel.lean` (model definitions)

---

## Testing Strategy

### Compilation Tests
1. **Local Build**: `lake build Logos.Core.Semantics.Truth`
   - Expected: No errors, successful compilation
   
2. **Full Build**: `lake build`
   - Expected: No errors, all modules compile
   
3. **Downstream Usage**: Check line 1171 compiles correctly
   - Expected: `is_valid_swap_involution ψ' h_swap_valid` type-checks

### Logical Correctness
1. **Review Proof**: Each case of the structural induction should be logically sound
   - Atom case: Trivial (swap is identity on atoms)
   - Bot case: Trivial (swap is identity on bot)
   - Imp case: Follows from IHs
   - Box case: Follows from IH
   - Temporal cases: Follow from IHs with double-swap cancellation

2. **Involution Verification**: Confirm `swap_past_future_involution` is used correctly
   - Expected: Theorem `φ.swap.swap = φ` is available and proven

### Regression Tests
1. **Existing Tests**: `lake exe test`
   - Expected: All existing tests pass
   
2. **No New Errors**: Check that removing the `sorry` doesn't expose new errors
   - Expected: Build succeeds with no new errors

---

## Implementation Checklist

- [ ] Add `truth_at_swap_swap` helper lemma with structural induction
- [ ] Prove atom case (trivial)
- [ ] Prove bot case (trivial)
- [ ] Prove imp case using IHs
- [ ] Prove box case using IH
- [ ] Prove all_past case using IH
- [ ] Prove all_future case using IH
- [ ] Update `is_valid_swap_involution` to use helper lemma
- [ ] Remove `sorry` placeholder
- [ ] Build Truth.lean: `lake build Logos.Core.Semantics.Truth`
- [ ] Build full codebase: `lake build`
- [ ] Run tests: `lake exe test`
- [ ] Verify line 1171 usage compiles
- [ ] Update SORRY_REGISTRY.md if tracked there

---

## Conclusion

The `is_valid_swap_involution` theorem can be proven by adding a helper lemma `truth_at_swap_swap` that uses structural induction to establish the equivalence `truth_at M τ t ht φ.swap.swap ↔ truth_at M τ t ht φ`. This approach is straightforward, low-risk, and follows standard Lean 4 proof patterns used throughout the codebase.

**Recommendation**: Proceed with implementation using the helper lemma strategy. Estimated completion time: 2 hours, consistent with TODO.md estimate.

**Next Steps**: Create implementation plan if needed, or proceed directly to implementation given the clear proof strategy outlined above.
