# Implementation Code for Task 193

**File**: `Logos/Core/Semantics/Truth.lean`  
**Lines**: 676-679  
**Action**: Replace current proof with Solution 1 below

---

## Current Code (BROKEN - Type Error)

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  exact (truth_at_swap_swap M τ t ht φ).mp (by simpa using h F M τ t ht)
```

**Error**: Type mismatch at line 679 - `simpa` doesn't successfully apply involution

---

## Solution 1: Direct simp only (RECOMMENDED - 95% confidence)

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h_swap : truth_at M τ t ht φ.swap_past_future := h F M τ t ht
  simp only [Formula.swap_past_future, Formula.swap_past_future_involution] at h_swap
  exact h_swap
```

**Pattern Source**: Perpetuity/Helpers.lean line 74  
**Why it works**: `simp only` unfolds `swap_past_future` and applies involution, simplifying `φ.swap_past_future` to `φ` in the hypothesis

---

## Solution 2: Helper Lemma (FALLBACK - 80% confidence)

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h1 : truth_at M τ t ht φ.swap_past_future := h F M τ t ht
  -- Rewrite using involution: φ.swap = φ.swap.swap.swap
  have h2 : φ.swap_past_future = φ.swap_past_future.swap_past_future.swap_past_future := by
    simp [Formula.swap_past_future_involution]
  rw [h2] at h1
  -- Now h1 : truth_at M τ t ht φ.swap.swap, use helper
  exact (truth_at_swap_swap M τ t ht φ).mp h1
```

**Why it works**: Explicitly constructs the equality needed to use the helper lemma

---

## Solution 3: Congruence Lemma (FALLBACK - 90% confidence)

**Step 1**: Add helper lemma before `is_valid_swap_involution`:

```lean
/--
Congruence lemma: truth_at respects formula equality.
-/
theorem truth_at_congr {F : TaskFrame T} {M : TaskModel F} {τ : WorldHistory F} 
    {t : T} {ht : τ.domain t} {φ ψ : Formula} (h_eq : φ = ψ) :
    truth_at M τ t ht φ ↔ truth_at M τ t ht ψ := by
  cases h_eq
  rfl
```

**Step 2**: Use congruence lemma in main theorem:

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h1 : truth_at M τ t ht φ.swap_past_future := h F M τ t ht
  have h_eq : φ.swap_past_future = φ := Formula.swap_past_future_involution φ
  exact (truth_at_congr h_eq).mp h1
```

**Why it works**: Explicitly uses propositional equality transport via congruence

---

## Testing Commands

```bash
# Test compilation
lake build Logos.Core.Semantics.Truth

# Full build
lake build

# Check for sorry
grep -n "sorry" Logos/Core/Semantics/Truth.lean

# Run tests
lake exe test
```

---

## Expected Results

[PASS] `lake build Logos.Core.Semantics.Truth` - Success, no type errors  
[PASS] `lake build` - Success, no new errors  
[PASS] `grep -n "sorry"` - No matches in `is_valid_swap_involution`  
[PASS] `lake exe test` - All tests pass

---

## Implementation Steps

1. Open `Logos/Core/Semantics/Truth.lean`
2. Navigate to line 676
3. Delete lines 677-679
4. Insert Solution 1 code (4 lines)
5. Save file
6. Run `lake build Logos.Core.Semantics.Truth`
7. If successful, run `lake build`
8. Mark task 193 as COMPLETED

**Estimated Time**: 5 minutes implementation + 10 minutes testing = 15 minutes total

---

## Docstring Update (Optional)

Current docstring (lines 672-675):
```lean
/--
Validity is invariant under the temporal swap involution.
If `φ.swap` is valid, then so is `φ` (since swap is involutive).
-/
```

Enhanced docstring (optional):
```lean
/--
Validity is invariant under the temporal swap involution.
If `φ.swap` is valid, then so is `φ` (since swap is involutive).

Proof strategy:
1. Instantiate hypothesis to get `truth_at M τ t ht φ.swap_past_future`
2. Use `simp only` with involution to simplify `φ.swap_past_future` to `φ`
3. Close goal with simplified hypothesis

The key technique is `simp only [Formula.swap_past_future, 
Formula.swap_past_future_involution] at h_swap`, which handles the involution
in the hypothesis. This pattern is used successfully in Perpetuity/Helpers.lean.
-/
```

---

## Quick Reference

**File**: `Logos/Core/Semantics/Truth.lean`  
**Lines**: 676-679  
**Solution**: Solution 1 (4 lines)  
**Pattern**: `simp only [Formula.swap_past_future, Formula.swap_past_future_involution] at h`  
**Source**: Perpetuity/Helpers.lean line 74  
**Confidence**: 95%+  
**Time**: 15 minutes
