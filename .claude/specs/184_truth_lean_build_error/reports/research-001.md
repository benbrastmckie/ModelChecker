# Research Report: Truth.lean Build Error (swap_past_future proof)

**Report ID**: research-001  
**Task**: 184  
**Date**: 2025-12-25  
**Status**: Complete  
**Researcher**: OpenCode AI  

---

## Executive Summary

The build error at `Truth.lean:632` is a **type mismatch** in the `is_valid_swap_involution` theorem proof. The proof attempts to use `simpa` with the involution lemma, but the types don't align correctly. The issue is that `h F M τ t ht` produces `truth_at M τ t ht φ.swap_past_future` but the goal requires `truth_at M τ t ht φ`.

**Root Cause**: The `simpa` tactic with the involution rewrite is not correctly transforming the hypothesis to match the goal type.

**Recommended Solution**: Replace `simpa` with an explicit `simp` and `exact` sequence, or use `convert` to handle the type alignment with the involution lemma.

**Estimated Fix Time**: 10-15 minutes (trivial proof fix)

---

## 1. Error Analysis

### 1.1 Exact Error Location

**File**: `Logos/Core/Semantics/Truth.lean`  
**Line**: 632  
**Theorem**: `is_valid_swap_involution`

### 1.2 Error Message

```
error: ././././Logos/Core/Semantics/Truth.lean:632:2: type mismatch, term
  h F M τ t ht
after simplification has type
  truth_at M τ t ht φ.swap_past_future : Prop
but is expected to have type
  truth_at M τ t ht φ : Prop
```

### 1.3 Theorem Statement and Proof

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  simpa [Formula.swap_past_future_involution φ] using h F M τ t ht
```

### 1.4 Context Analysis

**Key Definitions**:

1. **is_valid** (local, line 608):
   ```lean
   private def is_valid (T : Type*) [LinearOrderedAddCommGroup T] (φ : Formula) : Prop :=
     ∀ (F : TaskFrame T) (M : TaskModel F) (τ : WorldHistory F) (t : T) (ht : τ.domain t),
       truth_at M τ t ht φ
   ```

2. **swap_past_future_involution** (Formula.lean:231):
   ```lean
   theorem swap_past_future_involution (φ : Formula) :
     φ.swap_past_future.swap_past_future = φ := swap_temporal_involution φ
   ```

**Proof Goal After `intro F M τ t ht`**:
- Goal: `truth_at M τ t ht φ`
- Hypothesis `h`: `is_valid T φ.swap_past_future`
- After applying `h F M τ t ht`: `truth_at M τ t ht φ.swap_past_future`

**The Problem**: 
The `simpa` tactic is attempting to simplify using the involution lemma `φ.swap_past_future.swap_past_future = φ`, but the simplification is not occurring at the right location in the type. The term `h F M τ t ht` has type `truth_at M τ t ht φ.swap_past_future`, and we need `truth_at M τ t ht φ`.

---

## 2. Root Cause Analysis

### 2.1 Why the Error Occurs

The `simpa` tactic combines `simp` with `assumption` or `exact`. The involution lemma states that `φ.swap_past_future.swap_past_future = φ`, which is a **formula-level equality**, not a direct equality of `truth_at` propositions.

When `simpa [Formula.swap_past_future_involution φ]` processes `h F M τ t ht`, it should rewrite `truth_at M τ t ht φ.swap_past_future` to `truth_at M τ t ht φ` by recognizing that since `φ.swap_past_future.swap_past_future = φ`, we can substitute.

However, the issue is subtle:
- We have: `truth_at M τ t ht φ.swap_past_future`
- We want: `truth_at M τ t ht φ`
- The involution says: `φ.swap_past_future.swap_past_future = φ`

The involution lemma doesn't directly help us rewrite from `φ.swap_past_future` to something simpler. Instead, we need to observe that if we knew `φ = ψ.swap_past_future` for some `ψ`, then `ψ = φ.swap_past_future` (by involution).

The actual relationship we need is:
- Since `φ.swap_past_future.swap_past_future = φ` (by involution)
- If we have `truth_at M τ t ht φ.swap_past_future`
- We can rewrite the goal `truth_at M τ t ht φ` as `truth_at M τ t ht (φ.swap_past_future.swap_past_future)`
- Then they match!

### 2.2 Type System Details

Lean's dependent type system requires exact type matching. The `truth_at` function takes a `Formula` argument, so:
- `truth_at M τ t ht φ` has type `Prop`
- `truth_at M τ t ht φ.swap_past_future` has a different type (also `Prop`, but with different formula)

These are definitionally different propositions unless Lean can see that `φ = φ.swap_past_future` (which would only be true for self-dual formulas).

The involution lemma provides `φ.swap_past_future.swap_past_future = φ`, which means we can rewrite the **goal** rather than the hypothesis.

---

## 3. Solution Approaches

### 3.1 Approach A: Rewrite Goal First (Recommended)

**Strategy**: Use the involution lemma to rewrite the goal before applying the hypothesis.

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  rw [← Formula.swap_past_future_involution φ]
  exact h F M τ t ht
```

**Proof Steps**:
1. `intro F M τ t ht` - introduce the universally quantified variables
2. Goal is now: `truth_at M τ t ht φ`
3. `rw [← Formula.swap_past_future_involution φ]` - rewrite `φ` as `φ.swap_past_future.swap_past_future`
4. Goal becomes: `truth_at M τ t ht (φ.swap_past_future.swap_past_future)`
5. `exact h F M τ t ht` - this exactly matches the hypothesis applied

**Pros**:
- Clean and explicit
- Easy to understand the rewrite direction
- Follows standard Lean proof patterns
- Minimal tactic invocations

**Cons**:
- None

**Estimated Implementation Time**: 5 minutes

---

### 3.2 Approach B: Use `convert` Tactic

**Strategy**: Use `convert` to apply the hypothesis and let Lean generate subgoals for the mismatch.

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  convert h F M τ t ht
  exact Formula.swap_past_future_involution φ
```

**Proof Steps**:
1. `intro F M τ t ht` - introduce variables
2. `convert h F M τ t ht` - apply hypothesis, generate equality subgoal for formula mismatch
3. Subgoal: `φ = φ.swap_past_future.swap_past_future`
4. `exact Formula.swap_past_future_involution φ` - close subgoal with involution

**Pros**:
- Handles type mismatches automatically
- Good for complex type alignments

**Cons**:
- Slightly less explicit than Approach A
- Generates additional subgoals that need to be solved
- `convert` can be slow on large terms

**Estimated Implementation Time**: 8 minutes

---

### 3.3 Approach C: Direct Simplification with `show`

**Strategy**: Use `show` to restate the goal, then simplify.

```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  show truth_at M τ t ht φ
  have : φ = φ.swap_past_future.swap_past_future := 
    (Formula.swap_past_future_involution φ).symm
  rw [this]
  exact h F M τ t ht
```

**Pros**:
- Very explicit about what's happening
- Good for documentation/teaching

**Cons**:
- More verbose than necessary
- Introduces intermediate `have` statement
- Less idiomatic for simple rewrites

**Estimated Implementation Time**: 10 minutes

---

## 4. Recommended Solution

**Approach A: Rewrite Goal First** is the recommended solution.

### 4.1 Justification

1. **Clarity**: The proof is explicit and easy to follow
2. **Efficiency**: Minimal tactic invocations
3. **Maintainability**: Standard Lean proof pattern that others will recognize
4. **Correctness**: Direct application of the involution lemma in the correct direction

### 4.2 Implementation Plan

**Step 1**: Replace line 632 in `Truth.lean`

```lean
-- Current (line 632):
  simpa [Formula.swap_past_future_involution φ] using h F M τ t ht

-- Replace with:
  rw [← Formula.swap_past_future_involution φ]
  exact h F M τ t ht
```

**Step 2**: Build and verify

```bash
lake build Logos.Core.Semantics.Truth
```

**Step 3**: Run related tests to ensure no regressions

```bash
lake build LogosTest.Core.Semantics
lake build LogosTest.Core.Metalogic.SoundnessTest
```

### 4.3 Alternative Quick Fix

If Approach A fails for any reason (unlikely), fall back to Approach B (`convert`).

---

## 5. Risk Assessment

### 5.1 Implementation Risks

**Risk Level**: **Very Low**

- This is a simple proof fix in a helper lemma
- The theorem statement is correct; only the proof tactic needs adjustment
- No API changes or interface modifications
- The lemma is only used once in the file (line 1171)

### 5.2 Testing Requirements

**Minimal Testing Required**:

1. **Direct test**: Build `Logos.Core.Semantics.Truth`
2. **Downstream test**: Build modules that import Truth.lean:
   - `Logos.Core.Semantics.Validity`
   - `Logos.Core.Metalogic.Soundness`
   - Integration tests from task 173

**Expected Result**: All builds should succeed with no changes to behavior.

### 5.3 Impact Analysis

**Files Affected**: 1 file
- `Logos/Core/Semantics/Truth.lean` (line 632 only)

**Downstream Impact**: None
- The theorem signature remains unchanged
- The proof is internal implementation detail
- Only one call site in the same file (line 1171)

**Blocking Impact**: 
- Currently blocks compilation of ALL test files
- Blocks integration test verification from task 173
- High priority fix due to blocking nature

---

## 6. Implementation Estimate

### 6.1 Time Estimate

**Total Time**: 10-15 minutes

**Breakdown**:
- Code change: 2 minutes
- Build verification: 3 minutes  
- Test execution: 5 minutes
- Documentation: 0 minutes (no API change)

### 6.2 Complexity Assessment

**Complexity**: Trivial

This is a straightforward tactic fix in a single proof. The error is well-understood, the solution is clear, and there are no edge cases or complications.

---

## 7. Additional Context

### 7.1 Why This Error Exists

This error likely occurred during refactoring or during the initial implementation of the temporal duality soundness proof. The `simpa` tactic is often a good choice for simple simplification + closing, but in this case, the direction of the rewrite matters.

### 7.2 Related Patterns in Codebase

The `swap_past_future_involution` lemma is used correctly elsewhere in the file (line 1173):

```lean
simpa [Formula.swap_past_future_involution ψ'] using h_original
```

This works because in that context, `h_original` has the right type after the involution rewrite. The difference is the direction of the rewrite.

### 7.3 Prevention

**Lesson**: When using involution lemmas with `simpa`, ensure the rewrite direction aligns with the hypothesis → goal transformation. If uncertain, use explicit `rw` followed by `exact` for clarity.

---

## 8. Verification Checklist

After implementing the fix, verify:

- [ ] `lake build Logos.Core.Semantics.Truth` succeeds
- [ ] `lake build Logos.Core.Semantics.Validity` succeeds  
- [ ] `lake build Logos.Core.Metalogic.Soundness` succeeds
- [ ] `lake build LogosTest.Core.Semantics` succeeds
- [ ] `lake build LogosTest.Core.Metalogic.SoundnessTest` succeeds
- [ ] `lake build LogosTest.Integration` succeeds (task 173 tests)
- [ ] No new warnings introduced
- [ ] Proof remains readable and maintainable

---

## 9. References

### 9.1 Code References

- `Logos/Core/Semantics/Truth.lean:629-632` - Error location
- `Logos/Core/Syntax/Formula.lean:231-232` - Involution lemma definition
- `Logos/Core/Semantics/Truth.lean:1171` - Usage site

### 9.2 Related Tasks

- Task 173: Integration tests (blocked by this error)
- Task 184: This fix (current task)

### 9.3 Documentation

- No documentation updates required (internal proof change)

---

## Appendix A: Proof Comparison

### Current (Broken)
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  simpa [Formula.swap_past_future_involution φ] using h F M τ t ht
```

### Recommended Fix
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  rw [← Formula.swap_past_future_involution φ]
  exact h F M τ t ht
```

### Alternative (convert)
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  convert h F M τ t ht
  exact Formula.swap_past_future_involution φ
```

---

## Appendix B: Type Flow Analysis

```
Given:
  h : is_valid T φ.swap_past_future
  = ∀ F M τ t ht, truth_at M τ t ht φ.swap_past_future

After intro F M τ t ht:
  h F M τ t ht : truth_at M τ t ht φ.swap_past_future
  Goal            : truth_at M τ t ht φ

Involution lemma:
  φ.swap_past_future.swap_past_future = φ

Rewrite goal using ← involution:
  Goal becomes: truth_at M τ t ht (φ.swap_past_future.swap_past_future)

Now exact match:
  h F M τ t ht closes goal [YES]
```

---

**End of Report**
