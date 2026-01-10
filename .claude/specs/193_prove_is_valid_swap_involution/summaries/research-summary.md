# Research Summary: Task 193 - Prove is_valid_swap_involution

**Date**: 2025-12-28  
**Status**: Research Complete

---

## Problem

The `is_valid_swap_involution` theorem in Truth.lean (line 629) currently uses `sorry` and fails to compile with a type mismatch error. The theorem attempts to prove that if `φ.swap_past_future` is valid, then `φ` is also valid, using the involution property `φ.swap.swap = φ`. The current `simpa` tactic fails because `truth_at` is defined by structural recursion, preventing direct formula substitution.

---

## Solution

Replace the failed `simpa` proof with a two-part approach:

1. **Helper Lemma** (`truth_at_swap_swap`): Prove the equivalence `truth_at M τ t ht φ.swap.swap ↔ truth_at M τ t ht φ` using structural induction on formulas

2. **Main Theorem**: Use the helper lemma via rewrite to complete the proof

---

## Key Findings

- **Root Cause**: `truth_at` is pattern-matched (structurally recursive), so propositional equality `φ = φ.swap.swap` doesn't imply definitional equality of `truth_at M τ t ht φ` and `truth_at M τ t ht φ.swap.swap`

- **Proof Strategy**: Structural induction handles each formula constructor:
  - Atom, bot: Trivial (swap is identity)
  - Imp, box: Follow from induction hypotheses
  - All_past, all_future: Double-swap cancels temporal direction change

- **Effort**: 2 hours (1 hour for helper lemma, 15 min for main theorem, 45 min for testing)

---

## Implementation Outline

```lean
-- Helper lemma with structural induction
theorem truth_at_swap_swap : 
    truth_at M τ t ht φ.swap.swap ↔ truth_at M τ t ht φ := by
  induction φ with
  | atom p => simp [Formula.swap_past_future, truth_at]
  | bot => simp [Formula.swap_past_future, truth_at]
  | imp φ ψ ih_φ ih_ψ => ... -- use IHs
  | box φ ih => ... -- use IH
  | all_past φ ih => ... -- use IH
  | all_future φ ih => ... -- use IH

-- Main theorem using helper
theorem is_valid_swap_involution (φ : Formula) 
    (h : is_valid T φ.swap_past_future) : is_valid T φ := by
  intro F M τ t ht
  rw [← truth_at_swap_swap M τ t ht φ]
  exact h F M τ t ht
```

---

## Risk Assessment

**Low Risk**:
- Standard structural induction pattern used throughout codebase
- Minimal changes (one helper lemma + one theorem update)
- No API changes or downstream impacts
- Isolated to Truth.lean

---

## Next Steps

1. Implement `truth_at_swap_swap` helper lemma
2. Update `is_valid_swap_involution` theorem
3. Build and test: `lake build Logos.Core.Semantics.Truth`
4. Verify full build: `lake build`
5. Run tests: `lake exe test`
6. Update SORRY_REGISTRY.md if tracked

---

## References

- Main Report: `.opencode/specs/193_prove_is_valid_swap_involution/reports/research-001.md`
- Truth.lean: `Logos/Core/Semantics/Truth.lean` (lines 629-632)
- Formula.lean: `Logos/Core/Syntax/Formula.lean` (swap definition, lines 204-213)
