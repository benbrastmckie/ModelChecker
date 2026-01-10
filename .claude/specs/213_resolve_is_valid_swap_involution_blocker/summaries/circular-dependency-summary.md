# Circular Dependency Analysis Summary

**Date**: 2025-12-28  
**Task**: 213  
**Full Report**: [circular-dependency-analysis.md](../reports/circular-dependency-analysis.md)

---

## Quick Summary

A circular dependency exists between `Truth.lean` and `Soundness.lean`:

```
Truth.lean → (needs soundness) → Soundness.lean → Validity.lean → Truth.lean ↺
```

The `temporal_duality` case in `derivable_implies_swap_valid` requires the soundness theorem to complete, but soundness is proven in `Soundness.lean`, which transitively imports `Truth.lean`.

---

## Why It Occurs

The `temporal_duality` rule is self-referential:
- Rule: `DerivationTree [] ψ` implies `DerivationTree [] ψ.swap`
- To prove soundness of this rule, we need to show: if `ψ.swap` is valid, then `ψ` is valid
- But this requires knowing that derivable formulas are valid (i.e., the soundness theorem itself!)

**Circular reasoning**: We need soundness to prove soundness.

---

## Current Solution (Implemented)

Accept the `sorry` in Truth.lean (line 1256) with clear documentation:
- Explains why the sorry exists (circular dependency)
- Documents what's needed to complete it (soundness theorem)
- Notes where it will be completed (Soundness.lean)

**Completion plan**: After the main soundness theorem is proven in Soundness.lean, complete the temporal_duality case there.

---

## Root Cause

**Mixing concerns**: Truth.lean contains both:
1. Pure semantic theorems (no proof system dependencies)
2. Bridge theorems connecting derivations to validity

The `derivable_implies_swap_valid` theorem is a bridge theorem that naturally requires both layers, making it prone to circular dependencies.

---

## Prevention Strategies

### 1. Module Layering Policy
Establish strict dependency hierarchy:
```
Layer 3: Metalogic (Soundness, Completeness)
   ↓
Layer 2: Semantics (Truth, Validity)
   ↓
Layer 1: Proof System (Derivation, Axioms)
```
**Rule**: Higher layers import lower layers, never reverse.

### 2. Bridge Module Pattern
Create intermediate modules for cross-layer theorems:
```
Soundness.lean (Layer 3)
   ↓
SoundnessLemmas.lean (Layer 2.5 - bridge)
   ↓
Truth.lean (Layer 2) + Derivation.lean (Layer 1)
```

### 3. Design-Time Dependency Analysis
Before adding a theorem, check:
- What does it import?
- What layer does it belong to?
- Who will import it?
- Would this create a cycle?

---

## Recommended Refactoring

### Medium-term (6-12 months)
**Extract bridge theorems to separate module**:
1. Create `Logos/Core/Metalogic/SoundnessLemmas.lean`
2. Move `derivable_implies_swap_valid` from Truth.lean to SoundnessLemmas.lean
3. Complete temporal_duality case in Soundness.lean using main soundness theorem

**Effort**: 4-6 hours  
**Benefit**: Clean separation, no sorries, clear dependencies

### Long-term (Future refactoring)
**Split Truth.lean into semantic and metatheoretic parts**:
1. `Truth.lean` - Pure semantic theorems only
2. `TruthMetatheory.lean` - Bridge theorems (mentions DerivationTree)

**Effort**: 12-16 hours  
**Benefit**: Best practice organization, prevents future circular dependencies

---

## Key Lessons

1. **Semantic ≠ Metatheoretic**: Theorems about truth/validity (semantic) are different from theorems connecting derivations to validity (metatheoretic)

2. **Syntactic involution ≠ Semantic involution**: `φ.swap.swap = φ` doesn't imply `is_valid φ.swap → is_valid φ`

3. **Temporal asymmetry**: `all_past` and `all_future` quantify over different time ranges, breaking symmetry

4. **Circular dependencies signal design issues**: Don't work around them - fix the module structure

5. **Bridge theorems need special handling**: Create dedicated modules for cross-layer theorems

---

## Quick Reference

**Circular dependency path**:
```
Truth.lean (line 1256 - needs soundness)
   ↑ (imported by)
Validity.lean
   ↑ (imported by)  
Soundness.lean (defines soundness)
```

**Blocked theorem**: `derivable_implies_swap_valid`, case `temporal_duality`

**Completion**: After main soundness theorem proven in Soundness.lean

**Full analysis**: See [circular-dependency-analysis.md](../reports/circular-dependency-analysis.md)
