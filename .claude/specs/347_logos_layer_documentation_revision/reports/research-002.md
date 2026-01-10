# Research Report: Task #347 (Supplement)

**Task**: Revise Logos layer documentation for new layer organization
**Date**: 2026-01-09
**Focus**: Detailed semantic clauses from academic papers for RECURSIVE_SEMANTICS.md

## Summary

This supplementary report extracts detailed semantic clauses for tense, modal, counterfactual, and temporal reference operators from two source papers: `possible_worlds.tex` (for the TM bimodal logic with task semantics) and `counterfactual_worlds.tex` (for counterfactual conditionals with hyperintensional propositions). These clauses provide the formal foundations for the Causal Layer semantics in the new five-layer Logos architecture.

## Source Documents

1. **possible_worlds.tex** (PossibleWorlds/JPL): Primary source for frame definitions, task semantics, tense operators, and modal operators with bimodal interaction principles
2. **counterfactual_worlds.tex** (Counterfactuals/JPL): Primary source for counterfactual conditional semantics, hyperintensional propositions, and store/recall operators

**Note**: The treatment of time in `counterfactual_worlds.tex` uses discrete integers (Z) for simplicity, whereas `possible_worlds.tex` uses the more general totally ordered abelian group structure. The semantic clauses from `counterfactual_worlds.tex` remain correct and should be adapted to the more sophisticated temporal structure.

---

## Frame Definitions (from possible_worlds.tex)

### Definition: Frame

A *frame* is a structure F = ⟨W, D, ⇒⟩ where:

| Component | Description |
|-----------|-------------|
| **World States** | A nonempty set W of world states |
| **Temporal Order** | A totally ordered abelian group D = ⟨D, +, ≤⟩ |
| **Task Relation** | A parameterized task relation ⇒ satisfying: |
| | • **Nullity**: w ⇒₀ w |
| | • **Compositionality**: If w ⇒ₓ u and u ⇒ᵧ v, then w ⇒ₓ₊ᵧ v |

### Definition: World History

A *world history* over a frame F = ⟨W, D, ⇒⟩ is a function τ : X → W where:
- X ⊆ D is convex
- τ(x) ⇒ᵧ₋ₓ τ(y) for all times x, y ∈ X where x ≤ y

The set of all world histories over F is denoted H_F.

### Definition: Model

A *model* of the bimodal language BL is a structure M = ⟨W, D, ⇒, |·|⟩ where:
- F = ⟨W, D, ⇒⟩ is a frame
- |pᵢ| ⊆ W for every sentence letter pᵢ ∈ SL

---

## Semantic Clauses for TM Bimodal Logic (from possible_worlds.tex)

### Core Operators

Truth in a model at a world history and time is defined recursively:

| Operator | Semantic Clause |
|----------|-----------------|
| **(pᵢ)** | M, τ, x ⊨ pᵢ iff x ∈ dom(τ) and τ(x) ∈ \|pᵢ\| |
| **(⊥)** | M, τ, x ⊭ ⊥ |
| **(→)** | M, τ, x ⊨ φ → ψ iff M, τ, x ⊭ φ or M, τ, x ⊨ ψ |
| **(□)** | M, τ, x ⊨ □φ iff M, σ, x ⊨ φ for all σ ∈ H_F |
| **(H)** | M, τ, x ⊨ Hφ iff M, τ, y ⊨ φ for all y ∈ D where y < x |
| **(G)** | M, τ, x ⊨ Gφ iff M, τ, y ⊨ φ for all y ∈ D where x < y |

### Derived Operators

| Operator | Definition | Reading |
|----------|------------|---------|
| **◇φ** | ¬□¬φ | "Possibly φ" |
| **Pφ** | ¬H¬φ | "It was the case that φ" |
| **Fφ** | ¬G¬φ | "It will be the case that φ" |
| **△φ** | Hφ ∧ φ ∧ Gφ | "Always φ" (at all times) |
| **▽φ** | Pφ ∨ φ ∨ Fφ | "Sometimes φ" (at some time) |

### Extended Tense Operators

| Operator | Semantic Clause |
|----------|-----------------|
| **(X)** Next | M, τ, x ⊨ Xφ iff M, τ, y ⊨ φ for some y > x where y ≤ z for all times z > x |
| **(Y)** Previous | M, τ, x ⊨ Yφ iff M, τ, y ⊨ φ for some y < x where y ≥ z for all times z < x |
| **(S)** Since | M, τ, x ⊨ φ S ψ iff M, τ, z ⊨ ψ for some time z < x where M, τ, y ⊨ φ for all intermediate times y ∈ D where z < y < x |
| **(U)** Until | M, τ, x ⊨ φ U ψ iff M, τ, z ⊨ ψ for some time z > x where M, τ, y ⊨ φ for all intermediate times y ∈ D where x < y < z |

**Note**: The Next (X) and Previous (Y) operators only have natural applications given a restriction to discrete frames.

---

## Bimodal Interaction Principles (from possible_worlds.tex)

The task semantics validates the following perpetuity principles:

| Principle | Formula | Reading |
|-----------|---------|---------|
| **P1** | □φ → △φ | Necessary implies always |
| **P2** | ▽φ → ◇φ | Sometimes implies possible |
| **P3** | □△φ ↔ △□φ | Necessary-always equivalence |
| **P4** | ◇▽φ ↔ ▽◇φ | Possible-sometimes equivalence |
| **P5** | □φ → □△φ | Necessary implies necessary-always |
| **P6** | ▽◇φ → ◇φ | Sometimes-possible implies possible |

---

## Temporal Frame Extensions (from possible_worlds.tex)

Additional frame constraints on the temporal order D:

| Constraint | Description | Corresponding Axiom |
|------------|-------------|---------------------|
| **Discrete Past** | For any x ∈ D, if there is y < x, then there is a greatest y' < x where z ≤ y' for all z < x | DP: (Gφ ∧ φ ∧ Pφ⊤) → P(Gφ) |
| **Discrete Future** | For any x ∈ D, if there is y > x, then there is a least y' > x where z ≥ y' for all z > x | DF: (Hφ ∧ φ ∧ F⊤) → F(Hφ) |
| **Dense** | For any x, y ∈ D where x < y, there is z ∈ D where x < z < y | DN: GGφ → Gφ |
| **Complete** | Every set X ⊆ D bounded above has a least upper bound | CO: △(Hφ → FHφ) → (Hφ → Gφ) |
| **Unbounded Past** | Domain has no earliest time | UP: P⊤ |
| **Unbounded Future** | Domain has no latest time | UF: F⊤ |

---

## Counterfactual Semantics (from counterfactual_worlds.tex)

### Hyperintensional Propositions

An ordered pair ⟨V, F⟩ is a *bilateral proposition* iff:
- ⟨V, F⟩ is **exclusive**: states in V are incompatible with states in F
- ⟨V, F⟩ is **exhaustive**: every possible state is compatible with some state in V or F
- V and F are both **closed under fusion**

### Propositional Operations

| Operation | Definition |
|-----------|------------|
| **Product** | X ⊗ Y := {s.t \| s ∈ X, t ∈ Y} |
| **Sum** | X ⊕ Y := X ∪ Y ∪ (X ⊗ Y) |
| **Conjunction** | ⟨V,F⟩ ∧ ⟨V',F'⟩ := ⟨V ⊗ V', F ⊕ F'⟩ |
| **Disjunction** | ⟨V,F⟩ ∨ ⟨V',F'⟩ := ⟨V ⊕ V', F ⊗ F'⟩ |
| **Negation** | ¬⟨V,F⟩ := ⟨F, V⟩ |

### Interpretation Clauses (Exact Inclusive Semantics)

For extensional sentences (where |φ| = ⟨|φ|⁺, |φ|⁻⟩):

| Sentence | Interpretation |
|----------|---------------|
| **|¬φ|** | ¬|φ| |
| **|φ ∧ ψ|** | |φ| ∧ |ψ| |
| **|φ ∨ ψ|** | |φ| ∨ |ψ| |

### Truth at World-Time Pairs

| Operator | Semantic Clause |
|----------|-----------------|
| **(q)** Atomic | M, α, x ⊨ q iff there is some s ⊑ α(x) where s ∈ \|q\|⁺ |
| **(¬)** | M, α, x ⊨ ¬A iff M, α, x ⊭ A |
| **(∧)** | M, α, x ⊨ A ∧ B iff M, α, x ⊨ A and M, α, x ⊨ B |
| **(∨)** | M, α, x ⊨ A ∨ B iff M, α, x ⊨ A or M, α, x ⊨ B |
| **(H)** | M, α, x ⊨ Hφ iff M, α, y ⊨ φ for all y < x |
| **(G)** | M, α, x ⊨ Gφ iff M, α, y ⊨ φ for all y > x |

### Counterfactual Conditional

**Imposition-based clause**:
> M, α, x ⊨ φ □→ C iff M, β, x ⊨ C whenever t ∈ |φ|⁺ and t ▷_α(x) β(x)

**Mereological reformulation**:
> M, α, x ⊨ φ □→ C iff for all t ∈ |φ|⁺ and β ∈ H_Z, if s.t ⊑ β(x) for some maximal t-compatible part s ∈ α(x)_t, then M, β, x ⊨ C

**Intuitive reading**: A counterfactual is true in a world α at time x iff the consequent is true in any world β at x where β(x) is the result of minimally changing α(x) to make the antecedent true.

### Key Definitions for Counterfactual Evaluation

| Term | Definition |
|------|------------|
| **t-compatible** | State s is t-compatible iff s ∘ t (s and t are compatible, i.e., s.t is possible) |
| **Maximal t-compatible part** | r ∈ s_t is maximal iff r ⊑ s, r ∘ t, and for all r' where r ⊑ r' ⊑ s and r' ∘ t, we have r' ⊑ r |
| **Imposition** | t ▷_w w' iff there exists maximal t-compatible part s ∈ w_t where s.t ⊑ w' |

---

## Store and Recall Operators (from counterfactual_worlds.tex)

### Language Extension

L* extends L to include:
- Unary **store operator** ↑ᵢ for all i ∈ N
- Unary **recall operator** ↓ⁱ for all i ∈ N

### Semantic Clauses

The evaluation context is extended to include a vector v⃗ = ⟨v₁, v₂, ...⟩ of stored times:

| Operator | Semantic Clause | Effect |
|----------|-----------------|--------|
| **(↑)** Store | M, α, x, v⃗ ⊨ ↑ⁱA iff M, α, x, v⃗[x/vᵢ] ⊨ A | Replaces vᵢ with current time x |
| **(↓)** Recall | M, α, x, v⃗ ⊨ ↓ⁱA iff M, α, vᵢ, v⃗ ⊨ A | Shifts evaluation time to stored vᵢ |

**Usage Example** (Nixon button scenario):
- ↓¹(B □→ FH) - "If Nixon had pressed the button at the stored time, a nuclear holocaust would have occurred at some future time"
- ↑²↓¹(B □→ ↓²H) - "Store current time, go back to button-press time, if pressed then holocaust at the current (assertion) time"

---

## Modal Logic Derived from Counterfactuals

Metaphysical necessity can be defined in terms of counterfactuals:

| Definition | Formula | Reading |
|------------|---------|---------|
| **Necessity** | □A := ⊤ □→ A | "Necessarily A" |
| **Possibility** | ◇A := ¬□¬A | "Possibly A" |

This yields an S5 modal logic without requiring frame constraints.

---

## Logical Consequence

### For TM Bimodal Logic (from possible_worlds.tex)

Γ ⊨ C iff for any model M, world history τ ∈ H_F, and time x ∈ D: if M, τ, x ⊨ A for all A ∈ Γ, then M, τ, x ⊨ C

### For Counterfactual Logic (from counterfactual_worlds.tex)

Γ ⊨ C iff for any model M of L, world α, and time x: if M, α, x ⊨ A for all A ∈ Γ, then M, α, x ⊨ C

---

## Counterfactual Logic Axiom Schemata (from counterfactual_worlds.tex)

### Core Counterfactual Rules

| Axiom | Schema | Name |
|-------|--------|------|
| **R1** | If Γ ⊢ C, then φ □→ Γ ⊢ φ □→ C | Closure under deduction |
| **C1** | φ □→ φ | Identity |
| **C2** | φ, φ □→ A ⊢ A | Counterfactual Modus Ponens |
| **C3** | φ □→ ψ, φ ∧ ψ □→ A ⊢ φ □→ A | Weakened Transitivity |
| **C4** | φ ∨ ψ □→ A ⊢ φ ∧ ψ □→ A | Disjunction-Conjunction |
| **C5** | φ ∨ ψ □→ A ⊢ φ □→ A | Simplification (Left) |
| **C6** | φ ∨ ψ □→ A ⊢ ψ □→ A | Simplification (Right) |
| **C7** | φ □→ A, ψ □→ A, φ ∧ ψ □→ A ⊢ φ ∨ ψ □→ A | Disjunction Introduction |

### Modal Axioms

| Axiom | Schema |
|-------|--------|
| **M1** | ⊤ |
| **M2** | ¬⊥ |
| **M3** | A → □◇A |
| **M4** | □A → □□A |
| **M5** | □(φ → A) ⊢ φ □→ A |

### Tense Axioms (for CTL extension)

| Axiom | Schema | Description |
|-------|--------|-------------|
| **TK** | If Γ ⊢ C, then GΓ ⊢ GC | Future closure |
| **TD** | If Γ ⊢ C, then Γ[P↔F] ⊢ C[P↔F] | Temporal duality |
| **GP** | A → GPA | Present preserved in past |
| **TR** | GA → GGA | Future transitivity |
| **LN** | GHA → △A | Linearity |
| **FN** | □A → G□A | Future necessity |
| **UF** | FA | Unbounded future |

---

## Integration with Five-Layer Architecture

### Mapping to Logos Layers

| Paper Concept | Logos Layer | Notes |
|---------------|-------------|-------|
| Frame (W, D, ⇒) | Causal Layer | Core structure for world-histories |
| Task relation | Causal Layer | Constrains possible state transitions |
| Tense operators (H, G, P, F) | Causal Layer | Intra-world temporal quantification |
| Modal operators (□, ◇) | Causal Layer | Inter-world quantification |
| Counterfactual (□→) | Causal Layer | Minimal change semantics |
| Hyperintensional propositions | Constitutive Layer | Verification/falsification structure |
| Store/Recall (↑, ↓) | Causal Layer | Temporal reference operators |
| Epistemic operators | Epistemic Layer | [DETAILS] to be specified |
| Normative operators | Normative Layer | [DETAILS] to be specified |

### Key Architectural Notes

1. **Hyperintensional Foundation**: The Constitutive Layer provides the mereological state space with bilateral propositions (verifier/falsifier pairs) that the Causal Layer builds upon

2. **Intensional Evaluation**: The Causal Layer evaluates truth relative to world-history and time, using parthood (⊑) to connect atomic truth to state structure

3. **Counterfactual-Modal Connection**: Necessity (□) can be defined as ⊤ □→ A, showing modal operators derive from counterfactual structure

4. **Store/Recall for Cross-Temporal Reference**: The ↑/↓ operators enable referring to specific stored times within counterfactual evaluation, essential for natural language counterfactual expressions

---

## Recommendations for RECURSIVE_SEMANTICS.md

1. **Structure document by layer**, starting with Constitutive (hyperintensional propositions), then Causal (world-histories, tense, modal, counterfactual)

2. **Include formal definitions** for Frame, World History, Model exactly as given in possible_worlds.tex

3. **Present all semantic clauses** in consistent notation with both formal and intuitive readings

4. **Document the counterfactual mereological clause** as the primary semantic definition, with imposition as derived

5. **Add Store/Recall operators** to enable full temporal reference capabilities

6. **Mark Epistemic and Normative layers** with [DETAILS] tags pending further specification

---

## References

- possible_worlds.tex: §2 Primitive Worlds, §2.3 Extensions (lines 1106-1186), Appendix §5.2 Task Semantics (lines 1831-2101)
- counterfactual_worlds.tex: §3 Construction of Possible Worlds (lines 686-870), §4 Counterfactual Logic (lines 872-1044), §5.1 Temporal Operators (lines 1248-1295)
