# Adequacy of Witness-Family Certificates for Bimodal Countermodels

## Scope and status of this document

This document states and proves a soundness correspondence between the witness-family
certificate design for the bimodal (`BL`) theory and the task semantics of
`sec:Construction` in the source paper (`~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`,
cited below by line number, e.g. `:1068`). The certificate design it describes **is** the theory's
shipped encoding: the window-and-abundance encoding this document was originally written against
is retired outright (it refuted the paper's own MF axiom, which was decisive evidence it was not a
model of the paper's semantics — see `ARCHITECTURE.md`'s "Retired Designs" and `semantic/core.py`'s
module docstring), and `semantic/` now implements the certificate search this document's theorem
targets. It is **not** a validity claim: the theorem refutes single inferences, never
asserts them. It is stated for **discrete (ℤ) time only**; the reasons are recorded in
"Why ℤ-time only" below, not assumed. The stability modal is out of scope throughout.

Two statements are distinguished by name and by status:

- **(SOUND)** — mandatory, proved in full below, for the certificate design.
- **(ADEQ)** — the converse direction, recorded as **open**, reduced to three named components
  plus one permanent limit, never asserted. See "The (ADEQ) direction" below.

All Lean citations are to `~/Projects/BimodalLogic/FormalSystem/` unless marked `BimodalTools/`.
Every cited name was checked to resolve at the cited file and line at the time of writing.

For the pipeline these statements sit inside — which component carries which guarantee, what kind
of evidence backs each one, what is and is not in the trust base, and what remains open in this
repository and in the Lean development — see `TRUST_PIPELINE.md`. That document cites this one
rather than restating it.

---

## 1. The certificate

A **certificate** is a pair `𝒲 = (bx, ⟨Λ₀, …, Λ_k⟩)` together with a target time `t₀ ∈ ℤ`, over a
fixed finite formula closure `C := closureOf (Γ ++ Δ)` for premises `Γ` and conclusions `Δ`
(finite sets of `BL` sentences translated into the primitive grammar `atom | bot | imp | box |
untl | snce`). `bx : Formula → Bool` is the box guess. Each `Λᵢ = (backᵢ, midᵢ, fwdᵢ)` is a triple
of lists of subsets of `C`, with `backᵢ ≠ []` and `fwdᵢ ≠ []` (`mid` may be empty), decoded to a
bi-infinite label function `Lᵢ : ℤ → 𝒫(C)` by the three-segment scheme: `back` repeated strictly
left of `0`, `mid` on `[0, |mid|)`, and `fwd` repeated from `|mid|` onward. This is exactly
`LabelledLasso` (`Metalogic/Decidability/WitnessFamily/Basic.lean:76`) and its decoding function
`lab` (`Basic.lean:104`, via `Periodic.unrollOf`).

A certificate must satisfy four conditions, for every `i` and every `t ∈ ℤ`:

- **(C1) Local coherence.** `⊥ ∉ Lᵢ(t)`; for every `a → b ∈ C`,
  `(a → b) ∈ Lᵢ(t) ↔ (a ∈ Lᵢ(t) → b ∈ Lᵢ(t))`; for every `□χ ∈ C`,
  `□χ ∈ Lᵢ(t) ↔ bx(χ) = true`; for every `g U e ∈ C`,
  `(g U e) ∈ Lᵢ(t) ↔ (e ∈ Lᵢ(t+1) ∨ (g ∈ Lᵢ(t+1) ∧ (g U e) ∈ Lᵢ(t+1)))`; and the mirror for
  `g S e` at `t − 1`. **Atoms are deliberately unconstrained** — see Lemma 4's atom case below for
  why that is sound rather than a gap.
- **(C2) Fulfilment.** For every `i, t, g, e`: if `(g U e) ∈ Lᵢ(t)` then there is `s > t` with
  `e ∈ Lᵢ(s)` and `g ∈ Lᵢ(r)` for every `t < r < s`; and the mirror for `S` with `s < t`.
- **(C3) Box faithfulness.** For every `□χ ∈ C`: `bx(χ) = true ↔ ∀ i ∀ t. χ ∈ Lᵢ(t)`.
- **(C4) Target.** `∀ γ ∈ Γ. γ ∈ L₀(t₀)` and `∀ σ ∈ Δ. σ ∉ L₀(t₀)`.

Why both (C1) and (C2) are needed, and why discreteness matters, is explained after Lemma 4's
proof, where the mechanism becomes visible.

---

## 2. (SOUND): statement and obligations

**(SOUND).** *If the search reports a countermodel for `Γ / Δ`, presented as a certificate
`(𝒲, t₀)` satisfying (C1)–(C4), then there exist a model `M = ⟨W, 𝔇, ⇒, |·|⟩` of `BL` in the
paper's sense — `𝔇` a nontrivial totally ordered abelian group and `⇒` a task relation satisfying
Compositionality, Seriality, Limit and Saturation (`:989-994`) — a world history `τ ∈ H_F`, and a
time `x ∈ D`, such that `M, τ, x ⊨ γ` for every `γ ∈ Γ` and `M, τ, x ⊭ σ` for every `σ ∈ Δ`. Hence
`Γ ⊭ σ` for every `σ ∈ Δ`, in the sense of `def:logical-consequence` (`:1124`).*

This is mandatory. It decomposes into four obligations, of which only two require new work in
this repository:

| | Obligation | Status |
|---|---|---|
| **S1** | (C1)–(C4) ⟹ a paper countermodel exists | **Proved** below (§3); machine-checked, `WitnessFamily.joint_countermodel` (`Metalogic/Decidability/WitnessFamily/Agreement.lean:232`). |
| **S2** | The Lean definitions transcribe the paper's | Discharged by inspection, §4 (the transcription audit); an audit, not a theorem. |
| **S3** | Whatever the search reports satisfies (C1)–(C4) | Discharged by *deciding* the antecedent on every reported countermodel, independently, twice — §6 (presentation and re-verification). |
| **S4** | The `Sentence` → `Formula` translation preserves truth | Discharged for both the tense and box halves by a differential property test — §6.3; an upstream Lean theorem (`sat_iff`, `BimodalLogic`'s `SentenceTruth.lean`) now exists for BimodalLogic's own reference translation, but this repository's own translation is not yet diffed against it. |

**S3 is the architectural point of the whole design.** (SOUND)'s antecedent is decidable (the
four conditions collapse to finite windows — §5), so nothing in this repository has to prove the
Z3 encoder correct. The antecedent is re-decided on every reported countermodel, twice and
independently (§6). A verified antecedent together with S1 *is* a countermodel; an encoder bug
becomes a loud rejection, not a false report.

---

## 3. The construction and the proof of (SOUND)

Fix a certificate `(𝒲, t₀)` satisfying (C1)–(C4). Define:

- `𝔇 := ⟨ℤ, +, 0, ≤⟩`;
- `W := {0, …, k} × ℤ`;
- `(i, t) ⇒_x (j, u)` iff `i = j` and `u = t + x`, for all `x ∈ ℤ`;
- `|p| := {(i, t) ∈ W : atom p ∈ Lᵢ(t)}`;
- `τᵢ : ℤ → W`, `τᵢ(t) := (i, t)`;
- `F := ⟨W, 𝔇, ⇒⟩`, `M := ⟨W, 𝔇, ⇒, |·|⟩`.

**Reflection convention.** The paper defines `w ⇒_{-x} u := u ⇒_x w` for `x ≥ 0` (`:970`). The
relation above is given at every `x ∈ ℤ` directly; it is consistent with the convention rather
than merely compatible with it, since for `x ≥ 0`: `(j,u) ⇒_x (i,t)` iff `j = i ∧ t = u + x` iff
`i = j ∧ u = t + (−x)` iff `(i,t) ⇒_{−x} (j,u)`.

This construction is `WitnessFamily.std` (`Metalogic/Decidability/WitnessFamily/Std.lean:65`).

### Lemma 1 (Frame)

**Statement.** `F` is a task frame in the sense of `:989-994`.

**Proof.** `𝔇 = ⟨ℤ, +, 0, ≤⟩` is a totally ordered abelian group and is nontrivial (`1 ≠ 0`), so
it is a temporal order (`:961`). `W` is nonempty since `k ≥ 0`. The four constraints, for
`x, y ≥ 0` and `w, u, v ∈ W`:

- *Compositionality*: `w ⇒_{x+y} v` iff `∃ u ∈ W. w ⇒_x u ∧ u ⇒_y v`. Left to right: given
  `v = (w₁, w₂ + x + y)`, take `u := (w₁, w₂ + x)`; then `w ⇒_x u` and `u ⇒_y v`. Right to left:
  from `u = (w₁, w₂+x)` and `v = (u₁, u₂+y)` we get `v = (w₁, w₂+x+y)`, i.e. `w ⇒_{x+y} v`.
- *Seriality*: given `w` and `x ≥ 0`, put `u := (w₁, w₂ + x)` and `v := (w₁, w₂ − x)`; then
  `w ⇒_x u` and `v ⇒_x w`.
- *Limit*: `⋂_{x>0} (w)_x = {w}`, where `(w)_x = ⋃_{|y| < x} ⟨w, y⟩` and `⟨w,y⟩ = {u : w ⇒_y u}`.
  Over `ℤ`, `x > 0` implies `x ≥ 1`, so `(w)_1` is already a member of the family, and `|y| < 1`
  over `ℤ` forces `y = 0`, whence `(w)_1 = ⟨w, 0⟩ = {(w₁, w₂)} = {w}`. Since every `(w)_x` contains
  `w` (take `y = 0`), the intersection is exactly `{w}`.

  *(General-transcription note. This calculation proves the paper's Limit set-equation in full,
  both directions, for the concrete certified construction. The general Lean transcription is
  narrower: `TaskFrame.Limit` transcribes only the `⊆` half — the intersection is contained in
  `{w}`. The `⊇` half — that `w` lies in each of its own positive cones — is `lem:nullity`,
  **derived** choice-free from Seriality together with the `⊆` half, via
  `TaskFrame.nullity_of_serial_limit`, not postulated; carrying it as an axiom would duplicate a
  theorem. Nothing in this proof weakens: it is about the specific carrier above, not about
  `TaskFrame.Limit`'s general definition.)*
- *Saturation*: every fibre `⟨w, x⟩ = {(w₁, w₂+x)}` is a singleton, and every segment
  `[w,u]_x^y = ⟨w,x⟩ ∩ ⟨u,−y⟩` is a subset of a singleton, hence empty or a singleton. Let `𝒮` be a
  `⊇`-directed family of nonempty fibres and segments; every member is a singleton. For
  `S₁, S₂ ∈ 𝒮`, directedness gives `S ∈ 𝒮` with `S ⊆ S₁ ∩ S₂`; `S` is a nonempty singleton, so
  `S₁ ∩ S₂ ≠ ∅`, so `S₁ = S₂`. Thus `𝒮 = {S}` for a single singleton `S`, and `⋂ 𝒮 = S ≠ ∅`. ∎

*(This is the step at which determinism — every fibre a singleton — is load-bearing; see
"Why the design is deterministic" below.)*

### Lemma 2 (Histories)

**Statement.** Each `τᵢ` is a world history, and
`H_F = { t ↦ (i, t + c) : 0 ≤ i ≤ k, c ∈ ℤ }`.

**Proof.** `τᵢ` is total on `D = ℤ`, and for all `x, y ∈ ℤ`,
`τᵢ(x) = (i, x) ⇒_{y−x} (i, x + (y−x)) = (i, y) = τᵢ(y)`, so `τᵢ ∈ H_F` (`:1029`).

Conversely, let `σ ∈ H_F`. For all `x, y`, `σ(x) ⇒_{y−x} σ(y)`, which by definition of `⇒` forces
`σ(y)₁ = σ(x)₁` and `σ(y)₂ = σ(x)₂ + (y − x)`. Putting `i := σ(0)₁` and `c := σ(0)₂` gives
`σ(t) = (i, t + c)` for all `t`. ∎

**Corollary 2.1 (Translation closure, derived, not asserted).** `H_F` is closed under
translation: if `σ(t) = (i, t+c)` then `z ↦ σ(z + d)` is `z ↦ (i, z + c + d) ∈ H_F`. So
`app:auto_existence` (`:3197-3206`) holds *by construction* for this frame, in contrast to the
encoding's current abundance constraints, which *assert* translation-closure as a solver axiom.

**Corollary 2.2 (Box's range).** By Lemma 2, `H_F` is exactly the `k+1` lassos and their
translates. So the `(□)` clause at `:1073` quantifies over precisely the certified histories —
which is what makes (C3) a statement about the certificate rather than an oracle assumption.

### Lemma 3 (Time-shift preservation, instantiated)

**Statement.** For every `BL` sentence `ψ`, every `σ, ρ ∈ H_F` and `x, y ∈ D` with `σ ≈_x^y ρ`:
`M, σ, x ⊨ ψ` iff `M, ρ, y ⊨ ψ`.

This is `lem:history-time-shift-preservation` (`:3212`, proof at `:3216-3223`) applied to `M`; its
proof uses only that `|pᵢ| ⊆ W` (no temporal component in the valuation) and `app:auto_existence`,
both of which hold here — the latter by Corollary 2.1 rather than by hypothesis.

**Corollary 3.1.** Combining Lemmas 2 and 3, truth in `M` at `(σ, t)` depends only on the carrier
point `σ(t) = (i, t+c)`. In particular `M, τᵢ, t ⊨ ψ` and `M, τᵢ^{(c)}, t ⊨ ψ` agree with
`M, τᵢ, t + c ⊨ ψ`, and `M, σ, x ⊨ □χ` iff `M, τⱼ, u ⊨ χ` for every `j` and every `u ∈ ℤ`.

### Lemma 4 (Truth lemma / agreement)

**Statement.** For every `ψ ∈ C`, every `i`, and every `t ∈ ℤ`: `M, τᵢ, t ⊨ ψ` iff `ψ ∈ Lᵢ(t)`.

**Proof.** By induction on `ψ`. `C` is closed under subformulas, so every appeal to the induction
hypothesis is legitimate.

- **`ψ = p` (atom).** `M, τᵢ, t ⊨ p` iff `τᵢ(t) = (i,t) ∈ |p|` iff `atom p ∈ Lᵢ(t)`, by the
  definition of `|·|`. This is why (C1) leaves atoms unconstrained: the atom case is an identity,
  not an appeal to a valuation clause.
- **`ψ = ⊥`.** Neither side holds: `M, τᵢ, t ⊭ ⊥` by `(⊥)`, and `⊥ ∉ Lᵢ(t)` by (C1).
- **`ψ = a → b`.** `M, τᵢ, t ⊨ a → b` iff (`M, τᵢ, t ⊭ a` or `M, τᵢ, t ⊨ b`) by `(→)`, iff
  (`a ∈ Lᵢ(t) → b ∈ Lᵢ(t)`) by the induction hypothesis at `a` and `b`, iff `(a→b) ∈ Lᵢ(t)` by
  (C1)'s implication clause. (This is where (C1)'s clauses being *biconditionals* does the work
  that a maximal-consistent-set construction would otherwise do.)
- **`ψ = □χ`.** By Corollary 3.1, `M, τᵢ, t ⊨ □χ` iff `M, τⱼ, u ⊨ χ` for all `j, u`. By the
  induction hypothesis, iff `χ ∈ Lⱼ(u)` for all `j, u`. By (C3), iff `bx(χ) = true`. By (C1)'s box
  clause, iff `□χ ∈ Lᵢ(t)`.
- **`ψ = g U e`.**
  *(⇐)* Suppose `(g U e) ∈ Lᵢ(t)`. By **(C2)** there is `s > t` with `e ∈ Lᵢ(s)` and `g ∈ Lᵢ(r)`
  for all `t < r < s`. The induction hypothesis gives `M, τᵢ, s ⊨ e` and `M, τᵢ, r ⊨ g` for all
  such `r`, so `M, τᵢ, t ⊨ g U e` by `(U)` at `:1075`.
  *(⇒)* Suppose `M, τᵢ, t ⊨ g U e`, witnessed by `s > t`. Since `D = ℤ` is discrete,
  `n := s − t ≥ 1` is a positive integer; argue by strong induction on `n`. If `n = 1` then
  `s = t+1` and `M, τᵢ, t+1 ⊨ e`, so `e ∈ Lᵢ(t+1)` by the (outer) induction hypothesis at `e`, and
  (C1)'s until clause gives `(g U e) ∈ Lᵢ(t)`. If `n > 1` then `M, τᵢ, t+1 ⊨ g` (as
  `t < t+1 < s`) and `M, τᵢ, t+1 ⊨ g U e` with the same witness `s`, at distance `n − 1`; by the
  inner induction `(g U e) ∈ Lᵢ(t+1)`, and by the outer induction hypothesis `g ∈ Lᵢ(t+1)`, so
  (C1)'s until clause again gives `(g U e) ∈ Lᵢ(t)`.
- **`ψ = g S e`.** Symmetric, with `t−1` in place of `t+1` and the witness below `t`. ∎

**Remark (why both (C1) and (C2) are needed, and where discreteness enters).** The two directions
of the `U` case consume different conditions. `(⇐)` is exactly fulfilment: (C1)'s until clause is
a *fixpoint law*, satisfied equally by the label that carries `g U e` forward forever and never
delivers `e` — coherence alone admits infinite postponement, and (C2) is what excludes it.
`(⇒)` is a **downward induction on the coherence fixpoint law**, and it is the one place in the
whole proof where `D = ℤ` (rather than an arbitrary temporal order) is used: over a dense order
the descent `s − t → 0` does not terminate. This is one of the three reasons the design is
ℤ-time only; see "Why ℤ-time only" below.

### The theorem

**Theorem ((SOUND)).** *Under (C1)–(C4), `M, τ₀, t₀ ⊨ γ` for every `γ ∈ Γ` and `M, τ₀, t₀ ⊭ σ`
for every `σ ∈ Δ`, where `M` and `τ₀` are as constructed and `F` is a task frame with `τ₀ ∈ H_F`.
Hence `Γ ⊭ σ` for every `σ ∈ Δ`.*

**Proof.** `F` is a task frame by Lemma 1 and `τ₀ ∈ H_F` by Lemma 2, so `(M, τ₀, t₀)` is an
admissible evaluation point. Every `γ ∈ Γ` and `σ ∈ Δ` lies in `C`. By (C4), `γ ∈ L₀(t₀)` for
every `γ ∈ Γ` and `σ ∉ L₀(t₀)` for every `σ ∈ Δ`. Lemma 4 at `i = 0`, `t = t₀` converts both into
truth-value claims. By `def:logical-consequence` (`:1124`), which requires the conclusion to hold
at *every* model, possible world and time at which the premises hold, the point `(M, τ₀, t₀)`
refutes `Γ ⊨ σ` for each `σ ∈ Δ`. ∎

**Corollary (non-vacuity of the frame).** `H_F ≠ ∅` and every world state occurs in some history
(`cor:occurrence`, `:3075`) hold here by construction: `(i,t) = τᵢ(t)`. No appeal to Zorn's lemma
or `thm:extension` is made anywhere in this proof — the histories are exhibited, not extended.
This matters because `thm:extension` is a ZFC theorem (`:3060`) while everything above is
elementary.

---

## 4. Lean citation table and transcription audit (obligation S2)

### 4.1 Every step, mapped to a landed, sorry-free Lean counterpart

`grep -c sorry` returns `0` for `Semantics/ShiftSet.lean`, `WitnessFamily/Agreement.lean`,
`WitnessFamily/Decide.lean` and `Metalogic/Independence/ZTimeSharpness.lean`; the only `sorry` occurrences anywhere in `WitnessFamily/` and
`Metalogic/Soundness.lean` are in docstring prose, not in proof terms. `FormalSystem/` declares no
axioms (`FormalSystem/MainResults.lean` runs `#print axioms` at build time as a pinned audit).

| This document | Lean name | File:line |
|---|---|---|
| The construction (`𝔇`, `W`, `⇒`, `\|·\|`) | `WitnessFamily.std` | `Metalogic/Decidability/WitnessFamily/Std.lean:65` |
| Lemma 1, Compositionality | `ShiftSet.shRel_comp` | `Semantics/ShiftSet.lean:157` |
| Lemma 1, Seriality | `ShiftSet.shRel_serial` | `Semantics/ShiftSet.lean:172` |
| Lemma 1, Limit | the `sep` field, via `TaskFrame.limit_reflect_of_reflective` | `Semantics/ShiftSet.lean:115, 203`; discharged for `std` via `ShiftSet.ofIntAction` (`Semantics/ShiftSet.lean:494`) and `ShiftSet.sep_of_succOrder` (`Semantics/ShiftSet.lean:472`) — **kernel-checked** from discreteness, not hand-proved |
| Lemma 1, Saturation | `ShiftSet.shRel_saturation` (`saturation_of_fib_subsingleton`) | `Semantics/ShiftSet.lean:180` |
| Lemma 1, whole | `ShiftSet.fibre_isRegular` / `frame_isRegular` | `Semantics/ShiftSet.lean:209, 234` |
| The frame is ℤ-time | `WitnessFamily.std_isZTime`, `std_sat_ztime`, `std_sat_base` | `Metalogic/Decidability/WitnessFamily/Std.lean:81, 87, 92` |
| Lemma 2 | `ShiftSet.total_eq_orbit` | `Semantics/ShiftSet.lean:252` |
| Lemma 3 / Corollary 3.1 | `ShiftSet.forward_repr`, `WitnessFamily.sh_surj`, `Truth.box_const` | `Semantics/ShiftSet.lean:293`; `Metalogic/Decidability/WitnessFamily/Std.lean:98`; `Semantics/TruthTransport.lean:310` |
| Lemma 4 | `WitnessFamily.shiftTruth_iff_mem`, `truth_iff_mem` | `Metalogic/Decidability/WitnessFamily/Agreement.lean:109, 193` |
| Lemma 4, `U`/`S` helper | `untl_mem_of_witness`, `snce_mem_of_witness` | `Metalogic/Decidability/WitnessFamily/Agreement.lean:65, 85` |
| **The Theorem** | `WitnessFamily.joint_countermodel` | `Metalogic/Decidability/WitnessFamily/Agreement.lean:232` |
| Theorem, single-conclusion | `not_consequence_ztime`, `not_consequence_base` | `Metalogic/Decidability/WitnessFamily/Agreement.lean:203, 219` |
| The modal-future axiom is valid | `modal_future_valid` | `Metalogic/Soundness.lean:373` |
| No certificate refutes the modal-future axiom | `no_witnessFamily_of_MF` | `Metalogic/Decidability/WitnessFamily/Examples.lean:275` |
| A0: `prior_UZ` is not Base-valid | `not_validIn_base_prior_UZ` | `Metalogic/Independence/ZTimeSharpness.lean:263` |
| A0: `z1` is not Base-valid | `not_validIn_base_z1` | `Metalogic/Independence/ZTimeSharpness.lean:274` |
| A0: the `.ZTime` tag is minimal for both | `prior_UZ_minFrameClass_sharp`, `z1_minFrameClass_sharp` | `Metalogic/Independence/ZTimeSharpness.lean:289, 300` |

**Provenance note.** The declaration names in this table are the load-bearing citation; the line
numbers are a derived view taken from BimodalLogic's generated, C35-gated
`scripts/lean-citation-manifest.json`, and are re-resolvable by name against it. Every gate in
both repositories was green while several of the numbers above were stale — a docstring edit
upstream shifted them underneath unchanged names without breaking any check on either side — which
is exactly why the manifest and its C35 gate exist.

`joint_countermodel`'s statement is literally (SOUND)'s consequent:

```lean
theorem joint_countermodel (W : WitnessFamily Γ Del) {t : ℤ}
    (hloc : W.LocalCoherentLab) (hful : W.FulfillingLab) (hbox : W.BoxFaithful)
    (htgt : W.Target t) :
    ∃ (F : TaskFrame) (_ : FrameClass.ZTime.Sat F) (M : TaskModel F)
      (τ : WorldHistory F) (u : F.Duration),
      (∀ γ ∈ Γ, TruthAt M τ u γ) ∧ (∀ σ ∈ Del, ¬ TruthAt M τ u σ)
```

**A near-miss, recorded so it is not mistaken for the mechanization of Lemma 1.**
`Semantics/IntNormalForm.lean:456` supplies `ofStep {W} [Finite W] [Nonempty W] (R₁) (fwd) (bwd) :
FrameOver intOrder`, which does discharge all four constraints from bi-seriality alone —
Compositionality from `iter_add`, Limit from `limit_of_succOrder`, Saturation from
`saturation_of_finite`. It is **not** the mechanization of this document's Lemma 1: `ofStep`
requires `[Finite W]`, and Saturation is discharged *from finiteness*, whereas the certified
carrier `W = {0,…,k} × ℤ` is **infinite**, which is the whole point — `Probe476.fmp_false`
refutes the finite-carrier route as the searched object. Lemma 1's Saturation instead comes from
`shRel_saturation` (subsingleton fibres), i.e. from determinism, and the correct mechanization is
the `ShiftSet` chain in the table above. `ofStep` is the right tool for a fixed-frame
model-checking mode elsewhere in the redesign, and for nothing in this theorem.

### 4.2 The transcription audit (obligation S2)

(SOUND) is a claim about the paper; the Lean theorem is a claim about Lean's definitions. The
bridge is not a theorem and cannot be; it is an audit, discharged by inspection against the cited
paper line, not by proof.

| Paper | Lean | Verdict |
|---|---|---|
| `𝔇` = nontrivial totally ordered abelian group (`:961`) | `structure TemporalOrder` fields `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, `Nontrivial` (`Semantics/TemporalOrder.lean:83-93`) | **Exact**, field-by-field, with the paper's names in the docstrings |
| task frame + the four constraints (`:989-994`) | `structure TaskFrame` (`Semantics/TaskFrame.lean:2571`) with `TaskFrame.IsRegular` supplying `comp`, `serial`, `limit`, `saturation`, each cited to `def:frame` | **Exact.** `FrameClass.Base.Sat F = F.IsRegular` (`Semantics/FrameClassValidity.lean:152`) |
| `(pᵢ) (⊥) (→) (□) (S) (U)` (`:1068-1076`) | `def TruthAt` (`Semantics/Truth.lean:232-238`) | **Exact.** `box φ => ∀ σ : WorldHistory F, TruthAt M σ t φ` — no domain guard; `untl ψ φ` is guard-first, matching `φ U ψ` at `:1075` |
| `Γ ⊨ φ` (`:1124`, `def:logical-consequence` `:3236`) | `ConsequenceOnFrames P Γ φ` / `SemanticConsequenceIn .Base` (`Semantics/Validity.lean:80, 89`) | **Exact** modulo `Γ` finite (a `Context`, i.e. a list) rather than a set — harmless for model checking, where `Γ` is always finite |
| `app:auto_existence` (`:3197`) | not needed: Corollary 2.1 derives it | **Not a dependency** |
| `lem:history-time-shift-preservation` (`:3212`) | `TimeShift.timeShift_preserves_truth` (`Semantics/TruthTransport.lean`), consumed by `ShiftSet.reverse_repr` and `modal_future_valid` | **Exact**, and unconditional |
| — (no paper anchor of its own) | `FrameOver`'s `worldNonempty` field (`Semantics/TaskFrame.lean:1055`), accessed via `TaskFrame.worldNonempty` (`Semantics/TaskFrame.lean:2642`) | **Transcribed, not derived.** The paper's reading of `W` as a *nonempty* set is exactly this field. An empty carrier would satisfy all four frame constraints vacuously while validating falsehood — this document's own Lemma 1 proof above already relies on the fact ("`W` is nonempty since `k ≥ 0`") |
| `def:world-history` | `PartialHistory` (`Semantics/PartialHistory.lean:136`), `PartialHistory.IsTotal` (`:225`), `WorldHistory` (`:423`) | **Transcribed.** `TruthAt`'s Box clause quantifies over the **total** histories (row above, `Semantics/Truth.lean:232-238`; see also `joint_countermodel`'s `(τ : WorldHistory F)` at `:266`), so the whole Box case rests on this transcription |

**Residue row not reached.** `Semantics.TruthCorr` (`Semantics/TruthTransport.lean:92`) is
reachable as an audit row only if this table cites the *general* time-shift lemma
(`Truth.truthAt_of_truthCorr` at `TimeShift.shiftCorr`) rather than the *instantiated* one. The
row above cites the instantiated `TimeShift.timeShift_preserves_truth`, so the condition is unmet
and `TruthCorr`'s five fields do not currently enter this audit. This does not contradict the
`app:auto_existence` row's own position above ("not needed: Corollary 2.1 derives it"); it names
the structure that position's own derivation is stated in terms of, and applies only under the
general-lemma reading.

**Residual.** The paper's `BL` is `⟨SL, ⊥, →, □, S, U⟩`, exactly the Lean `Formula` grammar. This
theory's operator set is richer — nine primitives plus eight defined operators. The audit
therefore extends to the **translation** from theory sentences into the six-primitive grammar,
which is obligation S4. Both halves of that translation (tense and box) are now discharged by a
differential property test — see §6.3 for the evidence and its residual scope. Separately, an
upstream Lean theorem (`sat_iff`, `BimodalLogic`'s `SentenceTruth.lean`) now exists for
BimodalLogic's own reference translation, but this repository's own translation is not yet
diffed against it (see `docs/TRUST_PIPELINE.md`'s "What remains").

---

## Why the design is deterministic

Lemma 1's Limit and Saturation cases both use that every fibre `⟨w,x⟩` is a singleton — i.e. that
the constructed frame is deterministic (no lasso shares a state with another, and no lasso
revisits a state within one traversal in a way that would make a fibre have more than one
member). This section records why that is not merely convenient but load-bearing, and precisely
where the load is carried, because a natural-seeming later change — sharing lasso states across
histories, e.g. for a stability modal not otherwise addressed here — would put weight on exactly
this argument.

- **Limit is genuinely non-free**: it does not follow from the two action laws (`sh_zero`,
  `sh_add`) alone. `ShiftSet.SepNotDerivable.sep_not_derivable` (`Semantics/ShiftSet.lean:520`)
  proves this by counterexample: `D = ℚ` acting on `ℚ ⧸ DyadicGroup` by translation satisfies both
  action laws and refutes separation (a dense proper stabiliser). This is why `sep` is a
  structure field rather than a derived fact. Over `ℤ` it is **kernel-checked** — discharged from
  discreteness via `ShiftSet.ofIntAction` and `ShiftSet.sep_of_succOrder`
  (`Semantics/ShiftSet.lean`) — not a hand proof.
- **Saturation is free only from subsingleton fibres**
  (`TaskFrame.saturation_of_fib_subsingleton`, consumed at `Semantics/ShiftSet.lean:172`) —
  precisely Lemma 1's argument above.

**The real obstruction to state-sharing is not Limit or Saturation — it is Lemma 2 and the Box
case of Lemma 4.** Determinism is exactly what makes `ShiftSet.total_eq_orbit`
(`Semantics/ShiftSet.lean:252`) true — the fact that every world history is one of the lasso
orbits, which is Lemma 2's converse direction. If two lassos shared a state, a history could cross
from one lasso to another at the shared state, `total_eq_orbit` would fail, Corollary 2.2 (`H_F`
is exactly the certified histories) would fail with it, and the Box case of Lemma 4 would fail:
(C3) is calibrated against "every position of every lasso", which stops enumerating `H_F` once
histories can recombine. This is the same obstruction `Probe476.fmp_false` records for finite
digraphs: admitting recombined paths adds histories that Box must range over, beyond what the
certificate's four conditions were designed to certify.

**Consequence.** Adding state-sharing to the datatype for a future stability modal is not a
matter of re-proving Lemma 1 with a weaker Limit/Saturation argument; it requires re-proving
Lemma 2 and redesigning condition (C3). Any forward-compatibility note in the datatype should say
so explicitly, citing `total_eq_orbit` and the Box case of Lemma 4, not Limit and Saturation.

---

## 5. The re-check windows and the periodicity obligation

Lemma 4 quantifies over every `t ∈ ℤ`, while a re-checker inspects only finitely many stored
positions. The bridge from the universal statement to a finite check is a periodic-decoding
argument, and it is machine-checked, not assumed.

### 5.1 The two decoding periodicities

```lean
theorem lab_sub_back_length (Λ) {t : ℤ} (ht : t < 0) : Λ.lab (t - Λ.nb) = Λ.lab t
theorem lab_add_fwd_length  (Λ) {t : ℤ} (ht : Λ.nm ≤ t) : Λ.lab (t + Λ.nf) = Λ.lab t
```

(`Metalogic/Decidability/WitnessFamily/Basic.lean:117, 123`.) `nb := |back|`, `nm := |mid|`,
`nf := |fwd|`, all as integers.

### 5.2 The four collapse results and the window table

| Condition | Lean theorem | File:line | **Window (half-open)** |
|---|---|---|---|
| Local coherence | `coherent_iff_window` | `Metalogic/Decidability/WitnessFamily/Decide.lean:335` | `[−2·nb, nm + 2·nf)` |
| Fulfilment | `fulfil_iff_window` | `Metalogic/Decidability/WitnessFamily/Decide.lean:743` | `[−2·nb, nm + 2·nf)` |
| Box faithfulness (`∀t. χ ∈ Lᵢ t`) | `mem_all_iff_window` | `Metalogic/Decidability/WitnessFamily/Decide.lean:809` (lasso level), `:883` (family level) | `[−nb, nm + nf)` |
| Forward witness scan for (C2) | `scan_forward` | `Metalogic/Decidability/WitnessFamily/Decide.lean:192` | a witness exists in `(t, max(t, nm) + nf]` |
| Backward witness scan for (C2) | `scan_backward` | `Metalogic/Decidability/WitnessFamily/Decide.lean:212` | a witness exists in `[min(t, 0) − nb, t)` |

**Local coherence and fulfilment collapse to the same, wider window,
`[−2·nb, nm + 2·nf)` — two periods on each side, not one.** The reason, recorded in
`coherent_iff_window`'s own docstring: the clause at `t` reads `t−1` and `t+1` as well as `t`, so
a representative position must have its *whole neighbourhood* inside the periodic region, not
just itself. Box faithfulness reads no neighbours, so it collapses at exactly **one** period each
side, `[−nb, nm + nf)` — strictly narrower. Treating the two windows as the same, or using the
narrower one for local coherence or fulfilment, is unsound: it can accept a certificate whose
local-coherence or fulfilment violation lies outside `[−nb, nm+nf)` but inside
`[−2·nb, nm+2·nf)`.

The decidability instances `decidableLocalCoherentLab`, `decidableFulfillingLab`,
`decidableBoxFaithful`, `decidableTarget` (`Decide.lean:865, 878, 923, 927`) are built from
exactly these collapses, and the module opens no `Classical` — the four conditions are decided
computationally, not just classically true or false.

### 5.3 The periodicity obligation is a differential, not a proof

Lemma 4's universal statement over `ℤ` is machine-checked; what a *re-checker implementation*
must additionally satisfy — that it correctly implements the finite-window reduction it is
credited with — is not something a proof discharges for a specific piece of Python (or any other)
code. The honest discharge is a **differential obligation**: the Python re-checker's verdict must
agree with `lake exe check_certificate` (built directly on the four `Decidable` instances above)
over a corpus that includes, at minimum:

1. A family locally coherent but *not* fulfilling (infinite postponement of an eventuality).
2. A family failing (C1) or (C2) only at a position **outside** `[−nb, nm+nf)` but **inside**
   `[−2·nb, nm+2·nf)` — the fixture that distinguishes the wider proved window from the narrower
   one-period window.
3. A family failing (C3) only.

The fixture corpus at `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/`
and the differential test at
`code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`
implement this obligation.

---

## 6. Presentation and independent re-verification (obligation S3)

### 6.1 The wire contract

`BimodalTools/README.md`'s "Certificate re-verification protocol" and
`Metalogic/Decidability/WitnessFamily/Basic.lean`'s header both state that `back`, `mid`, `fwd`,
`bx`, `lassos` and `target` are an **export contract**: renaming any of them is a breaking change
on the producing side, not a local refactor.

Input:

```json
{"target": {"premises": [<formula>,...], "conclusions": [<formula>,...], "time": 0},
 "bx":     [[<formula>, true], [<formula>, false], ...],
 "lassos": [{"back": [<label>,...], "mid": [<label>,...], "fwd": [<label>,...]}, ...]}
```

- `target` is **required**: the three data of `WitnessFamily.Target`. `target.premises` and
  `target.conclusions` default to `[]`. **`target.time` is required, with no default** — it is
  (C4)'s existential witness, and every other existential in a certificate is explicitly
  witnessed (the box guess witnesses which boxes are false; the lassos witness the falsifying
  histories; the labels witness the types). A defaulted `t` would leave the outermost existential
  the only unwitnessed one, against the whole point of a certificate.
- `<label>` is a list of `<formula>`, read as a set. `<formula>` tags: `atom` (`name`), `bot`,
  `imp` (`left`, `right`), `box` (`child`), `untl`/`snce` (`event`, `guard`).
- `bx` is sparse: any formula not listed reads as `false`.
- `lassos[0]` is the main lasso, where the target is read.
- **Atom identity is base-only.** `Formula.toJson` drops `Atom.freshIndex`, so a certificate
  carrying a fresh/Skolem atom is rejected outright; an exporter must refuse to emit one.

**The consuming parser accepts canonical bytes only.** Compact separators (no interior
whitespace; trailing whitespace is skipped), the key order shown above (fixed by construction,
not by sorting), and `ensure_ascii=False` so a non-ASCII atom name survives unescaped. This
repository's single authoritative serializer is `semantic/certificate.py`'s
`canonical_wire_bytes`; every call site that feeds the binary uses it, never a bare
`json.dumps`.

Output, exactly one line, and **never a validity claim**:

- `{"status":"countermodel","time":0}` — optionally carrying `"acceptance"` (below) and `"echo"`.
- `{"status":"rejected","failed":[{"condition":…,"lasso":…,"position":…,"formula":…,"detail":…}]}`
  — also optionally carrying `"echo"`.
- `{"status":"error","message":…}` — never carries `"echo"`: a wire-level parse failure has
  nothing to echo.

`condition ∈ {structural, local_coherent, fulfilling, box_faithful, target, unlocalized}`. A
missing `target` or a missing `target.time` is `error`, never `rejected` — `error` covers input
that fails the *protocol*; `rejected` covers input that parses but fails a *condition*.

**`"acceptance"`** appears on `countermodel` verdicts only. `"entailment"` means Lean constructed
a `WitnessFamily.Refutes` term for this certificate by applying a compile-time kernel-checked
implication to four run-time decisions; an absent field reads as `"decided"` — the four
`Decidable` instances returned `true`, with no such term constructed. This is deliberately not
worded as "a kernel-checked proof for this particular certificate" — that phrase belongs to a
reserved third `Acceptance` value (per-certificate kernel checking by re-elaboration) that
nothing this checker produces today; see `docs/SETTINGS.md` and
`BimodalTools/CertificateImport.lean`'s `Acceptance` docstring. See §6.2.

**`"echo"`** is a canonical *reprint* of the certificate as parsed, not a verbatim copy — it
appears on `countermodel` and `rejected` verdicts, comparable bytewise against
`canonical_wire_bytes(payload)` because this repository already emits canonical key order.
`tests/_lean_check.py`'s `assert_echo_matches_sent` performs this comparison; a mismatch, or a
missing `"echo"` where one is expected, is a **protocol error** (§6.1's error-versus-rejected
distinction, applied on this side of the wire too), never a `rejected`-shaped outcome.

### 6.2 The four-step dual verification, on every reported countermodel

1. Extract `(𝒲, t₀)` from the Z3 model.
2. Decide (C1)–(C4) in a pure-Python re-checker over §5.2's windows, independent of the Z3 model
   object.
3. **Fail-fast** on any verdict but `countermodel`: a Z3-side bug becomes a loud rejection, never
   a false report.
4. Export the JSON and, where `lake` and the Lean development are present, re-decide with
   `lake exe check_certificate`; disagreement is a Python-side defect by definition, since the
   Lean predicates are the contract (§5.3).

This is why a machine-checkable re-verification of every reported countermodel, independent of
the solver, is a deliverable rather than a testing nicety: it is the only thing standing between
the Z3 encoder and (SOUND)'s antecedent. `countermodel` says the four `Decidable` instances all
returned `true` on the family rebuilt from the wire input — it is not a kernel-checked proof for
that particular certificate, the same honesty the tableau bridge's `"gates"` field records for
itself. `rejected` says only that the object handed over is not a certificate; it never says the
consequence holds.

Where the binary's verdict instead carries `"acceptance":"entailment"`, the honesty above is
strictly stronger for that certificate: `check_certificate`'s accepting branch applies
`WitnessFamily.joint_countermodel` to the decided hypothesis, *constructing* the
paper-countermodel existence term rather than printing a verdict — Lean constructed a
`WitnessFamily.Refutes` term for this certificate by applying a compile-time kernel-checked
implication to four run-time decisions, not merely four `Decidable` instances agreeing. This is
deliberately not "a kernel-checked proof for that particular certificate" — that phrase belongs
to a reserved third `Acceptance` value (per-certificate kernel checking by re-elaboration) that
nothing this checker produces today; see `docs/SETTINGS.md` and
`BimodalTools/CertificateImport.lean`'s `Acceptance` docstring. This upgrades the
differential test tier's confidence in each `countermodel` fixture and in the live-extracted
certificate `tests/unit/test_semantics_core.py` exercises (§7.3), but is silent on any run this
repository does not export to the Lean binary — the live path (`semantic/model.py`) still relies
on the Python re-checker alone, since it never calls `lake exe check_certificate`.

Both halves of the proof-producing checker have now landed and are consumed: the constructed
entailment above, and a bytewise comparison of the Lean side's `"echo"` against the bytes this
repository sent (§6.1, `assert_echo_matches_sent`). The residual decoding step this leaves — that
`checkCertified` rebuilt the family the sender meant — is no longer merely *trusted*; it is
*pinned* by `BimodalTools.CanonicalWire.print_parse_canonical`, which says that on canonical
bytes the echo is byte-identical to what was sent. Together, in the **differential test tier**
only, this makes the Python re-checker a fast **pre-filter** rather than part of what a
`countermodel` verdict there rests on: Lean's kernel checks the entailment for the certificate
actually sent, and the echo confirms it is the certificate this repository meant. The **live
path** (`semantic/model.py`) is unaffected — it never calls `lake exe check_certificate`, so the
Python re-checker remains fully in that path's trust base (`TRUST_PIPELINE.md`, "The trust
base").

### 6.3 Obligation S4: the translation bridge, uncovered by the round-trip alone

A round-trip comparing the Python re-checker against `lake exe check_certificate` on the same
already-translated `Formula` still tests the re-checker, not whether the theory's own
`Sentence → Formula` translation preserves truth — both sides of that comparison consume the
same translated object, structurally. The translation is non-trivial: it must eliminate the
defined operators (negation, conjunction, disjunction, the derived tense operators, `\next`,
`\prev`) into the six primitives, and it must correctly carry the guard/event distinction
`Until`/`Since` depend on. That second hazard used to be a **swap** — `UntilOperator.true_at` was
event-first while Lean's `untl` is guard-first — but ModelChecker has since been normalized to
guard-first throughout (`operators.py`, `semantic/formula.py`; see `docs/ARCHITECTURE.md`), so
`translate` is positional identity, not a swap, and there is no longer a swap for either half of
S4 to catch. The residual hazard is general truth preservation across the guard/event
distinction — a wrong translation could still misassign which operand is which even with no
swap-shaped bug left to name — which is why the asymmetric `Until`/`Since` coverage below is
retained for that reason rather than dropped. The wire format's named `event`/`guard` fields make
the wire itself order-free either way; the hazard is purely internal to the translation code, not
visible on the wire.

**Both halves are now discharged directly**, by a differential property test in
`tests/unit/test_formula.py`:

- The **tense half** (`TestTranslateTruthPreservation`): small generated and hand-built sentences
  over the propositional-plus-tense fragment, checked at every point of a small hand-built
  domain against an independent reference evaluator that never calls `translate`.
- The **box half** (`TestTranslateTruthPreservationBox`): the same differential, extended with a
  family-global `\Box` clause (both evaluators; see `NecessityOperator`'s own docstring and (C3)
  box faithfulness) and crossed against three hand-built multi-lasso label families
  (`TestPropertyFamiliesAreCoherent` asserts each is locally coherent and box-faithful as a
  precondition, using the same `coherent_at`/`box_faithful` this module's `03_box_unfaithful.json`
  fixture is checked against). `oracle/bimodal_logic/ground_truth.py`'s brute-force adjudicator
  covers only the five primitive tense tags with no box case, so it cannot discharge the box half
  on its own and is no longer load-bearing for it — the box half is covered directly instead.
- `TestDefinedOperatorCoverage`/`TestAsymmetryIsGenuine`/`TestNegativeControlsHaveTeeth` record
  that the generated corpus actually covers every defined operator, that the asymmetric
  `Until`/`Since` instances are genuinely order-sensitive (not merely operator coverage), and that
  a deliberately wrong translation (a dropped `Box` wrapper, an operand-swapped `Until`/`Since`, a
  single-lasso-only `Box`, or the retired event-first `\next` elimination) is detected rather than
  passing vacuously.

**Route decision.** Relocating the elimination into verified Lean code, so the obligation would be
deleted rather than tested, was considered and rejected as infeasible: `translate` runs at Python
*evaluation* time inside every primitive operator's own `true_at` (not only at export), and Lean
has no callable verified elimination pass to relocate into — its `neg`/`and`/`always` etc. are
already six-primitive `def`-level abbreviations. A Lean-side translation with its own
truth-preservation theorem is a real, separate improvement: it has now landed upstream
(`BimodalLogic`'s `SentenceTruth.lean` proves `sat_iff`), but it certifies BimodalLogic's own
reference translation, not this repository's, and this repository has not yet diffed its own
translation against the upstream fixture (see `docs/TRUST_PIPELINE.md`'s "What remains").

---

## 7. The (ADEQ) direction

**(ADEQ).** *Let `f` be a computable function of `|C|`. If some `σ ∈ Δ` is not a ℤ-time
consequence of `Γ` — i.e. `¬ SemanticConsequenceIn FrameClass.ZTime Γ σ` — then the search, run at
segment-length settings at which the compressed witness family is **representable** — `back` and
`fwd` common multiples of that family's back/fwd periods (each bounded by `f(|C|)`), and `mid` at
least the family's mid length — returns SAT and emits a certificate satisfying (C1)–(C4). This is
deliberately not stated as `back, mid, fwd ≥ f(|C|)`: `WitnessRegistry.wrap()` folds `back`/`fwd`
positions by exact period, so a family of back-period (or fwd-period) `p` is representable at
configured length `n` iff `p` divides `n` — magnitude alone does not suffice, and a bare `≥ f(|C|)`
condition can be false even when the underlying family exists (§7.1 states the two routes to a
genuine sufficient condition).*

**Precondition: `max_witnesses`.** (ADEQ) additionally presupposes that `max_witnesses` is `None`
(the default) or at least the number of boxed subformulas in the closure. A cap below that count
*forces* witness-lasso sharing — round-robin reassignment of further boxed subformulas to
already-allocated lasso indices once the cap is reached — which trades completeness for a bounded
search, exactly as `semantic/witness_registry.py`'s own module docstring and `SETTINGS.md`'s
Witness Budget section already record. This never affects soundness: a witness constraint
generated against a shared lasso is exactly as valid as one against a dedicated one.

**This direction must not be asserted.** It is bounded-search-relative, it is stated at frame
class ℤ-time only, and it decomposes into three components plus one permanent limit:

| | Component | Status |
|---|---|---|
| **A0** | Frame-class gap: ℤ-time completeness does not imply completeness for `def:logical-consequence` at every temporal order | **Permanent limit.** §7.2. |
| **A1** | Compression: a ℤ-time countermodel yields a certificate with lengths bounded by `f(\|C\|)` | **Open.** Route named, not built. §7.1. |
| **A2** | Encoding completeness: a certificate within the configured lengths implies the Z3 encoding is SAT (precondition: `max_witnesses` is `None` or at least the boxed-subformula count) | **Provable and testable now.** §7.3. |
| **A3** | Bound realization: configured `back`/`fwd` are common multiples of the compressed family's periods (each bounded by `f(\|C\|)`), and `mid` is at least its mid length — a representability, not a magnitude, condition (precondition: `max_witnesses` is `None` or at least the boxed-subformula count) | Vacuous until A1 supplies `f`. |

### 7.1 A1 — compression, open, with the route named

A1 is stated as item 1 of the compression task recorded in the BimodalLogic repository's own
task tracker:
*"if `¬ ValidZTime ψ` (equivalently `¬ SemanticConsequenceIn FrameClass.ZTime Γ σ`) then some
`WitnessFamily` satisfying the four conditions exists with every segment length bounded by a
computable function of the closure size, whose main lasso carries the refuting point."* Status:
`[NOT STARTED]`, effort 2–4 weeks, with the soundness half of its dependencies already complete.
The route recorded there: take a refuting model, history and time; for each boxed subformula
guessed false, pick a witnessing history; compress each history's *type* sequence into a bi-lasso
using the good-cycle lemmas of `Metalogic/Decidability/BiLasso/GoodCycle.lean` and
`BiLasso/Extraction.lean`'s `exists_annot_of_truth` as the template, re-run over subformula-set
space rather than presentation states; `Semantics/Frames/TranslationProduct.lean`'s `validIn_iff_recurrenceFree`
lets witness paths be taken recurrence-free, so only the type sequence need be eventually
periodic. **Reduction to cited results**: Gabbay–Kurucz–Wolter–Zakharyaschev, *Many-Dimensional
Modal Logics: Theory and Applications* (2003), Theorems 3.29, 5.30, 5.32, 11.7, 11.21.

**A1 is recorded as open. It is not asserted, and (SOUND) does not depend on it.** Its only
consequence is whether "no certificate within bounds" carries information beyond "no certificate
was found within these bounds" — and it must not, until A1 lands.

**The one candidate for reducing A1 to an already-landed Lean theorem, examined and rejected.**
`Metalogic/Decidability/BiLasso/Extraction.lean:354`:

```lean
theorem exists_annot_of_truth (hbx : BoxOracleSound P bx)
    (τ : WorldHistory P.toTaskFrame) (t : ℤ) (hφ : TruthAt P.toModel τ t φ) :
    ∃ A ∈ boundedAnnots P φ bx (bound P φ),
      ∃ i ∈ Finset.Ico (cohWindowLo A) (cohWindowHi A),
        A.lasso.unroll i = τ.state t ∧ φ ∈ A.label i
```

is proved and sorry-free, with enumeration completeness (`Enumerate.lean:153, 309`) and a truth
lemma (`TruthLemma.lean:149`) beside it, and it looks superficially like a bounded-completeness
result for exactly this setting. It does **not** discharge the reduction, for three verified
reasons:

1. **It is relative to a fixed finite presentation `P`.** Its hypothesis is
   `TruthAt P.toModel τ t φ` — truth in the model of a given `IntPresentation` — not truth in an
   arbitrary ℤ-time model, which is A1's hypothesis.
2. **Its bound is not a function of `|C|`.** `bound P φ := max (cycleBound P φ) (midBound P φ)`
   with `midBound P φ = 2 * (P.card * 2 ^ subformulaClosureCard φ)` (`Extraction.lean:284, 299`)
   depends on `P.card`, the size of the presented state space. A1 requires a bound computable
   from `|C|` alone.
3. **The missing premise is exactly what `Probe476.fmp_false` refutes**: to get from (2) to a
   `|C|`-only bound would need "every ℤ-time countermodel is realized in a finite
   `IntPresentation` whose `card` is bounded in `|C|`" — the finite-presentation small-model
   hypothesis, machine-refuted. `BoxOracleSound`'s own docstring
   (`Metalogic/Decidability/BiLasso/Annotation.lean:350-355`) says as much: constructing an oracle
   meeting that specification "requires the small-model theorem and is deliberately deferred".

So `exists_annot_of_truth` is the **template** for A1's compression argument, not a reduction of
it. What would have to be true for a genuine reduction: (i) an analogue whose hypothesis is
`¬ SemanticConsequenceIn FrameClass.ZTime Γ σ` rather than truth in a presented model;
(ii) a bound depending only on `|closureOf (Γ ++ Δ)|`, obtained by compressing over
**subformula-set space** (pigeonhole `2^|C|`, closed) rather than presentation states
(pigeonhole `P.card`, unbounded); and (iii) a demonstration that this repository's search
*represents* the compressed family at the configured `back`/`fwd`/`mid` — not merely that
`back, mid, fwd` are "at least" the bound, since `WitnessRegistry.wrap()` folds `back`/`fwd`
positions by exact period: a family with back-period (or fwd-period) `p` is representable at
configured length `n` iff `p` divides `n`, measured against the live search — one formula is SAT at
`(back, mid, fwd) = (3, 1, 3)` and `(6, 1, 6)` but genuinely UNSAT (`timeout=False`, sub-second) at
`(4, 1, 4)` and `(5, 1, 5)`, exactly as `6 ∤ 4`, `6 ∤ 5` predicts. Two routes to a genuine
sufficient condition are available, neither implemented: take `back`/`fwd` as a common multiple of
every candidate period up to `f(|C|)` — correct, but `lcm(1, ..., f)` grows as `e^{O(f)}`, so this
is impractical for any but the smallest `f` — or sweep `back' in [1, back]` and `fwd' in [1, fwd]`
independently with `mid` fixed (`mid` has no periodicity and never participates in this gap; see
`docs/SEARCH_COVERAGE.md` §3(b)) and re-run the search at each pair, `O(back * fwd)` solver
calls — quadratic in the two segment lengths that matter, not cubic in all three settings —
individually cheap but not yet built.
Both prerequisites §6 supplies — the certificate export and the independent re-checker — are now
in place, so condition (iii) is satisfiable **in principle** today. What remains is the following
concrete work in this repository, in dependency order:

- **(iii-a) Fix the length space** — either sweep `back' in [1, back]` and `fwd' in [1, fwd]`
  independently with `mid` fixed (`O(back * fwd)` individually cheap solves — quadratic, not
  cubic, since `mid` has no periodicity and never participates; `docs/SEARCH_COVERAGE.md` §3(b)
  — and the only form under which "the same family space" is literally true) or restate A3 in
  divisor terms. This is the **only blocking** prerequisite:
  without it, (iii) is unprovable rather than merely unproved. `docs/SEARCH_COVERAGE.md` compares
  this bullet's two options against a third (an encoding reformulation) and recommends the
  bounded sweep, staging the work this bullet still names as unbuilt.
- **(iii-b) State and check the represented space** — a written specification of exactly what the
  encoder's satisfying assignments represent: families over closure `C` with
  `1 + |{Box members}|` lassos when `max_witnesses` is uncapped, labels `⊆ C`, segment lengths
  exactly `(nb, nm, nf)`, atoms base-only; checked by a `family → assignment` inverse of
  `extract_certificate` plus a per-candidate agreement test.
- **(iii-c) Closure agreement** — `semantic/formula.py`'s `subformula_closure` is a hand-written
  mirror of the Lean subformula closure, and both sides' clauses are guarded by it; the Lean leg
  recomputes its own closure from the wire's target, so it covers this agreement **for accepted
  certificates only**. A direct set-level differential over generated formulas does not exist and
  is cheap.
- **(iii-d) Witness-lasso budget** — the `max_witnesses` precondition (§7.3 states it beside the
  A2 statement), cross-referenced rather than restated.
- **(iii-e) Segment-length parity with the bound's shape** — once A1 lands, check that the bound's
  components map onto `back`/`mid`/`fwd` as the search means them; the upstream bound is a single
  `n` over all three segments while the search takes three independent settings.

(iii-b) through (iii-d) are independently valuable now and do not wait on A1.

### 7.2 A0 — the frame-class gap, a permanent limit A1 cannot close

The paper's `def:logical-consequence` (`:1124`, `:3236`) quantifies over **every** model, hence
every temporal order. (SOUND) delivers refutation at that generality — the certified frame is one
particular task frame, and one countermodel suffices. **(ADEQ) does not run the other way.**
`FrameClass.ZTime.Sat F = F.IsRegular ∧ F.IsZTime` is strictly stronger than
`FrameClass.Base.Sat F = F.IsRegular`. Two axioms are classified minimum-frame-class `.ZTime`:

- `Axiom.prior_UZ φ : Fφ → (¬φ U φ)` (`ProofSystem/Axioms.lean:341, 612`) — "every definable
  future set has a least element"; Reynolds 1992 §10, Venema 1993 axiom (W). Its
  non-Base-validity is machine-checked: `not_validIn_base_prior_UZ`
  (`Metalogic/Independence/ZTimeSharpness.lean`).
- `Axiom.z1 φ : G(Gφ → φ) → (FGφ → Gφ)` (`ProofSystem/Axioms.lean:353, 613`) — the
  `IsSuccArchimedean` characteristic axiom; Doets 1987 Claim 10, Reynolds 1994 §10. Its
  non-Base-validity is machine-checked: `not_validIn_base_z1`
  (`Metalogic/Independence/ZTimeSharpness.lean`).

By (SOUND), **no certificate can ever exist for these**: any certificate would exhibit a ℤ-time
countermodel, contradicting their ℤ-time validity. Yet they are not Base-valid, and that half is
now **proved rather than cited**: `not_validIn_base_prior_UZ` and `not_validIn_base_z1`
(`Metalogic/Independence/ZTimeSharpness.lean`) refute both at `FrameClass.Base`, and
`prior_UZ_minFrameClass_sharp` / `z1_minFrameClass_sharp` (same file) strengthen this to every
`fc < FrameClass.ZTime` — so the `.ZTime` tag of `Axiom.minFrameClass` is minimal for both, not
merely asserted. So the search is, by design and **permanently**, silent on a nonempty class of paper-invalid inferences, independently of A1,
A2 and A3. Even a fully proved A1 upgrades "no certificate within bounds" to "ℤ-time valid",
never to "valid".

**Deciding test for A0**, standing in this repository's suite: run the search on
`\Future A \rightarrow (\neg A \Until A)` and on the `z1` instance. Both must report no
certificate at every configured length, and both must be rendered **inconclusive**, never as
validity. A rendering that says "valid" on either is a reportable defect.

### 7.3 A2 — encoding completeness, and the deciding test that discharges it now

**A companion document.** `A2_GAP.md` gives the deep treatment of why the deciding test below
*decides* A2 rather than *proving* it: the full category argument for why a proof about
(C1)–(C4) cannot discharge a claim about what the Z3 encoder, as running Python, actually emits;
the complete emitted-constraint surface the deciding test exercises, emitter by emitter; and a
per-route analysis of what would actually close the gap. It extends this section; it does not
replace it.

A2 holds iff the Z3 constraint set is exactly the conjunction of (C1)–(C4) over windows at least
as wide as §5.2's, with no extra constraint. It is testable today, without A1. **Precondition**:
this holds only when `max_witnesses` is `None` (the default) or at least the number of boxed
subformulas in the closure — see §7's precondition note above and `SETTINGS.md`'s Witness Budget
section; a capped search is under-complete by this precondition, never unsound. The A2-triangle
test below runs uncapped (`max_witnesses` unset), so the standing evidence below is evidence for
the **uncapped** case only:

> **Test (A2-triangle).** Fix a closure `C` with `|C| ≤ 4`, at two grid sizes — `back = mid =
> fwd = 1` (the historical minimum) and `back = 2, mid = 1, fwd = 2` (production's
> `DEFAULT_EXAMPLE_SETTINGS`). Exhaustively enumerate every candidate `(bx, Λ₀, …, Λ_k)` over
> subsets of `C` at those lengths. For each candidate, compare three verdicts: (i) the Python
> re-checker, (ii) `lake exe check_certificate`, (iii) a solver-free evaluation of the Z3
> encoding's own emitted constraint list under that candidate's pinned assignment (a per-candidate
> proxy for "would Z3 accept this candidate", compiled once per structure and evaluated without a
> solver call).
> - (i) ≠ (ii) localizes a re-checker defect (§5.3's differential obligation, failing).
> - (iii) false where (i) = (ii) = `countermodel` localizes an **encoding incompleteness**: a
>   constraint the encoder imposes that (C1)–(C4) do not require.
> - (iii) true where (i) = (ii) = `rejected` localizes an **encoding unsoundness** — caught at run
>   time by §6.2's fail-fast step, but this test finds it in the suite instead.
>
> Beside the per-candidate comparison, a retained **aggregate** assertion additionally compares
> "some candidate accepted" against the real Z3 *search*'s own SAT/UNSAT verdict — the only check
> in this test of the actual solver output, as distinct from evaluating the pinned constraint
> list.

**Deciding test for A2, standing in this repository's suite**:
`tests/integration/test_certificate_a2_triangle.py`. The grid now covers two sizes: `back = mid
= fwd = 1` (the historical minimum) and `back = 2, mid = 1, fwd = 2` (production's
`DEFAULT_EXAMPLE_SETTINGS`) — the `nb = 2` regime the narrow-window local-coherence defect (§5.2,
`witness_constraints.py`'s module docstring) actually required to manifest, and which
`back = mid = fwd = 1` alone cannot see. Two tiers at this grid: an exhaustive Tier 1 comparing
legs (i) and (iii) over every candidate, per-candidate (`_run_exhaustive_triangle`, raising on the
first divergence — see `A2_GAP.md` §8 limit 3 for why this discharges what used to be only an
aggregate comparison), over three closures (two box-free, one with a `Box`, so the witness-lasso
and `bx` dimensions are both exercised); and a bounded, deterministic Tier 2 sampling leg (ii)
against `lake exe check_certificate` on a small per-closure sample plus each SAT closure's live
Z3-extracted certificate (skipping cleanly without a BimodalLogic checkout). All three closures
agree across all three legs as of this writing — see the task's implementation summary for the
observed verdicts and counts. `test_certificate_lean_agreement.py` remains the fixture corpus's
own leg (i)/(ii) coverage; see that module's docstring. The widened grid applies to both box-free
closures and to one size-2 boxed closure; the pre-existing size-3 boxed closure remains
`back = mid = fwd = 1`-only: its exhaustive enumeration at `nb = nf = 2` is roughly 10.7 billion
candidates (~19h extrapolated), infeasible under the suite's per-test time budget — a standing
coverage gap, not a defect.

**Direction claim.** This whole standing test is liveness and regression evidence for **A2 — the
UNSAT direction — never for countermodel trust**: a reported countermodel is independently
checked per run by Stages 4-5 (`TRUST_PIPELINE.md`), which this test does not participate in at
all. What this test backs is the opposite, unwitnessed direction — that the encoding imposes
exactly (C1)–(C4) and nothing more, at the grid sizes actually exercised — which is exactly why
it is exhaustive-enumeration evidence rather than a per-run check. See `TRUST_PIPELINE.md`'s "The
standing test for A2" for the same claim, including the cost reassessment it licenses.

**The one-hot selector is conservative.** Decision D5 makes the target position a one-hot
selector `sel[t]` rather than a fixed origin — structure the A2-triangle test above does not
itself probe, since (C1)–(C4) as stated say nothing about `sel`. The selector is conservative
because it is a *lossless Skolemization* of (C4) `Target`'s existential target time: (C4) asks
only that *some* position satisfy the premise/conclusion condition, and `sel`'s domain,
`WitnessRegistry.target_window()`, supplies exactly one representative position per position
slot (`[-nb, nm+nf)`, now shared by construction with box faithfulness's proved
`mem_all_iff_window` window — see §5.2). Because `LabelledLasso.label` is exactly periodic,
every position outside the window shares its slot's label with the in-window representative, so
restricting `sel`'s domain to the window can discard only *duplicate* representations of an
in-window target time — never a target time the window omits, and never a satisfying position
the wide space of all integers would have found but the window does not. Consequently, "the Z3
constraint set is exactly the conjunction of (C1)–(C4)" is not weakened by the selector's
presence: `target_constraints` is satisfiable with some `sel[t]` true exactly when a certificate
satisfying (C1)–(C4) exists with target time `t`. `TestSelectorConservativity`
(`tests/unit/test_witness_constraints.py`) pins this directly — with only `target_constraints`
asserted (no (C1)–(C3)), a hand-built family's satisfying `sel[t]` positions agree, one for one,
with `certificate._target_holds` — and a companion, solver-free test pins the periodicity
corollary the argument above depends on.

### 7.4 The never-report-validity rule

The search must never report that a formula or inference is **valid**, on two independent
grounds: (i) the search is one-sided by construction — it looks for countermodels, and absence of
a found countermodel is not a proof of absence, which is exactly what A1/A3 being open means; and
(ii) even were A1/A2/A3 all discharged, A0 caps the strongest honest claim at "ℤ-time valid",
which the paper's semantics does not identify with "valid". Both grounds hold independently of
each other and of any future progress on A1.

**An unchecked countermodel is not a validity claim either** (item 1,
the certificate verification output gate). The rule above is about the *absence* of a
countermodel; this paragraph is about a *reported* one whose independent leg
(`semantic/checker.py`) did not run. Once the output gate introduces a third state — reported
but Python-re-checked only, versus reported and independently checked — a reader could mistake
"unchecked" for hedging about the *inference* itself, as though an unchecked countermodel were
somehow less of a refutation. It is not: the mandatory `recheck` guard (§6.2) already decided
(C1)-(C4) hold before either label is ever chosen, so a reported countermodel is a countermodel
either way. "Unchecked" hedges about *how strongly the report itself is corroborated* — whether
a second, independent implementation of the same four decision procedures agrees — never about
whether the certified model actually refutes the target. See `docs/SETTINGS.md`'s "Certificate
Verification" section for the three output states and their exact wording.

---

## Why ℤ-time only

Three independent reasons, none by fiat:

1. **Finite carriers force static frames over dense Archimedean orders.** With finite `W` the
   cones `(w)_x` form a decreasing family of subsets of a finite set, so they stabilize; *Limit*
   then forces every small-duration fibre to `{w}` and *Compositionality* propagates identity to
   every duration, so every possible world is constant and no valid formula is refutable. This is
   about finite `W` and does not directly apply to the certificate design, whose `W` is infinite
   — but it is why a *finite-frame* search cannot be lifted to dense time.
2. **The truth lemma's `U` case is a finite descent** (Lemma 4's remark, §3): the `(⇒)` direction
   inducts on `s − t ∈ ℕ`. Over a dense order this induction does not exist, and the fixpoint law
   (C1) no longer determines the eventuality's label from its witness. This reason is internal to
   this proof and is the sharpest of the three.
3. **The window collapse is a `ℤ`-periodicity argument** (§5): `lab_sub_back_length` /
   `lab_add_fwd_length` are statements about `Periodic.unrollOf` over `ℤ`. Dense-time certificates
   would need a different finite presentation (mosaic- or region-style), not a re-tuned window.

Dense and continuous time are therefore out of scope for cause, not by omission.
