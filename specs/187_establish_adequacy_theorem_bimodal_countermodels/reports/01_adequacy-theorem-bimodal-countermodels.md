# Research Report: Adequacy theorem for bimodal countermodels

- **Task**: 187 - Establish an adequacy theorem connecting ModelChecker's bimodal countermodels to the paper's task semantics
- **Started**: 2026-09-24T20:05:00Z
- **Completed**: 2026-09-24T21:40:00Z
- **Effort**: about 1.5 hours (paper appendix, Lean `WitnessFamily/` + `ShiftSet.lean` + `Soundness.lean`, two codebase surveys, proof restatement)
- **Dependencies**: None blocking. Reads task 184's reports 01/02/03 and its plan as authoritative prior art.
- **Sources/Inputs**:
  - `~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` — `:961` (temporal order), `:968-974`
    (reflection convention, Fiber/Cone/Segment), `:989-994` (task frame, the four constraints),
    `:1029` (world history + unboundedness footnote), `:1053-1055` (Time-Shift, Possible World),
    `:1068-1076` (semantic clauses), `:1124` (Logical Consequence), `:1136-1141` (SP1 proof),
    `:3190-3223` (`def:time-shift-histories`, `app:auto_existence`,
    `lem:history-time-shift-preservation`), `:3057-3081` (`thm:extension`, `cor:occurrence`)
  - `~/Projects/BimodalLogic/FormalSystem/` — `Semantics/ShiftSet.lean`, `Semantics/TaskFrame.lean`,
    `Semantics/TemporalOrder.lean`, `Semantics/Truth.lean`, `Semantics/Validity.lean`,
    `Semantics/FrameClassValidity.lean`, `Metalogic/Soundness.lean`,
    `Metalogic/Decidability/WitnessFamily/{Basic,Predicates,Std,Agreement,Decide,Examples,README}`,
    `ProofSystem/Axioms.lean`; `~/Projects/BimodalLogic/BimodalTools/README.md`;
    `~/Projects/BimodalLogic/specs/TODO.md` (task 623)
  - `code/src/model_checker/theory_lib/bimodal/` (`semantic/core.py`, `operators.py`,
    `semantic/model.py`, `semantic/proposition.py`, `iterate.py`, `examples.py`,
    `tests/unit/test_bimodal.py`); `oracle/bimodal_logic/`
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/reports/01,02,03` and
    `plans/01_witness-family-certificate-redesign.md`
- **Artifacts**: this report
- **Standards**: report-format.md, subagent-return.md
- **Task Type**: formal:logic (logic domain)

## Executive Summary

1. **(SOUND) is already machine-checked for the target design, and the finding is stronger than
   the dispatch assumed.** The dispatch records the proof as "drafted". It is in fact landed,
   sorry-free, in `~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/`:
   `WitnessFamily.joint_countermodel` (`Agreement.lean:232`) delivers exactly (SOUND)'s
   consequent — an explicit frame, model, world history and time — from the four certificate
   conditions. What remains is not a proof obligation but a **transcription audit** plus two
   ModelChecker-side obligations. Section 3 restates the four lemmas and the theorem in full, as
   the dispatch requires, and section 3.6 maps each line of the restated proof to its Lean name.

2. **Gap 1 (periodicity of the re-checker) is closed, and closing it exposes a concrete defect in
   task 184's plan.** The window collapses are machine-checked: `coherent_iff_window` and
   `fulfil_iff_window` (`Decide.lean:335,743`) reduce the ℤ-quantified conditions to
   `[-2·|back|, |mid| + 2·|fwd|)` — **two** periods each side, because the clause at `t` reads
   `t-1` and `t+1`. Task 184's decision **D7 states one period each side**, i.e.
   `[-|back|, |mid|+|fwd|)`. D7's own text names a wrong fulfilment bound as "the single most
   likely silent soundness bug in the whole redesign". That bug is presently in the plan. D7 must
   be amended before Phase 4 or Phase 8 is dispatched (section 4.1).

3. **Gap 2 (determinism) is closed and re-scoped: the obstruction to lasso state-sharing is the
   Box case, not Limit and Saturation.** Determinism is genuinely load-bearing for Limit (`sep`,
   proved *not* derivable from the action laws by `sep_not_derivable`, `ShiftSet.lean:520`) and
   for Saturation (`shRel_saturation`, `ShiftSet.lean:171`). But it is also what makes
   `total_eq_orbit` (`ShiftSet.lean:252`) true, and that lemma is what makes Box range over
   *exactly* the certified histories — which is what condition (C3) BoxFaithful is calibrated
   against. Adding sharing therefore requires re-proving Lemma 2 and the Box case of Lemma 4, not
   only Lemma 1 (section 4.2).

4. **(ADEQ) is recorded as OPEN, reduced to three named components, with the deciding test named
   — and it carries a prior, permanent limit the dispatch did not scope.** Even with full
   compression, a ℤ-time certificate search is complete only for ℤ-time countermodels, while the
   paper's `def:logical-consequence` quantifies over *every* nontrivial totally ordered abelian
   group. `Axiom.prior_UZ` (`Fφ → (¬φ U φ)`) and `Axiom.z1` (`G(Gφ→φ) → (FGφ→Gφ)`) are classified
   minimum-frame-class `.ZTime` in `ProofSystem/Axioms.lean:612-613`; by (SOUND) no certificate
   can ever refute them, though the paper's semantics has countermodels for them over e.g. ℚ. So
   "no certificate at any length" can at best become "ℤ-time valid", never "valid". Section 8.
   The one landed Lean theorem that looks like a reduction of (ADEQ) to a cited result —
   `exists_annot_of_truth` — is examined and **rejected** in §8.1a: it is relative to a fixed
   finite presentation and its bound depends on that presentation's cardinality, so it is the
   template for the open compression result, not a reduction of it.

5. **Relationship to task 184: option (a) — this task is the adequacy layer, and it subsumes no
   phase of 184.** 184's plan is entirely implementation and contains no statement of (SOUND); it
   cites the Lean theorems only as background. This task contributes the theorem, the corrected
   windows as a hard constraint on Phases 4/8/12, the (ADEQ) analysis, two tests 184 does not
   carry, and one uncovered soundness bridge — the Sentence→Formula translation, which 184's
   Phase 5 round-trip **cannot** test because both sides consume the same translated formula
   (sections 6.4, 9).

6. **The current encoding's obstruction is confirmed structural and is broader than the dispatch
   states.** `is_valid_time` (`core.py:997`) is not the only boundedness site: the two *active*
   abundance constraints bypass it entirely, inlining `z3.IntVal(-self.M + 1)` /
   `z3.IntVal(self.M - 1)` (`core.py:1639,1641,1740,1741`), and eleven further sites do `self.M`
   arithmetic directly. Deleting `is_valid_time` alone would not unbind the domain (section 1.2).

## Context & Scope

The dispatch asks for a proved correspondence, in two directions of unequal status, between what
the ModelChecker bimodal search reports and the paper's task semantics of `sec:Construction`;
and for the implementation changes that make the theorem's hypotheses true and its antecedent
mechanically checkable.

Scope is ℤ-time only, matching task 184's redesign. Dense and continuous time are out of scope
and the reason is recorded rather than assumed (section 8.4). The stability modal is out of
scope. The paper and the Lean development are read-only inputs; nothing is proved inside the Lean
development here, and where (SOUND) or (ADEQ) rests on a Lean result it is cited with its status.

## Findings

### 1. The current encoding: why (SOUND) is false for it, at file and line granularity

#### 1.1 The clauses are faithful; the structures are not

Verified directly. `NecessityOperator.true_at` (`operators.py:507-566`) builds
`∀ w. is_world(w) → true_at(arg, ⟨w, t⟩)` with no domain guard on the evaluation time, and its
docstring cites the paper's `(□)` clause. `UntilOperator.true_at` (`operators.py:1054-1102`)
builds `∃ s > t. event(s) ∧ ∀ r ∈ (t,s). guard(r)`. Both are correct transcriptions of
`:1068-1076`. The divergence is entirely in what the quantifiers range over.

#### 1.2 Boundedness is not confined to `is_valid_time`

`is_valid_time` (`core.py:997-1024`) is a one-line body:

```python
return z3.And(given_time > -self.M + offset, given_time < self.M + offset)
```

`M` is a plain settings key (`DEFAULT_EXAMPLE_SETTINGS` at `core.py:47-65`, `'M': 2`), never
derived inside the package; `self.M` is assigned only as a copy in `semantic/model.py:52` and
`semantic/proposition.py:52`. Callers set it: `oracle/bimodal_logic/provider.py:241` computes
`M = max(depth + 2, 3)`; `examples.py` hard-codes it per example.

The domain `(-M, M) ∩ ℤ` is neither closed under addition nor unbounded, so it is not a temporal
order at all, whereas the paper notes at `:1029` that every nontrivial ordered group is infinite
and unbounded. That mismatch alone falsifies (SOUND) for the current encoding.

**Verified correction to the dispatch's scoping.** `is_valid_time`'s live call sites are
`core.py:573` (`ForAllTime`), `:610` (`ExistsTime`), `:741`, `:797` (offset −1), `:869`
(`build_frame_constraints`), `:954`/`:956` (inside the *disabled* `task_restriction`), and
`:1385`/`:1389`, `:1497`/`:1501` (two unused abundance alternatives). The **active** abundance
constraints do not route through it — `capped_skolem_abundance_constraint` inlines
`z3.IntVal(-self.M + 1)` and `z3.IntVal(self.M - 1)` at `core.py:1639,1641`, and
`depth_bounded_skolem_abundance_constraint` does the same at `:1740,1741`. Further independent
`self.M` sites: `:208` (`max_world_id = self.M * (2 ** (self.M * self.N))`), `:257`
(`is_valid_duration`), `:1051`, `:1117`, `:1122`/`:1164`, `:1537-1558`, `:1639-1641`,
`:1740-1741`, `:2137-2138`; `semantic/model.py:53` (`all_times = range(-M+1, M)`); every
`find_truth_condition` in `operators.py` (`all_D_times = range(-semantics.M+1, semantics.M)`);
`iterate.py:424`. **Unbinding the domain is a whole-module replacement, not a guard swap.**

#### 1.3 The frame conditions are asserted, mis-ledgered, or absent

`build_frame_constraints` (`core.py:646-995`) returns thirteen constraints. Items 7–11 assert
`nullity_identity`, `converse`, `forward_comp`, `seriality`, `interpolation`. Its own docstring
(`core.py:681-687`) claims *Limit* and "Spherical" are "discharged at the sort level" —
`BitVecSort(N)` finite, `nullity_identity` unconditional over `IntSort`. **Both halves of that
claim are wrong as stated**: the evaluation domain is not `IntSort` but the finite window, and
the paper's fourth constraint is *Saturation*, which the ledger does not mention at all. So of
the paper's four frame constraints, two are asserted (Compositionality via forward_comp +
interpolation; Seriality), one is claimed discharged by an argument that does not apply (Limit),
and one is simply absent (Saturation).

`task_restriction` (defined `core.py:935-964`) is commented out of the returned list at
`core.py:993`; the 45-line comment at `core.py:891-934` records that it was disabled for MBQI
cost and concedes that SAT results therefore live in a frame class *strictly larger* than the
grounded one. That is an explicit admission that the implementation's SAT verdicts are not about
paper task frames.

Translation-closure of the history set — which the paper **proves** (`app:auto_existence`,
`:3197-3206`) — is instead **asserted** by `capped_skolem_abundance_constraint`
(`core.py:1582-1664`), with coverage bounded entirely by `M`, and with the `M ≥ 3` requirement
recorded in `build_frame_constraints`' docstring at `core.py:728-729`.

World states are `z3.BitVecSort(self.N)` (`core.py:153`), so `W` is finite. `is_world` is an
uninterpreted `z3.Function` over `IntSort` (`core.py:201-205`), bounded by
`max_world_id = M · 2^(M·N)` (`core.py:208`), and it is simultaneously (i) the Box quantifier
domain, (ii) the abundance target, and (iii) the only handle the extractor has for enumerating
worlds (`_extract_valid_world_ids`, `core.py:2062-2077`).

#### 1.4 The MF witness, confirmed on both sides

`MF_MODAL_FUTURE_TH` (`examples.py:1083-1101`) has conclusion
`(\Box A \rightarrow \Box \Future A)` and **`'expectation': False`** — the example file itself
records "a countermodel is expected". It is removed from the suite at collection time by
`tests/unit/test_bimodal.py:51`, an entry in `KNOWN_TIMEOUT_EXAMPLES`, whose comment at
`test_bimodal.py:35-37` states that MF "is NOT a theorem under current bimodal semantics
(countermodel found at N=1, M=2)".

Both are false with respect to the paper. `Metalogic/Soundness.lean:373`:

```lean
theorem modal_future_valid (φ : Formula) : ⊨ ((φ.box).imp ((φ.allFuture).box))
```

— sorry-free, at the **unrestricted** class (`⊨`, all task frames), proved by exactly the SP1
argument of `:1136-1141` run one step further, via `TimeShift.timeShift_preserves_truth`. And on
the certificate side, `WitnessFamily.no_witnessFamily_of_MF` (`Examples.lean:275`) proves that
**no** witness family, at **any** segment lengths, refutes MF.

The recorded settings `N=2, M=2` against a depth-1 formula violate the encoding's own
`M ≥ d + 2` safety criterion, which is precisely the boundary-vacuity failure mode that
`ForAllTime`'s docstring describes at `core.py:506-537` ("`G(p)` evaluated at `t = M-1` … is
vacuously true"). The dispatch's instruction not to repair this by tuning `M` is correct, and
the reason is structural: no finite `M` makes `(-M, M) ∩ ℤ` a temporal order.

The exclusion mechanism is also mis-filed: MF sits in a set named `KNOWN_TIMEOUT_EXAMPLES`
beside genuine timeout entries, although its stated reason is semantic disagreement with the
paper's axiom.

### 2. The two statements, precisely

Fix finite sets `Γ` (premises) and `Δ` (conclusions) of `BL` sentences, translated into the
Lean-primitive `Formula` grammar `atom | bot | imp | box | untl | snce`. Let
`C := closureOf (Γ ++ Δ)` be the subformula closure.

A **certificate** is a pair `𝒲 = (bx, ⟨Λ₀, …, Λ_k⟩)` together with a target time `t₀ ∈ ℤ`,
where `bx : Formula → Bool` and each `Λᵢ = (backᵢ, midᵢ, fwdᵢ)` is a triple of lists of subsets
of `C` with `backᵢ ≠ []` and `fwdᵢ ≠ []`, decoded to `Lᵢ : ℤ → 𝒫(C)` by the three-segment
scheme (`back` repeated strictly left of 0, `mid` on `[0,|mid|)`, `fwd` repeated from `|mid|`).
The four conditions:

- **(C1) Local coherence.** For every `i` and every `t ∈ ℤ`: `⊥ ∉ Lᵢ(t)`; for every
  `a → b ∈ C`, `(a → b) ∈ Lᵢ(t) ↔ (a ∈ Lᵢ(t) → b ∈ Lᵢ(t))`; for every `□χ ∈ C`,
  `□χ ∈ Lᵢ(t) ↔ bx(χ) = true`; for every `g U e ∈ C`,
  `(g U e) ∈ Lᵢ(t) ↔ (e ∈ Lᵢ(t+1) ∨ (g ∈ Lᵢ(t+1) ∧ (g U e) ∈ Lᵢ(t+1)))`; for every `g S e ∈ C`,
  the mirror at `t−1`. **Atoms are deliberately unconstrained.**
- **(C2) Fulfilment.** For every `i, t, g, e`: if `(g U e) ∈ Lᵢ(t)` then there is `s > t` with
  `e ∈ Lᵢ(s)` and `g ∈ Lᵢ(r)` for every `t < r < s`; and the mirror for `S` with `s < t`.
- **(C3) Box faithfulness.** For every `□χ ∈ C`:
  `bx(χ) = true ↔ ∀ i ∀ t. χ ∈ Lᵢ(t)`.
- **(C4) Target.** `∀ γ ∈ Γ. γ ∈ L₀(t₀)` and `∀ σ ∈ Δ. σ ∉ L₀(t₀)`.

---

**(SOUND).** *If the search reports a countermodel for `Γ / Δ`, presented as a certificate
`(𝒲, t₀)` satisfying (C1)–(C4), then there exist a model `M = ⟨W, 𝔇, ⇒, |·|⟩` of `BL` in the
paper's sense — `𝔇` a nontrivial totally ordered abelian group and `⇒` a task relation
satisfying Compositionality, Seriality, Limit and Saturation — a world history `τ ∈ H_F`, and a
time `x ∈ D`, such that `M, τ, x ⊨ γ` for every `γ ∈ Γ` and `M, τ, x ⊭ σ` for every `σ ∈ Δ`.
Hence `Γ ⊭ σ` for every `σ ∈ Δ`, in the sense of `def:logical-consequence` (`:1124`).*

This is **mandatory**. It decomposes into four obligations, of which only two are new work:

| | Obligation | Status |
|---|---|---|
| **S1** | (C1)–(C4) ⟹ a paper countermodel exists | **Proved.** Section 3; machine-checked, `Agreement.lean:232`. |
| **S2** | The Lean definitions transcribe the paper's | **Discharged by inspection** in section 3.7; recorded as an audit deliverable, not a theorem. |
| **S3** | Whatever the search reports satisfies (C1)–(C4) | **New.** Discharged by *deciding*, not by proving the encoder correct — section 7. |
| **S4** | The Sentence→`Formula` translation preserves truth | **New, and uncovered by 184's plan** — section 6.4. |

**S3 is the architectural point of the whole design.** (SOUND)'s antecedent is decidable
(section 4.1), so ModelChecker never has to prove its Z3 encoder sound. It re-decides the
antecedent on every reported countermodel, twice and independently. A verified antecedent plus
S1 is a countermodel; an encoder bug becomes a loud rejection, not a false report.

---

**(ADEQ).** *Let `f` be a computable function of `|C|`. If some `σ ∈ Δ` is not a ℤ-time
consequence of `Γ` — i.e. `¬ SemanticConsequenceIn FrameClass.ZTime Γ σ` — then the search, run
at segment-length settings `back, mid, fwd ≥ f(|C|)`, returns SAT and emits a certificate
satisfying (C1)–(C4).*

This direction **must not be asserted**. It is bounded-search-relative, it is stated at frame
class ℤ-time only, and it decomposes as follows (section 8):

| | Component | Status |
|---|---|---|
| **A1** | Compression: a ℤ-time countermodel yields a certificate with lengths bounded by `f(|C|)` | **Open.** BimodalLogic task 623 item 1, `[NOT STARTED]`, 2–4 weeks, route named. The one candidate for reducing it to a cited result is examined and **rejected** in §8.1a. |
| **A2** | Encoding completeness: a certificate within the configured lengths ⟹ the encoding is SAT | **Provable and testable now.** Deciding test in section 8.3. |
| **A3** | Bound realization: configured lengths ≥ `f(|C|)` | Vacuous until A1 supplies `f`. |
| **A0** | Frame-class gap: ℤ-time completeness ⇏ completeness for `def:logical-consequence` | **Permanent limit**, quantified in section 8.2. |

### 3. The proof of (SOUND): four lemmas and the theorem, in full

Fix a certificate `(𝒲, t₀)` satisfying (C1)–(C4). Define:

- `𝔇 := ⟨ℤ, +, 0, ≤⟩`;
- `W := {0, …, k} × ℤ`;
- `(i, t) ⇒_x (j, u)` iff `i = j` and `u = t + x`, for all `x ∈ ℤ`;
- `|p| := {(i, t) ∈ W : atom p ∈ Lᵢ(t)}`;
- `τᵢ : ℤ → W`, `τᵢ(t) := (i, t)`; `F := ⟨W, 𝔇, ⇒⟩`; `M := ⟨W, 𝔇, ⇒, |·|⟩`.

**Reflection convention.** The paper defines `w ⇒_{-x} u := u ⇒_x w` for `x ≥ 0` (`:970`). The
relation above is given at every `x ∈ ℤ` at once; it respects the convention, since for `x ≥ 0`,
`(j,u) ⇒_x (i,t)` iff `j = i ∧ t = u + x` iff `i = j ∧ u = t + (−x)` iff `(i,t) ⇒_{−x} (j,u)`.
So the definition is consistent with reflection rather than in tension with it.

---

**Lemma 1 (Frame).** *`F` is a task frame in the sense of `:989-994`.*

*Proof.* `𝔇 = ⟨ℤ, +, 0, ≤⟩` is a totally ordered abelian group, and it is nontrivial
(`1 ≠ 0`), so it is a temporal order (`:961`). `W` is nonempty since `k ≥ 0`. The four
constraints, for `x, y ≥ 0` and `w, u, v ∈ W`:

*Compositionality*: `w ⇒_{x+y} v` iff `∃ u ∈ W. w ⇒_x u ∧ u ⇒_y v`. Left to right: given
`v = (w₁, w₂ + x + y)`, take `u := (w₁, w₂ + x)`; then `w ⇒_x u` and `u ⇒_y v`. Right to left:
from `u = (w₁, w₂+x)` and `v = (u₁, u₂+y)` we get `v = (w₁, w₂+x+y)`, i.e. `w ⇒_{x+y} v`. ∎

*Seriality*: given `w` and `x ≥ 0`, put `u := (w₁, w₂ + x)` and `v := (w₁, w₂ − x)`; then
`w ⇒_x u` and `v ⇒_x w`. ∎

*Limit*: `⋂_{x>0} (w)_x = {w}`, where `(w)_x = ⋃_{|y| < x} ⟨w, y⟩` and `⟨w,y⟩ = {u : w ⇒_y u}`.
Over `ℤ`, `x > 0` implies `x ≥ 1`, so `(w)_1` is already a member of the family, and
`|y| < 1` over `ℤ` forces `y = 0`, whence `(w)_1 = ⟨w, 0⟩ = {(w₁, w₂)} = {w}`. Since every `(w)_x`
contains `w` (take `y = 0`), the intersection is exactly `{w}`. ∎

*Saturation*: every fibre `⟨w, x⟩ = {(w₁, w₂+x)}` is a singleton, and every segment
`[w,u]_x^y = ⟨w,x⟩ ∩ ⟨u,−y⟩` is a subset of a singleton, hence empty or a singleton. Let `𝒮` be
a `⊇`-directed family of **nonempty** fibres and segments; every member is a singleton. For
`S₁, S₂ ∈ 𝒮`, directedness gives `S ∈ 𝒮` with `S ⊆ S₁ ∩ S₂`; `S` is a nonempty singleton, so
`S₁ ∩ S₂ ≠ ∅`, so `S₁ = S₂`. Thus `𝒮 = {S}` for a single singleton `S`, and `⋂ 𝒮 = S ≠ ∅`. ∎

*(This is the step at which determinism is load-bearing; see section 4.2.)*

---

**Lemma 2 (Histories).** *Each `τᵢ` is a world history, and*
`H_F = { t ↦ (i, t + c) : 0 ≤ i ≤ k, c ∈ ℤ }`.

*Proof.* `τᵢ` is total on `D = ℤ`, and for all `x, y ∈ ℤ`,
`τᵢ(x) = (i, x) ⇒_{y−x} (i, x + (y−x)) = (i, y) = τᵢ(y)`, so `τᵢ ∈ H_F` (`:1029`).

Conversely, let `σ ∈ H_F`. For all `x, y`, `σ(x) ⇒_{y−x} σ(y)`, which by definition of `⇒`
forces `σ(y)₁ = σ(x)₁` and `σ(y)₂ = σ(x)₂ + (y − x)`. Putting `i := σ(0)₁` and `c := σ(0)₂`
gives `σ(t) = (i, t + c)` for all `t`. ∎

**Corollary 2.1 (Translation closure, derived).** `H_F` is closed under translation: if
`σ(t) = (i, t+c)` then `z ↦ σ(z + d)` is `z ↦ (i, z + c + d) ∈ H_F`. So `app:auto_existence`
holds *by construction* for this frame, rather than being asserted as in
`capped_skolem_abundance_constraint`.

**Corollary 2.2 (Box's range).** By Lemma 2, `H_F` is exactly the `k+1` lassos and their
translates. So the `(□)` clause at `:1073` quantifies over precisely the certified histories —
which is what makes (C3) a *statement about the certificate* rather than an oracle assumption.

---

**Lemma 3 (Time-shift preservation, instantiated).** *For every `BL` sentence `ψ`, every
`σ, ρ ∈ H_F` and `x, y ∈ D` with `σ ≈_x^y ρ`: `M, σ, x ⊨ ψ` iff `M, ρ, y ⊨ ψ`.*

This is `lem:history-time-shift-preservation` (`:3212`) applied to `M`; its proof at
`:3216-3223` uses only that `|pᵢ| ⊆ W` (no temporal component in the valuation) and
`app:auto_existence`, both of which hold here — the latter by Corollary 2.1 rather than by
hypothesis.

**Corollary 3.1.** Combining Lemmas 2 and 3, truth in `M` at `(σ, t)` depends only on the
carrier point `σ(t) = (i, t+c)`. In particular `M, τᵢ, t ⊨ ψ` and `M, τᵢ^{(c)}, t ⊨ ψ` agree
with `M, τᵢ, t + c ⊨ ψ`, and `M, σ, x ⊨ □χ` iff `M, τⱼ, u ⊨ χ` for every `j` and every `u ∈ ℤ`.

---

**Lemma 4 (Truth lemma / agreement).** *For every `ψ ∈ C`, every `i`, and every `t ∈ ℤ`:*
`M, τᵢ, t ⊨ ψ` *iff* `ψ ∈ Lᵢ(t)`.

*Proof.* By induction on `ψ`. `C` is closed under subformulas, so every appeal to the induction
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
  induction hypothesis, iff `χ ∈ Lⱼ(u)` for all `j, u`. By (C3), iff `bx(χ) = true`. By (C1)'s
  box clause, iff `□χ ∈ Lᵢ(t)`.
- **`ψ = g U e`.**
  *(⇐)* Suppose `(g U e) ∈ Lᵢ(t)`. By **(C2)** there is `s > t` with `e ∈ Lᵢ(s)` and
  `g ∈ Lᵢ(r)` for all `t < r < s`. The induction hypothesis gives `M, τᵢ, s ⊨ e` and
  `M, τᵢ, r ⊨ g` for all such `r`, so `M, τᵢ, t ⊨ g U e` by `(U)` at `:1075`.
  *(⇒)* Suppose `M, τᵢ, t ⊨ g U e`, witnessed by `s > t`. Since `D = ℤ` is discrete,
  `n := s − t ≥ 1` is a positive integer; argue by strong induction on `n`.
  If `n = 1` then `s = t+1` and `M, τᵢ, t+1 ⊨ e`, so `e ∈ Lᵢ(t+1)` by the (outer) induction
  hypothesis at `e`, and (C1)'s until clause gives `(g U e) ∈ Lᵢ(t)`.
  If `n > 1` then `M, τᵢ, t+1 ⊨ g` (as `t < t+1 < s`) and `M, τᵢ, t+1 ⊨ g U e` with the same
  witness `s`, at distance `n − 1`; by the inner induction `(g U e) ∈ Lᵢ(t+1)`, and by the outer
  induction hypothesis `g ∈ Lᵢ(t+1)`, so (C1)'s until clause again gives `(g U e) ∈ Lᵢ(t)`.
- **`ψ = g S e`.** Symmetric, with `t−1` in place of `t+1` and the witness below `t`. ∎

**Remark (why both (C1) and (C2) are needed, and where discreteness enters).** The two
directions of the `U` case consume different conditions. `(⇐)` is exactly fulfilment: (C1)'s
until clause is a *fixpoint law*, satisfied by the label that carries `g U e` forward forever and
never delivers `e` — coherence alone admits infinite postponement, and (C2) is what excludes it.
`(⇒)` is a **downward induction on the coherence fixpoint law**, and it is the one place in the
whole proof where `D = ℤ` (rather than an arbitrary temporal order) is used: over a dense order
the descent `s − t → 0` does not terminate. This is a second, independent reason the design is
ℤ-time only, distinct from the finite-carrier argument of section 8.4.

---

**Theorem ((SOUND)).** *Under (C1)–(C4), `M, τ₀, t₀ ⊨ γ` for every `γ ∈ Γ` and
`M, τ₀, t₀ ⊭ σ` for every `σ ∈ Δ`, where `M` and `τ₀` are as constructed and `F` is a task frame
with `τ₀ ∈ H_F`. Hence `Γ ⊭ σ` for every `σ ∈ Δ`.*

*Proof.* `F` is a task frame by Lemma 1 and `τ₀ ∈ H_F` by Lemma 2, so `(M, τ₀, t₀)` is an
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

#### 3.6 The proof is already machine-checked

Every step above has a landed, sorry-free Lean counterpart. Verified: `grep -c sorry` returns 0
for `Semantics/ShiftSet.lean`, `WitnessFamily/Agreement.lean` and `WitnessFamily/Decide.lean`;
the only `sorry` occurrences in `WitnessFamily/` and `Metalogic/Soundness.lean` are in docstring
prose. A peer survey reports the whole `FormalSystem/`, `BimodalTools/`, `Tests/` tree is
sorry-free and declares no axioms, with `FormalSystem/MainResults.lean` running `#print axioms`
at build time as a pinned audit; I spot-checked this over the files cited below and found it to
hold, and note that it means **the gaps in the Lean development are unstated theorems, not
admitted ones.**

| This report | Lean name | File:line |
|---|---|---|
| The construction (`𝔇`, `W`, `⇒`, `|·|`) | `WitnessFamily.std` | `WitnessFamily/Std.lean:65` |
| Lemma 1, Compositionality | `ShiftSet.shRel_comp` | `Semantics/ShiftSet.lean:148` |
| Lemma 1, Seriality | `ShiftSet.shRel_serial` | `ShiftSet.lean:163` |
| Lemma 1, Limit | the `sep` field, via `TaskFrame.limit_reflect_of_reflective` | `ShiftSet.lean:115, 203`; discharged for `std` at `Std.lean:73-80` by `Int.abs_lt_one_iff` |
| Lemma 1, Saturation | `ShiftSet.shRel_saturation` (`saturation_of_fib_subsingleton`) | `ShiftSet.lean:171` |
| Lemma 1, whole | `ShiftSet.fibre_isRegular` / `frame_isRegular` | `ShiftSet.lean:200, 225` |
| The frame is ℤ-time | `WitnessFamily.std_isZTime`, `std_sat_ztime`, `std_sat_base` | `Std.lean:84, 91, 96` |
| Lemma 2 | `ShiftSet.total_eq_orbit` | `ShiftSet.lean:252` |
| Lemma 3 / Corollary 3.1 | `ShiftSet.forward_repr`, `WitnessFamily.sh_surj`, `Truth.box_const` | `ShiftSet.lean:284`; `Std.lean:101` |
| Lemma 4 | `WitnessFamily.shiftTruth_iff_mem`, `truth_iff_mem` | `Agreement.lean:109, 193` |
| Lemma 4, `U`/`S` helper | `untl_mem_of_witness`, `snce_mem_of_witness` | `Agreement.lean:65, 85` |
| **The Theorem** | `WitnessFamily.joint_countermodel` | `Agreement.lean:232` |
| Theorem, single-conclusion | `not_consequence_ztime`, `not_consequence_base` | `Agreement.lean:203, 219` |
| MF is valid (§1.4) | `modal_future_valid` | `Metalogic/Soundness.lean:373` |
| No certificate refutes MF | `no_witnessFamily_of_MF` | `Examples.lean:275` |

`joint_countermodel`'s statement is literally (SOUND)'s consequent:

```lean
theorem joint_countermodel (W : WitnessFamily Γ Del) {t : ℤ}
    (hloc : W.LocalCoherentLab) (hful : W.FulfillingLab) (hbox : W.BoxFaithful)
    (htgt : W.Target t) :
    ∃ (F : TaskFrame) (_ : FrameClass.ZTime.Sat F) (M : TaskModel F)
      (τ : WorldHistory F) (u : F.Duration),
      (∀ γ ∈ Γ, TruthAt M τ u γ) ∧ (∀ σ ∈ Del, ¬ TruthAt M τ u σ)
```

**A near-miss worth recording, so it is not mistaken for the mechanization of Lemma 1.**
`Semantics/IntNormalForm.lean:456` supplies `ofStep {W} [Finite W] [Nonempty W] (R₁) (fwd) (bwd)
: FrameOver intOrder`, which does discharge all four constraints from bi-seriality alone —
Compositionality from `iter_add`, Limit from `limit_of_succOrder`, Saturation from
`saturation_of_finite` (its sole `Classical.choice` cost, accepted for `ofStep` specifically).
It is **not** the mechanization of this report's Lemma 1: `ofStep` requires **`[Finite W]`**, and
Saturation is discharged *from finiteness*, whereas the certified carrier
`W = {0,…,k} × ℤ` is **infinite** — which is the whole point, since `Probe476.fmp_false` refutes
the finite-carrier route. Lemma 1's Saturation comes instead from `shRel_saturation`
(subsingleton fibres), and the correct mechanization is the `ShiftSet` chain in the table above.
`ofStep` is the right tool for a *fixed-frame* model-checking mode (184 report 01 §4.4's optional
"New C"), and for nothing in this theorem.

#### 3.7 The transcription audit (obligation S2), discharged by inspection

(SOUND) is a claim about the *paper*; the Lean theorem is a claim about *Lean's* definitions.
The bridge is not a theorem and cannot be; it is an audit. Each item below was checked verbatim
against the cited paper line.

| Paper | Lean | Verdict |
|---|---|---|
| `𝔇` = nontrivial totally ordered abelian group (`:961`) | `structure TemporalOrder` fields `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, `Nontrivial` (`Semantics/TemporalOrder.lean:83-93`) | **Exact**, field-by-field, with the paper's names in the docstrings |
| task frame + the four constraints (`:989-994`) | `structure TaskFrame` (`Semantics/TaskFrame.lean:2571`) with `TaskFrame.IsRegular` supplying `comp`, `serial`, `limit`, `saturation`, each cited to `def:frame` | **Exact.** `FrameClass.Base.Sat F = F.IsRegular` (`FrameClassValidity.lean:152`) |
| `(pᵢ) (⊥) (→) (□) (S) (U)` (`:1068-1076`) | `def TruthAt` (`Semantics/Truth.lean:232-238`) | **Exact.** `box φ => ∀ σ : WorldHistory F, TruthAt M σ t φ` — no domain guard; `untl ψ φ` is **guard-first**, matching `φ U ψ` at `:1075` |
| `Γ ⊨ φ` (`:1124`, `def:logical-consequence` `:3236`) | `ConsequenceOnFrames P Γ φ` / `SemanticConsequenceIn .Base` (`Semantics/Validity.lean:80, 89`) | **Exact** modulo `Γ` finite (a `Context`, i.e. a list) rather than a set — harmless for model checking, where `Γ` is always finite |
| `app:auto_existence` (`:3197`) | not needed: Corollary 2.1 derives it | **Not a dependency** |
| `lem:history-time-shift-preservation` (`:3212`) | `TimeShift.timeShift_preserves_truth` (`Semantics/TruthTransport.lean`), consumed by `ShiftSet.reverse_repr` and `modal_future_valid` | **Exact**, and recorded as unconditional (the shift-closure hypothesis it once carried is retired) |

**Residual**: the paper's `BL` is `⟨SL, ⊥, →, □, S, U⟩`, exactly the Lean `Formula` grammar.
ModelChecker's operator set is richer — nine primitives (`\neg \wedge \vee \bot \Box \Future
\Past \Until \Since`) plus eight defined. The audit therefore extends to the **translation**,
which is obligation S4 and is *not* covered by the Lean theorems. Section 6.4.

### 4. The two identified gaps, closed

#### 4.1 Gap 1 — periodicity, and the window bound D7 gets wrong

Lemma 4 quantifies over every `t ∈ ℤ`, while a re-checker inspects finitely many stored
positions. The bridging argument is the periodic decoding plus a window collapse, and both are
machine-checked.

The two periodicities (`WitnessFamily/Basic.lean:117, 123`):

```lean
theorem lab_sub_back_length (Λ) {t : ℤ} (ht : t < 0) : Λ.lab (t - Λ.nb) = Λ.lab t
theorem lab_add_fwd_length  (Λ) {t : ℤ} (ht : Λ.nm ≤ t) : Λ.lab (t + Λ.nf) = Λ.lab t
```

The collapses, with `nb := |back|`, `nm := |mid|`, `nf := |fwd|`:

| Condition | Lean theorem | File:line | **Window (half-open)** |
|---|---|---|---|
| Local coherence | `coherent_iff_window` | `Decide.lean:335` | `[−2·nb, nm + 2·nf)` |
| Fulfilment | `fulfil_iff_window` | `Decide.lean:743` | `[−2·nb, nm + 2·nf)` |
| Box faithfulness (`∀t. χ ∈ Lᵢ t`) | `mem_all_iff_window` | `Decide.lean:~880` | `[−nb, nm + nf)` |
| Forward witness scan for (C2) | `scan_forward` | `Decide.lean:192` | a witness exists in `(t, max(t, nm) + nf]` |
| Backward witness scan for (C2) | `scan_backward` | `Decide.lean:212` | a witness exists in `[min(t, 0) − nb, t)` |

The reason for **two** periods rather than one is recorded in `coherent_iff_window`'s own
docstring: the clause at `t` reads `t−1` and `t+1` as well as `t`, so a representative position
must have its whole neighbourhood inside the periodic region. The decidability instances
`decidableLocalCoherentLab`, `decidableFulfillingLab`, `decidableBoxFaithful`,
`decidableTarget` (`Decide.lean:865, 878, 923, 927`) are built from exactly these collapses and
are computable (the module states it opens no `Classical`).

> **DEFECT IN TASK 184'S PLAN.** Decision **D7** (`plans/01_...md`, "Decisions Fixed at Plan
> Time") states the fulfilment window as *"one full `fwd` period past the `mid` segment forward,
> symmetrically one `back` period before the origin"* — i.e. `[−nb, nm + nf)`. The proved window
> is `[−2·nb, nm + 2·nf)`. D7 also treats coherence and fulfilment as sharing a window with box
> faithfulness, whereas box faithfulness collapses at **one** period. D7's own sentence reads:
> *"Getting this bound wrong is the single most likely silent soundness bug in the whole
> redesign."* It is presently wrong in the plan. The correction is cheap now (184 is
> `[NOT STARTED]`) and expensive after Phases 4, 8 and 12 are written against it.

**Second half of Gap 1** — "the re-checker must be shown to implement the condition it is
credited with". The honest discharge is not a proof but a **differential obligation**: the
Python re-checker's verdict must agree with `lake exe check_certificate`, which is built
directly on the four `Decidable` instances above, on the whole fixture corpus including
adversarial negatives. That is 184's Phase 5. This report adds the requirement that the corpus
include, at minimum, (i) a family locally coherent but *not* fulfilling (infinite postponement —
`Examples.lean` exhibits one), (ii) a family failing (C2) only at a position **outside**
`[−nb, nm+nf)` but inside `[−2·nb, nm+2·nf)`, which is exactly the fixture that distinguishes
D7's bound from the proved one, and (iii) a family failing (C3) only.

#### 4.2 Gap 2 — determinism, re-scoped

The dispatch records that Limit and Saturation were discharged "using the fact that fibres are
singletons", so the proof does not transfer if lasso state-sharing is added. Confirmed, and
sharper than stated:

- **Limit is genuinely non-free.** `ShiftSet.lean:51-54` records, and
  `ShiftSet.SepNotDerivable.sep_not_derivable` (`ShiftSet.lean:520`) *proves*, that separation
  does not follow from the two action laws: `D = ℚ` acting on `ℚ ⧸ DyadicGroup` by translation
  satisfies `sh_zero` and `sh_add` and refutes separation (failure mode: a dense proper
  stabiliser). This is why `sep` is a structure field. Over `ℤ` it is discharged trivially
  (`Std.lean:73-80`, `Int.abs_lt_one_iff`).
- **Saturation is free only from subsingleton fibres**
  (`TaskFrame.saturation_of_fib_subsingleton`, consumed at `ShiftSet.lean:171`) — precisely
  Lemma 1's argument above.

**The re-scoping.** Determinism is also what makes **Lemma 2** true. If two lassos shared a
state, the frame's world histories would no longer be the orbits: a path could cross from one
lasso to another at the shared state, and `total_eq_orbit` (`ShiftSet.lean:252`, whose proof
reads `σ = S.hist (σ.state 0)` straight off functionality) would fail. Corollary 2.2 would then
fail, and with it the **Box case of Lemma 4**, because (C3) is calibrated to "every position of
every lasso" and would no longer enumerate `H_F`. This is the same obstruction that
`Probe476.fmp_false` records for finite digraphs: admitting recombined paths adds histories that
Box must range over.

**Consequence.** Adding state-sharing for the stability modal is not a matter of re-proving
Lemma 1 with a weaker argument; it requires re-proving Lemma 2 and redesigning (C3). Task 184's
decision **D9** (design for sharing, do not implement it) is the right call and should stand.
This report adds that the datatype's forward-compatibility note must say *why*: the blocker is
`total_eq_orbit` and the Box case, not Limit and Saturation.

### 5. Lean and Mathlib theorem inventory consumed

Discovered by direct file reading (`WitnessFamily/`, `ShiftSet.lean`, `Soundness.lean`,
`Axioms.lean`, `TemporalOrder.lean`, `Truth.lean`, `Validity.lean`,
`FrameClassValidity.lean`) rather than by Mathlib lookup: the relevant results are all in the
project-local development, not in Mathlib. The three Mathlib dependencies that *are* load-bearing
and were confirmed in place: `Mathlib.Data.Int.SuccPred` and
`Mathlib.Order.SuccPred.LinearLocallyFinite` supply `SuccOrder ℤ`, `PredOrder ℤ`,
`IsSuccArchimedean ℤ`, `IsPredArchimedean ℤ` for `std_isZTime` (`Std.lean` header records that
removing either breaks the build); `Mathlib.Data.Int.Interval` supplies `Finset.Ico` for the
window collapses; `Int.abs_lt_one_iff` discharges `sep`.

No Lean implementation tools were used; nothing was proved inside the Lean development, per the
dispatch's scope.

### 6. What must change in the implementation, at file and function granularity

#### 6.1 Deletions (the theorem's hypotheses cannot hold while these exist)

| Target | File:line | Why the theorem forbids it |
|---|---|---|
| `is_valid_time` | `semantic/core.py:997-1024` | `D` must be `ℤ` (Lemma 1); a finite window is not a temporal order |
| `is_valid_time_for_world` | `core.py:1026-1039` | same; also the source of the per-world interval fiction |
| `ForAllTime`, `ExistsTime` | `core.py:505-577`, `:578-616` | tense quantification becomes label-position algebra over `ℤ` with the §4.1 collapse; no operator may be vacuous at a boundary |
| `is_world` | `core.py:201-205` and its ~30 uses | Box's range is `H_F`, **derived** by Lemma 2, never the extension of an uninterpreted predicate |
| `build_frame_constraints` (all 13 items) | `core.py:646-995` | Lemma 1 discharges the four constraints by construction; none is a solver constraint |
| `capped_skolem_abundance_constraint`, `depth_bounded_skolem_abundance_constraint`, and the unused `full_abundance_constraint` (`:1353`), `skolem_full_abundance_constraint` (`:1463`) | `core.py:1582-1664`, `:1700-1790`, `:1353-`, `:1463-` | translation-closure is Corollary 2.1, proved, not asserted |
| `task_restriction` and its soundness-analysis comment | `core.py:891-964`, `:993` | the frame-class-too-large concession disappears with the frame it concerns |
| `WorldStateSort = z3.BitVecSort(self.N)`, `max_world_id` | `core.py:153`, `:208` | `W = {0..k} × ℤ` is infinite |
| every inline `self.M` site | `core.py:257,1051,1117,1122,1164,1537-1558,1639-1641,1740-1741,2137-2138`; `model.py:53`; every `operators.py` `find_truth_condition`; `iterate.py:424` | §1.2: these do not follow a change to `is_valid_time` |

#### 6.2 Rewrites

- `operators.py:507` `NecessityOperator.true_at`, `:1054` `UntilOperator.true_at`, `:1287`
  `SinceOperator.true_at` — the **clauses are correct** and must be preserved as written; only
  the structures change. Each becomes a label-constraint generator: Box introduces the `bx`
  variable and, when guessed false, requests a witness lasso; `U`/`S` emit (C1)'s one-step
  unfolding at `t±1` plus (C2)'s bounded scan over the §4.1 window.
- `semantic/model.py` extraction path (`extract_model_elements`, `core.py:2007-2060`, and the
  five helpers producing `world_histories`, `world_arrays`, `world_time_intervals`,
  `time_shift_relations`) — replaced by `extract_certificate(z3_model) -> (WitnessFamily, int)`.
  The output is **a presentation of a paper-sense model**, not a Z3 model view.
- `semantic/proposition.py:138-190` `find_extension` — truth values come from labels.
- `semantic/witness_registry.py`, `semantic/witness_constraints.py` — currently instantiated and
  unused; become the label-bit registry and the constraint generators.

#### 6.3 Expectation corrections that the theorem forces

- `examples.py:1089-1096` — `MF_MODAL_FUTURE_TH_settings['expectation']` must become `True`
  (no countermodel). `modal_future_valid` proves MF valid over **all** task frames.
- `tests/unit/test_bimodal.py:35-37` — the comment asserting MF "is NOT a theorem under current
  bimodal semantics" must be **deleted, not softened**. `no_witnessFamily_of_MF` proves no
  certificate can refute MF at any lengths.
- `tests/unit/test_bimodal.py:51` — remove MF from `KNOWN_TIMEOUT_EXAMPLES`. Its presence there
  is also a mis-filing: the recorded reason is semantic disagreement, not a timeout.
- The `N`/`M` keys in every example's settings; `N` and `M` cease to exist (184's D4).

#### 6.4 The uncovered bridge: obligation S4

184's Phase 5 round-trip compares the Python re-checker against `lake exe check_certificate`.
**Both sides consume the same already-translated `Formula`.** So the round-trip tests the
re-checker; it cannot test whether the ModelChecker `Sentence` → Lean `Formula` translation
preserves truth. That translation is non-trivial: it must eliminate `\neg`, `\wedge`, `\vee`,
`\Future`, `\Past`, `\Diamond`, `\next`, `\prev` into the six primitives, and it must **swap**
`\Until`/`\Since` arguments, since `UntilOperator.true_at(self, event_arg, guard_arg, …)` is
event-first (`operators.py:1054`) while Lean's `untl` is guard-first (`Truth.lean:236`, and the
wire format's named `event`/`guard` fields make the wire itself order-free, so the swap hazard
is purely internal).

**Recommended discharge** (a deliverable of this task, not of 184): a property test over
randomly generated small `Sentence`s comparing, at every point of a small hand-built ℤ-model,
`BimodalSemantics.true_at(s, …)` against a direct evaluator for `tr(s)`. This is the one place
where `oracle/bimodal_logic/ground_truth.py` remains useful — but note (§9.2) it handles only
the five temporal-only primitive tags and **has no box case**, so it can cover the tense half of
the translation only.

### 7. How a countermodel is presented and independently re-checked

#### 7.1 The wire contract (fixed, external, breaking-change-gated)

`BimodalTools/README.md`'s "Certificate re-verification protocol" and
`WitnessFamily/Basic.lean`'s header both state that `back`, `mid`, `fwd`, `bx`, `lassos`,
`target` are an export contract. Input:

```json
{"target": {"premises": [<formula>,...], "conclusions": [<formula>,...], "time": 0},
 "bx":     [[<formula>, true], [<formula>, false], ...],
 "lassos": [{"back": [<label>,...], "mid": [<label>,...], "fwd": [<label>,...]}, ...]}
```

`<label>` is a list of `<formula>`, read as a set. `<formula>` tags: `atom` (`name`), `bot`,
`imp` (`left`,`right`), `box` (`child`), `untl`/`snce` (`event`,`guard`). `target.time` is
**required with no default** — it is (C4)'s existential witness, and the README's rationale is
that every other existential in a certificate is explicitly witnessed. `bx` is sparse (absent
reads `false`). `lassos[0]` is the main lasso. **Atom identity is base-only**: `Formula.toJson`
drops `Atom.freshIndex`, so a certificate carrying a fresh/Skolem atom is rejected outright; the
Python exporter must refuse to emit one.

Output, exactly one line, and **never a validity claim**:
`{"status":"countermodel","time":0}` |
`{"status":"rejected","failed":[{"condition":…,"lasso":…,"position":…,"formula":…,"detail":…}]}` |
`{"status":"error","message":…}`, with
`condition ∈ {structural, local_coherent, fulfilling, box_faithful, target, unlocalized}`.
A missing `target` or `target.time` is `error`, never `rejected`.

#### 7.2 The mechanism that discharges obligation S3

Dual verification, in this order, on **every** reported countermodel:

1. Extract `(𝒲, t₀)` from the Z3 model.
2. Decide (C1)–(C4) in a pure-Python re-checker over the §4.1 windows — independent of the Z3
   model object.
3. Fail-fast (project philosophy) on any verdict but `countermodel`. A Z3-side bug becomes a
   loud rejection, never a false report.
4. Export the JSON and, where `lake` and BimodalLogic are present, re-decide with
   `lake exe check_certificate`; disagreement is a Python-side defect by definition, since the
   Lean predicates are the contract.

This is why "a machine-checkable re-verification of every reported countermodel, independent of
the solver" is a deliverable rather than a testing nicety: it is the only thing standing between
the Z3 encoder and (SOUND)'s antecedent.

**Nothing of this exists today.** `grep -rin certificate` over
`code/src/model_checker/theory_lib/bimodal/` and `oracle/` returns **zero** matches. The nearest
analogues are `oracle/bimodal_logic/serialization.py:150` `serialize_countermodel` (a JSON
*report* that nothing re-verifies) and `oracle/bimodal_logic/ground_truth.py:152`
`ground_truth_verdict` (re-checks *verdicts* by brute force over `[-window, window]`, five
primitive tags, **no box**).

### 8. (ADEQ): status, reduction, and the deciding tests

#### 8.1 A1 — compression, open, with the route named

A1 is BimodalLogic task 623 item 1, verbatim from `~/Projects/BimodalLogic/specs/TODO.md`:
*"if `¬ ValidZTime ψ` (equivalently, for the consequence form,
`¬ SemanticConsequenceIn FrameClass.ZTime Γ σ`) then some `WitnessFamily` satisfying the four
conditions exists with every segment length bounded by a computable function of the closure size,
whose main lasso carries the refuting point."*

Status `[NOT STARTED]`, dependencies 534, 645, 665 (665 = the soundness half, complete), effort
2–4 weeks. Route recorded there: take a refuting model, history and time; for each boxed
subformula guessed false pick a witnessing history; compress each history's *type* sequence into
a bi-lasso using `BiLasso/GoodCycle.lean`'s eventuality-propagation and good-cycle lemmas with
`BiLasso/Extraction.lean`'s `exists_annot_of_truth` as the template, re-run over subformula-set
space rather than presentation states; `TranslationProduct.lean`'s `validIn_iff_recurrenceFree`
lets the witness paths be taken recurrence-free, so only the type sequence need be eventually
periodic. **Reduction to cited results**: Gabbay–Kurucz–Wolter–Zakharyaschev 2003, Theorems 3.29,
5.30, 5.32, 11.7, 11.21.

**A1 is recorded as open. It is not asserted, and ModelChecker's soundness does not depend on
it.** Its only consequence for ModelChecker is whether "no certificate within bounds" carries
information — and by 184's D8 it must not, until A1 lands.

#### 8.1a The one candidate for "reduced to a cited result", examined and **rejected**

The dispatch permits (ADEQ) to be reduced to a cited result rather than proved. Exactly one
landed Lean theorem is a plausible candidate, and it does **not** discharge the reduction. It is
recorded here so the reduction is not attempted again from the same premise.

`BiLasso/Extraction.lean:354` is a bounded-completeness theorem with an explicit closed bound:

```lean
theorem exists_annot_of_truth (hbx : BoxOracleSound P bx)
    (τ : WorldHistory P.toTaskFrame) (t : ℤ) (hφ : TruthAt P.toModel τ t φ) :
    ∃ A ∈ boundedAnnots P φ bx (bound P φ),
      ∃ i ∈ Finset.Ico (cohWindowLo A) (cohWindowHi A),
        A.lasso.unroll i = τ.state t ∧ φ ∈ A.label i
```

It is proved and sorry-free, with enumeration completeness
(`Enumerate.lean:153 mem_boundedBiLassos`, `:309 mem_boundedAnnots`) and the truth lemma
(`TruthLemma.lean:149 truth_along_annot`) beside it. **Three verified facts block the
reduction:**

1. **It is relative to a fixed finite presentation `P`.** Its hypothesis is
   `TruthAt P.toModel τ t φ` — truth in the model of a given `IntPresentation`, not in an
   arbitrary ℤ-time model. (ADEQ)'s hypothesis is the latter.
2. **Its bound is not a function of `|C|`.** `bound P φ := max (cycleBound P φ) (midBound P φ)`
   with `midBound P φ = 2 * (P.card * 2 ^ subformulaClosureCard φ)` (`Extraction.lean:284, 299`)
   — it depends on **`P.card`**, the size of the presented state space. A1 requires a bound
   computable from `|C|` alone.
3. **The missing premise is exactly the one `Probe476.fmp_false` refutes.** To get from (2) to a
   `|C|`-bound one would need "every ℤ-time countermodel is realized in a finite
   `IntPresentation` whose `card` is bounded in `|C|`" — the finite-presentation small-model
   hypothesis, machine-refuted (`specs/archive/476_.../evidence/fmp-hypothesis-is-false.lean`).
   `BoxOracleSound`'s own docstring (`Annotation.lean:350-355`) says as much in terms:
   constructing an oracle meeting that specification "requires the small-model theorem and is
   deliberately deferred".

So `exists_annot_of_truth` is the **template** for A1, not a reduction of it — which is precisely
how task 184's report 02 §3 already classified it ("the within-one-presentation version … must be
re-run over subformula-set space rather than presentation states"), and how BimodalLogic task
623's own description names it. This report confirms that classification against the source and
records the reduction as **rejected**.

**What would have to be true for a reduction to go through** (state this, do not attempt it):
(i) an analogue of `exists_annot_of_truth` whose hypothesis is `¬ SemanticConsequenceIn
FrameClass.ZTime Γ σ` rather than truth in a presented model; (ii) a bound depending only on
`|closureOf (Γ ++ Δ)|`, obtained by running the compression over **subformula-set space**
(where the pigeonhole is `2^|C|`, closed) instead of over presentation states (where it is
`P.card`, unbounded); and (iii) a demonstration that ModelChecker's Z3 search enumerates the same
family space at a segment length at least that bound. **(iii) is currently unbuildable**: there
is no certificate export and no independent re-checker in this repository at all (`grep -rin
certificate` returns zero matches across both trees, §7.2), so there is nothing whose enumeration
could be compared. (i) and (ii) are BimodalLogic task 623 item 1; (iii) is §8.3's A2-triangle
test, which becomes meaningful once 184's Phases 3–5 land.

#### 8.2 A0 — the frame-class gap, a permanent limit A1 cannot close

The paper's `def:logical-consequence` (`:1124`, `:3236`) quantifies over **every** model, hence
every temporal order. (SOUND) delivers refutation at that generality — the certified frame is one
particular task frame, and one countermodel suffices. **(ADEQ) does not run the other way.**

`FrameClass.ZTime.Sat F = F.IsRegular ∧ F.IsZTime` is strictly stronger than
`FrameClass.Base.Sat F = F.IsRegular`, so `ValidZTime ⊋ ValidBase`. Two axioms are classified
minimum-frame-class `.ZTime` in `ProofSystem/Axioms.lean:612-613`:

- `Axiom.prior_UZ φ : Fφ → (¬φ U φ)` (`Axioms.lean:341`) — "every definable future set has a
  least element"; the development cites Reynolds 1992 §10, Venema 1993 axiom (W).
- `Axiom.z1 φ : G(Gφ → φ) → (FGφ → Gφ)` (`Axioms.lean:353`) — the `IsSuccArchimedean`
  characteristic axiom; Doets 1987 Claim 10, Reynolds 1994 §10.

By (SOUND), **no certificate can ever exist for these**: any certificate would exhibit a ℤ-time
countermodel, contradicting their ℤ-time validity. Yet as the development's own classification
records, they are not Base-valid — a paper countermodel exists at a non-discrete temporal order
(e.g. `D = ℚ`). So the search is, *by design and permanently*, silent on a nonempty class of
paper-invalid inferences, independently of A1, A2 and A3.

**Consequence for the (ADEQ) statement.** (ADEQ) is stated at frame class ℤ-time and must stay
there. Even fully proved, it upgrades "no certificate within bounds" to "ℤ-time valid", never to
"valid". This is a second, independent reason for 184's D8, and one the plan does not currently
record.

**Deciding test for A0** (new; the plan does not carry it): run the search on
`\Future A \rightarrow (\neg A \Until A)` and on the `z1` instance. Both must report no
certificate at every configured length, and both must be rendered **inconclusive**, never as
validity. A rendering that says "valid" on either is a reportable defect. (A confirming
ℚ-countermodel for each, if wanted, is Lean-side work outside this task's scope; the
classification in `Axioms.lean` is cited here, not re-derived.)

#### 8.3 A2 — encoding completeness, and the deciding test that discharges it now

A2 holds iff the Z3 constraint set is **exactly** the conjunction of (C1)–(C4) over windows at
least as wide as §4.1's, with no extra constraint. It is testable today, without A1, by a
three-way differential at the smallest lengths:

> **Test (A2-triangle).** Fix `back = mid = fwd = 1` and a closure `C` with `|C| ≤ 4`.
> Exhaustively enumerate every candidate `(bx, Λ₀, …, Λ_k)` over subsets of `C` at those lengths.
> For each, compare three verdicts: (i) the Python re-checker, (ii) `lake exe
> check_certificate`, (iii) whether the Z3 encoding, run at those lengths on the same `Γ/Δ`,
> reports SAT.
> - (i) ≠ (ii) localizes a re-checker defect (Gap 1's second half).
> - (iii) false where (i) = (ii) = `countermodel` localizes an **encoding incompleteness**: a
>   constraint the encoder imposes that (C1)–(C4) do not require.
> - (iii) true where (i) = (ii) = `rejected` localizes an **encoding unsoundness** — caught at
>   run time by §7.2's fail-fast hook, but this test finds it in the suite instead.

This test is small, exhaustive, and belongs in 184's Phase 5 or a sibling. It is the concrete
"deciding test" the dispatch asks (ADEQ) to name for the component that is discharge-able now.

#### 8.4 Why ℤ-time only, recorded rather than assumed

Three independent reasons, all verified:

1. **Finite carriers force static frames over dense Archimedean orders** (184 report 01 §2): with
   finite `W` the cones `(w)_x` form a decreasing family of subsets of a finite set, so they
   stabilize; *Limit* then forces every small-duration fibre to `{w}` and *Compositionality*
   propagates identity to every duration. Every possible world is constant and no valid formula
   is refutable. This is about finite `W` and does not directly apply to the certificate design,
   whose `W` is infinite — but it is why a *finite-frame* search cannot be lifted to dense time.
2. **The truth lemma's `U` case is a finite descent** (§3, Lemma 4 remark): the `(⇒)` direction
   inducts on `s − t ∈ ℕ`. Over a dense order this induction does not exist, and the fixpoint law
   (C1) no longer determines the eventuality's label from its witness. This is a reason internal
   to *this* proof and is the sharper one.
3. **The window collapse is a `ℤ`-periodicity argument** (§4.1): `lab_sub_back_length` /
   `lab_add_fwd_length` are statements about `Periodic.unrollOf` over `ℤ`. Dense-time
   certificates would need a different finite presentation (mosaic- or region-style), not a
   re-tuned window.

Dense and continuous time are therefore out of scope for cause, not by fiat.

### 9. Relationship to task 184, settled

**Verdict: option (a).** This task is the adequacy layer over the certificate redesign and should
depend on it. It **subsumes no phase** of 184's plan.

#### 9.1 Justification

184's three reports establish *what to search for* and *why the current encoding is replaced*;
its plan is 24 phases of implementation. Neither states (SOUND) or (ADEQ), neither restates the
proof, and the plan cites the Lean theorems only as background ("Research Integration", "D1",
"D7"). Conversely, nothing in this report re-specifies the searched object, the wire format, the
settings, or the phase structure — those are 184's, and this report takes them as fixed.

#### 9.2 What this task contributes, and which of 184's phases the theorem constrains

| Contribution | 184 phases constrained | Nature of the constraint |
|---|---|---|
| **The corrected collapse windows** (§4.1) | **Phase 4** (pure-Python re-checker), **Phase 8** (fulfilment + box-faithfulness constraint generators), **D7** | Hard correction: `[−2·nb, nm+2·nf)` for (C1) and (C2), `[−nb, nm+nf)` for (C3). **D7 must be amended before either phase is dispatched.** |
| **The window-discriminating fixture** (§4.1) | **Phase 4**, **Phase 5** | New required negative fixture: (C2) failing only in `[−2nb,−nb) ∪ [nm+nf, nm+2nf)` |
| **The A2-triangle test** (§8.3) | **Phase 5** (round-trip) | New test; extends the two-way round-trip to a three-way differential including the encoder |
| **The A0 frame-class test** (§8.2) | **Phase 9** / **Phase 12** (never-report-validity), **Phase 16** (expectation audit) | New test: `prior_UZ` and `z1` instances must render inconclusive |
| **Obligation S4, the translation bridge** (§6.4) | **Phase 2** (Sentence→Formula translation) | New: a truth-preservation test Phase 5 structurally cannot provide |
| **The theorem itself**, §3, for the theory docs | **Phase 22** (documentation rewrite) | The docs must carry the statement, the four lemmas, and the Lean citation table of §3.6, replacing the retired frame-axiom ledger |
| **The fail-fast re-check hook's role** (§7.2) | **Phase 12** | Recast: the hook is not a safety net, it is the mechanism discharging (SOUND)'s obligation S3 |
| **Gap 2's real obstruction** (§4.2) | **D9**, **Phase 3** (datatype) | The forward-compatibility note must cite `total_eq_orbit` and the Box case, not Limit/Saturation |
| **MF's expectation and comment** (§6.3) | **Phase 16**, **Phase 17** | The audit's source of truth for MF is `modal_future_valid` + `no_witnessFamily_of_MF`, both cited |
| **(ADEQ)'s status and reduction** (§8) | **Phase 22**, and the follow-on tableau-oracle task | Recorded as open, reduced to A1/A2/A3 with A0 as a permanent limit |

#### 9.3 One scope note on `oracle/bimodal_logic/`

The dispatch's scope includes `oracle/bimodal_logic/`. Verified: it is **not** a differential
oracle against the Lean development. `provider.py` constructs the very same
`BimodalSemantics`/`ModelConstraints`/`BimodalStructure` pipeline (docstring at
`provider.py:180-190`), and the README states plainly that the package "is **not** independent of
`model_checker`". The genuinely independent second oracle is `bimodal_harness`, a sibling
checkout never in CI. `ground_truth.py` is a brute-force adjudicator over a `[-window, window]`
radius with five primitive tags and **no box case**, so it cannot adjudicate anything modal under
either the old or the new semantics. Its residual use is §6.4's tense-half translation check. The
provider rewrite and the manifest regeneration are 184's Phases 20–21; this report adds no
oracle work beyond §6.4.

## Decisions

- **D-187-1.** (SOUND) is stated as §2 and proved as §3. Its proof is restated in full here per
  the dispatch, and each step is mapped to its landed, sorry-free Lean counterpart (§3.6). The
  residual obligation is the transcription audit of §3.7, discharged by inspection and recorded
  as an audit rather than claimed as a theorem.
- **D-187-2.** Obligation S3 is discharged by **deciding** (SOUND)'s antecedent on every reported
  countermodel, twice and independently (§7.2), not by proving the Z3 encoder correct. This is
  the design's architectural commitment and the reason the re-checker is a deliverable.
- **D-187-3.** Gap 1 is closed by the machine-checked window collapses, and the proved windows
  are `[−2·nb, nm+2·nf)` for (C1)/(C2) and `[−nb, nm+nf)` for (C3). **Task 184's D7 is wrong and
  must be amended before Phases 4 and 8.** This is the single highest-value output of this
  report.
- **D-187-4.** Gap 2 is closed and re-scoped: the blocker to state-sharing is `total_eq_orbit`
  and the Box case of Lemma 4, not Limit and Saturation. 184's D9 stands, with its rationale
  corrected.
- **D-187-5.** (ADEQ) is **recorded as open**, reduced to A1 (BimodalLogic 623 item 1, open,
  route and literature cited), A2 (testable now, §8.3) and A3 (vacuous until A1), with A0 as a
  permanent frame-class limit. It is **not asserted** anywhere. ModelChecker must never report
  validity.
- **D-187-5a.** The "reduce to a cited result" branch is **closed negatively**:
  `BiLasso/Extraction.lean`'s `exists_annot_of_truth` is presentation-relative and its bound
  depends on `P.card`, so it is the template for A1, not a reduction of it (§8.1a). The three
  conditions under which a reduction *would* go through are stated there, and the third of them
  is unbuildable today because no certificate export or re-checker exists in this repository.
- **D-187-6.** Relationship to 184: **option (a)**. This task is the adequacy layer, depends on
  184, and subsumes none of its phases. Its own implementation surface is narrow: the D7
  correction (routed into 184 as a plan amendment), the three new tests (§4.1 fixture, §8.3
  A2-triangle, §8.2 A0), the S4 translation bridge (§6.4), and the theory-doc statement of the
  theorem (§9.2).
- **D-187-7.** ℤ-time only, for three recorded reasons (§8.4), the sharpest being internal to
  Lemma 4's `U` case. Dense and continuous time need a different finite presentation, not a
  re-tuned bound.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| D7's narrow window is implemented before the correction lands, and the §4.1 fixture is not written, so unsound certificates pass silently | **H** | **M** | Amend D7 as a plan revision to 184 *now*, while it is `[NOT STARTED]`; make the discriminating fixture a Phase 4 acceptance criterion |
| The Sentence→`Formula` translation is wrong (argument swap, or a defined operator unfolded incorrectly) and Phase 5's round-trip reports green regardless | **H** | **M** | §6.4's property test against a direct evaluator; note that `ground_truth.py` covers only the tense half |
| (ADEQ) drifts into an assertion once A1 lands, and A0 is forgotten | **M** | **M** | §8.2's `prior_UZ`/`z1` test is a standing regression that makes A0 observable; D8's never-report-validity is restated with two independent grounds |
| The Lean development's field names change and the exporter breaks silently | **M** | **L** | `WitnessFamily/Basic.lean` and `BimodalTools/README.md` both declare the names a breaking-change contract; a field-presence check in the Python exporter is cheap |
| The transcription audit (S2) is treated as proved rather than inspected, and a future Lean refactor moves a definition away from the paper | **M** | **L** | §3.7 records the audit as an audit, with paper line numbers, so it can be re-run mechanically against the same anchors |
| MF's expectation flip is read as weakening the suite rather than correcting it | **L** | **M** | §6.3 cites `modal_future_valid` (valid at the unrestricted class) and `no_witnessFamily_of_MF` (no certificate at any length); the old comment is deleted, not softened |
| Lasso state-sharing is added later for the stability modal on the strength of a weakened Limit argument | **M** | **L** | §4.2 records that the blocker is `total_eq_orbit` and the Box case, so a Limit-only repair cannot suffice |

## Appendix

### A. Verification commands run

```
grep -c sorry FormalSystem/Semantics/ShiftSet.lean \
              FormalSystem/Metalogic/Decidability/WitnessFamily/Agreement.lean \
              FormalSystem/Metalogic/Decidability/WitnessFamily/Decide.lean     # all 0
grep -rn "^axiom " FormalSystem/ BimodalTools/ --include=*.lean                 # prose only
grep -rin certificate code/src/model_checker/theory_lib/bimodal/ oracle/        # 0 matches
grep -rn "self\.M *=" code/src/model_checker/theory_lib/bimodal/                # 2 copies only
grep -n "IntVal(-self.M\|IntVal(self.M" .../bimodal/semantic/core.py            # 1051,1117,1639,1641,1740,1741
```

### B. Paper anchors consulted, by line

`:940-942` (motivation), `:948-961` (temporal order + group footnote), `:968-974` (reflection
convention; Fiber, Cone, Segment), `:989-994` (task frame; Compositionality, Seriality, Limit,
Saturation), `:1000-1009` (partial history, nesting, Saturation's role), `:1026-1031` (convex and
world history; the unboundedness footnote; `thm:extension`, `cor:occurrence`), `:1050-1058`
(`H_F`, Time-Shift, Possible World), `:1063-1076` (model of `BL`; the six semantic clauses),
`:1078-1085` (derived `Past`/`Future`/`Next`/`Previous`), `:1124` (Logical Consequence),
`:1136-1141` (the SP1 proof), `:3190-3223` (`def:time-shift-histories`, `app:auto_existence`
with proof, `lem:history-time-shift-preservation` with proof), `:3236-3248`
(`def:logical-consequence`, `def:frame-validity`), `:3043-3081` (`lem:step`, `thm:extension`,
`cor:occurrence`).

### C. Lean anchors consulted

`Semantics/TemporalOrder.lean:83-99`; `Semantics/TaskFrame.lean:2571-2680`;
`Semantics/Truth.lean:225-240`; `Semantics/Validity.lean:80-92, 555`;
`Semantics/FrameClassValidity.lean:151-156`; `Semantics/ShiftSet.lean:30-55, 88-115, 140-171,
197-236, 252, 284, 383-410, 500-543`; `Metalogic/Soundness.lean:371-380`;
`ProofSystem/Axioms.lean:335-356, 540-560, 595, 612-613`;
`Metalogic/Decidability/WitnessFamily/{README.md, Basic.lean:76-201, Predicates.lean:70-127,
Std.lean:55-115, Agreement.lean:61-247, Decide.lean:10-75, 185-235, 316-400, 700-800, 865-930,
Examples.lean:240-283}`; `Semantics/IntNormalForm.lean:450-505` (`ofStep`, finite-`W` only);
`Metalogic/Decidability/BiLasso/{Extraction.lean:270-375, Annotation.lean:350-358,
BoxOracle.lean:12-62}`; `BimodalTools/README.md` (tableau bridge + certificate protocols).

### E. Two supplementary claims received and corrected against source

Both arrived as peer-survey input and were checked before use; each is wrong in a way that
would have propagated into the report:

1. *"`IntNormalForm.ofStep` already mechanizes the (SOUND) construction's frame-condition
   discharge for ℤ-time."* **False.** `ofStep` carries `[Finite W]` and discharges Saturation by
   `saturation_of_finite` (`IntNormalForm.lean:456, 488`). The certified carrier is infinite.
   Corrected in §3.6.
2. *"`exists_annot_of_truth` is a live candidate for reducing (ADEQ) to a cited result."*
   **False as a reduction.** It is presentation-relative and its bound depends on `P.card`
   (`Extraction.lean:284, 299, 354`). Corrected, with the conditions for a genuine reduction
   stated, in §8.1a.

### D. Prior-art artifacts read in full

`specs/184_.../reports/01_finite-certificate-redesign.md`,
`02_partial-model-formal-results.md`, `03_bimodallogic-665-668-alignment.md`, and
`plans/01_witness-family-certificate-redesign.md` (overview, D1–D9, goals/non-goals, dependency
waves, Phases 4, 5, 10, 12).
