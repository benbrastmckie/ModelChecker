# Partial models for Z3 and the formal results that turn them into standard models

- **Task**: 184 - Refactor bimodal theory tests green and paper lean aligned
- **Started**: 2026-09-24T18:25:00Z
- **Completed**: 2026-09-24T18:40:00Z
- **Effort**: about 0.5 hours (follow-up to `01_finite-certificate-redesign.md`)
- **Dependencies**: `01_finite-certificate-redesign.md`
- **Sources/Inputs**:
  - `~/Projects/BimodalLogic/FormalSystem/Semantics/ShiftSet.lean` (`ShiftSet`, `frame`, `model`, `hist`,
    `total_eq_orbit`, `forward_repr`)
  - `~/Projects/BimodalLogic/FormalSystem/Semantics/Validity.lean` (`ConsequenceOnFrames`,
    `SemanticConsequenceIn`, `ValidZTime`), `Semantics/FrameClassValidity.lean` (`Sat.anti`)
  - `~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/BiLasso/` (`Basic.lean` `BiLasso`/`unrollOf`,
    `Periodic.lean`, `Annotation.lean` `LocalCoherent`/`Fulfilling`/`BoxOracleSound`, `Unfold.lean`,
    `TruthLemma.lean` `truth_along_annot`, `Decide.lean`, `Extraction.lean` `exists_annot_of_truth`,
    `Agreement.lean`, `Assembly.lean`)
  - `~/Projects/BimodalLogic/specs/archive/476_.../evidence/fmp-hypothesis-is-false.lean`; `specs/TODO.md` task 623
- **Artifacts**: this report
- **Standards**: report-format.md

## Executive Summary

- The question "given a finite partial model found by Z3, is there a standard model satisfying the
  same sentences?" has a clean answer once the partial model is defined correctly: a **labelled
  bi-lasso family**. Its standard model is a `ShiftSet` over `intOrder`, which BimodalLogic already
  defines together with its task frame, model, and histories. No Zorn-style extension is involved:
  a labelled bi-lasso *decodes* to a total history (`BiLasso.unrollOf`), and the conditions on the
  labels are what make the decoded histories' truth coincide with the labels.
- Two definitions that look natural are wrong and are ruled out by machine-checked results:
  a finite window of a history (Agreement.lean's three limits: nothing about Box or about tense
  claims outside the window transfers, and path periodicity is not truth periodicity), and a finite
  digraph with all-paths semantics (`Probe476.fmp_false`).
- The theorem ModelChecker needs is the **soundness half** of BimodalLogic task 623: labelled family
  satisfying the four conditions ⇒ its ShiftSet model agrees with the labels on the closure ⇒ the
  consequence Γ ⊨ σ fails over Z-time frames (and hence over all task frames). Everything else it
  consumes is landed. Recommend splitting that half out of 623 as its own task so it lands first;
  623 keeps the completeness half (compression) and decidability.

## Context & Scope

Follow-up to the redesign report, answering the user's question about which formal results should be
checked in BimodalLogic before ModelChecker's redesign is planned, how partial models should be
defined, and how they are extended to or realized by standard models already defined there. Scope:
discrete (Z) time, the language without the stability modal.

## Findings

### 1. The partial model: a labelled bi-lasso family

Fix premises Γ and conclusions Σ, and let `C := subformulaClosure` of Γ ∪ Σ.

**Labelled bi-lasso.** `back, mid, fwd : List (Finset Formula)` with `back ≠ []`, `fwd ≠ []`, every
label a subset of `C`. It decodes to `L : ℤ → Finset Formula` by the three-segment scheme of
`BiLasso.unrollOf` (`BiLasso/Basic.lean:127`; `Periodic.lean` already states the decoding at an
arbitrary inhabited type): `back` repeated strictly left of 0, `mid` on `[0, |mid|)`, `fwd` repeated
from `|mid|`. The origin is pinned, as in `BiLasso`.

**Family.** A box guess `b : Formula → Bool` (read only at `χ` with `□χ ∈ C`) and lassos
`Λ₀, …, Λ_k`. Conditions:

1. **Local coherence** (label-space `LocalCoherent`, `Annotation.lean:301` minus the atom and
   presentation clauses): for every `i, t`: `⊥ ∉ L_i t`; `(a → b) ∈ L_i t ↔ (a ∈ L_i t → b ∈ L_i t)`;
   `□χ ∈ L_i t ↔ b χ`; `(g U e) ∈ L_i t ↔ e ∈ L_i (t+1) ∨ (g ∈ L_i (t+1) ∧ (g U e) ∈ L_i (t+1))`;
   dually for `S` with `t-1`. Atoms are unconstrained: the valuation *is* the atom part of the label.
2. **Fulfilment** (`Fulfilling`, `Annotation.lean:336`, verbatim): every `(g U e) ∈ L_i t` has
   `s > t` with `e ∈ L_i s` and `g` on `(t, s)`; dually for `S`.
3. **Box faithfulness** (new; replaces `BoxOracleSound`): `b χ = true ↔ ∀ i t, χ ∈ L_i t`, for each
   `□χ ∈ C`. Equivalently: every box guessed true holds at every position of every lasso, and every
   box guessed false has a position on some lasso where the argument is absent.
4. **Target**: some `t₀` with `Γ ⊆ L₀ t₀` and `Σ ∩ L₀ t₀ = ∅`.

All four are decidable on the finite data. Conditions 1 and 2 are periodic in each direction, so a
bounded window suffices (`Decide.lean`'s window collapses do exactly this for `Annot`). Condition 3
is a finite conjunction over one period of each lasso. Condition 4 is a finite search.

Why labels on *positions of histories* rather than on world states: two positions with equal
labels are distinct states of the standard model. Identifying them would add histories (the
recombined paths) over which Box would also range, which is precisely how `fmp_false` refutes the
finite-digraph route.

### 2. The standard model, already defined

Let `S : ShiftSet intOrder` with `Carrier := Fin (k+1) × ℤ`, `sh (i,t) d := (i, t+d)`,
`A p (i,t) := atom p ∈ L_i t`. `sh_zero`, `sh_add` are arithmetic; `sep` is trivial over ℤ (a shift
by `|d| < 1` is `d = 0`). Then:

- `S.frame : TaskFrame` with all six frame fields discharged (`ShiftSet.lean`'s header lists which
  are free under a functional relation); `S.model : TaskModel S.frame` (`ShiftSet.lean:236`).
- Its world histories are exactly the orbits `S.hist (i,0)` (`total_eq_orbit`), i.e. the lassos
  and their shifts. So Box in `S.model` ranges over exactly the certified histories.
- `S.frame` is in the Z-time class by `TaskFrame.isZTime_of_instances` (used this way in
  `fmp-hypothesis-is-false.lean`).

This is the "extension to a standard model already defined": the family *is* a finite presentation
of `S`; nothing is extended, only decoded.

### 3. The results to establish (and which are new)

| # | Statement | Status |
|---|---|---|
| T1 Agreement (soundness) | For a family satisfying 1–3: `∀ i t (χ ∈ C), TruthAt S.model (S.hist (i,0)) t χ ↔ χ ∈ L_i t` | **New.** Induction on `χ` through `ShiftSet.forward_repr`; `untl`/`snce` via `Unfold.lean`'s `truth_untl_succ`/`truth_snce_pred` plus condition 2, as in `truth_along_annot` (`TruthLemma.lean`), which is the single-lasso version relative to an oracle. The new step is that condition 3 makes `b` a sound oracle *for this model*, which is immediate because the model's histories are exactly the lassos. |
| T1′ Consequence corollary | Condition 4 ⇒ for every `σ ∈ Σ`, `¬ SemanticConsequenceIn .ZTime Γ σ` (`Validity.lean`), and by `FrameClass.Sat.anti` `¬ SemanticConsequenceIn .Base Γ σ`; plus the joint form `∃ F ∈ ZTime, M, τ, t, (∀ γ ∈ Γ, TruthAt M τ t γ) ∧ (∀ σ ∈ Σ, ¬ TruthAt M τ t σ)`, which is what ModelChecker reports | **New**, a few lines given T1. Mirrors `not_validZTime_of_satAtState` (`Assembly.lean:58`). |
| T2 Decidability of conditions 1–4 | `Decidable` instances computing by bounded window scans | **New**, adapting `Decide.lean` from `Annot` to the presentation-free lasso. Gives `#eval` re-verification and the `check_certificate` executable. |
| T3 Non-vacuity | A family for `□(p ∨ Fp ∨ Pp) ∧ □(p → ¬Pp)` (one lasso, `p` only at 0) checked by T2; a negative check that no family exists for the negation of MF at small bounds | **New**, small; `Examples.lean` is the precedent. |
| T4 Completeness (compression) | `¬ SemanticConsequenceIn .ZTime Γ σ` ⇒ a family exists with segment lengths bounded in `|C|` | **Open**; this is 623 proper. `exists_annot_of_truth` (`Extraction.lean:354`) is the within-one-presentation version; `validIn_iff_recurrenceFree` lets the witness paths be taken recurrence-free. Needed for decidability and to make "no certificate within bounds" informative; not needed for ModelChecker's soundness. |

Already landed and consumed as is: `ShiftSet.frame/model/hist/forward_repr/total_eq_orbit`,
`Truth.box_const`, `BiLasso.unrollOf`/`Periodic.lean` decoding, `Unfold.lean`,
`Fulfilling`, the window-collapse lemmas in `Decide.lean`, `TaskFrame.isZTime_of_instances`,
`SemanticConsequenceIn`, `FrameClass.Sat.anti`.

### 4. What "same sentences" means here

T1 gives agreement on the **closure** at corresponding points, which is what refuting Γ ⊨ Σ needs.
Sentences outside the closure are not determined by the labels and no claim is made about them.
This is the honest form; a full elementary-equivalence claim would be false and is not needed.

## Decisions

- The partial model is the labelled bi-lasso family of section 1, searched by Z3 directly as
  Boolean label variables over fixed segment lengths. ModelChecker never searches windows and never
  relies on `thm:extension` or `extend_periodic` for truth; those results are about frames whose
  path set is not controlled.
- The standard model is the `ShiftSet` of section 2; no new frame construction is needed in Lean.
- ModelChecker's correctness claim is T1′'s joint form at the Z-time class, with Base following by
  antitonicity.

## Recommendations

**BimodalLogic (`~/Projects/BimodalLogic/specs/TODO.md`)**

1. **Create** "Witness-family certificates: soundness" carrying T1, T1′, T2, T3. Deliverables: a
   presentation-free `LabelledLasso` and `WitnessFamily` structure with the four conditions; the
   `ShiftSet` construction `WitnessFamily.std`; the agreement theorem; the consequence corollaries at
   ZTime and Base in both single-conclusion and joint form; computable `Decidable` instances; the two
   examples. No dependencies. Estimated one to two weeks against 623's three to six.
2. **Revise 623** to depend on the new task and to keep only T4 (compression) and the
   `Decidable (ValidZTime φ)` assembly, dropping the soundness deliverables it currently lists; keep
   its docstring corrections to `Assembly.lean` and the BiLasso README.
3. **Create** `lake exe check_certificate` (JSON family in, verdict out) depending on task 1; this
   was already recommended in the redesign report, now with a precise input definition.
4. Keep the bridge-gates task from the redesign report; unchanged.

**ModelChecker**

5. No further revision to 184's description is needed: it already names the certificate per the
   redesign report, and section 1 above is the precise definition the planner should import. The
   plan for 184 should state that Z3 variables are label bits per lasso position plus the guess,
   with segment lengths iterated, and that the JSON export mirrors `LabelledLasso`/`WitnessFamily`
   field for field.
6. The certificate-export task (redesign report, New B) depends on BimodalLogic tasks 1 and 3.

## Risks & Mitigations

- **Risk**: naming drift between the Python JSON and the Lean structure. **Mitigation**: define the
  Lean structure first (task 1) and generate the Python dataclass names from it.
- **Risk**: T4 turns out harder than estimated and "no certificate within bounds" stays
  uninformative for longer. **Mitigation**: ModelChecker's soundness does not depend on T4; validity
  claims are routed to the tableau and proof system.
