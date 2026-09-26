# Redesigning the bimodal theory around finite certificates (discrete time)

- **Task**: 184 - Refactor bimodal theory tests green and paper lean aligned (sequencing gate for all bimodal work)
- **Started**: 2026-09-24T17:10:00Z
- **Completed**: 2026-09-24T18:20:00Z
- **Effort**: about 1.5 hours (paper and Lean source reading, two codebase surveys, design)
- **Dependencies**: none
- **Sources/Inputs**:
  - `~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` (`app:TaskSemantics`, `thm:extension`,
    `def:BL-semantics`, `lem:history-time-shift-preservation`)
  - `~/Projects/BimodalLogic/FormalSystem/` (`Semantics/IntNormalForm.lean`, `Semantics/ShiftSet.lean`,
    `Semantics/Extension/PeriodicExtension.lean`, `Metalogic/Decidability/IntPresentation.lean`,
    `Metalogic/Decidability/BiLasso/*`, `Metalogic/Decidability/Verified/*`)
  - `~/Projects/BimodalLogic/specs/archive/476_box_faithful_small_model_theorem/evidence/fmp-hypothesis-is-false.lean`
    and `~/Projects/BimodalLogic/specs/TODO.md` task 623
  - `code/src/model_checker/theory_lib/bimodal/`, `oracle/bimodal_logic/`
- **Artifacts**: this report
- **Standards**: report-format.md
- **Scope decision (user)**: discrete time (Z-time) only. Dense and continuous time are future work.

## Executive Summary

1. **Over Z-time, a finite task frame is a finite bi-serial digraph.** Compositionality makes every
   duration relation a power of the unit step, Limit makes the zero-duration relation identity,
   Seriality makes the step relation serial and co-serial, and Saturation is automatic for finite W
   (`cor:saturation-finite`). BimodalLogic already formalizes this as the Z-frame normal form
   (`FrameOver.taskRel_eq_iter`, `mem_HF_iff_adjacent`) and the computational presentation
   `IntPresentation`. The worry that finite models force a trivial task relation is unfounded for
   Z-time. (It is exactly right for dense Archimedean time, where finite W forces the identity
   relation; that is one reason to defer dense time.)

2. **But finite digraphs with all-paths semantics are incomplete for TM_z.** This is machine-checked:
   `Probe476.fmp_false` refutes `∀ φ, ¬ValidZTime φ → ∃ P ∈ cands φ, ∃ w, SatAtState P w φ.neg` for
   every candidate list. Witness: `□(p ∨ Fp ∨ Pp) ∧ □(p → ¬Pp)` is satisfiable over Z-time (carrier
   Z, p only at 0) but on any finite digraph a pumped p-free cycle is itself a history. Because Box
   quantifies over all bi-infinite paths of the frame, countermodels need infinitely many world
   states in general.

3. **The finite object to search for is therefore a *witness family*, not a finite frame**: a guess
   of the truth value of each boxed subformula, plus finitely many annotated bi-lassos (ultimately
   periodic in both directions, each position labelled by a subset of the subformula closure),
   satisfying local coherence and fulfilment. The full model is the ShiftSet whose carrier is the
   disjoint union of the lassos' (index, time) points: infinitely many world states, infinite
   durations, box-faithful by construction. This is precisely the certificate that BimodalLogic
   task 623 ("Decidable ValidZTime via the quasimodel / ShiftSet witness-family route") plans to
   prove sound and complete. It is also exactly the "partial model that is a fragment of a full
   model" the user asked for.

4. **The current Z3 encoding should be replaced, not tuned.** It evaluates tense operators over a
   bounded window with acknowledged boundary vacuity, lets Box range over a finite set of window
   histories, and patches with abundance/shift-closure constraints. It refutes the paper's own
   bimodal axiom MF (`MF_MODAL_FUTURE_TH` is excluded from tests because a countermodel is found at
   N=1, M=2), the perpetuity theorems depend on abundance, nine examples are excluded as timeouts,
   and every open test-reliability task chases the cost of those constraints.

5. **Task consequences.** Revise 184 into the certificate redesign; abandon 154, 172, 176, 178, 183
   (all point-fixes on machinery being deleted); add a tableau-oracle task and a certificate-export
   task in ModelChecker; in BimodalLogic, prioritize 623 (its dependencies are complete) and add a
   certificate re-verification tool task depending on it. Details in sections 5 and 6.

## Context & Scope

The user's aim is to redesign the bimodal theory in ModelChecker so that it constructs finite
models of the appropriate kind, given that every partial history over a task frame extends to a
possible world (`thm:extension`). This report reviews the open bimodal tasks, the current Z3
encoding, the paper's task semantics, and the BimodalLogic formalization, and settles what the
finite object to search for must be, why the current encoding is replaced rather than repaired,
how the tableau should be used, and which tasks to revise, add, or abandon. The user restricted
scope to discrete time; dense and continuous time are recorded as future work.

## Findings

### 1. What the paper and the Lean development already establish

| Fact | Paper | Lean (BimodalLogic) |
|---|---|---|
| Task frame on finite W over Z is a bi-serial digraph; `⇒_n = step^n`, `⇒_0 = id` | `def:frame`, `lem:nullity`, `cor:saturation-finite` | `Semantics/IntNormalForm.lean`: `FrameOver.taskRel_eq_iter`, `FrameOver.mem_HF_iff_adjacent`, `TaskFrame.ofStep` (all seven frame fields from a bi-serial relation) |
| Every partial history extends to a possible world | `thm:extension` (Zorn) | `Semantics/Extension/Extension.lean`; Saturation redundant over Z (`Extension/Completion.lean`) |
| Effective extension: a finite window extends to a doubly ultimately periodic possible world with both periods ≤ card W, as a finite object | (not stated) | `Semantics/Extension/PeriodicExtension.lean`; `IntPresentation.extend_periodic`, `extend_periodic_of_icc` (`BiLasso/Orbit.lean:805,858`) |
| Box is the universal modality: its value is independent of history and time | `lem:history-time-shift-preservation` + `(□)` clause | `Truth.box_const`, `Truth.box_time_const` |
| A presented Z-frame countermodel refutes `ValidZTime` with no bridge lemma | — | `not_validZTime_of_satAtState` (`BiLasso/Assembly.lean:58`) |
| Truth at a state of a *given* finite digraph is decidable | — | `check` / `check_correct` (`BiLasso/Check.lean`), via annotated bi-lassos: `LocalCoherent`, `Fulfilling`, `BoxOracleSound`, truth lemma `truth_along_annot` |
| Window agreement licenses `Extends` and nothing about Box or about Past/Future outside the window | — | `BiLasso/Agreement.lean` (three limits, each cited) |
| Finite digraphs are incomplete for TM_z | — | `Probe476.fmp_false` (archived task 476 evidence) |
| Validity over Z-frames equals validity over recurrence-free Z-frames | — | `validIn_iff_recurrenceFree` (`Semantics/Frames/TranslationProduct.lean:613`) |
| Shift sets represent task models both ways, with truth transfer | — | `ShiftSet.forward_repr`, `ShiftSet.reverse_repr` (`Semantics/ShiftSet.lean`) |
| Tableau: `isValid φ fc = true → ⊨ φ` proved; open saturated branch gives a Z-carrier countermodel with a truth lemma; completeness direction open | — | `Decidability/Correctness.lean`, `Verified/Bridge/IntTruth.lean`; open: tasks 410–412, 428–430, 482 |

Two consequences shape the design:

- **Over Z-time, "finite model ⇒ genuine model" needs no new theorem.** A finite bi-serial digraph with
  a valuation *is* a task frame model over Z (`IntPresentation.toModel`), and its refutation of
  `ValidZTime` is `not_validZTime_of_satAtState`. Durations are already infinite.
- **Completeness needs a different finite object.** By `fmp_false`, the search must range over
  witness families whose full model has infinitely many states. Task 623 is that theorem.

### 2. The trivial-frame worry, resolved by temporal order

- **Z-time.** Finite W supports every serial and co-serial relation: total relations, cycles, a
  looping state feeding another looping state. Possible worlds are the bi-infinite paths (in general
  uncountably many). Nothing is trivial. What is *incomplete* is the class of finite digraphs as
  countermodels (section 1, `fmp_false`), which is a different problem with a different fix.
- **Dense Archimedean time (deferred).** With finite W the cones `(w)_x` form a decreasing family
  of subsets of a finite set, so they stabilize; Limit then forces every small-duration fibre to be
  `{w}`, and Compositionality propagates identity to every duration. The frame is static and every
  possible world constant, so finite models refute nothing valid on constant worlds (DF, DN, CO).
  Dense-time countermodel search needs finite *presentations* of infinite W (mosaic-style or
  region-style). Out of scope now; recorded so the scoping is justified rather than assumed.

### 3. Defects of the current encoding (why replace rather than repair)

Anchors are in `code/src/model_checker/theory_lib/bimodal/`.

- **Bounded time with boundary vacuity.** `ForAllTime`/`ExistsTime` (`semantic/core.py:505,578`)
  quantify over the window `(-M, M)`; `G φ` is vacuously true at the last window time. The
  `M ≥ d+2` rule is a sizing convention, not a semantics.
- **Box over a finite set of window histories.** `NecessityOperator.true_at` (`operators.py:508`)
  ranges over `is_world` ids; the paper's `(□)` ranges over all of `H_F`. Abundance/shift-closure
  (`capped_skolem_abundance_constraint`, `depth_bounded_skolem_abundance_constraint`) approximate
  the missing histories. Five dead abundance variants remain in `core.py`.
- **Spurious refutation of the paper's axiom MF.** `MF_MODAL_FUTURE_TH` (`□A → □GA`, `thm:MF-valid`
  in the paper) is excluded from the suite because the encoding finds a countermodel at N=1, M=2
  (`tests/unit/test_bimodal.py:35-37`). This alone shows the encoding is not a model of the paper's
  semantics.
- **Perpetuity theorems depend on the approximation.** `BM_TH_1`/`BM_TH_2` are valid only with M=3
  shift closure, 30 s budgets, and are excluded as too slow.
- **Phantom task pairs.** `task_restriction` is disabled for solver cost; SAT results are admitted
  to live in a larger frame class than the grounded one (`core.py:869-935`).
- **Cost and instability.** Every open test-reliability task (172, 176, 178, 183) chases rlimit
  growth from the Skolemized Seriality/Interpolation axioms and MBQI behaviour. The frame axioms
  are being asserted *inside* the search, which the Z-frame normal form makes unnecessary: over Z
  they are discharged by `TaskFrame.ofStep` from bi-seriality alone.
- **Inert scaffolding.** `WitnessRegistry`/`WitnessConstraintGenerator` are instantiated and never
  used; `iterate.py` performs no isomorphism rejection.

## Decisions

### 4. The redesign: witness-family certificates

#### 4.1 The searched object

Fix premises Γ and conclusions Σ; let C be the subformula closure of Γ ∪ Σ. A **certificate** is:

- a **box guess** `b : {χ : □χ ∈ C} → Bool`;
- a **main lasso** Λ₀ and, for each `□χ ∈ C` with `b χ = false`, a **witness lasso** Λ_χ (so at most
  1 + #boxes lassos; the same lasso may serve several boxes);
- each lasso Λ = `(back, mid, fwd)` with lengths `|back| ≥ 1`, `|mid| ≥ 0`, `|fwd| ≥ 1`, and a label
  `L(t) ⊆ C` at each position; positions left of the origin repeat `back`, `[0, |mid|)` is `mid`,
  positions at or after `|mid|` repeat `fwd` (the `Annot`/`BiLasso` shape of
  `BiLasso/Annotation.lean`, which pins the origin);

subject to:

1. **Local coherence** at every position (finitely many after periodic wrap), exactly
   `LocalCoherent`: `⊥ ∉ L(t)`; `(a → b) ∈ L(t) ↔ (a ∈ L(t) → b ∈ L(t))`; `□χ ∈ L(t) ↔ b χ`;
   `(g U e) ∈ L(t) ↔ e ∈ L(t+1) ∨ (g ∈ L(t+1) ∧ (g U e) ∈ L(t+1))`; symmetric for Since with `t-1`.
   Atoms are free: the valuation *is* the atom part of the label.
2. **Fulfilment** (`Fulfilling`): every `(g U e) ∈ L(t)` has a witness `s > t` with `e ∈ L(s)` and
   `g` on `(t, s)`; symmetric for Since. On a periodic annotation this is decided within a bounded
   window (`BiLasso/Decide.lean` has the exact collapse; for Z3 a scan of one period past the mid
   segment suffices).
3. **Box faithfulness**: for each `□χ` with `b χ = true`, `χ ∈ L(t)` at every position of every
   lasso; for each `□χ` with `b χ = false`, some position of some lasso has `χ ∉ L(t)`.
4. **Target**: some position `t₀` of Λ₀ has every γ ∈ Γ in `L(t₀)` and no σ ∈ Σ in `L(t₀)`.

#### 4.2 The full model it certifies

The ShiftSet with carrier `⊔_i {i} × Z`, action `sh (i,t) d = (i, t+d)`, valuation `p` true at
`(i,t)` iff `atom p ∈ L_i(t)`. Its task frame is deterministic (`TaskRel w d u := u = sh w d`);
Seriality, interpolation, Saturation and Limit are discharged in `ShiftSet.frame`. Its possible
worlds are exactly the orbits (`total_eq_orbit`), i.e. the lassos and their shifts, so Box ranges
over exactly the certified histories. The truth lemma "label = truth on this model" is the main new
proof of task 623 (`truth_along_annot` is the per-lasso half already landed relative to a sound box
oracle; condition 3 makes the guess a sound oracle for this model). Given it, `(Λ₀, t₀)` is a point
where Γ holds and Σ fails, so `Γ ⊭_Z Σ` and a fortiori `Γ ⊭ Σ` over all task frames. The model has
infinitely many world states and infinite durations, as the user's target statement requires.

Completeness (every Z-refutable inference has such a certificate, with bounds on lengths) is the
compression lemma of task 623, simplified by `validIn_iff_recurrenceFree`. ModelChecker does not
depend on it for soundness; it determines only whether "no certificate within the length bounds"
carries information. ModelChecker should never report validity; that is the tableau's and the proof
system's job (section 5).

#### 4.3 Why this shape

- **Sound by a theorem that is true on paper and planned in Lean**, with the certificate literally
  re-checkable by Lean's decidable `LocalCoherent`/`Fulfilling` instances once 623 lands its
  label-space variant.
- **Complete for the language without the stability modal** (623's target), whereas finite digraphs
  are not (`fmp_false`).
- **Quantifier-free.** Variables are Booleans `L[i][t][ψ]`, the guess `b`, and fixed segment lengths
  per iteration. No `ForAll`, no MBQI, no E-matching patterns, no rlimit tuning. Expected solve
  times are milliseconds for the current example set. Iteration is blocking clauses on labels.
- **Settings become formula-derived.** `N` (BitVec width) and `M` (window) disappear. Replace with
  maximum segment lengths (`back`, `mid`, `fwd`) and an optional cap on witness count; defaults
  small and increased on demand.
- **What is given up.** Certified frames are deterministic (no branching at a shared state). For the
  current language this is without loss (`validIn_iff_recurrenceFree`; 623's recommendation 2).
  For the stability modal `⊡` (open-future work) branching witness families are needed; that is the
  open problem of BimodalLogic's completeness research and must not be promised here. Design the
  certificate datatype so lassos *may* later share states, but do not implement sharing now.

#### 4.4 Output and framework fit

- **Printing.** Each history as `(back)^ω | mid | (fwd)^ω` of atom valuations with the evaluation
  position marked; a table of boxed subformulas with their guessed values; for each false box, the
  witness history and position. World states are (history, time) points; the task relation is the
  shift. Remove the "time-shift relations" and interval displays.
- **Operators.** `true_at`/`false_at` become label-constraint generators over positions; Box's
  generator introduces the guess variable and, when false, requests a witness lasso through the
  registry. The existing (inert) `WitnessRegistry`/`WitnessConstraintGenerator` is the natural home
  and should be rewritten, not deleted.
- **Iterate.** Difference constraints on labels and guesses; add isomorphism rejection modulo
  rotation of periodic segments and renaming of witness lassos.
- **Certificate export.** JSON in the `Annot` shape (segments of label sets, origin, guess) so
  BimodalLogic can re-verify it. A pure-Python re-checker of conditions 1–4, independent of the Z3
  model object, should run on every found model in tests.
- **Fixed-frame mode (later, optional).** Model checking a *given* finite dynamical system (a
  digraph) is a different feature; its reference is Lean's `check`. Not part of this refactor.

### 5. The tableau: together, not instead

BimodalLogic's `decide` (`Metalogic/Decidability/DecisionProcedure.lean`) returns a derivation
(`valid`, soundness machine-checked: `isValid_sound`), a countermodel from an open saturated branch
(`invalid`), or `fuelExhausted` / `extractionFailed`. An open saturated branch is proved to refute
Z-time validity (`not_validZTime_of_hasOpen_int`, `Verified/Bridge/IntTruth.lean:1073`) **only under
four decidable branch gates** (`timeOrderTotal`, `boxAnchoredCheck`, `regionLabelCheck`,
`temporalWitnessCheck`) that neither `decide` nor the bridge currently evaluates, so an `invalid`
verdict is theorem-backed only once those gates are run on the returned branch. It is rule-gated by frame class (Base, Dense, Z-time, Dedekind). It is exposed
as a JSONL REPL, `lake exe tableau_bridge` (`BimodalTools/TableauBridgeMain.lean`), with commands
`tableau_decide`, `countermodel`, `ping`.

Recommendation:

- **Use the tableau as the differential oracle** for the bimodal theory, replacing the current
  Z3-vs-same-Z3 self-consistency scan and the BimodalHarness Z3-vs-Z3 comparison (which is a third
  Z3 encoding, temporal-only, and unavailable in CI). Verdict matrix at frame class Z-time:
  ModelChecker `certificate` vs tableau `valid` is a ModelChecker bug (tableau soundness is proved);
  ModelChecker `none within bounds` vs tableau `invalid` is a bound shortfall, logged not failed,
  and only counts as evidence when the branch gates pass; `timeout` is inconclusive. Pass
  `frame_class` as `ZTime`; the bridge maps any unrecognized string (including `RTime`) to `Base`
  silently (`TableauBridgeMain.lean:297-302`), so the client must validate the tag itself. Keep `ground_truth.py` as a tie-breaker for the temporal-only
  fragment.
- **Do not replace ModelChecker with the tableau.** The tableau's completeness direction is open,
  its engine has a 50000-branch cap and fuel exhaustion, its countermodels are branch/region
  structures rather than the certificates of section 4, and it does not support iteration, theory
  comparison, or the Python ecosystem. The two are complementary: certificates for invalidity,
  derivations for validity.
- **Oracle-tree consequences.** `oracle/bimodal_logic/provider.py` is rewritten against the new
  semantics; `test_soundness_regression.py`'s abundance/shift-closure tests are deleted with the
  machinery; the known-conclusive manifest is regenerated; the `development` blanket and every
  `and not development` gating clause are removed when the refactor lands (this is the exit
  condition the CI comments already name).

## Recommendations

### 6. Task revisions

#### 6.1 ModelChecker (`specs/TODO.md`)

| Task | Action | Reason |
|---|---|---|
| 184 Refactor bimodal theory | **Revise** into "Redesign bimodal theory around witness-family certificates (Z-time)". Deliverables: new `semantic/` core (certificate encoding, sections 4.1–4.2), operators as label-constraint generators, model structure/printing per 4.4, iterate with isomorphism rejection, Python re-checker, examples migrated (restore `MF_MODAL_FUTURE_TH`, `BM_TH_1/2`, all nine excluded examples; expectations checked against the paper's axioms), theory docs rewritten (retire the frame-axiom ledger and the duration-guard gap note), `development` marker removed. Scope: Z-time; no dense time; no `⊡`. | Aims (1) and (2) of the current text both follow from the redesign; the current text still presumes the frame-axiom encoding is repaired rather than replaced. |
| 154 Extension-certified search | **Abandon** (or fold into 184 as a note). | Its deliverables assume the window-and-abundance design: the lasso *is* now the searched object, the polarity split and abundance disappear, and its warning about the existential/universal asymmetry is honoured by construction (box guess + faithfulness). |
| 172 Contention-flaky soundness tests | **Abandon**. | The three tests and their 5000 ms budgets belong to the encoding being deleted. |
| 176 M=3 shift-closure SAT regression | **Abandon**. | Shift closure no longer exists. |
| 178 Frame-axiom solver cost | **Abandon**. | Skolemized Seriality/Interpolation no longer exist; over Z they are discharged by bi-seriality. |
| 183 Gating shortfall discrimination | **Abandon**. | Measures the cost of the old encoding; manifest is regenerated under the new one. |
| 186 Counterfactual semantics review | Untouched. | Logos, not bimodal. |
| **New A** Tableau oracle for bimodal | **Add**, depends on 184. Wire `lake exe tableau_bridge` as an oracle provider (JSONL, frame class Z-time), verdict matrix per section 5, regenerate the conclusive manifest, retire the BimodalHarness comparison and the self-consistency scan, keep `ground_truth.py` as tie-breaker. | Replaces a Z3-vs-Z3 oracle with a Lean-proved one. |
| **New B** Certificate export and Lean re-verification | **Add**, depends on 184 and on the BimodalLogic checker task below. JSON export in the `Annot` shape; a test that round-trips certificates through the Lean checker when it is available. | Makes ModelChecker output machine-checkable. |
| **New C** (optional) Fixed-frame model checking mode | Add later if wanted. | Section 4.4, last bullet. |
| ROADMAP note | Record dense/continuous time as future work with the static-frame argument of section 2. | Scoping justification. |

#### 6.2 BimodalLogic (`~/Projects/BimodalLogic/specs/TODO.md`)

| Task | Action | Reason |
|---|---|---|
| 623 Decidable ValidZTime via ShiftSet witness families | **Prioritize**; its dependencies (534, 645) are complete. Add to its deliverables: state the certificate as a standalone structure over label space (guess + list of annotated lassos) with the soundness theorem in the form "certificate ⇒ ¬(Γ ⊨_Z Σ)" (consequence form, not just validity of a single formula), since that is what ModelChecker emits. | This is the load-bearing theorem for the redesign: it is the "finite partial model ⇒ full model with infinite states" result. |
| **New** Certificate re-verification executable | **Add**, depends on 623. `lake exe check_certificate`: parse the JSON certificate, decide conditions 1–4 with the decidable instances, print a verdict; document the JSON schema next to `TableauBridgeMain`. | Closes the loop from Z3 search to a Lean-checked countermodel. |
| **New** (optional) Static frames on finite carriers over dense Archimedean orders | Add as a short lemma task: `[Finite W]`, dense Archimedean `D`, task frame ⇒ `TaskRel w d u ↔ w = u`. | Machine-checks the reason dense time is deferred; small. |
| **New** (optional) State-labelled truth lemma for `IntPresentation` | Add only if the fixed-frame mode (6.1, New C) is pursued: a labelling on *states* satisfying local coherence, a no-pending-cycle condition, and `□χ ↔ ∀ states` equals truth on every path. | Cheaper certificate than `check`'s enumeration for a given digraph; not needed for countermodel search. |
| **New** Tableau bridge: run the branch gates on `invalid` | **Add** (small), needed by ModelChecker New A. `tableau_decide` already distinguishes `valid`, `invalid`, `timeout`, `valid_no_proof_term` and accepts `frame_class` (`TableauBridgeMain.lean:440-462,379`). Add: evaluate `timeOrderTotal`, `boxAnchoredCheck`, `regionLabelCheck`, `temporalWitnessCheck` on the open branch and report their outcomes in the `invalid` payload; reject unrecognized `frame_class` strings instead of defaulting to `Base`. | Makes an `invalid` verdict citable via `not_validZTime_of_hasOpen_int`, whose hypotheses are exactly those gates. |

No task is needed for "finite Z-model ⇒ genuine countermodel": that is `not_validZTime_of_satAtState`
and the ShiftSet representation theorem, both landed.

### 7. Sequencing

1. Revise 184 and abandon 154/172/176/178/183 (ModelChecker); create the BimodalLogic checker task
   and re-prioritize 623.
2. Implement 184 now. Its soundness argument is true on paper and its certificate format is fixed
   by Lean's `Annot`; 623 supplies the formal guarantee later without changing the format.
3. New A (tableau oracle) can proceed in parallel with 184's later phases.
4. New B waits for 623 and the checker task.

## Risks & Mitigations

- **Risk**: the soundness theorem for witness families (BimodalLogic task 623's ShiftSet truth
  lemma) is not yet machine-checked. **Mitigation**: the argument is the standard quasimodel one and
  the certificate format is fixed by Lean's landed `Annot`/`LocalCoherent`/`Fulfilling` shape, so
  ModelChecker can proceed and the Lean proof lands without changing the format; recommend
  splitting the soundness half out of 623 so it lands first.
- **Risk**: over-claiming validity from "no certificate within bounds". **Mitigation**: ModelChecker
  never reports validity; the tableau and proof system do.
- **Risk**: a `frame_class` typo silently becomes `Base` at the tableau bridge. **Mitigation**: the
  oracle client validates the tag before sending.
