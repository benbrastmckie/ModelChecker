# Implementation Plan: Task #186

- **Task**: 186 - Review manual counterfactual semantics for uniform clauses
- **Status**: [IMPLEMENTING]
- **Effort**: 8.25 hours
- **Dependencies**: None
- **Research Inputs**: `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/reports/01_family-level-settled-verification.md` (round 1, complete; F1-F10, D1-D6)
- **Artifacts**: plans/01_uniform-clauses-evidence-closure.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal:logic
- **Lean Intent**: false

## Overview

Round 1 answered every question the dispatch posed (a)-(f) and met deliverable (i): Settled Event
Verification states as one family-level principle, with the counterfactual as the family-level
`ILMC` instance, the null-family convention derived, the DT restriction lifted and report 02's F4
refuted. It closed with five explicitly undecided items, each with a named deciding test, and one
new user-facing input arrived with this dispatch that round 1 never saw: the user's instruction to
review BimodalLogic tasks 665-668 for alignment. This plan does exactly two things — it runs the
alignment review, and it executes the deciding tests that are reachable from inside this
repository — then folds both back into report 01 and hands the manual/Lean edit list to a
follow-up task.

The dispatch's SCOPE clause governs throughout: research only. Every write this plan authorizes
lands under `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/`. The Logos
manual, the Logos Lean development, the BimodalLogic tree and `code/src/model_checker/**` are
**read-only inputs**; no phase edits any of them.

### Research Integration

From `reports/01_family-level-settled-verification.md`:

- The principle (F2) and its three definitional adjustments (D2) are settled and are carried in,
  not re-derived. So are F3 (null family derived), F4 (singleton-domain alignment with the
  untensed `ILMC`), F5.1 (the measured nested-logic profile), F6 (DT restriction lifts), F7 (the
  proof-theory table) and F8 (F4 refuted at the family level).
- The five items under "Where the evidence does not decide" are this plan's work list. Items 1,
  2 and 5 are executable from here (Phases 2-4). Item 3 (Settler Minimality's necessity) is
  argumentative and is where the BimodalLogic alignment pays off (Phase 5). Item 4 (padding) is a
  recorded design choice and is closed by decision, not measurement (Phase 5).
- The report's own frame-dependency risk — "all executable evidence uses the manual's memoryless
  schema" — is the single largest gap, and Phases 2-3 exist to close it.

### Prior Plan Reference

No prior plan. This is the first plan round for task 186.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch and no ROADMAP.md was consulted.

### User Focus Integration

The dispatch carries `User focus: Review the tasks 665-668 recently completed in
/home/benjamin/Projects/BimodalLogic/ to ensure alignment.` All four are archived and complete:

- `specs/archive/665_witness_family_certificate_soundness/` — the quasimodel/ShiftSet route,
  soundness half: a labelled bi-lasso family satisfying local coherence, fulfilment and box
  faithfulness provably presents a `ShiftSet intOrder` model agreeing with its labels; all four
  certificate predicates decidable by **bounded window scans**.
- `specs/archive/666_check_certificate_executable/` — `lake exe check_certificate`, the runtime
  certificate checker (`BimodalTools/CertificateImport.lean`, `JsonParse.lean`).
- `specs/archive/667_tableau_bridge_branch_gates_and_frame_class/` — `BranchGates`, and
  `parseFrameClass` rejecting unrecognized frame classes instead of silently deciding at `.Base`.
- `specs/archive/668_clear_c34b_residual_enforce_c34b/` — invariant C34 fully enforced over the
  `FrameOver.IsRegular` bundling class; `FormalSystem/Semantics/TaskFrame.lean` gained the
  binder-free `nullity_identity_of_serial_limit`.

Three of these bear directly on round 1's open items, which is why the alignment review is a
substantive phase rather than a courtesy read: BimodalLogic's frame-constraint family
(*Seriality*, *Limit*, *Saturation*, *Compositionality*, derived Nullity) is the closest existing
relative of the report's proposed **Settler Minimality**; the witness-family route's bounded-window
decidability is the formal analogue of F5.3's "automatic where settling depends on a bounded time
window over a finite lattice"; and the bi-lasso/`ShiftSet` presentation of a ℤ-time history is a
candidate answer to F9.1's deferred world-history completion principle. Phase 1 establishes which
of these are genuine correspondences and which are false friends.

## Goals & Non-Goals

**Goals**:

- Answer the user's alignment question with a definite verdict per BimodalLogic task, recorded as
  a new finding in report 01.
- Decide report 01's open items 1, 2 and 5 by measurement: a certified **temporally constrained**
  frame (one whose task relation forbids some transition), run against the manual's
  `@def-maximal-compatible-subevolutions` clauses (a)-(d) directly instead of the duration-uniform
  product shortcut.
- Decide open items 3 and 4 by argument and by recorded decision (D3, D2), using whatever Phase 1
  and Phase 3 establish.
- Leave report 01 internally consistent: Executive Summary, Decisions, Results index and the
  "Where the evidence does not decide" list all updated, so a reader of the report alone gets the
  final state.
- Hand the manual/Lean change list (report 01 F10) to a follow-up task as a written, reviewable
  specification, since this task must not make those edits.

**Non-Goals**:

- Editing `~/Projects/Logos/Theory/typst/manual/**`, the Logos Lean tree, the BimodalLogic tree,
  or `code/src/model_checker/**`. Read-only, per the dispatch SCOPE clause.
- Re-deriving any of the six settled results, or re-litigating D1 (the principle itself).
- Creating the follow-up task. Phase 6 writes its specification; task creation is the user's call.
- Any Z3 work. Round 1's evidence is pure-Python and the new experiments stay pure-Python; the
  Z3-confirmed untensed results are carried in as given.
- Proving Settler Minimality in Lean, in either repository.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The certified constrained frame admits no multi-time realizable settler, so open item 1's prediction fails | M | M | A negative result is a result: record it as such with the frame's certificate, and state what it rules out. Do not keep hunting frames past the Phase 3 timing budget; escalate the remaining search to the follow-up spec |
| Generalizing the oracle to an arbitrary task relation changes an E1-E5 outcome, i.e. the new engine and the pinned baseline disagree | H | L | Phase 2's verification criterion is exactly this regression: the general engine instantiated at the duration-uniform relation must reproduce E1-E5's conclusions before any new frame is run. A disagreement stops Phase 3 and is triaged as an oracle defect, not a finding |
| Combinatorial blow-up: direct clauses (a)-(d) over general threads are far costlier than the product shortcut | M | H | Keep windows at 2-3 times and atoms at 4; cap candidate enumeration by anchor; run long experiments detached per `context/patterns/bounded-build-waiter.md`. Round 1 already needed a background run for E4 at 256 states |
| BimodalLogic's *Saturation*/*Limit* turn out to be false friends of Settler Minimality (one is about intersections of cones, the other about descending chains of settlers) | M | M | Phase 1 states the correspondence as a table with an explicit verdict column, including "no correspondence" as a permitted verdict. A negative alignment verdict is reported, not smoothed over |
| D3 (Settler Minimality as axiom vs. conditional sufficiency) is not decided by any evidence this plan can reach | L | M | Phase 5 surfaces it in the follow-up spec as an explicit open decision for the user, with both options' consequences stated, rather than choosing silently. Report 01 already records it non-blocking |
| Concurrent sibling task 184 shares this working tree with no declared file scope | M | M | Re-read every file immediately before editing; stage only this task's own hunks with explicit path lists; never `git add -A`, a directory pathspec, or `git-snapshot.sh` in its reverting default mode. See the Territory note in the dispatch |
| Appending to report 01 (already committed in round 1) makes a large diff hard to review | L | M | Each phase appends one clearly-headed new section (F11-F14) and touches nothing already written, except Phase 6 which is the single declared integration pass over the Executive Summary, Decisions, Results index and open-items list |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4, 5 | 3 (and 1 for phase 5) |
| 4 | 6 | 1, 3, 4, 5 |

Phases within the same wave can execute in parallel. Wave 1 is file-disjoint by construction
(Phase 1 writes `reports/01_*`, Phase 2 writes `baselines/02_*`); so is Wave 3 (Phase 4 writes
`baselines/**`, Phase 5 writes `reports/01_*`).

---

### Phase 1: BimodalLogic 665-668 alignment review [COMPLETED]

**Goal**: Answer the user's alignment question with a per-task verdict, and extract from the
BimodalLogic constraint family and witness-family route whatever bears on report 01's open items 3
(Settler Minimality) and 2/F9.1 (world-history completion).

**Tasks**:
- [x] Read all three artifacts (report, plan, summary) of each of
      `/home/benjamin/Projects/BimodalLogic/specs/archive/665_witness_family_certificate_soundness/`,
      `666_check_certificate_executable/`, `667_tableau_bridge_branch_gates_and_frame_class/`,
      `668_clear_c34b_residual_enforce_c34b/`. *(completed: summaries read in full for all four;
      reports/plans consulted for the specific Lean modules and decisions the summaries named)*
- [x] Read the Lean modules those artifacts name, at minimum:
      `FormalSystem/Semantics/TaskFrame.lean` (the constraint family and its derived-Nullity
      story), `FormalSystem/Metalogic/Decidability/WitnessFamily/{Basic,Predicates,Std,Agreement,Examples}.lean`,
      `BimodalTools/CertificateImport.lean`, and the C34 block of
      `scripts/check-module-invariants.sh`. *(completed: TaskFrame.lean and
      WitnessFamily/{Basic,Predicates,Std}.lean read directly; `Extension/Completion.lean` and
      `Extension/Extension.lean` added beyond the enumerated list, since they hold the
      `thm:extension`/`Completion` apparatus that answers question (iii) and the enumerated list's
      "at minimum" phrasing anticipated exactly this; `Agreement.lean`/`Examples.lean` and
      `CertificateImport.lean`/C34 not read line-by-line since 665-668's own summaries already gave
      their headline theorems and none bears further on (i)-(iii))*
- [x] Build a correspondence table: manual notion (`@def-maximal-constraint`,
      `@def-nullity-constraint`, `@def-evolution-maximality`, world-history, thread, anchored
      family) against BimodalLogic notion (`TaskFrame.Saturation`, `TaskFrame.Serial`,
      `TaskFrame.Limit`, `TaskFrame.Compositional`, `nullity_identity_of_serial_limit`,
      bi-lasso / `WitnessFamily.std` / `ShiftSet intOrder`, label sets), with a verdict column
      whose permitted values include "no correspondence". *(completed: F11's five-row table)*
- [x] Answer, explicitly: (i) does any BimodalLogic constraint already supply the content of
      Settler Minimality (attend to *Saturation*'s `⋂𝒮 ≠ ∅`, `exists_uniform_radius_of_finite`,
      and `limit_of_succOrder`), or is it independent? (ii) does the witness-family route's
      bounded-window decidability corroborate F5.3's "automatic" region, and does its
      **decidability** argument transfer or only its shape? (iii) does the bi-lasso/`ShiftSet`
      presentation of a ℤ-time history settle, corroborate or bypass F9.1's deferred
      world-history completion principle? *(completed: independent/corroborates-form;
      corroborates-shape-not-decidability; bypasses-but-Extension/Completion.lean-corroborates)*
- [x] Record vocabulary divergences that a shared write-up would have to reconcile (duration
      indexing, "thread" vs. "lasso", anchoring vs. labelling, possibility vs. `ShiftSet`
      membership). *(completed)*
- [x] Append the result to `reports/01_family-level-settled-verification.md` as
      `### F11. Alignment with the BimodalLogic certificate route (user focus)`, immediately
      after F10 and before the `## Decisions` separator. *(completed: F11 also carries a preamble
      note, beyond the plan's task list, on the manual's currency relative to report 01 — see
      Plan Deviations)*

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The four tasks and the Lean module list above are asserted from an archive
listing and from the tasks' own summaries; the module set may be incomplete or renamed. Confirm at
implementation time by listing each task directory and by reading each summary's "What Changed"
section for its actual file list before relying on the enumeration; record any module the summaries
name that this list omits.

**Files to modify**:
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/reports/01_family-level-settled-verification.md` — append F11 only; touch nothing already written

**Verification**:
- F11 exists, carries the correspondence table with a verdict for every row, and answers (i),
  (ii), (iii) each in its own labelled paragraph.
- Every BimodalLogic path cited in F11 resolves (`ls` each one); no path outside
  `specs/186_*/` was written (`git status --short` shows only the report).

---

### Phase 2: General-task-relation oracle with direct clauses (a)-(d) [COMPLETED]

**Goal**: Produce a second oracle that takes the task relation as a parameter and computes
world-histories, threads and maximal compatible subevolutions from the manual's clauses directly,
and prove it agrees with round 1's pinned engine where the two overlap.

**Tasks**:
- [x] Create `baselines/02_constrained-frame-oracle.py`, loading round 1's
      `01_family-recipe-oracle.py` as a module via `importlib.util.spec_from_file_location` (its
      filename begins with a digit, so a plain `import` will not work) and reusing its formula
      constructors, `Model`, recipe and reporting code unchanged. *(completed)*
- [x] Parameterize the frame by a task relation `R(s, d, t)` over possible states and durations,
      replacing `Frame.histories`' hardcoded "all world-valued total functions" with the set of
      window-functions every consecutive pair of which satisfies `R`; keep the duration-uniform
      relation as the default instantiation. *(completed: implemented as EVERY pair y<z in the
      window, not only consecutive ones, since `@def-task-coherent` itself quantifies over every
      `y < z` in the domain, not just adjacent points — a duration-uniform `R` makes the two
      coincide, so the pinned E1/E2/E3/E5 regression is unaffected, but a future non-transitive `R`
      would only be caught correctly by the all-pairs form)*
- [x] Replace the `Frame.thread` shortcut (convex + all-possible + all-or-none-null) and
      `Model.mcs`' product shortcut with direct implementations of
      `@def-maximal-compatible-subevolutions` clauses (a)-(d) over an arbitrary bounding family —
      the generalization report 01 D2 adjustment 1 requires — retaining the shortcut behind a flag
      for cross-checking. *(completed: `GeneralFrame.mcs_direct` enumerates all parts of `g(z)`
      per point rather than only per-point maximal-compatible parts, since a general/interacting
      relation can make a jointly-maximal `rho` fail to decompose into independently-maximal
      per-point choices; `base.Model.mcs`/`base.Frame.thread` remain the pinned shortcut, invoked
      by `base.Model` directly, so "behind a flag" is realized as two classes rather than a runtime
      flag — `GeneralModel` for direct, `base.Model` for shortcut)*
- [x] Add an assertion path that the direct `mcs` and the product `mcs` agree on the
      duration-uniform schema for every bounding family and candidate in the small frame.
      *(completed: 131,584/131,584 bounding-family/candidate pairs agree at window `{0,1}`)*
- [x] Re-run the round-1 experiments (E1, E2, E3, E5 at their original windows; E4 if the timing
      budget allows, detached) through the general engine at the duration-uniform relation and
      diff the conclusions against the saved outputs in `baselines/01_family-recipe-oracle-output-*.txt`.
      *(completed: E1/E2/E3/E5 all agree; E4 deferred — see Plan Deviations)*
- [x] Save the regression output as `baselines/02_constrained-frame-oracle-output-regression.txt`.
      *(completed)*

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts one new file and that round 1's 806-line script is
importable as a module (it guards its experiment driver behind `if __name__ == "__main__"`).
Confirm at implementation time by importing it and calling `frame_small`/`experiment_alignment`
from a throwaway REPL line before building on it; if module-level side effects appear, fall back to
a documented fork and say so in the new script's docstring.

**Files to modify**:
- `specs/186_.../baselines/02_constrained-frame-oracle.py` — new
- `specs/186_.../baselines/02_constrained-frame-oracle-output-regression.txt` — new
- `specs/186_.../baselines/01_family-recipe-oracle.py` — **not modified**; it is the pinned
  baseline the regression compares against

**Verification**:
- `python3 02_constrained-frame-oracle.py regression` exits 0 and every E1/E2/E3/E5 conclusion
  matches the corresponding round-1 saved output (verifier and falsifier sets, soundness,
  sufficiency, history-form E3, and the F5.1 validity profile). A mismatch blocks Phase 3.
- The direct-vs-product `mcs` agreement assertion passes on the duration-uniform schema.
- `python3 -m py_compile 02_constrained-frame-oracle.py` is clean.

---

### Phase 3: Certify a temporally constrained frame and run open items 1 and 2 [COMPLETED]

**Goal**: Decide report 01's open items 1 (multi-time realizable settlers; realizable non-convex
minimal settlers) and 2 (pointwise E3 among realizable members) on a frame whose task relation
genuinely forbids a transition.

**Tasks**:
- [x] Choose and certify the constrained frame: a small state lattice plus a task relation that
      forbids at least one world-to-world transition while satisfying the manual's containment pair
      and parthood constraints, in the style of `@def-certified-frame`. Take the constraint *shape*
      from Phase 1 if the BimodalLogic positive certificate's "`p` occurs exactly once along every
      history" pattern transfers; otherwise construct one directly (e.g. a one-way transition ban
      between two worlds). *(completed: constructed directly — a one-way transition ban `a.b -> a.c`
      on `frame_small`; the BimodalLogic shape did not transfer, since "occurs exactly once along
      every history" is a property of an entire lasso, not a single forbidden pair, and Phase 1's
      alignment review found no correspondence claim strong enough to license reusing it here)*
- [x] Record the certificate in the script as a checked predicate, not a comment: assert the frame
      satisfies each constraint the manual requires before any experiment runs.
      *(completed: `certify_constrained_frame`)*
- [x] Experiment C1: recompute the family recipe for a CF-constituent counterfactual on this frame
      at windows `{0}` and `{0,1}`. Report whether a **realizable** minimal settler with domain
      larger than `{x}` exists — report 01 F4's prediction is `{x: t, z: u}` with `t` not a
      state-level settler — and whether any realizable minimal settler has a non-convex domain
      (F9.3). *(completed: negative result, recorded with the structural reason — see F12)*
- [x] Experiment C2: search for a pointwise-compatible settler/co-settler pair on disjoint
      non-anchor domains with no world-history above both, among **realizable** members. Report
      pointwise E3 and history-form E3 separately, per F9.1. *(completed: positive result — F12)*
- [x] Re-check the recipe's soundness and sufficiency in both polarities on this frame, and record
      whether the F5.1 validity profile (identity, MP, strict→cf, cf→strict, AS, might-identity)
      changes off the memoryless schema. *(completed: sound/sufficient in both polarities; F5.1
      spot-check at consequent B qualitatively unchanged)*
- [x] Save output as `baselines/02_constrained-frame-oracle-output-c12.txt`; run detached with a
      hard timeout and liveness check per `context/patterns/bounded-build-waiter.md` if the window
      `{0,1}` run exceeds a few minutes. *(completed; window {0,1,2} exploratory run for C1 also
      performed ad hoc, confirming the same negative result, not saved as a separate artifact since
      it was a scope-widening check rather than a plan-required experiment)*
- [x] Append `### F12. The recipe on a temporally constrained frame (open items 1 and 2)` to
      `reports/01_family-level-settled-verification.md`, stating the certificate, both outcomes
      (including a negative outcome as such), and what each rules in or out. *(completed)*

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that a frame meeting the manual's constraints while
forbidding a transition exists at the 4-atom scale and that the predicted multi-time settler will
appear. Confirm at implementation time by the in-script certificate assertions; if no qualifying
frame is found within the timing budget, or the frame is found but exhibits no multi-time settler,
record the negative result with the frames tried and carry the remaining search to Phase 6's
follow-up specification rather than extending this phase.

**Files to modify**:
- `specs/186_.../baselines/02_constrained-frame-oracle.py` — add the certified frame and
  experiments C1, C2
- `specs/186_.../baselines/02_constrained-frame-oracle-output-c12.txt` — new
- `specs/186_.../reports/01_family-level-settled-verification.md` — append F12 only

**Verification**:
- The certificate assertions pass; the script refuses to run the experiments on a frame that fails
  them (verified by deliberately perturbing one constraint once and observing the refusal).
- C1 and C2 each print an explicit verdict line, and F12 quotes it.
- The Phase 2 regression still passes after the additions.

---

### Phase 4: Frame G2 at the family level (open item 5) [COMPLETED]

**Goal**: Pin a family-level hyperintensionality witness, closing report 01's open item 5 and
F8's family-level refutation of report 02's F4 by measurement rather than by embedding argument.

**Tasks**:
- [x] Port Frame G2 (task 185 report 01 F8; `specs/185_*/baselines/03_research-witnesses.py`) into
      the general oracle, with the identity task relation so that world-histories are the constant
      histories. *(completed: verbatim port — same 8 atoms, 4 worlds, letters)*
- [x] Run the recipe on `A []-> B` and `C []-> D` at windows `{0}` and `{0,1}`: confirm the two
      have the same truth set over world-histories and distinct `V`/`F`, and record the nested
      truth-value that separates them. *(completed: same truth-set confirmed at both windows,
      distinct V/F confirmed at both windows; the nested check `[](A[]->B)` vs `[](C[]->D)` agrees
      on this particular frame rather than separating — recorded honestly as such in F13 rather
      than claimed as a separating witness)*
- [x] Cross-check against the state-level `ILMC` result task 185 pinned, as E4 did for the 8-atom
      F3 frame. *(completed: matches)*
- [x] Save output as `baselines/02_constrained-frame-oracle-output-g2.txt`. *(completed)*
- [x] Append `### F13. Family-level hyperintensionality witness (open item 5)` to
      `reports/01_family-level-settled-verification.md`. *(completed)*

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `specs/186_.../baselines/02_constrained-frame-oracle.py` — add the G2 frame and experiment
- `specs/186_.../baselines/02_constrained-frame-oracle-output-g2.txt` — new
- `specs/186_.../reports/01_family-level-settled-verification.md` — append F13 only

**Verification**:
- The run prints equal truth sets and distinct verifier/falsifier sets for the two
  counterfactuals, plus the separating nested truth-value; F13 quotes the sets.
- The state-level cross-check matches task 185 report 01 F8's pinned values.
- Phase 2's regression and Phase 3's certificate assertions still pass.

---

### Phase 5: Settler Minimality and the recorded decisions (open items 3 and 4) [COMPLETED]

**Goal**: Resolve open item 3 as far as the evidence reaches, and close open item 4 (padding) as a
recorded decision, using Phase 1's alignment verdict and Phase 3's constrained-frame measurements.

**Tasks**:
- [x] State Settler Minimality precisely, in the form it would take beside
      `@def-evolution-maximality` and `@def-maximal-constraint`, and give the exact conditional
      form of sufficiency that replaces it if it is not adopted (report 01 F5.3's fallback).
      *(completed: the manual has already adopted it verbatim as `@def-minimal-settler`, quoted in
      F14; the conditional fallback is F5.3's `ILC`, restated)*
- [x] Settle whether Phase 1 found a BimodalLogic constraint that supplies it, corroborates it, or
      is merely analogous, and say which. *(completed: corroborates the methodology and the
      specific finite-carrier automaticity claim, does not supply the content)*
- [x] Record the descending-chain construction for `G p` that shows the principle is not vacuous,
      in the manual's continuous candidate model (`@rem-threading-general-open`, closed subsets of
      `ℝ`), and state plainly that it is not executable at the oracle's scale. *(completed: an
      informal sketch, honestly caveated as riding on constraints — Limit, the relativized
      Spherical — the manual itself records as unverified for that candidate model)*
- [x] Re-state where the principle is automatic (finite lattice, bounded settling window) in light
      of Phase 3: does the constrained frame stay inside that region? *(completed: yes, Phase 3's
      frame stays inside the automatic region on both counts, so C1/C2 do not test non-automaticity)*
- [x] Close D2 (padding) with the conceptual argument report 01 item 4 names — which exact
      falsifier of "if `A` were going to happen, `B` would" the manual wants — and state the
      decision with its consequence for tensed-antecedent falsifier shapes. *(completed: full
      padding, decided)*
- [x] Record D3's remaining judgment (axiom vs. conditional theorem) with both options' costs, for
      the follow-up task's author. *(completed, reframed per Plan Deviations: the manual has
      already decided D3; the costs are recorded for a reader who might reconsider it, not as an
      open choice handed to the follow-up task)*
- [x] Append `### F14. Settler Minimality, padding, and what the evidence still does not decide`
      to `reports/01_family-level-settled-verification.md`. *(completed)*

**Timing**: 1 hour

**Depends on**: 1, 3

**Verification Tier**: prose

**Files to modify**:
- `specs/186_.../reports/01_family-level-settled-verification.md` — append F14 only

**Verification**:
- F14 states Settler Minimality and its conditional alternative as displayed, quotable
  formulations.
- Every claim in F14 is attributed: to Phase 1's table, to a Phase 3 output line, or to an
  argument given in full on the page. No claim rests on an unrun test presented as settled.
- D2 is closed with a stated decision; D3 is stated as open with both options costed.

---

### Phase 6: Integrate report 01 and write the follow-up specification [NOT STARTED]

**Goal**: Leave report 01 internally consistent end to end, and hand the manual/Lean change list
to a follow-up task as a written specification this task is forbidden to execute.

**Tasks**:
- [ ] Update report 01's Executive Summary with the alignment verdict (F11) and any bullet that
      F12-F14 changed; the summary must not still claim as open anything now decided.
- [ ] Update `## Decisions`: D2 closed per F14; D3 restated with its remaining judgment; D4
      (Exclusivity form) revised if Phase 3's C2 changed the picture; add a D7 for the alignment
      verdict if F11 warrants one.
- [ ] Rewrite `## Where the evidence does not decide, and the test that would`: remove items now
      decided, keep the rest with their tests, and add any new gap Phases 3-5 opened.
- [ ] Extend Appendix B's results index with rows for the regression run, C1, C2 and G2, each
      naming its output file; extend Appendix A with the general oracle's description and the
      direct clauses (a)-(d) implementation.
- [ ] Update the report's `**Artifacts**` and `**Sources/Inputs**` header lists with the new
      baselines and the BimodalLogic inputs.
- [ ] Write `specs/186_.../followup-task-spec.md`: the F10 edit list (ten `03-dynamics.typ` sites,
      the two `02-constitutive.typ` sites, the `11-proof-theory.typ` sites), the Lean landing shape
      recorded at the end of F10, the open D3 decision the follow-up's author must make first, and
      an explicit statement that both target trees are separate repositories.
- [ ] Re-run `bash .claude/scripts/validate-artifact.sh` on report 01 and on this plan, and fix
      any reported format defect.

**Timing**: 1.5 hours

**Depends on**: 1, 3, 4, 5

**Verification Tier**: prose

**Scope Hypothesis**: The follow-up specification asserts F10's count of edit sites (ten in
`03-dynamics.typ`, two in `02-constitutive.typ`, five in `11-proof-theory.typ`) and their line
numbers, recorded in round 1 against a file that has not been re-read since. Confirm at
implementation time by re-reading each cited label in
`~/Projects/Logos/Theory/typst/manual/chapters/` and correcting any line number that has moved;
where a label no longer exists, say so in the spec rather than carrying the stale reference.

**Files to modify**:
- `specs/186_.../reports/01_family-level-settled-verification.md` — the single declared
  integration pass (Executive Summary, Decisions, open-items list, appendices, header lists)
- `specs/186_.../followup-task-spec.md` — new

**Verification**:
- `validate-artifact.sh` reports no error on report 01 or on this plan.
- Report 01 contains no sentence claiming as undecided anything F12-F14 decided, and no claim of a
  result no saved output supports (spot-check each new Appendix B row against its file).
- `followup-task-spec.md` cites every F10 site with a re-read line number or an explicit note that
  the reference moved.
- `git status --short` shows modifications only under
  `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/`.

---

## Testing & Validation

- [ ] `python3 02_constrained-frame-oracle.py regression` reproduces every E1/E2/E3/E5 conclusion
      from round 1's saved outputs (Phase 2 gate; blocks Phase 3 on failure).
- [ ] The direct clauses (a)-(d) `mcs` agrees with round 1's product shortcut on the
      duration-uniform schema, for every bounding family and candidate in `frame_small`.
- [ ] The constrained frame's certificate assertions pass, and are shown to fail on a deliberately
      perturbed constraint.
- [ ] Every new experiment writes a saved output file under `baselines/`, and every numeric or
      set-valued claim in F11-F14 is traceable to one of those files or to a stated argument.
- [ ] `python3 -m py_compile` clean on every script touched.
- [ ] `bash .claude/scripts/validate-artifact.sh` clean on `plans/01_uniform-clauses-evidence-closure.md`
      and `reports/01_family-level-settled-verification.md`.
- [ ] Scope gate, run before each commit: `git status --short` shows no path outside
      `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/`. In particular
      nothing under `~/Projects/Logos/`, `/home/benjamin/Projects/BimodalLogic/`, or `code/`.

## Artifacts & Outputs

- `specs/186_.../reports/01_family-level-settled-verification.md` — amended: new findings F11
  (alignment), F12 (constrained frame), F13 (G2 family-level witness), F14 (Settler Minimality,
  padding), plus the Phase 6 integration pass.
- `specs/186_.../baselines/02_constrained-frame-oracle.py` — the general-task-relation oracle with
  direct `@def-maximal-compatible-subevolutions` clauses (a)-(d).
- `specs/186_.../baselines/02_constrained-frame-oracle-output-regression.txt`,
  `...-output-c12.txt`, `...-output-g2.txt` — saved outputs.
- `specs/186_.../followup-task-spec.md` — the manual/Lean change specification for the following
  task, which this task must not execute.
- `specs/186_.../summaries/01_uniform-clauses-evidence-closure-summary.md` — implementation summary
  (written by the implement phase's postflight, not by a phase above).

## Rollback/Contingency

Every change is additive and confined to
`specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/`, and round 1's
`baselines/01_*` files are never modified, so the round-1 evidence base cannot be damaged by this
work.

- Per-substep commits are the rollback unit: to undo a landed phase, `git revert` its commit(s).
  No history rewriting.
- To abandon an in-progress phase whose edits are still uncommitted, snapshot before discarding —
  see `context/contracts/recovery.md`'s rollback rung for the exact `git-snapshot.sh` invocation,
  including its out-of-scope override flag. Never a bare default-mode snapshot call as a routine
  precaution; a defensive checkpoint before risky work uses `--no-revert`.
- Contingency per phase: Phase 2 failing its regression stops Phases 3 and 4 and is reported as an
  oracle defect, with Phases 1, 5 and 6 still deliverable (F14 and the integration then record the
  constrained-frame questions as still open, which is the honest state and is what report 01
  already says). Phase 3 finding no qualifying frame, or no multi-time settler, is a recorded
  negative result, not a blocker. Phase 6 runs in every case, so the task always ends with a
  consistent report and a follow-up specification.
- Sibling-task hazard: task 184 shares this tree with no declared file scope. Before each commit,
  re-read the target file, stage an explicit path list (never `git add -A`, never a directory or
  glob pathspec), and if a foreign commit or foreign uncommitted modification appears, stop and
  report it after checking `git log` to confirm the work is not this task's own.
