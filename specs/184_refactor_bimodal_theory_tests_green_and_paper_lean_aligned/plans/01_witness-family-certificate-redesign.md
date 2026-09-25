# Implementation Plan: Task #184

- **Task**: 184 - Redesign the bimodal theory around witness-family certificates (discrete Z-time)
- **Status**: [IMPLEMENTING]
- **Effort**: 46 hours
- **Dependencies**: None (the five previously-dependent bimodal tasks 154, 172, 176, 178, 183 were
  abandoned in the operation that created this revision; BimodalLogic tasks 665/666/667 are
  complete, so nothing external is pending)
- **Research Inputs**:
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/reports/01_finite-certificate-redesign.md` (authority)
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/reports/02_partial-model-formal-results.md`
  - `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/reports/03_bimodallogic-665-668-alignment.md`
- **Artifacts**: plans/01_witness-family-certificate-redesign.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Replace the bimodal theory's window-and-abundance Z3 encoding with a quantifier-free search for
**witness-family certificates** over discrete (Z) time, and replace the model it reports with the
**certified ShiftSet** those certificates denote. A certificate is a box guess plus a main
labelled bi-lasso and one witness lasso per box guessed false, satisfying local coherence,
fulfilment, box faithfulness and a target condition; its denoted model has infinitely many world
states and infinite durations, so Box ranges over exactly the certified histories rather than over
a finite set of window histories. Definition of done: every bimodal example runs green and fast
under the new encoding with all nine currently-excluded examples restored, every found model
re-checked by an independent pure-Python checker and round-tripped through BimodalLogic's
`lake exe check_certificate`, the oracle provider rewritten, and the `development` marker plus
every `and not development` gating clause removed so bimodal is gating again.

### Research Integration

- **Report 01** (authority) fixes the searched object (§4.1), the certified model (§4.2), why the
  current encoding is replaced rather than repaired (§3), and the deliverable list. Its §4.4 fixes
  the output shape, operator role, iteration strategy and export format.
- **Report 02** supplies the precise predicate definitions (`LocalCoherentLab`, `FulfillingLab`,
  `BoxFaithful`, `Target`) and confirms the standard model is BimodalLogic's landed `ShiftSet` —
  nothing is extended, only decoded. It also records that ModelChecker's soundness does not depend
  on the open completeness half (BimodalLogic task 623).
- **Report 03** (the user-focus dispatch) converts the export format from a proposal into a
  **fixed external contract**: the JSON wire shape (`target{premises,conclusions,time}`, sparse
  `bx` pairs, `lassos` with `back`/`mid`/`fwd`), the formula tag vocabulary
  (`atom`/`bot`/`imp`/`box`/`untl`/`snce`), the base-atoms-only rule, and the three verdict
  shapes. It also establishes that `lake exe check_certificate` is **already live**, so the
  round-trip test is a direct integration (Phase 5), not future work. Its `gated: false` finding
  about ZTime tableau verdicts is explicitly carried forward to the follow-on tableau-oracle task,
  not compensated for here.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch and no roadmap flag was set, so ROADMAP.md was not
consulted and no roadmap phases are included. Report 01 §6.1 recommends a ROADMAP note recording
dense/continuous time as future work with the static-frame argument; that note is **not** a
deliverable of this plan and should be made by whoever next edits ROADMAP.md.

## Decisions Fixed at Plan Time

These are design decisions the implementer should follow rather than re-derive. Each is grounded
in a verified fact about the code or the Lean contract, cited inline.

**D1 — The label alphabet is the Lean primitive `Formula`, and the label domain is exactly the
Lean closure.** `FormalSystem/Syntax/Formula.lean:76` defines `Formula` with only
`atom | bot | imp | box | untl | snce`; `WitnessFamily/Predicates.lean`'s `LocalCoherentLab`
imposes a **biconditional** clause on every `imp`/`box`/`untl`/`snce` member of
`closureOf (Γ ++ Del)`, and `LabelledLasso.label_sub` requires every label to be a subset of that
closure. A certificate whose labels carry ModelChecker's richer operators (`\wedge`, `\vee`,
`\neg`, `\Future`, `\Past`) is therefore **rejected structurally**, and one that omits the
intermediate `imp` nodes a translation introduces fails `local_coherent`. Consequence: translate
premises and conclusions into Lean-primitive `Formula` first, compute the closure over the
translated context, and run the whole Z3 encoding over that closure. This is not an export-time
concern; it is the shape of the search space.

**D2 — `\Until`/`\Since` argument order is swapped between the two sides, and the examples must be
audited for it.** `FormalSystem/Syntax/Formula.lean:86` states, in terms: *"Until, `φ U ψ`.
Argument 1 is the guard, argument 2 is the event"* — guard-first, matching the paper's
`def:BL-semantics`. ModelChecker's `UntilOperator.true_at(self, event_arg, guard_arg, eval_point)`
(`operators.py:1055`) is **event-first**. Translation must swap. Separately, the BX example
formulas were transcribed with the paper's names (`(psi \Until phi)` with the comments naming
`psi`/`phi`), so whether each example means what its comment says under the event-first convention
is an open semantic-alignment question, resolved in Phase 16 with the chosen source of truth
recorded.

**D3 — `N` and `all_states` stay as vestigial attributes; the framework is not changed.**
`models/structure.py:102-103` unconditionally reads `self.semantics.all_states` and
`self.semantics.N`, while `models/semantic.py:119` only defines them when `'N'` is in settings. So
`BimodalSemantics.__init__` must set `self.N = 0` and `self.all_states = []` explicitly after
`super().__init__()`. No framework edit, no compatibility layer, no `N` setting.

**D4 — Settings.** Remove `N`, `M`, `contingent`, `disjoint`, `temporal_depth`. Add `back`, `mid`,
`fwd` (maximum segment lengths, defaults small) and `max_witnesses` (optional cap). Keep
`max_time`, `expectation`, `iterate`, `solver`. Unknown settings only warn
(`settings/settings.py:141`), so stale `N`/`M` keys elsewhere degrade to warnings rather than
failures — but they must still be cleaned up. `max_time` must stay at or above the example budget
floor enforced by `code/tests/ci/test_example_budget_floor.py`.

**D5 — The target position is a one-hot selector, not a fixed origin.** `Target` is existential in
`t` and the wire format requires `target.time` explicitly. Encode a one-hot Boolean vector
`sel[t]` over the main lasso's finite position window; `premise_behavior(p)` returns
`And(Implies(sel[t], bit(0, t, tr(p))) for t in window)` and `conclusion_behavior(c)` the negated
form. Exactly-one over `sel` is added at finalize. Fixing `t0 = 0` would be sound but would lose
certificates that exist at the same segment lengths with the target elsewhere.

**D6 — Two-phase constraint emission with an idempotent `finalize_certificate()`.** Label bits and
per-position coherence can be emitted lazily as the closure is discovered from
`premise_behavior`/`conclusion_behavior`, but three constraint families are global: box
faithfulness (quantifies over *all* lassos, and a box discovered late adds a lasso), exactly-one
over `sel`, and the false-box witness clauses. `ModelConstraints.__init__`
(`models/constraints.py:80`) reads `semantics.frame_constraints` by reference and
`ModelDefaults._setup_solver` (`models/structure.py:181`) iterates that same list, so the clean
hook is to override `_setup_solver` in `BimodalStructure` to call `finalize_certificate()` before
delegating to `super()._setup_solver`. It must be idempotent: `re_solve()` and the iterator call
it again.

**D7 — The local-coherence and fulfilment window is wider than the box-faithfulness window, both
proved and both distinct from a single shared one-period bound, and `check_certificate` is the
authority.** *(Amended; see the Amendment block below.)* The window collapses are machine-checked
in `Metalogic/Decidability/WitnessFamily/Decide.lean`: `coherent_iff_window` (`:335`) and
`fulfil_iff_window` (`:743`) both collapse to **`[-2*nb, nm + 2*nf)`** — **two** periods on each
side — while `mem_all_iff_window` (`:809`, `:883`), which box faithfulness is built from, collapses
to the **narrower**, one-period **`[-nb, nm + nf)`**. **These are not the same window.** The reason
two periods are needed for local coherence and fulfilment is that the clause at position `t` reads
`t-1` and `t+1` as well as `t` (a representative position needs its whole neighbourhood inside the
periodic region), whereas box faithfulness reads no neighbours and collapses at one period. Encode
fulfilment as a bounded scan using the corrected bounds `scan_forward`/`scan_backward`
(`Decide.lean:192, 212`): a forward witness within `(t, max(t, nm) + nf]`, a backward witness
within `[min(t, 0) - nb, t)`. Getting this bound wrong is the single most likely silent soundness
bug in the whole redesign; that risk is now **discharged rather than pending** — the corrected
windows are proved in Lean, mechanically demonstrated by a window-discriminating certificate
fixture (`code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/`), and the guard
remains that the same bound is implemented once in the Python re-checker, with Phase 5's
round-trip test comparing verdicts against the Lean binary on every fixture including the
window-discriminating one.

**D8 — ModelChecker never reports validity.** UNSAT within the configured segment lengths means
"no certificate found within bounds" and must be rendered as inconclusive, never as a validity
claim. Report 01 §4.2 and `check_certificate`'s own one-sidedness both require this.

**D9 — Lassos are deterministic and do not share states.** *(Rationale corrected; see the
Amendment block below.)* Design `LabelledLasso`/`WitnessFamily` so sharing could later be added,
but do not implement it. Branching families are needed only for the stability modal, which is open
research in BimodalLogic and must not be promised. **The real blocker to adding state-sharing is
not Limit and Saturation** — over `ℤ`, Limit and Saturation are both discharged cheaply, from
`Int.abs_lt_one_iff` and from subsingleton fibres respectively
(`Metalogic/Decidability/WitnessFamily/Std.lean:73-80`;
`Semantics/TaskFrame.saturation_of_fib_subsingleton`, consumed at `Semantics/ShiftSet.lean:171`).
**The real blocker is `ShiftSet.total_eq_orbit` (`Semantics/ShiftSet.lean:252`) and the Box case
of the certificate truth lemma.** Determinism is exactly what makes every world history equal to
one of the lasso orbits (`total_eq_orbit`); if two lassos shared a state, a history could cross
between them at the shared point, `total_eq_orbit` would fail, the certified frame's history set
would no longer be exactly the certified lassos, and the Box case of the truth lemma would fail
with it, since box faithfulness is calibrated against "every position of every lasso" enumerating
exactly the certified histories. So adding state-sharing later requires re-proving the histories
lemma and redesigning box faithfulness, not re-arguing Limit or Saturation. See
`code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`'s "Why the design is deterministic"
section for the full argument.

### Amendment (adequacy-layer task, prior to this plan's Phase 1 dispatch)

The following decisions and phases were amended by the report and plan of the adequacy-layer
task that depends on this plan (see "Relationship to task 184, settled" in that task's own
research report, filed alongside its plan). Every phase of this plan was still at its initial,
not-yet-begun status at the time of the amendment, so every change below is an in-place
correction rather than a revision of completed work. Touched: **D7**, **D9**, and Phases **2, 3, 4, 5, 8, 9, 12, 16, 22** (17's
amendment is folded into 16's, per that task's Scope Hypothesis finding that Phase 17 carries no
separate window or expectation reference of its own). No phase status marker and no plan-level
status field were changed by this amendment.

## Goals & Non-Goals

**Goals**:
- A certificate-based `semantic/` core replacing the window-and-abundance encoding outright, with
  no ForAll, no MBQI, no E-matching patterns and no rlimit tuning.
- A certified-ShiftSet model whose world states are (history, time) points and whose task relation
  is the shift, printed as `(back)^ω | mid | (fwd)^ω` with the evaluation position marked.
- A pure-Python re-checker of the four certificate conditions, run on every found model in tests
  and independent of the Z3 model object.
- JSON certificate export mirroring BimodalLogic's wire contract field-for-field, with a
  round-trip test against the live `lake exe check_certificate`.
- All nine currently-excluded examples restored (`TN_CM_1`, `TN_CM_2`, `BM_CM_3`, `MD_TH_2`,
  `BM_TH_1`, `BM_TH_2`, `MF_MODAL_FUTURE_TH`, `BX7_LINEAR_U_TH`, `BX7P_LINEAR_S_TH`), with every
  expectation checked against the paper's axioms rather than carried over.
- Theory docs rewritten, retiring the frame-axiom ledger and the duration-guard gap note.
- `development` marker and every `and not development` gating clause removed; bimodal gating again.
- Oracle provider rewritten; abundance/shift-closure soundness tests deleted with their machinery;
  known-conclusive manifest regenerated.

**Non-Goals**:
- Dense and continuous time (finite carriers force static frames over dense Archimedean orders;
  finite presentations of infinite carriers are out of scope).
- The stability modal `⊡` and branching witness families.
- The tableau differential oracle (report 01's New A) and a fixed-frame model-checking mode
  (New C). New A must carry forward report 03's finding that ZTime `invalid` verdicts are
  `gated: false` today by design-in-progress on the BimodalLogic side.
- Any change to the oracle's own soundness core or its unconditional-gating property.
- Proving soundness or completeness of the certificate route; that is BimodalLogic's work
  (665 landed the soundness half; 623 holds compression).
- Reporting validity from ModelChecker under any circumstance.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fulfilment window bound wrong -> unsound certificates accepted | H | M | One implementation shared by encoding and re-checker (D7); Phase 5 round-trip against `lake exe check_certificate` on every fixture; a deliberately unfulfilled family in the negative fixtures |
| Label domain diverges from Lean's `closureOf` -> every export `rejected` structurally | H | M | D1 makes the Lean closure the search space itself; Phase 1 tests `closure_of` against hand-computed closures and Phase 5 catches divergence against the binary |
| `\Until`/`\Since` order silently swapped | H | M | D2 pins the direction with the Lean docstring cited; Phase 2 carries an order-sensitive fixture that fails if the swap is dropped; Phase 16 audits the examples |
| BimodalLogic or `lake` unavailable on the host -> round-trip untestable | M | M | Phase 5's test skips cleanly when absent and the Python re-checker remains a full independent check; the round-trip is a corroboration layer, not the only guard |
| Removing the `development` marker exposes unrelated pre-existing failures to the gate | M | M | Phase 23 is gated on Phase 19's and 21's green suites; if unrelated failures surface, record them and keep the marker removal as the final step rather than weakening the gate |
| Restored examples turn out genuinely invalid under the paper's axioms | M | M | Phase 16 audits expectations against the paper first and records the source of truth per example; an expectation change is a legitimate outcome, a silent patch is not |
| `finalize_certificate()` not idempotent -> duplicate/contradictory constraints on `re_solve` or iteration | M | M | D6 makes idempotence an explicit requirement with a unit test that calls it twice and compares constraint counts |
| Phase count (24) and total effort (46h) understate a 13.8k-line theory plus a 12.7k-line oracle test tree | M | M | Scope Hypothesis lines on every phase that asserts a count; the implementer confirms or reports at dispatch time rather than silently absorbing overrun |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 6 | 1, 3 |
| 4 | 5, 7 | 2, 4, 6 |
| 5 | 8 | 7 |
| 6 | 9 | 2, 8 |
| 7 | 10, 11, 14 | 9 |
| 8 | 12 | 4, 10 |
| 9 | 13, 15, 16 | 12, 14 |
| 10 | 17, 18, 20 | 14, 15, 16 |
| 11 | 19, 21 | 4, 17, 18, 20 |
| 12 | 22, 23 | 19, 21 |
| 13 | 24 | 22, 23 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Lean-mirroring Formula ADT and closure [COMPLETED]

**Goal**: A Python `Formula` type that is structurally identical to BimodalLogic's `Formula`, with
the subformula closure and the JSON codec the wire contract requires.

**Tasks**:
- [ ] Write unit tests first: constructor identity/hashing, `subformula_closure` on hand-computed
      cases, `closure_of` over a two-element context, `to_json`/`from_json` round-trip for each of
      the six tags, and rejection of any non-base atom.
- [ ] Create `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` with frozen
      dataclasses `Atom`, `Bot`, `Imp`, `Box`, `Untl`, `Snce` (guard-first field order for
      `Untl`/`Snce`, mirroring the Lean constructors).
- [ ] Implement `subformula_closure(f) -> frozenset[Formula]` and
      `closure_of(context) -> frozenset[Formula]` matching `Closure.lean`'s `closureOf` (union of
      each member's own closure, member included).
- [ ] Implement `to_json(f)` emitting the exact tag vocabulary (`atom` with `name`, `bot`, `imp`
      with `left`/`right`, `box` with `child`, `untl`/`snce` with `event`/`guard`) and `from_json`.
- [ ] Add an explicit guard that rejects any internally generated fresh/Skolem atom name from
      reaching `to_json`, with the reason in the error message.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` - new
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` - new

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v` green.
- `to_json` output for a hand-built formula matches the shape in `BimodalTools/README.md`'s
  "Certificate re-verification protocol" section byte-for-byte modulo key order.

---

### Phase 2: Sentence-to-Formula translation [COMPLETED]

**Deviation note**: the amendment's truth-preservation property test is implemented as two
independent from-scratch pure-Python evaluators (one mirroring `operators.py`'s ModelChecker
semantics over a small sentence-shaped AST, one mirroring the Lean `untl`/`snce` semantics over
the translated `Formula`), compared across several hand-built valuations and a bounded time
domain -- rather than by extracting a concrete Z3 model from the live (soon-to-be-replaced)
`BimodalSemantics`. This was a deliberate scoping choice: it avoids depending on the old Z3
encoding's boundary-vacuity behaviour (which this whole task replaces) while still giving an
independent, faithful cross-check of `translate`'s fidelity to the original operator
definitions. As the amendment itself notes for `ground_truth.py`, Box is out of scope for this
particular property test (recorded, not silently dropped); Box fidelity is discharged by later
phases' pure-Python re-checker and the `check_certificate` round-trip.

**Goal**: A total, tested translation from ModelChecker bimodal sentence ASTs into Lean-primitive
`Formula`, with the guard/event swap pinned.

**Tasks**:
- [ ] Write unit tests first, including an order-sensitive `\Until` fixture that fails if the
      guard/event swap is dropped, and fixtures for `\Future`/`\Past` as `¬F¬`/`¬P¬`.
- [ ] Confirm by inspection whether `syntactic.DefinedOperator` instances are expanded before the
      semantics sees a sentence; if they are, translate the nine primitives only, and if not, add
      translation rules for the defined operators too. Record which case holds.
- [ ] Implement `translate(sentence) -> Formula` in `formula.py`: atoms to `Atom`; `\bot` to `Bot`;
      `\neg A` to `Imp(A, Bot)`; `\wedge`/`\vee` to their `imp` encodings; `\Box` to `Box`;
      `\Until(event, guard)` to `Untl(guard, event)` and `\Since` likewise (the swap of D2);
      `\Future A` to `Imp(Untl(Imp(Bot,Bot), Imp(A,Bot)), Bot)` and `\Past A` to the `Snce` mirror.
- [ ] Add a memoizing cache keyed by sentence identity so repeated translation is free.
- [ ] **(Amendment, adequacy-layer task)** Add the truth-preservation obligation for this
      translation: Phase 5's round-trip against `lake exe check_certificate` compares the Python
      re-checker and the Lean binary on the *same already-translated* `Formula`, so it structurally
      cannot test whether `translate` itself preserves truth. Add a property test comparing, at
      every point of a small hand-built discrete-time model, the theory's own `true_at` evaluation
      against a direct evaluator for `translate(sentence)`. Note that
      `oracle/bimodal_logic/ground_truth.py`'s brute-force adjudicator covers only the tense half
      of the translation (five primitive tags, no box case), so it cannot discharge the box half of
      this obligation on its own.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: the primitive operator set requiring a translation rule is the nine in
`operators.py` declared as `syntactic.Operator` (`\neg`, `\wedge`, `\vee`, `\bot`, `\Box`,
`\Future`, `\Past`, `\Until`, `\Since`), with the eight `DefinedOperator` subclasses expanded
before the semantics is consulted. Confirm by grepping `operators.py` for `syntactic.Operator` vs
`syntactic.DefinedOperator` and by asserting in a test that a `\Diamond` sentence reaching
`translate` is already expanded; if it is not, add rules for the defined operators and report the
widened scope.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` - add translation
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` - extend

**Verification**:
- Translation unit tests green; the order-sensitive `\Until` fixture fails when the swap is
  reverted (verify by temporarily reverting it).

---

### Phase 3: Certificate datatypes and JSON writer [COMPLETED]

**Goal**: `LabelledLasso` and `WitnessFamily` dataclasses that decode to a bi-infinite label
function and serialize to the fixed wire shape.

**Tasks**:
- [ ] Write unit tests first: decoding at negative, mid and far-forward positions; non-empty
      `back`/`fwd` enforcement; `mid` allowed empty; labels confined to the closure; JSON shape.
- [ ] Create `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` with
      `LabelledLasso(back, mid, fwd)` (lists of `frozenset[Formula]`) and
      `WitnessFamily(bx, lassos)` with `lassos[0]` the main lasso.
- [ ] Implement `LabelledLasso.label(t)` by the three-segment scheme: `back` repeated strictly left
      of 0, `mid` on `[0, len(mid))`, `fwd` repeated from `len(mid)`.
- [ ] Implement `WitnessFamily.to_json(premises, conclusions, target_time)` emitting
      `{"target": {"premises": [...], "conclusions": [...], "time": t}, "bx": [[f, b], ...],
      "lassos": [{"back": [...], "mid": [...], "fwd": [...]}, ...]}` with `bx` sparse (omitted
      formulas read as false) and `target.time` always explicit.
- [ ] Leave a documented extension point for later state sharing between lassos (D9) without
      implementing it. **(Amendment, adequacy-layer task)** The extension-point comment must say
      *why* sharing is deferred, and the corrected reason is: determinism is what makes
      `ShiftSet.total_eq_orbit` true — every world history equals one of the lasso orbits — which
      is what makes Box's range exactly the certified histories and hence what makes the Box case
      of the certificate truth lemma go through (not Limit or Saturation, which are cheap over
      `ℤ`). Adding sharing later requires re-proving the histories correspondence and redesigning
      box faithfulness, not re-arguing Limit/Saturation. See D9's amended text above and
      `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`'s "Why the design is
      deterministic" section.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - new
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py` - new

**Verification**:
- Decoding tests green for `t` in a range spanning at least two periods each side.
- Emitted JSON validates against the field table in `BimodalTools/README.md`.

---

### Phase 4: Pure-Python re-checker of the four conditions [NOT STARTED]

**Goal**: An independent checker of structural validity, local coherence, fulfilment, box
faithfulness and the target, returning the same verdict vocabulary as the Lean binary.

**Tasks**:
- [ ] Write unit tests first: one positive family and one family failing each condition, each
      asserting the reported `condition`, `lasso` and `position`.
- [ ] Implement `recheck(family, premises, conclusions, target_time) -> Verdict` in
      `certificate.py`, with `Verdict` mirroring
      `{"status": "countermodel"|"rejected"|"error", ...}` and `failed` entries carrying
      `condition` in `{structural, local_coherent, fulfilling, box_faithful, target, unlocalized}`
      plus `lasso`, `position`, `formula`, `detail`.
- [ ] Implement local coherence as the five biconditional clauses of `LocalCoherentLab`, restricted
      to closure members, over the finite position window. **(Amendment, adequacy-layer task)** The
      window is the amended D7's `[-2*nb, nm + 2*nf)`, **not** a single shared one-period window —
      see D7 above.
- [ ] Implement fulfilment with the bounded window of the amended D7 (`[-2*nb, nm + 2*nf)`, using
      the corrected `scan_forward`/`scan_backward` bounds), with the bound and its justification in
      a docstring citing `Decide.lean`'s window-collapse lemmas (`coherent_iff_window:335`,
      `fulfil_iff_window:743`).
- [ ] Implement box faithfulness as the two-directional check (`bx χ` true iff `χ` labelled at
      every position of every lasso), using the **narrower** one-period window `[-nb, nm + nf)`
      (`mem_all_iff_window`, `Decide.lean:809, 883`) — this window is distinct from local
      coherence's and fulfilment's, not a rename of the same bound — and the target as the
      `Γ ⊆ L₀ t`, `Σ ∩ L₀ t = ∅` pair.
- [ ] Add the positive fixture from report 02 §3 (T3): `□(p ∨ Fp ∨ Pp) ∧ □(p → ¬Pp)` with one lasso
      and `p` only at 0.
- [ ] **(Amendment, adequacy-layer task)** Acceptance criterion: the re-checker must also pass the
      window-discriminating fixture at
      `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/04_window_discriminator_coherence.json`
      (that corpus's own `README.md` records the construction and the fulfilment-side negative
      finding), reporting `rejected`/`local_coherent` at the position in the outer band
      `[-2*nb, -nb)` — and must report `countermodel` (wrongly) if its window is narrowed to one
      period, confirming the wider window is load-bearing rather than cosmetic.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - add re-checker
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py` - extend

**Verification**:
- All six condition branches exercised by at least one test each.
- The positive fixture returns `countermodel`; the unfulfilled variant returns `rejected` with
  `condition == "fulfilling"`.

---

### Phase 5: Round-trip against `lake exe check_certificate` [NOT STARTED]

**Goal**: Every fixture certificate receives the same verdict from the Python re-checker and from
BimodalLogic's Lean binary.

**Tasks**:
- [ ] Write the integration test first: locate `~/Projects/BimodalLogic` and `lake`, skip with a
      clear reason when either is absent, otherwise pipe each fixture's JSON to
      `lake exe check_certificate` on stdin and parse the single output line.
- [ ] Assert verdict agreement (`countermodel` vs `rejected` vs `error`) on the whole fixture
      corpus from Phases 3-4, positive and negative.
- [ ] Assert that a certificate missing `target` or `target.time` produces `error` from both sides,
      and that a fresh-indexed atom is refused by the Python exporter before it can be sent.
- [ ] Record the BimodalLogic commit or version the agreement was observed against, in the test
      module docstring.
- [ ] **(Amendment, adequacy-layer task)** Add this task's own fixture corpus
      (`code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/`) to the round-trip's
      fixture set, including the window-discriminating fixture.
- [ ] **(Amendment, adequacy-layer task)** Add the A2-triangle test (ADEQUACY.md §7.3): at
      `back = mid = fwd = 1` and a closure `|C| <= 4`, exhaustively enumerate every candidate
      `(bx, lassos)` over subsets of the closure at those lengths, and compare three verdicts —
      (i) the Python re-checker, (ii) `lake exe check_certificate`, (iii) whether the Z3 encoding,
      run at those lengths on the same premises/conclusions, reports SAT — with three named failure
      localizations: (i) ≠ (ii) localizes a re-checker defect; (iii) false where (i) = (ii) =
      `countermodel` localizes an encoding incompleteness (a constraint the encoder imposes that
      (C1)-(C4) do not require); (iii) true where (i) = (ii) = `rejected` localizes an encoding
      unsoundness (which the fail-fast re-check hook of Phase 12 catches at run time regardless,
      but this test finds it in the suite instead).

**Timing**: 1.5 hours

**Depends on**: 2, 4

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_roundtrip.py` - new

**Verification**:
- Test green on a host with BimodalLogic present; cleanly skipped (not errored) on one without.
- Any disagreement is treated as a Python-side defect, since the Lean predicates are the contract.

---

### Phase 6: Label-bit registry and position algebra [NOT STARTED]

**Goal**: The Z3 variable layer: one Boolean per (lasso, position index, closure formula), plus
witness-lasso allocation, replacing the inert `WitnessRegistry`.

**Tasks**:
- [ ] Write unit tests first: the position-index wrap function agrees with
      `LabelledLasso.label`'s decoding for `t` spanning several periods each side; bit identity is
      stable across repeated lookups; `clear()` releases everything.
- [ ] Rewrite `semantic/witness_registry.py`: construct from segment lengths
      (`back`, `mid`, `fwd`) and the closure; index set per lasso of size `back + mid + fwd`;
      `wrap(t) -> index`; `bit(lasso, t, formula) -> z3.Bool` memoized; `guess(formula) -> z3.Bool`
      for the box guess; `allocate_witness_lasso(box_formula) -> int` honouring `max_witnesses`.
- [ ] Keep the public class name `WitnessRegistry` (report 01 §4.4: rewritten, not deleted) and
      document the change of meaning at the top of the file.
- [ ] Expose the position window used for the target selector.

**Timing**: 2 hours

**Depends on**: 1, 3

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` - rewrite

**Verification**:
- Wrap-function agreement test green across at least two periods in each direction.
- Bit count equals `lassos * (back + mid + fwd) * |closure|` for a hand-computed case.

---

### Phase 7: Local-coherence and target constraint generators [NOT STARTED]

**Goal**: Quantifier-free Z3 constraints for condition 1 (local coherence) and condition 4 (target,
via the one-hot selector).

**Tasks**:
- [ ] Write unit tests first: for a small closure, assert the generated constraint set is
      quantifier-free (no `ForAll`/`Exists` in the AST), and that a hand-built satisfying
      assignment satisfies it while a hand-built incoherent one does not.
- [ ] Rewrite the first half of `semantic/witness_constraints.py`: for each lasso, each position
      index, and each closure member, emit the five `LocalCoherentLab` biconditionals (bot absent;
      `imp` iff; `box` iff guess; `untl`/`snce` unfolding at `t+1`/`t-1` through the wrap).
- [ ] Emit the one-hot target selector `sel[t]` over the main lasso's position window with
      exactly-one, and the guarded premise/conclusion implications of D5.
- [ ] Document, in the module docstring, that atoms are deliberately unconstrained: the valuation
      *is* the atom part of the label.

**Timing**: 2 hours

**Depends on**: 6

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - rewrite (part 1)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` - rewrite

**Verification**:
- Quantifier-free assertion test green (AST walk finds no quantifier node).
- Hand-built positive/negative assignment discrimination test green.

---

### Phase 8: Fulfilment and box-faithfulness constraint generators [NOT STARTED]

**Goal**: Quantifier-free Z3 constraints for condition 2 (fulfilment) and condition 3 (box
faithfulness), with the fulfilment window identical to the re-checker's.

**Tasks**:
- [ ] Write unit tests first: a family that is locally coherent but unfulfilled is UNSAT once the
      fulfilment constraints are added; a box guessed true forces its argument everywhere; a box
      guessed false forces an omitting position on some lasso.
- [ ] Emit fulfilment: for each lasso, position and `untl`/`snce` closure member, a disjunction over
      the bounded window of the amended D7 (`[-2*nb, nm + 2*nf)`, corrected `scan_forward` /
      `scan_backward` bounds) of "event at `s`, guard at every `r` strictly between", all indices
      through the wrap.
- [ ] Emit box faithfulness: `guess(χ)` implies `bit(i, t, χ)` for every lasso `i` and position `t`;
      `Not(guess(χ))` implies a disjunction over all (lasso, position) of `Not(bit(i, t, χ))`,
      with the witness lasso allocated for that box included in the disjunction.
      **(Amendment, adequacy-layer task)** Box faithfulness uses the **narrower** one-period window
      `[-nb, nm + nf)`, distinct from fulfilment's wider `[-2*nb, nm + 2*nf)` — record this
      distinction in the module docstring so a future reader does not collapse the two windows
      into one.
- [ ] Factor the fulfilment window computation into a single function shared with the Phase 4
      re-checker, so the two cannot drift.

**Timing**: 2 hours

**Depends on**: 7

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - rewrite (part 2)
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - extract shared window helper
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` - extend

**Verification**:
- The unfulfilled-family UNSAT test green.
- A grep confirms exactly one definition of the fulfilment window, imported by both the encoder and
  the re-checker.

---

### Phase 9: BimodalSemantics rewrite - settings and framework contract [NOT STARTED]

**Goal**: A `BimodalSemantics` that satisfies the framework's contract with the certificate
encoding and carries none of the deleted machinery.

**Tasks**:
- [ ] Write tests first: construction with the new settings succeeds; `self.N` and
      `self.all_states` are present (D3); `true_at` returns a label bit; `finalize_certificate()`
      called twice adds constraints only once.
- [ ] Rewrite `semantic/core.py`: new `DEFAULT_EXAMPLE_SETTINGS` per D4;
      `ADDITIONAL_GENERAL_SETTINGS` reduced to what the new printer uses; `self.N = 0`,
      `self.all_states = []`; `main_point` as `{"lasso": 0, "position": <selector>}` or the
      equivalent the printer needs.
- [ ] Implement `true_at(sentence, eval_point)` / `false_at(...)` as translate-then-look-up against
      the registry, and `premise_behavior` / `conclusion_behavior` per D5.
- [ ] Implement `finalize_certificate()` (idempotent) appending the global constraints of D6 to
      `self.frame_constraints`.
- [ ] Delete every method belonging to the retired encoding: `define_sorts`, `define_primitives`,
      `is_valid_duration`, `build_task_rel_at`, the five frame-axiom builders, `ForAllTime`,
      `ExistsTime`, `build_frame_constraints`, the interval/shift helpers, all six abundance
      variants, `build_task_minimization_constraint`, `generate_time_intervals`,
      `is_time_shifted`, and the whole `extract_model_elements` family.
- [ ] **(Amendment, adequacy-layer task)** Add the A0 frame-class standing test (ADEQUACY.md §7.2):
      run the search on `\Future A \rightarrow (\neg A \Until A)` (the `prior_UZ` instance) and on
      the `z1` instance (`G(Gφ→φ) → (FGφ→Gφ)`); both must report no certificate at every configured
      length, and both must be rendered **inconclusive**, never as validity — a rendering that says
      "valid" on either is a reportable defect. Both axioms are classified minimum-frame-class
      `.ZTime` in `ProofSystem/Axioms.lean:612-613`, so by (SOUND) no certificate can ever exist for
      them even though they are not valid at every temporal order. That second half is now **proved,
      not cited**: `not_validIn_base_prior_UZ` and `not_validIn_base_z1`
      (`Metalogic/Independence/ZTimeSharpness.lean:225, 236`) refute both at `FrameClass.Base`, and
      `prior_UZ_minFrameClass_sharp` / `z1_minFrameClass_sharp` (`:251, 262`) strengthen this to
      every `fc < FrameClass.ZTime`. This test is what makes that permanent gap observable rather
      than silently forgotten.

**Timing**: 2 hours

**Depends on**: 2, 8

**Verification Tier**: interface

**Scope Hypothesis**: `semantic/core.py` currently spans 2,329 lines and roughly 45 methods, of
which the retired-encoding set enumerated above is the large majority, leaving a core of a few
hundred lines. Confirm at implementation time with `wc -l` before and after and by grepping the
rest of the theory (and `oracle/`) for every deleted method name to be sure no live caller remains;
report the actual counts rather than assuming these.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - new

**Verification**:
- Construction and idempotence tests green.
- `grep -rn` for each deleted method name across `code/src` and `oracle/` returns no live call site
  (docstring mentions to be cleaned in Phase 22).

---

### Phase 10: Certificate extraction from the Z3 model [NOT STARTED]

**Goal**: Turn a satisfying Z3 model into a `WitnessFamily` plus a target time.

**Tasks**:
- [ ] Write tests first: solve a tiny example, extract, and assert the extracted family passes the
      Phase 4 re-checker; assert the target time read from the selector satisfies `Target`.
- [ ] Implement `extract_certificate(z3_model) -> tuple[WitnessFamily, int]` on the semantics:
      read every label bit into `frozenset`s per (lasso, index), rebuild the three segments, read
      the box guess, read the one-hot selector to recover `target.time`.
- [ ] Rewrite `inject_z3_model_values` for the label/guess variable set (used by the iterator).
- [ ] Add `export_certificate_json(...)` delegating to `WitnessFamily.to_json`.

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - add extraction
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - extend

**Verification**:
- Extracted families from at least three solved examples all pass the re-checker.
- Exported JSON for one of them is accepted by `lake exe check_certificate` when available.

---

### Phase 11: BimodalProposition rewrite [NOT STARTED]

**Goal**: Propositions whose truth values come from labels, with atoms free.

**Tasks**:
- [ ] Write tests first: `truth_value_at` agrees with label membership for atoms and for one
      compound of each operator class; `proposition_constraints` adds nothing beyond what coherence
      already imposes.
- [ ] Rewrite `semantic/proposition.py`: `proposition_constraints` reduced to whatever the atom
      part genuinely needs (expected: empty, since atoms are free); `find_extension` /
      `truth_value_at` / `_find_proposition_at` reading labels at (lasso, position);
      `print_proposition` updated to the new eval-point shape.
- [ ] Remove the `contingent`/`disjoint` constraint paths along with their settings.

**Timing**: 1.5 hours

**Depends on**: 9

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` - new

**Verification**:
- Proposition unit tests green; a compound's printed truth value matches the label's.

---

### Phase 12: BimodalStructure rewrite - structure and re-check hook [NOT STARTED]

**Goal**: A model structure that finalizes the certificate before solving, extracts it after, and
re-checks it independently.

**Tasks**:
- [ ] Write tests first: `_setup_solver` triggers finalize exactly once even across `re_solve`;
      every satisfiable solve produces a certificate that passes the re-checker; an unsatisfiable
      solve leaves `certificate is None` and never claims validity.
- [ ] Rewrite `semantic/model.py`'s structure half: override `_setup_solver` to call
      `self.semantics.finalize_certificate()` then delegate; after solving, store
      `self.certificate` and `self.target_time` via Phase 10's extractor.
- [ ] Call the Phase 4 re-checker on every extracted certificate and fail loudly (fail-fast, per
      the project's philosophy) if it reports anything but `countermodel`.
      **(Amendment, adequacy-layer task)** This hook's role is not a safety net: it is **the**
      mechanism that discharges (SOUND)'s obligation S3 (ADEQUACY.md §2, §6.2) — the theorem's
      antecedent, that whatever the search reports actually satisfies (C1)-(C4), is decided here,
      on every reported countermodel, independently of the Z3 model object. Document this role in
      the hook's own docstring rather than describing it only as defensive testing.
- [ ] Rewrite `extract_states`, `extract_evaluation_world`, `extract_relations`,
      `extract_propositions` for (history, time) world states with the shift as the task relation.
- [ ] Delete `get_world_array`, `get_world_history`, `get_world_state_at`, the `time_shift_relations`
      field, and the `M`/`all_times` attributes.
- [ ] **(Amendment, adequacy-layer task)** Confirm the A0 frame-class standing test added in
      Phase 9 exercises this structure's own solve-and-re-check path end to end (not only the
      constraint-generation layer), since it is this phase's re-check hook that must render the
      `prior_UZ`/`z1` instances inconclusive rather than valid.

**Timing**: 2 hours

**Depends on**: 4, 10

**Verification Tier**: interface

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - rewrite (structure half)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - new

**Verification**:
- Finalize-once test green; re-check-on-every-model test green.
- A deliberately corrupted certificate causes a loud failure, not a silent pass.

---

### Phase 13: BimodalStructure rewrite - printing [NOT STARTED]

**Goal**: The output shape report 01 §4.4 specifies, with nothing left of the time-shift or
interval displays.

**Tasks**:
- [ ] Write tests first (golden-output style, in the spirit of the existing print-encoding test):
      a history renders as `(back)^ω | mid | (fwd)^ω` over atom valuations with the evaluation
      position marked; the boxed-subformula table lists each box with its guessed value; each
      false box is followed by its witness history and position.
- [ ] Rewrite `semantic/model.py`'s printing half: `print_evaluation`, the history renderer, the
      box-guess table, the witness section, `print_all`, `print_to`, `save_to`.
- [ ] Delete `print_world_histories`, `print_world_histories_vertical`, the column-width and
      time-position helpers for the retired display, and the `align_vertically` setting if unused.
- [ ] Render the unsatisfiable case as "no certificate found within the configured bounds
      (back=..., mid=..., fwd=...)" with an explicit note that this is not a validity claim (D8).

**Timing**: 2 hours

**Depends on**: 12

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - rewrite (printing half)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_print_encoding.py` - rewrite

**Verification**:
- Golden-output tests green.
- `grep -rn "time.shift\|interval"` over `semantic/model.py` finds no display code.
- A no-certificate run's output contains no word claiming validity.

---

### Phase 14: Operators rewrite [NOT STARTED]

**Goal**: Operators as label-constraint generators plus print methods, with all quantifier
machinery gone.

**Tasks**:
- [ ] Write tests first: each operator's `true_at` returns the label bit of its translated formula
      at the eval point; `\Box`'s generator introduces the guess variable and, when the guess is
      false, requests a witness lasso through the registry.
- [ ] Rewrite `operators.py`: each primitive operator carries its translation rule and its
      `true_at`/`false_at` as bit lookup; the defined operators keep their `derived_definition`s
      unchanged (they already reduce to primitives).
- [ ] Delete `_fresh_bound_int`, the process-global bound-variable counter and its reset, and every
      `ForAll`/`Exists` construction; drop `reset_bound_var_counter` from `core.py`'s
      `_reset_global_state`.
- [ ] Keep and update each operator's `print_method` for the new eval-point shape.

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: interface

**Scope Hypothesis**: `operators.py` is currently 1,777 lines across 9 primitive and 8 defined
operator classes; the rewrite is expected to remove the large majority of it (the per-operator Z3
quantifier bodies) and leave translation rules plus print methods. Confirm with `wc -l` before and
after, and by asserting in a test that no quantifier node appears anywhere in a fully built
constraint set for a nested-modal example.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators.py` - new
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py` - delete
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py` - delete

**Verification**:
- Per-operator tests green.
- Whole-constraint-set quantifier-free assertion green for a nested `\Box\Future` example.

---

### Phase 15: Iterator rewrite [NOT STARTED]

**Goal**: Iteration by difference constraints on labels and guesses, with isomorphism rejection.

**Tasks**:
- [ ] Write tests first: two successive models differ in at least one label bit or guess;
      a model that is a rotation of a previous one's periodic segments is rejected; a model that
      differs only by renaming witness lassos is rejected.
- [ ] Rewrite `iterate.py`'s `_create_difference_constraint` as a blocking clause over the label
      bits and the box guess.
- [ ] Implement `_create_non_isomorphic_constraint` as rejection modulo rotation of each lasso's
      `back`/`fwd` segments and permutation of the witness lassos (lasso 0 fixed).
- [ ] Rewrite `_calculate_differences` / `display_model_differences` to report label and guess
      differences instead of world-array differences.

**Timing**: 2 hours

**Depends on**: 12, 14

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - rewrite

**Verification**:
- Iteration tests green; `iterate: 3` on a countermodel example yields three pairwise
  non-isomorphic certificates, each passing the re-checker.

---

### Phase 16: Examples migration - settings and expectation audit [NOT STARTED]

**Goal**: Every example carries the new settings, and every expectation has been checked against
the paper rather than carried over.

**Tasks**:
- [ ] Replace `N`/`M`/`contingent`/`disjoint` in every example settings dict with `back`/`mid`/`fwd`
      (and `max_witnesses` where a box count warrants it), keeping `max_time` at or above the
      example budget floor.
- [ ] Audit the `\Until`/`\Since` argument order in every BX example against the paper's
      guard-first `until`/`since` clauses (D2), and record per example whether the formula as
      written means what its comment claims; fix the formula or the comment, and record which
      source of truth was chosen.
- [ ] Audit every `expectation` value against the paper's axioms, in particular `MF_MODAL_FUTURE_TH`
      (`□A → □GA`, valid per `thm:MF-valid`) and the perpetuity theorems `BM_TH_1`/`BM_TH_2`.
      **(Amendment, adequacy-layer task)** For `MF_MODAL_FUTURE_TH` specifically, the source of
      truth for the expectation flip (to `True`, no countermodel) is two landed, sorry-free Lean
      theorems, not a re-derivation: `modal_future_valid` (`Metalogic/Soundness.lean:373`) proves
      MF valid over the **unrestricted** frame class, and `no_witnessFamily_of_MF`
      (`Metalogic/Decidability/WitnessFamily/Examples.lean:275`) proves no certificate at any
      segment lengths refutes it. Cite both by name in the audit table's row for MF.
- [ ] **(Amendment, adequacy-layer task, folded in from the now-merged Phase 17 restoration step
      for this one example)** In `tests/unit/test_bimodal.py`, delete — not soften — the comment
      asserting MF "is NOT a theorem under current bimodal semantics (countermodel found at N=1,
      M=2)" and its trailing inline comment on the `KNOWN_TIMEOUT_EXAMPLES` entry; replace both with
      a statement that MF is valid in the paper's semantics (citing `modal_future_valid` and
      `no_witnessFamily_of_MF` as above), that the old countermodel was an artifact of the
      bounded-window encoding's boundary vacuity, and remove MF from `KNOWN_TIMEOUT_EXAMPLES`
      (its presence there was itself a mis-filing: the reason was semantic disagreement, not a
      timeout).
- [ ] Record the audit as a table in a comment block at the top of the affected section of
      `examples.py`, citing the paper's label for each axiom (no task-number references: this file
      is outside `specs/`).
- [ ] **(Amendment, adequacy-layer task)** Include the A0 frame-class standing test's two example
      formulas (Phase 9's `prior_UZ` and `z1` instances) in this audit pass, recording their
      expected verdict as "no certificate at any configured length, rendered inconclusive" rather
      than a `True`/`False` expectation — see ADEQUACY.md §7.2 and §7.4's never-report-validity
      rule.

**Timing**: 2 hours

**Depends on**: 12, 14

**Verification Tier**: local

**Scope Hypothesis**: `examples.py` is 1,482 lines carrying roughly 50 example settings dicts, of
which the BX-axiom family using `\Until`/`\Since` is the subset needing the order audit. Confirm
the exact counts at implementation time by counting `_settings = {` occurrences and
`\\Until\|\\Since` occurrences, and report them.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - migrate settings, audit expectations

**Verification**:
- `PYTHONPATH=code/src ./code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py`
  runs with no unknown-setting warnings.
- Every expectation change is accompanied by a cited paper reference in the audit table.

---

### Phase 17: Examples migration - restore the excluded examples [NOT STARTED]

**Goal**: The examples excluded by the retired encoding are active and passing.

**Tasks**:
- [ ] Re-activate `TN_CM_1`, `TN_CM_2`, `BM_CM_3`, `MD_TH_2`, `BM_TH_1`, `BM_TH_2`,
      `MF_MODAL_FUTURE_TH`, `BX7_LINEAR_U_TH`, `BX7P_LINEAR_S_TH` in `example_range` and confirm
      each has an entry in `countermodel_examples`/`theorem_examples`.
- [ ] Re-activate `BM_TH_5` (previously excluded "for Z3 state reasons") and confirm it behaves.
- [ ] For each, record the segment lengths at which it decides and its measured solve time.
- [ ] Raise the default segment lengths only if a genuinely needed example requires it, and record
      the reason.

**Timing**: 2 hours

**Depends on**: 16

**Verification Tier**: local

**Scope Hypothesis**: the exclusion set is the nine names in `test_bimodal.py`'s
`KNOWN_TIMEOUT_EXAMPLES` plus `BM_TH_5`. Confirm by reading that constant at implementation time
rather than trusting this list, and report any discrepancy.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - re-activate examples

**Verification**:
- Each of the ten runs to a decided verdict matching its audited expectation.
- Measured solve times recorded in the phase's commit message or the summary.

---

### Phase 18: Test suite part 1 - retire tests bound to deleted machinery [NOT STARTED]

**Goal**: No test in the tree asserts behaviour of the retired encoding.

**Tasks**:
- [ ] Enumerate every test module asserting retired behaviour and classify each as delete, rewrite,
      or keep: expected deletions include `test_frame_constraints.py`,
      `test_world_history_alignment.py`, `test_frame_class_mapping.py`,
      `test_enriched_equivalence.py`, and the retired-witness tests already replaced in Phases 6-7.
- [ ] Rewrite the behaviour-level temporal tests (`test_until_since.py`, `test_next_prev.py`,
      `test_until_since_integration.py`) against the certificate encoding, preserving the semantic
      claims they encode while dropping their window assumptions.
- [ ] Update `tests/conftest.py` fixtures: `basic_settings` / `minimal_settings` /
      `complex_settings` to the new settings, and the `witness_registry` /
      `constraint_generator` fixtures to the rewritten constructors.
- [ ] Update `tests/integration/test_injection.py`, `test_data_extraction.py`,
      `test_strict_semantics.py`, `test_api_consistency.py` for the new attribute surface.

**Timing**: 2 hours

**Depends on**: 14, 15

**Verification Tier**: local

**Scope Hypothesis**: the bimodal test tree is 20 modules totalling roughly 5,400 lines; the
delete/rewrite split above is a hypothesis, not an inventory. Confirm by running the suite after
Phase 15 and classifying each failing module by whether its claim survives the redesign; report the
actual classification.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` - update fixtures
- `code/src/model_checker/theory_lib/bimodal/tests/unit/` - delete/rewrite per the classification
- `code/src/model_checker/theory_lib/bimodal/tests/integration/` - update

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` collects with no
  import errors and no test referencing a deleted method.

---

### Phase 19: Test suite part 2 - green, fast, re-checked [NOT STARTED]

**Goal**: The whole bimodal suite green with no exclusion list, every found model re-checked, and a
recorded timing improvement.

**Tasks**:
- [ ] Empty `KNOWN_TIMEOUT_EXAMPLES` in `test_bimodal.py` (or delete the constant) and confirm the
      full parametrized example suite passes.
- [ ] Re-assess `UNSTABLE_EXAMPLES`: remove `BM_CM_1`'s marking if the redesign collapses its tail,
      and if anything is retained, re-justify it against the four entry criteria rather than
      carrying the old justification over.
- [ ] Assert the Phase 4 re-checker runs on every found model in the example suite (via the
      Phase 12 hook, with a test that the hook is actually reached).
- [ ] Record before/after wall-clock for the suite, and confirm no test needs a `max_time` above the
      floor for solver reasons.

**Timing**: 2 hours

**Depends on**: 4, 17, 18

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - remove exclusions
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - update

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` fully green.
- `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q` green (no regressions
  elsewhere).
- Timing record present in the commit message or summary.

---

### Phase 20: Oracle provider rewrite [NOT STARTED]

**Goal**: `oracle/bimodal_logic/` speaks the new semantics, and never claims validity.

**Tasks**:
- [ ] Write tests first against the provider interface: the verdict vocabulary, the frame-class
      declaration, and the never-claims-validity property.
- [ ] Rewrite `provider.py`: settings built from segment lengths instead of `N`/`M`/`temporal_depth`;
      `capabilities` re-declared (`max_back`/`max_mid`/`max_fwd` in place of `max_N`/`max_M`);
      `supported_frame_classes` re-declared for Z-time; `find_countermodel` returning the
      certificate-derived countermodel; the timeout contract preserved.
- [ ] Update `serialization.py` to serialize certificate-derived countermodels, and `translation.py`
      where it assumes the retired model shape.
- [ ] Delete the `temporal_depth`/`M = max(depth+2, 3)` sizing logic and its comments.

**Timing**: 2 hours

**Depends on**: 14, 16

**Verification Tier**: interface

**Files to modify**:
- `oracle/bimodal_logic/provider.py` - rewrite
- `oracle/bimodal_logic/serialization.py` - update
- `oracle/bimodal_logic/translation.py` - update
- `oracle/bimodal_logic/tests/test_oracle_provider.py` - rewrite
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - update

**Verification**:
- `pytest oracle/bimodal_logic/tests/test_oracle_provider.py -v` green.
- No code path returns a verdict that asserts validity.

---

### Phase 21: Oracle part 2 - retire abundance tests, regenerate the manifest [NOT STARTED]

**Goal**: The oracle suite carries no test of deleted machinery, and its conclusive manifest
reflects the new encoding.

**Tasks**:
- [ ] Delete the abundance and shift-closure soundness tests in `test_soundness_regression.py`
      together with the machinery they test, leaving the oracle's own soundness core and its
      unconditional-gating property untouched (explicitly out of scope).
- [ ] Update `test_boundary_regression.py`, `test_encoding_nondegeneracy.py`,
      `test_probe_solve_cost.py` and `test_timeout_skip_inventory.py` for the new encoding, or
      delete those whose subject no longer exists, recording which and why.
- [ ] Regenerate `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` under the new
      encoding and update its `notes` field with the regeneration method.
- [ ] Update the floor constant guarding the conclusive scan if the regenerated population changes
      it, with the measured new value recorded.

**Timing**: 2 hours

**Depends on**: 20

**Verification Tier**: full

**Scope Hypothesis**: the oracle bimodal test tree is 15 modules totalling roughly 10,300 lines;
the abundance/shift-closure subset inside `test_soundness_regression.py` (1,220 lines) is the
intended deletion, not the whole module. Confirm by grepping for `abundance`/`shift_closure` inside
it at implementation time and report the actual line counts deleted.

**Files to modify**:
- `oracle/bimodal_logic/tests/test_soundness_regression.py` - delete the abundance/shift-closure tests
- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` - regenerate
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - update the floor constant
- `oracle/bimodal_logic/tests/` - update or delete per the classification

**Verification**:
- `bash oracle/run-oracle-suite.sh` green (with the gating clause still present at this point).
- The soundness core's test node ids are unchanged, confirming it was not modified.

---

### Phase 22: Documentation rewrite [NOT STARTED]

**Goal**: Theory documentation describes the certificate design, with the frame-axiom ledger and
duration-guard gap note retired.

**Tasks**:
- [ ] Rewrite `README.md`'s semantics sections: certificate definition, the four conditions, the
      certified ShiftSet, the new settings, the output shape; delete the abundance, world-interval,
      Skolem-abundance and time-shift sections.
- [ ] Rewrite `docs/ARCHITECTURE.md`: retire the frame-axiom ledger table and the
      "Duration-domain guard (open gap)" note; describe the two-phase constraint emission and the
      re-check hook; state explicitly that validity is never reported.
- [ ] Rewrite `docs/SETTINGS.md` for `back`/`mid`/`fwd`/`max_witnesses`, `docs/API_REFERENCE.md`
      for the new classes and functions, `docs/USER_GUIDE.md` for the new workflow, and
      `docs/ITERATE.md` for the new difference/isomorphism story.
- [ ] Update `oracle/bimodal_logic/README.md` and `KNOWN_EXTERNAL_DEFECTS.md`, and document the
      certificate JSON export with a pointer to BimodalLogic's protocol section as the contract.
- [ ] Check every rewritten file for task-number references and remove them (these files are
      outside `specs/`).
- [ ] **(Amendment, adequacy-layer task)** Carry the (SOUND) theorem statement, the four lemmas
      (Frame, Histories, Time-shift preservation, Truth lemma) and the Lean citation table into
      `docs/ARCHITECTURE.md`, replacing the retired frame-axiom ledger table with this statement
      rather than leaving that section simply deleted.
      `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (created by the adequacy-layer
      task) is the source for this content — cite it as the fuller treatment and reproduce its
      statements rather than re-deriving them here.

**Timing**: 2 hours

**Depends on**: 19, 21

**Verification Tier**: prose

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/README.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md`
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md`
- `oracle/bimodal_logic/README.md`

**Verification**:
- `grep -rn "abundance\|shift.closure\|frame.axiom\|ForAllTime"` over the bimodal docs returns only
  historical-context mentions, if any.
- `bash .claude/scripts/check-task-references.sh` (or equivalent) reports no new violations.

---

### Phase 23: Remove the development marker and re-enable gating [NOT STARTED]

**Goal**: Bimodal is a gating theory again, with every quarantine mechanism removed rather than
left inert.

**Tasks**:
- [ ] Delete the `pytest_collection_modifyitems` hook from
      `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` (its own docstring names this
      as the exit path).
- [ ] Delete the `development` half of `oracle/conftest.py`'s hook and the marker registration in
      `code/pyproject.toml`.
- [ ] Remove `and not development` from every gating invocation: `flake.nix` (2), `.github/workflows/tests.yml` (2),
      `packaging.yml` (1), `release.yml` (2), `pypi-smoke.yml` (1), `oracle/run-oracle-suite.sh` (2),
      and the documentation strings in `code/run_tests.py`.
- [ ] Retire or rewrite the CI contract tests that assert the marker's application:
      `test_development_marker_application.py`, `test_oracle_development_marker_application.py`,
      `test_gating_selection_bimodal_decoupling.py`, and the `development` clauses in
      `test_run_tests_markers.py` and `test_unstable_deselection_wiring.py`.
- [ ] Update `code/docs/core/TESTING_GUIDE.md` section 8.14 to record that the marker's single
      subject has exited development, and update `code/tests/README.md` and
      `bimodal/tests/README.md` accordingly.
- [ ] Re-assess the `test_example_budget_floor.py` comments that cite bimodal exclusions as
      justification, since those exclusions no longer exist.

**Timing**: 2 hours

**Depends on**: 19, 21

**Verification Tier**: full

**Scope Hypothesis**: ten gating invocations carry `and not development` across seven files, and
five CI contract tests assert the marker. Confirm at implementation time with
`grep -rn "not development"` across the repository (excluding `specs/`) and report the actual
counts; the guard that the count is right is `test_unstable_deselection_wiring.py`'s own
enumeration of the gating invocations.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`
- `oracle/conftest.py`
- `code/pyproject.toml`
- `flake.nix`
- `.github/workflows/tests.yml`, `packaging.yml`, `release.yml`, `pypi-smoke.yml`
- `oracle/run-oracle-suite.sh`
- `code/run_tests.py`
- `code/tests/ci/test_development_marker_application.py`, `test_oracle_development_marker_application.py`,
  `test_gating_selection_bimodal_decoupling.py`, `test_run_tests_markers.py`, `test_unstable_deselection_wiring.py`
- `code/docs/core/TESTING_GUIDE.md`

**Verification**:
- `grep -rn "not development"` outside `specs/` returns nothing (or only historical CHANGELOG text).
- `pytest code/tests/ci -v` green.
- The gating expression now collects bimodal's tests: verify with `--collect-only` that the count
  rises by the bimodal tree's size.

---

### Phase 24: Final verification [NOT STARTED]

**Goal**: The whole repository green under the real gating selections, with the redesign's claims
measured rather than asserted.

**Tasks**:
- [ ] Run the main gating selection (`pytest src/model_checker tests` with the release `-m`
      expression, now without `and not development`) and record the result and wall-clock.
- [ ] Run `bash oracle/run-oracle-suite.sh` and record the result.
- [ ] Run the example suite through `dev_cli.py` and confirm the printed output matches the new
      shape for at least one countermodel and one no-certificate case.
- [ ] Record the before/after comparison: examples active, examples excluded, suite wall-clock,
      and the certificate round-trip status.
- [ ] Confirm every deliverable in the task description has a corresponding landed change, and
      name explicitly anything deliberately left out.

**Timing**: 1.5 hours

**Depends on**: 22, 23

**Verification Tier**: full

**Files to modify**:
- none (verification only; findings go in the implementation summary)

**Verification**:
- Both gating suites green.
- The recorded comparison shows zero excluded bimodal examples and a measured speedup.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` fully green
      with no exclusion list and no `development` marker.
- [ ] Every found model in the example suite passes the pure-Python re-checker (enforced in the
      structure, not only in tests).
- [ ] Every fixture certificate receives the same verdict from the Python re-checker and from
      `lake exe check_certificate` (skipped cleanly when BimodalLogic is unavailable).
- [ ] The full constraint set for a nested-modal example contains no quantifier node.
- [ ] `bash oracle/run-oracle-suite.sh` green, with the oracle soundness core unmodified.
- [ ] `pytest code/tests/ code/src/model_checker -q` green under the release gating `-m` expression.
- [ ] `pytest code/tests/ci -v` green after the marker removal.
- [ ] No output path claims validity; the no-certificate case is rendered as inconclusive.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` (new)
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (new)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, `model.py`, `proposition.py`,
  `witness_registry.py`, `witness_constraints.py` (rewritten)
- `code/src/model_checker/theory_lib/bimodal/operators.py`, `iterate.py`, `examples.py` (rewritten)
- `code/src/model_checker/theory_lib/bimodal/tests/` (rewritten, incl. new
  `test_formula.py`, `test_certificate.py`, `test_semantics_core.py`, `test_structure.py`,
  `test_operators.py`, `test_proposition.py`, `integration/test_certificate_roundtrip.py`)
- `code/src/model_checker/theory_lib/bimodal/README.md` and `docs/*.md` (rewritten)
- `oracle/bimodal_logic/provider.py`, `serialization.py`, `translation.py`, tests, and
  `tests/data/known_conclusive_complexity5.json` (rewritten/regenerated)
- Gating and CI wiring with the `development` marker removed
- `specs/184_.../summaries/01_witness-family-certificate-redesign-summary.md` (at completion)

## Rollback/Contingency

The redesign is a clean break with no compatibility layer, so partial landing is the real risk
rather than an unrecoverable one. Each phase commits independently at its own green sub-step, so
the safe rollback unit is a phase: `git revert` the phase's commits, which leaves earlier phases
intact. The one point where the theory is unavoidably red between commits is Waves 6-8 (Phases
9-13), where the semantics, structure and operators are replaced; before starting Phase 9, take a
durable non-reverting checkpoint with `bash .claude/scripts/git-snapshot.sh 184 --no-revert` so
the pre-rewrite tree is recoverable without discarding the working tree. If a genuine whole-tree
rollback becomes necessary, follow `context/contracts/recovery.md`'s rollback rung for the exact
snapshot-then-revert invocation, including its out-of-scope override flag. Should the task be
abandoned mid-flight, the `development` marker (Phase 23) is the last thing removed, so bimodal
stays off the gate for the entire period the theory is in transition.
