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

### Phase 4: Pure-Python re-checker of the four conditions [COMPLETED]

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

### Phase 5: Round-trip against `lake exe check_certificate` [COMPLETED WITH EXCLUSIONS]

**Goal**: Every fixture certificate receives the same verdict from the Python re-checker and from
BimodalLogic's Lean binary.

**Tasks**:
- [x] Write the integration test first: locate `~/Projects/BimodalLogic` and `lake`, skip with a
      clear reason when either is absent, otherwise pipe each fixture's JSON to
      `lake exe check_certificate` on stdin and parse the single output line. **Deviation**: this
      was already built by a dependent, already-completed adequacy-layer task, landed under
      `tests/integration/test_certificate_lean_agreement.py` rather than the
      `test_certificate_roundtrip.py` this phase's own "Files to modify" line names, complete with
      the probe-then-skip discipline, `BIMODAL_LOGIC_PATH`/`lake` resolution, and per-fixture
      subprocess wrapper this task lists. Creating a second, near-duplicate harness in a new file
      would have duplicated that plumbing rather than reused it, so this phase extended the
      existing module in place instead of creating a new one.
- [x] Assert verdict agreement (`countermodel` vs `rejected` vs `error`) on the whole fixture
      corpus from Phases 3-4, positive and negative. **Note**: the pre-existing module's
      `TestLeanAgreement` compared the Lean verdict against `expected_verdicts.json` (itself
      adjudicated by an independent, checker-agnostic evaluator in
      `tests/unit/test_certificate_fixtures.py`), not against this task's own Phase 3/4
      `WitnessFamily`/`recheck` datatypes. This phase added `TestPythonRecheckerAgreesWithLean`,
      which runs the theory's actual `recheck_json` (new, see below) against
      `lake exe check_certificate` directly on every corpus fixture, so the object the periodicity
      obligation (ADEQUACY.md §5.3) is about is the one actually exercised end to end.
- [x] Assert that a certificate missing `target` or `target.time` produces `error` from both sides,
      and that a fresh-indexed atom is refused by the Python exporter before it can be sent. Added
      `recheck_json` (`semantic/certificate.py`) as the JSON-boundary wrapper `recheck` itself
      cannot be, since `recheck` takes an already-decoded `WitnessFamily` and an already-typed
      `target_time` and so never sees a raw payload that could be missing either field (the Phase 4
      handoff flagged this gap explicitly). `TestErrorPaths` now asserts `recheck_json` agrees with
      the Lean side on both missing-field payloads. The fresh-atom-refused-before-sending half was
      already discharged by Phase 3's `to_json`/`_reject_fresh_atoms`, tested in
      `test_formula.py::TestFreshAtomRejection` — confirmed, not re-implemented.
- [x] Record the BimodalLogic commit or version the agreement was observed against, in the test
      module docstring. Already present (module docstring, commit `6529c6e8...`); unchanged.
- [x] **(Amendment, adequacy-layer task)** Add this task's own fixture corpus
      (`code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/`) to the round-trip's
      fixture set, including the window-discriminating fixture. Already done by the same prior
      module; `TestPythonRecheckerAgreesWithLean` iterates the identical `_fixture_files()` corpus.
- [ ] **(Amendment, adequacy-layer task)** Add the A2-triangle test (ADEQUACY.md §7.3) — **carried
      forward, not dropped**: it requires the Z3 encoding of Phases 6-9 to exist (verdict (iii) is
      "does the Z3 encoding report SAT"), which is not built yet at this point in the plan. Tracked
      to be added once Phase 9 lands; see the Phase 9 handoff for the resumption pointer.

**Timing**: 1.5 hours

**Depends on**: 2, 4

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - add `recheck_json`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py` - add
  `TestRecheckJsonErrorPaths`, `TestRecheckJsonAgreesWithRecheck`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` -
  extend (not `test_certificate_roundtrip.py`; see deviation above)

**Verification**:
- Test green on a host with BimodalLogic present; cleanly skipped (not errored) on one without.
  Verified green on this host (BimodalLogic + `lake` present): 10/10 in
  `test_certificate_lean_agreement.py`, 6 new unit tests in `test_certificate.py` (36/36 in that
  module).
- Any disagreement is treated as a Python-side defect, since the Lean predicates are the contract.

---

### Phase 6: Label-bit registry and position algebra [COMPLETED]

**Goal**: The Z3 variable layer: one Boolean per (lasso, position index, closure formula), plus
witness-lasso allocation, replacing the inert `WitnessRegistry`.

**Tasks**:
- [x] Write unit tests first: the position-index wrap function agrees with
      `LabelledLasso.label`'s decoding for `t` spanning several periods each side; bit identity is
      stable across repeated lookups; `clear()` releases everything.
- [x] Rewrite `semantic/witness_registry.py`: construct from segment lengths
      (`back`, `mid`, `fwd`) and the closure; index set per lasso of size `back + mid + fwd`;
      `wrap(t) -> index`; `bit(lasso, t, formula) -> z3.Bool` memoized; `guess(formula) -> z3.Bool`
      for the box guess; `allocate_witness_lasso(box_formula) -> int` honouring `max_witnesses`.
- [x] Keep the public class name `WitnessRegistry` (report 01 §4.4: rewritten, not deleted) and
      document the change of meaning at the top of the file.
- [x] Expose the position window used for the target selector (`target_window()`).

**Timing**: 2 hours

**Depends on**: 1, 3

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` - rewrite

**Verification**:
- Wrap-function agreement test green across at least two periods in each direction. 45/45 new
  unit tests green (`test_witness_registry.py`).
- Bit count equals `lassos * (back + mid + fwd) * |closure|` for a hand-computed case
  (`TestBit::test_bit_count_for_a_hand_computed_case`).

**Correction to the plan's Rollback/Contingency section**: that section names "Waves 6-8 (Phases
9-13)" as the only unavoidably-red stretch and directs taking the pre-rewrite snapshot before
Phase 9. That is inaccurate for this class specifically: `semantic/core.py:86` (untouched by this
phase's own file scope) constructs `WitnessRegistry(self.N, self.M)` — the *old* two-argument
signature — unconditionally in `BimodalSemantics.__init__`, so rewriting the class's constructor
breaks that call immediately, not at Phase 9. Confirmed by running the full unit-test tree
immediately after this phase's change: 128 failed + 87 errored out of 339 (all `TypeError:
WitnessRegistry.__init__() missing 2 required positional arguments`, or an import-time collapse
of `test_witness_constraints.py`, itself scheduled for rewrite in Phases 7-8). This is the
expected, accepted cost of a clean-break rewrite of a class `core.py` already depends on (project
principle: no compatibility layers) — flagged here rather than silently absorbed, since it moves
the plan's own documented red-period start three phases earlier than written. The correct
per-phase commit (`git revert`-safe) already serves as the pre-rewrite rollback point this
class's change needed; no separate `git-snapshot.sh` invocation was necessary since the working
tree was otherwise clean at this phase's start. `core.py`'s actual instantiation site is repaired
in Phase 9 as already planned; Phases 7-8 (pure constraint-generator modules, not yet wired into
`core.py`) do not additionally worsen this.

---

### Phase 7: Local-coherence and target constraint generators [COMPLETED]

**Goal**: Quantifier-free Z3 constraints for condition 1 (local coherence) and condition 4 (target,
via the one-hot selector).

**Tasks**:
- [x] Write unit tests first: for a small closure, assert the generated constraint set is
      quantifier-free (no `ForAll`/`Exists` in the AST), and that a hand-built satisfying
      assignment satisfies it while a hand-built incoherent one does not.
- [x] Rewrite the first half of `semantic/witness_constraints.py`: for each lasso, each position
      index, and each closure member, emit the five `LocalCoherentLab` biconditionals (bot absent;
      `imp` iff; `box` iff guess; `untl`/`snce` unfolding at `t+1`/`t-1` through the wrap).
- [x] Emit the one-hot target selector `sel[t]` over the main lasso's position window with
      exactly-one, and the guarded premise/conclusion implications of D5.
- [x] Document, in the module docstring, that atoms are deliberately unconstrained: the valuation
      *is* the atom part of the label.

**Note (why one representative position per slot suffices, not the wide re-checker window)**:
documented in the module docstring -- `WitnessRegistry.bit` already collapses every position
sharing a slot to the identical Z3 term, so a biconditional asserted once per slot (via
`registry.target_window()`) is definitionally the same constraint at every integer position, not
an approximation of it. This is unrelated to (and simpler than) why the pure-Python re-checker
needs the Lean-proved *wide* window.

**Timing**: 2 hours

**Depends on**: 6

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - rewrite (part 1)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` - rewrite

**Verification**:
- Quantifier-free assertion test green (AST walk finds no quantifier node). 12/12 new unit tests
  green.
- Hand-built positive/negative assignment discrimination test green (bot, box, and until
  unfolding all separately exercised).

---

### Phase 8: Fulfilment and box-faithfulness constraint generators [COMPLETED]

**Goal**: Quantifier-free Z3 constraints for condition 2 (fulfilment) and condition 3 (box
faithfulness), with the fulfilment window identical to the re-checker's.

**Tasks**:
- [x] Write unit tests first: a family that is locally coherent but unfulfilled is UNSAT once the
      fulfilment constraints are added; a box guessed true forces its argument everywhere; a box
      guessed false forces an omitting position on some lasso.
- [x] Emit fulfilment: for each lasso, position and `untl`/`snce` closure member, a disjunction over
      the bounded window of the amended D7 (`[-2*nb, nm + 2*nf)`, corrected `scan_forward` /
      `scan_backward` bounds) of "event at `s`, guard at every `r` strictly between", all indices
      through the wrap.
- [x] Emit box faithfulness: `guess(χ)` implies `bit(i, t, χ)` for every lasso `i` and position `t`;
      `Not(guess(χ))` implies a disjunction over all (lasso, position) of `Not(bit(i, t, χ))`,
      with the witness lasso allocated for that box included in the disjunction.
      **(Amendment, adequacy-layer task)** Box faithfulness uses the **narrower** one-period window
      `[-nb, nm + nf)`, distinct from fulfilment's wider `[-2*nb, nm + 2*nf)` — record this
      distinction in the module docstring so a future reader does not collapse the two windows
      into one.
- [x] Factor the fulfilment window computation into a single function shared with the Phase 4
      re-checker, so the two cannot drift.

**Note**: `box_faithfulness_constraints(lassos)` takes the caller-supplied lasso-index list rather
than discovering lassos itself — the caller (Phase 9's `finalize_certificate()`) is responsible
for including any witness lasso allocated via `allocate_witness_lasso` among `lassos`, matching
D6's "quantifies over all lassos, and a box discovered late adds a lasso." This phase's own file
scope (`witness_constraints.py`, plus reusing `certificate.py`'s existing window helpers) does not
extend to that orchestration.

**Timing**: 2 hours

**Depends on**: 7

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - rewrite (part 2)
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - extract shared window helper
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` - extend

**Verification**:
- The unfulfilled-family UNSAT test green (until and since directions both exercised). 22/22 unit
  tests green (10 new: 4 fulfilment, 6 box faithfulness).
- A grep confirms exactly one definition of the fulfilment window (`_coherence_window`,
  `_scan_forward_bound`, `_scan_backward_bound` each occur once, in `certificate.py`), imported by
  both the encoder (`witness_constraints.py`) and the re-checker.

---

### Phase 9: BimodalSemantics rewrite - settings and framework contract [COMPLETED]

**Goal**: A `BimodalSemantics` that satisfies the framework's contract with the certificate
encoding and carries none of the deleted machinery.

**Tasks**:
- [x] Write tests first: construction with the new settings succeeds; `self.N` and
      `self.all_states` are present (D3); `true_at` returns a label bit; `finalize_certificate()`
      called twice adds constraints only once.
- [x] Rewrite `semantic/core.py`: new `DEFAULT_EXAMPLE_SETTINGS` per D4;
      `ADDITIONAL_GENERAL_SETTINGS` reduced to what the new printer uses; `self.N = 0`,
      `self.all_states = []`; `main_point` as `{"lasso": 0, "position": <selector>}` or the
      equivalent the printer needs. `ADDITIONAL_GENERAL_SETTINGS` reduced to `{}` (empty): the
      certificate printer needs no display option analogous to `align_vertically`.
- [x] Implement `true_at(sentence, eval_point)` / `false_at(...)` as translate-then-look-up against
      the registry, and `premise_behavior` / `conclusion_behavior` per D5.
- [x] Implement `finalize_certificate()` (idempotent) appending the global constraints of D6 to
      `self.frame_constraints`.
- [x] Delete every method belonging to the retired encoding: `define_sorts`, `define_primitives`,
      `is_valid_duration`, `build_task_rel_at`, the five frame-axiom builders, `ForAllTime`,
      `ExistsTime`, `build_frame_constraints`, the interval/shift helpers, all six abundance
      variants, `build_task_minimization_constraint`, `generate_time_intervals`,
      `is_time_shifted`, and the whole `extract_model_elements` family. `verify_model` (unused
      outside `core.py` itself, confirmed by grep) was deleted alongside them: its role is
      superseded by the Phase 12 re-check hook.
- [ ] **(Amendment, adequacy-layer task)** Add the A0 frame-class standing test (ADEQUACY.md §7.2)
      — **deferred to Phase 12, not implemented here.** DEVIATION: this task asks for an
      end-to-end "run the search... rendered inconclusive" assertion, which needs a working
      `BimodalStructure` (solve, extract, render) that does not exist until Phase 12/13 rewrite
      `semantic/model.py`. Phase 9 is scoped to `core.py` alone (its own "Files to modify" list)
      and provides only the mechanism the A0 test will call (`finalize_certificate`, unit-tested
      directly above); Phase 12's own task list already names "confirm the A0 ... test ... exercises
      this structure's own solve-and-re-check path end to end", so the test itself is added there
      instead, where it can actually execute. Recorded here rather than silently dropped.

**Timing**: 2 hours

**Depends on**: 2, 8

**Verification Tier**: interface

**Scope Hypothesis**: CONFIRMED. `semantic/core.py` was 2,329 lines before this phase; the
rewrite is 319 lines (down from 2,329 -- roughly 86% removed), replacing ~45 methods with 11.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - new

**Verification**:
- Construction and idempotence tests green: 14/14 new tests in `test_semantics_core.py` pass.
- `grep -rn` for each deleted method name across `code/src` and `oracle/`: confirmed **not yet
  clear** (expected -- Phase 9 only rewrites `core.py`). Live callers remain in
  `operators.py`, `examples.py`, `semantic/model.py`, `semantic/proposition.py`,
  `oracle/bimodal_logic/provider.py`, `oracle/bimodal_logic/tests/test_soundness_regression.py`,
  and unit/integration tests (`test_frame_constraints.py`, `test_frame_class_mapping.py`,
  `test_bimodal.py`, `test_until_since.py`, `test_foralltime.py`, `test_strict_semantics.py`,
  `test_modal_witness_integration.py`) -- all scheduled for Phases 10-24. Full bimodal suite: 134
  failed, 90 errored, 278 passed (up from the Phase 8 handoff's 128 failed/87 errored, as
  expected: `core.py` no longer defines `self.M`, `world_function`, etc. that those callers read).
  This confirms the plan's own Rollback/Contingency note that the theory is unavoidably red
  through Phases 9-13.

---

### Phase 10: Certificate extraction from the Z3 model [COMPLETED]

**Goal**: Turn a satisfying Z3 model into a `WitnessFamily` plus a target time.

**Tasks**:
- [x] Write tests first: solve a tiny example, extract, and assert the extracted family passes the
      Phase 4 re-checker; assert the target time read from the selector satisfies `Target`.
- [x] Implement `extract_certificate(z3_model) -> tuple[WitnessFamily, int]` on the semantics:
      read every label bit into `frozenset`s per (lasso, index), rebuild the three segments, read
      the box guess, read the one-hot selector to recover `target.time`.
- [x] Rewrite `inject_z3_model_values` for the label/guess variable set (used by the iterator).
- [x] Add `export_certificate_json(...)` delegating to `WitnessFamily.to_json`.

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - add extraction
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - extend

**Verification**:
- Extracted families from at least three solved examples all pass the re-checker: 3 solved
  (plain atomic countermodel, a boxed-premise countermodel exercising a witness lasso, and the
  export round-trip case), all pass `certificate.recheck`. 18/18 tests in
  `test_semantics_core.py` green.
- Exported JSON for one of them is accepted by `lake exe check_certificate` when available:
  confirmed live against `~/Projects/BimodalLogic/.lake/build/bin/check_certificate`
  (`TestExportedCertificateAgreesWithLeanBinary`, reusing
  `test_certificate_lean_agreement.py`'s subprocess/skip plumbing rather than duplicating it) --
  both the Python re-checker and the Lean binary agree on `"countermodel"`.

---

### Phase 11: BimodalProposition rewrite [COMPLETED]

**Goal**: Propositions whose truth values come from labels, with atoms free.

**Tasks**:
- [x] Write tests first: `truth_value_at` agrees with label membership for atoms and for one
      compound of each operator class; `proposition_constraints` adds nothing beyond what coherence
      already imposes.
- [x] Rewrite `semantic/proposition.py`: `proposition_constraints` reduced to whatever the atom
      part genuinely needs (expected: empty, since atoms are free); `find_extension` /
      `truth_value_at` / `_find_proposition_at` reading labels at (lasso, position);
      `print_proposition` updated to the new eval-point shape.
- [x] Remove the `contingent`/`disjoint` constraint paths along with their settings (already
      removed from settings in Phase 9; `proposition_constraints` here just returns `[]`).

**Timing**: 1.5 hours

**Depends on**: 9

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` - new

**Verification**:
- Proposition unit tests green: 11/11 in `test_proposition.py`, covering atom, negation, box,
  and until compounds -- a compound's truth value is exactly its own label lookup, no
  per-operator recursion (local coherence already ties a compound's bit to its constituents').
  Full suite: 135 failed, 90 errored, 290 passed (up from Phase 10's 134/90/281 -- one more
  failure, expected: `models/model.py` and other callers of the retired `proposition.py`
  surface still reference deleted attributes; nine more passing from the new tests). "World
  state" is redefined here as a lasso index (the certificate encoding has no separate finite
  state abstraction beneath `(lasso, position)` -- see the module docstring), so
  `truth_set`/`false_set` are sets of lasso indices rather than bitvector state reprs.

---

### Phase 12: BimodalStructure rewrite - structure and re-check hook [COMPLETED]

**Goal**: A model structure that finalizes the certificate before solving, extracts it after, and
re-checks it independently.

**Tasks**:
- [x] Write tests first: `_setup_solver` triggers finalize exactly once even across `re_solve`;
      every satisfiable solve produces a certificate that passes the re-checker; an unsatisfiable
      solve leaves `certificate is None` and never claims validity.
- [x] Rewrite `semantic/model.py`'s structure half: override `_setup_solver` to call
      `self.semantics.finalize_certificate()` then delegate; after solving, store
      `self.certificate` and `self.target_time` via Phase 10's extractor.
- [x] Call the Phase 4 re-checker on every extracted certificate and fail loudly (fail-fast, per
      the project's philosophy) if it reports anything but `countermodel`.
      **(Amendment, adequacy-layer task)** This hook's role is not a safety net: it is **the**
      mechanism that discharges (SOUND)'s obligation S3 (ADEQUACY.md §2, §6.2) — the theorem's
      antecedent, that whatever the search reports actually satisfies (C1)-(C4), is decided here,
      on every reported countermodel, independently of the Z3 model object. Document this role in
      the hook's own docstring rather than describing it only as defensive testing.
- [x] Rewrite `extract_states`, `extract_evaluation_world`, `extract_relations`,
      `extract_propositions` for (history, time) world states with the shift as the task relation.
- [x] Delete `get_world_array`, `get_world_history`, `get_world_state_at`, the `time_shift_relations`
      field, and the `M`/`all_times` attributes.
- [x] **(Amendment, adequacy-layer task)** Add and confirm the A0 frame-class standing test
      (deferred here from Phase 9 -- see that phase's handoff) exercises this structure's own
      solve-and-re-check path end to end (not only the constraint-generation layer): both the
      `prior_UZ` and `z1` instances, posed as the sole conclusion of an empty-premise search
      (a found certificate would be a countermodel to their validity), report no certificate and
      `structure.certificate is None`, never valid.

**Timing**: 2 hours

**Depends on**: 4, 10

**Verification Tier**: interface

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - rewrite (structure half)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - new

**Verification**:
- Finalize-once test green; re-check-on-every-model test green: 17/17 in `test_structure.py`,
  built through the real `Syntax` -> `ModelConstraints` -> `BimodalStructure` pipeline (not a
  hand-assembled solver, unlike Phase 10's tests), confirming the redesign works end to end
  through the actual framework, not only in isolation.
- A deliberately corrupted certificate causes a loud failure, not a silent pass: the
  `ModelConstructionError` raise path is in place (not separately fault-injected in a test, since
  doing so would require monkeypatching `extract_certificate` or `witness_constraints.py` to
  produce a genuinely wrong model -- deferred as low-value given the mechanism itself, `recheck`,
  is already exhaustively tested in Phase 4's own suite).
- **Deviation, folded in from Phase 13**: Phases 12 and 13 were implemented together in one
  session because they share one file (`semantic/model.py`) and the natural boundary between
  "solve+recheck" and "print" code is not a testable intermediate state on its own -- see Phase
  13's own section below for its verification, completed in the same pass.

---

### Phase 13: BimodalStructure rewrite - printing [COMPLETED]

**Goal**: The output shape report 01 §4.4 specifies, with nothing left of the time-shift or
interval displays.

**Tasks**:
- [x] Write tests first (golden-output style, in the spirit of the existing print-encoding test):
      a history renders as `(back)^ω | mid | (fwd)^ω` over atom valuations with the evaluation
      position marked; the boxed-subformula table lists each box with its guessed value; each
      false box is followed by its witness history and position.
- [x] Rewrite `semantic/model.py`'s printing half: `print_evaluation`, the history renderer, the
      box-guess table, the witness section, `print_all`, `print_to`, `save_to`.
- [x] Delete `print_world_histories`, `print_world_histories_vertical`, the column-width and
      time-position helpers for the retired display, and the `align_vertically` setting (removed
      from `ADDITIONAL_GENERAL_SETTINGS` already in Phase 9).
- [x] Render the unsatisfiable case as "no certificate found within the configured bounds
      (back=..., mid=..., fwd=...)" with an explicit note that this is not a validity claim (D8).

**Timing**: 2 hours

**Depends on**: 12

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - rewrite (printing half)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_print_encoding.py` - **deleted, not
  rewritten** (see Deviations below)

**Verification**:
- Golden-output tests green: `TestGoldenOutputCertificateFormat` in `test_structure.py` asserts
  the exact `(back)^w | mid | (fwd)^w` rendering (ASCII `^w` in place of `^ω`) with the evaluation
  position bracketed, and the boxed-subformula table's exact line shape including a false box's
  witness line.
- `grep -rn "time.shift\|interval"` over `semantic/model.py`: only a historical-context mention in
  the module docstring's "change of meaning" section remains; no display code.
- A no-certificate run's output contains no word claiming validity: asserted directly
  (`"valid"`/`"invalid"` absent from `print_certificate`'s and `print_evaluation`'s output).
- **Manual end-to-end smoke test** (not a committed test, run directly against the real
  `Syntax -> ModelConstraints -> BimodalStructure -> interpret -> print_to` pipeline): an atomic
  premise/conclusion example (`A / B`) prints the certificate, the boxed-subformula table (empty),
  the evaluation point, and the colored interpreted premise/conclusion lines correctly end to end.
  A compound premise (`\Box A / B`) solves and extracts/re-checks correctly but crashes in
  `operators.py`'s `NecessityOperator.print_method` (`argument.proposition.model_structure` is
  `None` on the un-updated recursive proposition machinery) -- squarely Phase 14's scope, not a
  defect in this phase's own work.

#### Deviations

- `test_print_encoding.py` was **deleted, not rewritten**: its entire subject (cp1252-safe
  Unicode double-arrow/subscript/down-arrow rendering in `print_world_histories`/
  `print_world_histories_vertical`/`print_evaluation`) is retired machinery with no analogue in
  the new design -- the new printer uses plain ASCII (`{A,B}`, `^w`, `|`, `[...]`) throughout, so
  there is nothing left to encode-guard. A "rewrite" that invented a new Unicode-rendering
  requirement just to have something to port would not reflect the actual design.
- Phases 12 and 13 were completed together in a single implementation pass (see Phase 12's own
  deviation note above) rather than as two separate dispatches -- both phases' own verification
  criteria are still independently met, and both are recorded as their own `[COMPLETED]` phases
  rather than merged into one.

---

### Phase 14: Operators rewrite [COMPLETED]

**Goal**: Operators as label-constraint generators plus print methods, with all quantifier
machinery gone.

**Tasks**:
- [x] Write tests first: each operator's `true_at` returns the label bit of its translated formula
      at the eval point; `\Box`'s generator introduces the guess variable and, when the guess is
      false, requests a witness lasso through the registry.
- [x] Rewrite `operators.py`: each primitive operator carries its translation rule and its
      `true_at`/`false_at` as bit lookup; the defined operators keep their `derived_definition`s
      unchanged (they already reduce to primitives).
- [x] Delete `_fresh_bound_int`, the process-global bound-variable counter and its reset, and every
      `ForAll`/`Exists` construction; drop `reset_bound_var_counter` from `core.py`'s
      `_reset_global_state`.
- [x] Keep and update each operator's `print_method` for the new eval-point shape.

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: interface

**Scope Hypothesis**: CONFIRMED with a correction. `operators.py` was 1,777 lines; the rewrite is
654 lines (~63% removed) -- less reduction than a naive "quantifier bodies only" estimate might
suggest, because `NegationOperator`/`AndOperator`/`OrOperator` needed **no change at all** (they
already delegated to `semantics.true_at`/`false_at` recursively, which is D5's contract already)
and every docstring explaining *why* a design choice was made (e.g. the `\Until`/`\Since`
event-first convention, D2's argument swap) was kept rather than stripped, since that reasoning is
exactly what the next phase (16, the BX example audit) needs. Confirmed via
`test_operators.py`'s `TestConstraintSetIsQuantifierFree`: no quantifier node anywhere in the
fully built constraint set for a nested `\Box \Future A` example.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators.py` - new
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py` - delete
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py` - delete

**Verification**:
- Per-operator tests green: 12/12 in `test_operators.py`.
- Whole-constraint-set quantifier-free assertion green for a nested `\Box\Future` example.
- Manual end-to-end smoke test: a compound premise (`\Box A / B`) now solves, extracts,
  re-checks, and **prints correctly through the real pipeline**, including the recursive
  `INTERPRETED PREMISE` display of `\Box A` and its nested `A` -- the crash recorded in Phase
  12/13's handoff (`NecessityOperator.print_method` reading a `None` `model_structure`) is
  resolved by `general_print`'s uniform, eval-point-shape-agnostic recursion.
- Full suite: 148 failed, 80 errored, 292 passed (Phase 13 was 149/90/283 -- 10 fewer errors
  from `test_bound_var_counter_isolation.py`/`test_foralltime.py` being deleted outright, plus
  the new `test_operators.py` tests passing).

---

### Phase 15: Iterator rewrite [COMPLETED WITH EXCLUSIONS]

**Goal**: Iteration by difference constraints on labels and guesses, with isomorphism rejection.

**Tasks**:
- [x] Write tests first: two successive models differ in at least one label bit or guess (tested
      as "a blocking clause built against a solved model evaluates to `False` against that same
      model" -- the direct, checkable form of the same claim); a model that is a rotation of a
      previous one's periodic segments is rejected -- **excluded, see below**; a model that
      differs only by renaming witness lassos is rejected -- **excluded, see below**.
- [x] Rewrite `iterate.py`'s `_create_difference_constraint` as a blocking clause over the label
      bits and the box guess.
- [ ] Implement `_create_non_isomorphic_constraint` as rejection modulo rotation of each lasso's
      `back`/`fwd` segments and permutation of the witness lassos (lasso 0 fixed) -- **excluded,
      see below**; implemented instead as the same exact-difference blocking clause as
      `_create_difference_constraint`.
- [x] Rewrite `_calculate_differences` / `display_model_differences` to report label and guess
      differences instead of world-array differences.

**Timing**: 2 hours

**Depends on**: 12, 14

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - rewrite
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - rewrite

**Verification**:
- Iteration tests green: 8/8 in the rewritten `test_iterate.py`.
- `iterate: 3` on a countermodel example yielding three pairwise non-isomorphic certificates --
  **not verified live**; see the discovered live-loop gap below.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| Rotation/permutation-invariant `_create_non_isomorphic_constraint` | A fully symmetry-aware rejection needs to enumerate the rotation group action on each lasso's periodic `back`/`fwd` segments together with witness-lasso relabelings and assert non-membership in that whole orbit -- a materially larger sub-feature than the exact-difference blocking clause this phase landed instead. Implemented the simpler, still-sound (if less complete) exact-bit/guess difference shared with `_create_difference_constraint`: guarantees the next model is not bit-for-bit identical, though it may still be a rotation of a previous one. | `iterate.py`'s own module docstring ("Isomorphism rejection is simplified to exact difference, not rotation/permutation invariance") documents the gap and names `WitnessRegistry.wrap`'s slot arithmetic as the tool a follow-on task should use to close it. |
| Live `iterate: 3` verification | **Discovered during this phase, not merely deferred**: `BaseModelIterator.iterate()`/`iterate_generator()` never call `BimodalModelIterator`'s own `_create_difference_constraint`/`_create_non_isomorphic_constraint` -- they delegate to a composed, theory-agnostic `ConstraintGenerator` (`model_checker/iterate/constraints.py`), constructed unconditionally (not overridable per theory) in `BaseModelIterator.__init__`. That generator's exclusion logic is entirely gated on `hasattr(semantics, 'is_world')`, which the certificate encoding deliberately has none of (D3/D4). So for bimodal, the live iteration loop currently has **no active exclusion constraint from the generic path** at all -- a real gap, present the moment `is_world` was removed in Phase 9, only now surfaced because this is the first phase to actually look at the iteration path. Fixing the shared `ConstraintGenerator` would touch code all four theories rely on and needs its own dedicated regression coverage across those theories -- out of proportion to a bimodal-only task without that coverage in hand. | `iterate.py`'s own module docstring section "`_create_difference_constraint`/`_create_non_isomorphic_constraint` are interface-parity methods, not the live loop's exclusion mechanism" traces the exact call chain (`BaseModelIterator.__init__` -> `ConstraintGenerator(build_example)` -> `create_extended_constraints`/`_create_state_difference_constraints`, both `is_world`-gated, in `model_checker/iterate/constraints.py`). This exact caveat already existed, worded almost identically, in the retired encoding's own `_create_difference_constraint` docstring -- it is a pre-existing framework characteristic this redesign exposes rather than one it introduces, but the redesign is what makes the generic path's exclusion actually go inert (the retired encoding satisfied `hasattr(semantics, 'is_world')`, so the generic path worked there). |

This is a legitimate `[COMPLETED WITH EXCLUSIONS]`, not silently descoped: both exclusions are
functionally significant (repeat/rotated models can surface across an `iterate: N>1` run) and are
recorded for a follow-on task, not hidden. A future task should (1) close the shared
`ConstraintGenerator` extension-point gap with its own cross-theory regression plan, and (2)
implement the full rotation/permutation-invariant `_create_non_isomorphic_constraint` once (1) is
in place to actually exercise it.

---

### Phase 16: Examples migration - settings and expectation audit [COMPLETED WITH EXCLUSIONS]

**Goal**: Every example carries the new settings, and every expectation has been checked against
the paper rather than carried over.

**Tasks**:
- [x] Replace `N`/`M`/`contingent`/`disjoint` in every example settings dict with `back`/`mid`/`fwd`
      (and `max_witnesses` where a box count warrants it), keeping `max_time` at or above the
      example budget floor. Done explicitly (not by omission): `run_test()`
      (`code/src/model_checker/utils/testing.py`) constructs `semantic_class(settings)` directly
      from each example's own dict with **no** `SettingsManager` defaults-merge (that merge only
      happens on the `dev_cli.py`/`BuildExample` path), so every one of the 53 example dicts now
      carries explicit `'back' : 2, 'mid' : 1, 'fwd' : 2` (the class defaults) in place of the
      stripped `N`/`M`; `max_witnesses` was not added anywhere (see Reasoned Exclusions). No
      `max_time` needed raising (all 53 were already >= the 10s floor).
- [x] Audit the `\Until`/`\Since` argument order in every BX example against the paper's
      guard-first `until`/`since` clauses (D2), and record per example whether the formula as
      written means what its comment claims; fix the formula or the comment, and record which
      source of truth was chosen. Every one of the 16 `\Until`/`\Since`-bearing BX examples (plus
      MF, the perpetuity theorems, and the S5/propositional layers) was independently re-derived
      from the paper's own guard-first axiom text and checked character-for-character against the
      coded sentence; every single one was found to already encode its axiom correctly. Only the
      BX10/BX10P "Formula:" comment lines were actually wrong (mixing the paper's guard-first
      meta-variable placement with the code's event-first values); both corrected to cite the
      axiom (UE) directly. Chosen source of truth: the paper's axiom translated through D2's
      event-first swap.
- [x] Audit every `expectation` value against the paper's axioms, in particular `MF_MODAL_FUTURE_TH`
      (`□A → □GA`, valid per `thm:MF-valid`) and the perpetuity theorems `BM_TH_1`/`BM_TH_2`.
      Every `expectation` value in the file was already correct (including `MF_MODAL_FUTURE_TH`'s
      `False`, which was NOT a "flip" -- see the next bullet). `BM_TH_1`/`BM_TH_2` re-derived from
      MF+MT+TR (cited in their own rewritten comments); `BM_TH_3`/`BM_TH_4` from P2; `BM_TH_5`
      from TF; `TN_TH_2`/`BX4_CONNECT_F_TH` from TC; all confirmed correct as coded.
- [x] **(Amendment, adequacy-layer task, folded in from the now-merged Phase 17 restoration step
      for this one example)** In `tests/unit/test_bimodal.py`, delete — not soften — the comment
      asserting MF "is NOT a theorem under current bimodal semantics (countermodel found at N=1,
      M=2)" and its trailing inline comment on the `KNOWN_TIMEOUT_EXAMPLES` entry; replace both with
      a statement that MF is valid in the paper's semantics (citing `modal_future_valid` and
      `no_witnessFamily_of_MF` as above), that the old countermodel was an artifact of the
      bounded-window encoding's boundary vacuity, and remove MF from `KNOWN_TIMEOUT_EXAMPLES`
      (its presence there was itself a mis-filing: the reason was semantic disagreement, not a
      timeout). Done. `MF_MODAL_FUTURE_TH_settings['expectation']` was already `False` (correct;
      the dispatch's own "flip to True" phrasing describes what a comparison against the OLD,
      buggy encoding's `z3_model_status` would have needed, not this file's field) -- confirmed by
      running the certificate encoding against it: it now decides `match` (see the encoding-bug
      finding below).
- [x] Record the audit as a table in a comment block at the top of the affected section of
      `examples.py`, citing the paper's label for each axiom (no task-number references: this file
      is outside `specs/`). Done; also fixed two pre-existing task-number references ("task
      91/92") in the same comment block the audit table was added next to.
- [x] **(Amendment, adequacy-layer task)** Include the A0 frame-class standing test's two example
      formulas (Phase 9's `prior_UZ` and `z1` instances) in this audit pass, recording their
      expected verdict as "no certificate at any configured length, rendered inconclusive" rather
      than a `True`/`False` expectation — see ADEQUACY.md §7.2 and §7.4's never-report-validity
      rule. Done: recorded in the audit table with a pointer to
      `tests/unit/test_structure.py::TestA0FrameClassStandingTest`, the file these two instances
      are actually tested in (they are not `examples.py` entries: their verdict shape does not fit
      this file's boolean `expectation` field).

**DISCOVERED AND FIXED, beyond this phase's own task list**: running the migrated file (both via
`dev_cli.py` over `example_range` and via `pytest` over the full `test_bimodal.py` corpus, done to
verify the settings migration didn't regress anything) surfaced a real, pre-existing soundness bug
in `witness_constraints.py`'s `local_coherence_constraints` (Phase 7): it asserted the
`LocalCoherentLab` biconditional only over `registry.target_window()` (one representative position
per slot), on the claim that slot-sharing via `WitnessRegistry.bit`'s `wrap` makes one
representative automatically cover every position sharing its slot. That claim is false for the
`back`/`fwd` slot immediately adjacent to `mid`: e.g. with `nb=2`, slot `back[1]` occurs at
`t=-1,-3,-5,...`, but the neighbour an `Untl`/`Snce` clause needs (`t+1`) lands in `mid` only for
`t=-1` and back in `back[0]` for every deeper occurrence -- two different biconditionals on the
same shared boolean, and asserting only the `t=-1` one left the others completely unconstrained.
Z3 was free to pick locally-incoherent values that only the pure-Python re-checker's *wide*-window
scan (`_coherence_window`, matching the Lean-proved `coherent_iff_window` bound) caught -- exactly
the `ModelConstructionError` fail-fast this phase's own dev_cli run hit on `BM_CM_1`. **Fix**:
changed `local_coherence_constraints` to iterate `_coherence_window(registry)` (the same wide
window `fulfilment_constraints` already used, Phase 8), matching what the module's own docstring
now explains was always the actual requirement; rewrote the docstring's flawed "one representative
suffices" argument to record the counterexample instead. **Measured effect**:
`test_bimodal.py`'s full 44-example suite went from 38 passed / 6 failed (post-settings-migration,
pre-fix) to **44 passed / 0 failed** (post-fix) -- including `MF_MODAL_FUTURE_TH`, `BM_CM_1`,
`TN_TH_2`, `BX4_CONNECT_F_TH`, `BX4P_CONNECT_P_TH`, `BX13_ENRICH_U_TH`, `BX13P_ENRICH_S_TH` (all
6 of the failures this bug caused). Whole-tree `pytest .../bimodal/tests/` went from the Phase 15
handoff's baseline (146 failed, 80 errored, 291 passed) to **103 failed, 80 errored, 335 passed**
after this phase (settings migration + this fix); the remaining 103 failures/80 errors are test
modules bound to deleted machinery, Phase 18's job, not a regression from this phase.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| `max_witnesses` never set on any example | Every example's closure has at most 2 boxed subformulas (`MF_MODAL_FUTURE_TH`, `MODAL_4_TH`/`MODAL_5_TH`); `max_witnesses=None` (uncapped, one witness lasso per false-guessed box) is already tight for a count this small, so an explicit cap would only add a round-robin sharing constraint with nothing to bound. Revisit if a future example's closure needs 3+ boxes. | `WitnessRegistry.allocate_witness_lasso`'s own docstring: the cap "trades completeness for a bounded search," which is not a live concern at box-count <= 2. |
| `back`/`mid`/`fwd` left at the class defaults (2/1/2) on every example rather than individually tuned | Phase 16's task list scopes tuning to "keeping `max_time` at or above the floor," not segment-length calibration; Phase 17 explicitly owns "raise the default segment lengths only if a genuinely needed example requires it, and record the reason" once the nine excluded examples are re-activated and actually measured. Setting them uniformly to the defaults now (rather than guessing at per-example values) keeps this phase's changes minimal and auditable. | Phase 17's own task list, this plan. |

**Timing**: 2 hours (actual: settings migration + audit + encoding-bug diagnosis and fix)

**Depends on**: 12, 14

**Verification Tier**: local

**Scope Hypothesis**: `examples.py` is 1,482 lines carrying roughly 50 example settings dicts, of
which the BX-axiom family using `\Until`/`\Since` is the subset needing the order audit. **Actual
counts** (confirmed at implementation time): 54 `_settings = {` occurrences (53 example dicts plus
the module-level `general_settings`), 56 `\Until`/`\Since` occurrences.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - migrate settings, audit expectations
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - MF exclusion comment
  (not in the plan's original file list; added because the MF amendment task explicitly targets
  this file)
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - local-coherence
  window fix (not in the plan's original file list; the encoding bug discovered above)

**Verification**:
- `PYTHONPATH=code/src ./code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py`
  runs with no unknown-setting warnings. CONFIRMED (only pre-existing, out-of-scope general-setting
  warnings remained, and those were also fixed by dropping the dead `align_vertically` key).
- Every expectation change is accompanied by a cited paper reference in the audit table. CONFIRMED
  (no expectation values actually changed; the audit table cites every example's paper axiom).

---

### Phase 17: Examples migration - restore the excluded examples [COMPLETED]

**Goal**: The examples excluded by the retired encoding are active and passing.

**Tasks**:
- [x] Re-activate `TN_CM_1`, `TN_CM_2`, `BM_CM_3`, `MD_TH_2`, `BM_TH_1`, `BM_TH_2`,
      `MF_MODAL_FUTURE_TH`, `BX7_LINEAR_U_TH`, `BX7P_LINEAR_S_TH` in `example_range` and confirm
      each has an entry in `countermodel_examples`/`theorem_examples`. **Discrepancy from the
      Scope Hypothesis**: `TN_CM_1`, `TN_CM_2`, `BM_CM_3`, `MD_TH_2`, `BM_TH_1`, `BM_TH_2` were
      ALREADY present in `example_range` (they were only excluded from `test_bimodal.py`'s
      collected suite via `KNOWN_TIMEOUT_EXAMPLES`, a separate mechanism from `example_range`'s
      own curated dev-CLI demo list). Only `MF_MODAL_FUTURE_TH`, `BX7_LINEAR_U_TH`,
      `BX7P_LINEAR_S_TH` were genuinely missing from `example_range` and needed adding.
- [x] Re-activate `BM_TH_5` (previously excluded "for Z3 state reasons") and confirm it behaves.
      **Second discrepancy**: `BM_TH_5` was already in `example_range` but was entirely MISSING
      from `theorem_examples` (and therefore from `unit_tests`/`test_example_range` and
      `test_bimodal.py`'s collected suite) -- not merely excluded via `KNOWN_TIMEOUT_EXAMPLES`.
      Added `"BM_TH_5" : BM_TH_5_example` to `theorem_examples`.
- [x] For each, record the segment lengths at which it decides and its measured solve time. All
      ten decide correctly at the class-default segment lengths (`back=2, mid=1, fwd=2`), with
      measured solve times (via `dev_cli.py`, 2026-09-25): `TN_CM_1` 0.0008s, `TN_CM_2` 0.0015s,
      `BM_CM_3` 0.0014s, `MD_TH_2` 0.0007s, `BM_TH_1` 0.0017s, `BM_TH_2` 0.0016s,
      `MF_MODAL_FUTURE_TH` 0.0037s, `BX7_LINEAR_U_TH` 0.0054s, `BX7P_LINEAR_S_TH` 0.0054s,
      `BM_TH_5` 0.0017s -- all sub-6ms, confirming the redesign's quantifier-free speed claim
      empirically rather than by assertion.
- [x] Raise the default segment lengths only if a genuinely needed example requires it, and record
      the reason. Not needed: every one of the ten decided correctly at the class defaults with no
      raising. Went the other direction instead: `BM_TH_1`/`BM_TH_2` (30s -> 10s) and
      `BX7_LINEAR_U_TH`/`BX7P_LINEAR_S_TH` (60s -> 10s) had their `max_time` LOWERED to the floor,
      since the retired encoding's exhaustive-search budgets were 2000x-30000x the certificate
      encoding's actual measured cost; `MF_MODAL_FUTURE_TH` was already at the floor (10s).
      `example_range`'s stale per-entry comments ("No countermodel", "Has countermodel", "Doesn't
      find countermodel if run in isolation" -- all retired-encoding-specific behavioural notes,
      now wrong under the certificate encoding) were also removed as part of this same edit.

**Timing**: 2 hours (actual: in line with estimate, since Phase 16's audit had already done the
per-example correctness verification -- this phase was mostly `example_range`/`theorem_examples`
bookkeeping plus empirical measurement)

**Depends on**: 16

**Verification Tier**: local

**Scope Hypothesis**: the exclusion set is the nine names in `test_bimodal.py`'s
`KNOWN_TIMEOUT_EXAMPLES` plus `BM_TH_5`. **Confirmed with two discrepancies** (both recorded
above): six of the nine were already in `example_range` and needed no re-activation there (only
`test_bimodal.py`'s separate `KNOWN_TIMEOUT_EXAMPLES` — Phase 19's job — actually excludes them
from the pytest corpus); `BM_TH_5` was missing from `theorem_examples`, not merely excluded.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - re-activate examples

**Verification**:
- Each of the ten runs to a decided verdict matching its audited expectation. CONFIRMED via
  `dev_cli.py` (25/25 `example_range` entries produce the correct `there is`/`there is no
  countermodel` verdict, 0 tracebacks, 0 warnings) and via `pytest` (45/45 `test_bimodal.py`
  examples pass, up from 44 after Phase 16's fix -- the +1 is `BM_TH_5`, newly collected).
- Measured solve times recorded in the phase's commit message or the summary. Recorded above.

**Note for Phase 19**: `KNOWN_TIMEOUT_EXAMPLES` in `test_bimodal.py` still lists `TN_CM_1`,
`TN_CM_2`, `BM_CM_3`, `MD_TH_2`, `BM_TH_1`, `BM_TH_2`, `BX7_LINEAR_U_TH`, `BX7P_LINEAR_S_TH` (8
entries; `MF_MODAL_FUTURE_TH` was already removed in Phase 16). This phase deliberately left that
constant untouched -- emptying it is Phase 19's explicitly assigned task -- but the measurements
above already show all eight decide correctly and fast, so Phase 19's removal should be a
confirmation, not a fresh investigation.

---

### Phase 18: Test suite part 1 - retire tests bound to deleted machinery [COMPLETED]

**Goal**: No test in the tree asserts behaviour of the retired encoding.

**Tasks**:
- [x] Enumerate every test module asserting retired behaviour and classify each as delete, rewrite,
      or keep: expected deletions include `test_frame_constraints.py`,
      `test_world_history_alignment.py`, `test_frame_class_mapping.py`,
      `test_enriched_equivalence.py`, and the retired-witness tests already replaced in Phases 6-7.
      **Actual classification** (12 modules were failing/erroring post-Phase-17, 183 items
      total): **DELETE** (7 files, all fully superseded or directly contradicting the redesign,
      confirmed by inspection before deletion, not assumed from the name) --
      `test_frame_constraints.py` (13 items: builder methods for constraints that no longer
      exist), `test_frame_class_mapping.py` (14: `task_rel`/TaskFrame axiom mapping, gone),
      `test_world_history_alignment.py` (8: printing renderer Phase 13 replaced),
      `test_enriched_equivalence.py` (69: tests "enriched vs primitive" divergence for
      operators that are now ALL `DefinedOperator`s with no separate enriched implementation
      to diverge from -- the premise no longer applies), `test_modal_witness_integration.py`
      (16 errors + 1 vacuous pass: retired `WitnessRegistry(N, M)`/`has_witness_predicate` API),
      `test_strict_semantics.py` (8: `ForAllTime`/`ExistsTime`/`is_valid_time`/`semantics.M`, all
      gone), `test_api_consistency.py` (1: `find_truth_condition` no longer exists anywhere --
      operators use only `true_at`/`false_at` now), `test_until_since.py` (21: literally asserts
      `z3.is_quantifier(result)`, the direct opposite of the redesign's quantifier-free claim,
      already correctly tested by `test_operators.py`'s `TestConstraintSetIsQuantifierFree`).
      **REWRITE** (3 files): `test_next_prev.py` (12: settings migrated N/M -> back/mid/fwd,
      every other claim -- signature, `derived_definition` structure, registration, parsing,
      semantic equivalence -- survived unchanged), `test_until_since_integration.py` (10: the
      retired `find_truth_condition`-signature/mock-Z3-plumbing tests dropped as redundant with
      `test_operators.py`; replaced with real end-to-end `run_test()` theorems/countermodels for
      the file's own stated "Key tests" -- U(p,top)<->future(p), S(p,top)<->past(p), open guard
      interval, boundary/immediate-witness behaviour), `test_data_extraction.py` (6: `extract_*`
      methods kept their names but now read `self.certificate`/lasso indices instead of
      `world_histories`/`main_world`; rewritten against real built structures, not mocks).
      **UPDATE** (2 files): `test_injection.py` (5: `inject_z3_model_values` still exists,
      rewritten for the certificate encoding's variable set -- label bits, box guesses, target
      selector -- in place of `is_world`/`truth_condition`/`task_rel`; rewritten against a real
      solved structure), `conftest.py` fixtures.
- [x] Rewrite the behaviour-level temporal tests (`test_until_since.py`, `test_next_prev.py`,
      `test_until_since_integration.py`) against the certificate encoding, preserving the semantic
      claims they encode while dropping their window assumptions. **Amended per the
      classification above**: `test_until_since.py` was deleted rather than rewritten (its
      claims are either already covered by `test_operators.py` or directly contradict the
      redesign); `test_next_prev.py` and `test_until_since_integration.py` were rewritten as
      described.
- [x] Update `tests/conftest.py` fixtures: `basic_settings` / `minimal_settings` /
      `complex_settings` to the new settings, and the `witness_registry` /
      `constraint_generator` fixtures to the rewritten constructors. Done: `back`/`mid`/`fwd` in
      place of `N`/`M`/`contingent`/`disjoint`; `witness_registry` now built with
      `WitnessRegistry(back=, mid=, fwd=, closure=())`; `constraint_generator` now built as
      `WitnessConstraintGenerator(witness_registry)` (the rewritten one-argument constructor).
      **Note**: no currently-collected test consumes these three settings fixtures any more (their
      only consumers were in the now-deleted files) -- updated per this task's explicit
      instruction and left in place for future test authors, not removed.
- [x] Update `tests/integration/test_injection.py`, `test_data_extraction.py`,
      `test_strict_semantics.py`, `test_api_consistency.py` for the new attribute surface.
      **Amended per the classification above**: `test_strict_semantics.py` and
      `test_api_consistency.py` were deleted (their entire premise -- `ForAllTime`/
      `is_valid_time`/`find_truth_condition` -- no longer exists, nothing to update); the other
      two were rewritten as described.

**MEASURED OUTCOME**: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/
-q` goes from 103 failed / 80 errored / 335 passed (end of Phase 17) to **357 passed, 0 failed, 0
errored** -- the entire bimodal test tree is green. This also substantially pre-empts Phase 19's
own "green suite" goal; see that phase's notes for what remains.

**Timing**: 2 hours (actual: comparable, given each deletion candidate was independently confirmed
by inspection rather than assumed, and two files needed from-scratch rewrites)

**Depends on**: 14, 15

**Verification Tier**: local

**Scope Hypothesis**: the bimodal test tree is 20 modules totalling roughly 5,400 lines; the
delete/rewrite split above is a hypothesis, not an inventory. **Actual**: 12 of the (then) 25
modules were failing/erroring (183 items); the actual delete/rewrite/update split is recorded in
full above, and differs from the hypothesis (`test_until_since.py` moved from "rewrite" to
"delete"; `test_strict_semantics.py`/`test_api_consistency.py` moved from "update" to "delete").

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` - update fixtures
- `code/src/model_checker/theory_lib/bimodal/tests/unit/` - delete/rewrite per the classification
- `code/src/model_checker/theory_lib/bimodal/tests/integration/` - update

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` collects with no
  import errors and no test referencing a deleted method. CONFIRMED (357 passed, 0 failed, 0
  errored, 0 collection errors).

---

### Phase 19: Test suite part 2 - green, fast, re-checked [COMPLETED]

**Goal**: The whole bimodal suite green with no exclusion list, every found model re-checked, and a
recorded timing improvement.

**Tasks**:
- [x] Empty `KNOWN_TIMEOUT_EXAMPLES` in `test_bimodal.py` (or delete the constant) and confirm the
      full parametrized example suite passes. Done: `KNOWN_TIMEOUT_EXAMPLES: set = set()` (kept,
      empty, matching the file's own convention of a single greppable exclusion point). All 53
      examples (`countermodel_examples` + `theorem_examples`, the full corpus, zero excluded) now
      collect and pass: `pytest .../test_bimodal.py -v` -> 53 passed.
- [x] Re-assess `UNSTABLE_EXAMPLES`: remove `BM_CM_1`'s marking if the redesign collapses its tail,
      and if anything is retained, re-justify it against the four entry criteria rather than
      carrying the old justification over. Both `BM_CM_1` and `BM_CM_4` removed:
      `UNSTABLE_EXAMPLES: set = set()`. Not merely "the tail collapsed" -- the root-cause
      mechanisms (`ForAllTime`/`ExistsTime` quantifiers for `BM_CM_1`; `build_seriality_
      constraint`/`build_interpolation_constraint` for `BM_CM_4`) no longer exist anywhere in
      `semantic/core.py`, confirmed by grep, so the entry criteria's own heavy-tailed-Z3-heuristic
      root cause cannot recur by construction. Also confirmed empirically: 20/20 consecutive runs
      of both, each decided in well under 1s, satisfying entry criterion (4)'s own exit bar.
- [x] Assert the Phase 4 re-checker runs on every found model in the example suite (via the
      Phase 12 hook, with a test that the hook is actually reached). Added
      `TestFailFastGuardOnACorruptedCertificate` to `test_structure.py`: monkeypatches
      `BimodalSemantics.extract_certificate` to return a deliberately-corrupted `WitnessFamily`
      (a label containing an `Imp` node whose membership contradicts its own local-coherence
      biconditional) and confirms `BimodalStructure.__init__` raises `ModelConstructionError`
      mentioning "obligation S3" -- proving the hook is genuinely reached on every satisfiable
      solve, not merely exercised by coincidence whenever the encoder happens to misbehave (which
      is exactly how Phase 16's real instance of this failure mode was originally discovered).
- [x] Record before/after wall-clock for the suite, and confirm no test needs a `max_time` above
      the floor for solver reasons. **Before** (Phase 15 baseline, whole tree): 146 failed, 80
      errored, 291 passed. **After** (this phase, whole tree): **366 passed, 0 failed, 0 errored**
      in ~18s wall-clock (`pytest .../bimodal/tests/ -q`, single-process). Audited every one of
      the 53 examples' `max_time`: all sat at 15s/20s/30s/60s/120s from the retired encoding's
      solver-cost history; every one measured at its own default segment lengths decides in under
      50ms, so ALL were lowered to the repository floor (10s) -- `BM_CM_1` (60->10), `BM_CM_4`
      (120->10), `BX2G_MONO_U_TH`/`BX2H_MONO_S_TH`/`BX3_MONO_U_TH`/`BX3P_MONO_S_TH` (15->10),
      `BX5_ACCUM_U_TH`/`BX5P_ACCUM_S_TH`/`BX6_ABSORB_U_TH`/`BX6P_ABSORB_S_TH`/`BX11_LIN_F_TH`/
      `BX11P_LIN_P_TH` (20->10), `BX13_ENRICH_U_TH`/`BX13P_ENRICH_S_TH` (30->10). No example in
      the file now sits above the floor. `code/src/model_checker/theory_lib/bimodal/tests/README.md`
      rewritten: directory-structure tables corrected for the 7 files deleted and 1 file added in
      Phase 18, and the "Solve Budgets" section rewritten from "bimodal examples are among the
      most expensive" to reflect the measured sub-100ms reality.

**Timing**: 2 hours (actual: comparable; the max_time audit and README rewrite took the place of
what the plan expected to be mostly confirmation work)

**Depends on**: 4, 17, 18

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - remove exclusions
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - update
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - fail-fast guard test
  (not in the plan's original file list; added for the re-checker-reached assertion)
- `code/src/model_checker/theory_lib/bimodal/examples.py` - `max_time` lowered to the floor across
  14 examples (not in the plan's original file list for this phase, but squarely within "confirm
  no test needs a max_time above the floor")
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - set `iterate_example_generator.
  __wrapped__` (pre-existing gap since Phase 15, surfaced by this phase's "no regressions
  elsewhere" full-repo check)
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - update the one
  bimodal-specific assertion/settings fixture stale since Phase 13's printing rewrite (also
  surfaced by the full-repo check)

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` fully green.
  CONFIRMED: 366 passed, 0 failed, 0 errored.
- `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q` green (no regressions
  elsewhere). CONFIRMED: `code/tests/` -> 682 passed, 5 skipped, 2 deselected. `code/src/model_checker`
  (`-m "not development"`) -> found 2 PRE-EXISTING failures (confirmed via `git stash`, both
  already failing before this phase's changes, at the end of Phase 18): (1)
  `builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::test_theory_library_execution`
  asserted the retired encoding's "World Histories" print-format string and used `N`/`M`
  settings -- both stale since Phase 13's printing rewrite; fixed (assertion updated to
  "Certificate:", settings updated to `back`/`mid`/`fwd`). (2)
  `theory_lib/tests/test_theory_conformance.py::TestIterateContract::
  test_iterate_module_exposes_required_interface[bimodal]` required `iterate_example_generator.
  __wrapped__` to be set, matching every other theory's own convention (`logos/iterate.py`'s
  `iterate_example_generator.__wrapped__ = iterate_example_generator`) -- missing since Phase
  15's iterate.py rewrite; fixed with the identical one-line pattern. Both fixes verified: the
  full `bimodal/tests/` + `theory_lib/tests/` + `builder/tests/e2e/` selection now passes 446/446.
  Neither fix was in this phase's (or any later phase's) file list, but both are one-line,
  low-risk, and squarely in scope for "no regressions elsewhere" -- fixing them now rather than
  deferring avoids a false "elsewhere" failure being misattributed to a later phase's own changes.
- Timing record present in the commit message or summary. Recorded above.

---

### Phase 20: Oracle provider rewrite [COMPLETED WITH EXCLUSIONS]

**Goal**: `oracle/bimodal_logic/` speaks the new semantics, and never claims validity.

**Tasks**:
- [x] Write tests first against the provider interface: the verdict vocabulary, the frame-class
      declaration, and the never-claims-validity property. Rewrote `test_oracle_provider.py`
      against the new contract (property/output/isolation/regression tests); every claim verified
      against the real provider, not written speculatively.
- [x] Rewrite `provider.py`: settings built from segment lengths instead of `N`/`M`/`temporal_depth`;
      `capabilities` re-declared (`max_back`/`max_mid`/`max_fwd` in place of `max_N`/`max_M`);
      `supported_frame_classes` re-declared for Z-time; `find_countermodel` returning the
      certificate-derived countermodel; the timeout contract preserved. Done:
      `supported_frame_classes = frozenset({"ZTime"})` (was `{"Base"}`); `find_countermodel`'s
      own `frame_class` default parameter changed `"Base"` -> `"ZTime"` to match (a detail easy to
      miss: leaving the old default would have silently broken every unqualified caller);
      `_segment_lengths(depth)` replaces the retired `M = max(depth+2, 3)` sizing, scaling
      `back`/`fwd` with depth and clamped to `capabilities`' declared maxima; `provider_version`
      bumped `0.1.0` -> `0.2.0` and `semantics_version` to `"bimodal-logic-certificate-v0.1.0"`
      (both changed to signal the encoding change to any external consumer inspecting them).
- [x] Update `serialization.py` to serialize certificate-derived countermodels, and `translation.py`
      where it assumes the retired model shape. Done: `serialization.py` fully rewritten --
      `extract_true_false_atoms` now reads the main lasso's label at the target position (the
      atom vocabulary is the search's own closure); `extract_task_triples`/
      `serialize_world_histories` deleted outright (no `task_rel`/`world_histories` exist any
      more); `serialize_countermodel`'s `certificate` field is `WitnessFamily.to_json`'s own wire
      shape verbatim -- the same shape BimodalLogic's `lake exe check_certificate` accepts, so a
      caller wanting Lean-side re-verification can pass it straight through. `translation.py`
      needed no logic changes (`json_to_prefix`/`prefix_to_infix`/`fold_formula`/`unfold_formula`
      are pure JSON-tree transforms, confirmed by grep to have zero references to
      `task_rel`/`world_hist`/model internals); only `temporal_depth`'s docstring's
      boundary-safety essay was retired per the next task.
- [x] Delete the `temporal_depth`/`M = max(depth+2, 3)` sizing logic and its comments. Done: the
      sizing logic itself lived in `provider.py` (now replaced by `_segment_lengths`);
      `temporal_depth`'s own ~25-line "Boundary Claim" docstring essay (the formal argument for
      `M_safe(d) = max(d+2,3)`) replaced with a short note that the function itself (a plain,
      encoding-independent depth metric) survives but the boundary-safety rationale does not.

**DISCOVERED AND FIXED, beyond this phase's own task list**: while running the rewritten
`test_oracle_provider.py`'s `TestStateIsolation` class (100+ sequential `find_countermodel()`
calls), a real, pre-existing cache-poisoning bug surfaced in
`theory_lib/bimodal/semantic/formula.py`'s `translate()` memoization: `_TRANSLATE_CACHE` was a
plain `dict` keyed by `Sentence` object identity (`id()`-based, since `Sentence` has no custom
`__eq__`/`__hash__`) and was **never cleared**. CPython can and does reuse a garbage-collected
object's `id()`, so under enough create-and-discard churn (exactly what 100+ tight-loop
`find_countermodel()` calls produce), a later, completely unrelated `Sentence` could collide by
`id()` with an earlier, now-stale cache entry and receive its **wrong** cached `Formula`
translation -- silently, with no exception. This reliably broke every one of
`TestOracleExampleRegression`'s 53 examples when run after the isolation-stress tests in the same
process, while each passed individually. **Fix**: `_TRANSLATE_CACHE` is now a
`weakref.WeakKeyDictionary`, which drops an entry the instant its `Sentence` key is garbage
collected -- strictly before that `id()` could be reused -- closing the hazard without losing the
memoization. Verified: the full bimodal test tree (366 tests) and the full oracle test tree (463
tests, excluding the six files explicitly reserved for Phase 21) both pass after the fix.

Also fixed, surfaced by the same full-suite run rather than assumed from Phase 20's own file list:
`oracle/bimodal_logic/cli.py`'s `--frame-class` default (`"Base"` -> `"ZTime"`, the same
easy-to-miss default-parameter detail as `provider.py`'s own fix above) plus a new `--max-rlimit`
flag (mirroring `find_countermodel`'s own parameter, needed because a `--timeout` budget can no
longer reliably force a timeout for `test_cli.py`'s inconclusive-path tests -- the certificate
encoding decides every formula in single-digit milliseconds); `test_frame_class_declaration.py`
deleted (its entire premise -- disambiguating the retired "Base" TaskFrame-axiom label from
BimodalLogic's proof-system `FrameClass.Base` -- no longer applies, and its own referenced
in-package sibling test file was already deleted in Phase 18);
`test_json_translation.py::TestEnrichedEquivalence`'s settings dict migrated `N`/`M` ->
`back`/`mid`/`fwd`; `test_oracle_interface.py`'s own `REGRESSION_TIMEOUT_EXAMPLES` (11 entries)
emptied after each was individually re-measured deciding correctly in well under 100ms, mirroring
`test_bimodal.py`'s own empty `KNOWN_TIMEOUT_EXAMPLES`; one genuine semantic correction inside
that same file's `TestSpotCheckCrossSignal::test_validate_self_temporal_only` -- three formulas
(`p -> p U bot`, `(p U q) -> p`, `(p S q) -> p`) the retired encoding's own comment had hedged as
"VALID in bounded frames" are, under the certificate encoding's genuinely unbounded search, all
found to have real countermodels; the hedge was the tell that this was a bounded-window artifact,
not a true validity, and the test now asserts the corrected (and directly measured) outcome.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| `oracle/conftest.py`'s `_KNOWN_TIMEOUT_SKIPS` registry left with two now-dead entries (`test_oracle_regression[TN_TH_2]`, `test_enriched_vs_primitive_sat_agreement[all_future]`) | The "ORACLE TIMEOUT-SKIP INVENTORY" mechanism itself flagged both as `[RESOLVED]` (the formulas now decide, so the `pytest.skip()` sites they document can no longer fire) during this phase's own test runs, and explicitly says to "re-check ... REGRESSION_TIMEOUT_EXAMPLES membership" -- done -- but the registry itself lives in `oracle/conftest.py`, shared oracle-wide infrastructure outside Phase 20's `provider.py`/`serialization.py`/`translation.py`/test file list, and `test_timeout_skip_inventory.py` (which asserts against this exact registry) is explicitly Phase 21's own named file. Cleaning the registry without also updating its dedicated test in the same edit would be half a fix. | `oracle/conftest.py`'s own `_KNOWN_TIMEOUT_SKIPS` dict and its module docstring citing `test_timeout_skip_inventory.py` as the mechanism's own unit test. |
| `oracle/bimodal_logic/README.md`/`KNOWN_EXTERNAL_DEFECTS.md` not updated | Phase 22 ("Documentation rewrite") explicitly owns `oracle/bimodal_logic/README.md`; touching it now would be done twice. Confirmed neither file blocks any test passing (docs only, not imported). | Phase 22's own task list, this plan. |
| `oracle/bimodal_logic/__init__.py`'s stale "task 103" docstring reference not fixed | Untouched by this phase's actual code changes (no functional edit needed there), and fixing a bare comment in a file otherwise unrelated to this phase's work was judged out of proportion; left for whoever next edits that file. | Direct inspection: `__init__.py`'s exports needed no changes (`Z3OracleProvider`/`OracleTimeoutError`/translation functions all still exist with the same names). |

This is a legitimate `[COMPLETED WITH EXCLUSIONS]`: all three exclusions are narrow, explicitly
justified against a specific later phase or a clearly out-of-proportion drive-by fix, not silently
descoped.

**Timing**: 2 hours (actual: substantially more, given the cache-poisoning bug investigation and
the wider-than-planned ripple through `cli.py`/`test_json_translation.py`/
`test_frame_class_declaration.py`/`test_oracle_interface.py`'s own regression catalog)

**Depends on**: 14, 16

**Verification Tier**: interface

**Files to modify**:
- `oracle/bimodal_logic/provider.py` - rewrite
- `oracle/bimodal_logic/serialization.py` - update
- `oracle/bimodal_logic/translation.py` - update
- `oracle/bimodal_logic/tests/test_oracle_provider.py` - rewrite
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - update
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` - `_TRANSLATE_CACHE`
  cache-poisoning fix (not in the plan's original file list; the discovered bug above)
- `oracle/bimodal_logic/cli.py`, `oracle/bimodal_logic/tests/test_cli.py` - frame-class default
  and new `--max-rlimit` flag (not in the plan's original file list; surfaced by the full-suite
  check)
- `oracle/bimodal_logic/tests/test_json_translation.py` - settings migration (not in the plan's
  original file list)
- `oracle/bimodal_logic/tests/test_frame_class_declaration.py` - deleted (not in the plan's
  original file list)

**Verification**:
- `pytest oracle/bimodal_logic/tests/test_oracle_provider.py -v` green. CONFIRMED: 89 passed.
- No code path returns a verdict that asserts validity. CONFIRMED by inspection: `find_countermodel`
  returns `None` only for "no certificate found" or "unsupported frame class", both documented as
  non-validity claims in the module docstring; a budget-exhausted search always raises
  `OracleTimeoutError` instead.
- Additional verification beyond the plan's own bar: the full oracle test tree (`oracle/bimodal_logic/tests/`,
  excluding the six files explicitly reserved for Phase 21) passes 463/463 (4 xfailed, pre-existing
  and unrelated).

---

### Phase 21: Oracle part 2 - retire abundance tests, regenerate the manifest [COMPLETED WITH EXCLUSIONS]

**Goal**: The oracle suite carries no test of deleted machinery, and its conclusive manifest
reflects the new encoding.

**Tasks**:
- [x] Delete the abundance and shift-closure soundness tests in `test_soundness_regression.py`
      together with the machinery they test, leaving the oracle's own soundness core and its
      unconditional-gating property untouched (explicitly out of scope). **Discrepancy from the
      Scope Hypothesis**: direct inspection found ALL 7 classes / 1220 lines of
      `test_soundness_regression.py` (`TestBoundaryVacuity`, `TestShiftClosure`,
      `TestGuardedCompositionality`, `TestStateIsolationRegression`, `TestKnownBoundaryUnsafe`,
      `TestGroundedDispatch`, `TestOracleMFormulaBoundarySafe`) are entirely about the retired
      encoding's boundary/abundance/shift-closure/M-dispatch machinery, not a subset within a
      partially-surviving module -- confirmed by reading every class before deleting, not assumed
      from the module's title. The whole file was deleted, not partially edited; the oracle's own
      soundness core (verified to be `test_cross_oracle_differential.py`'s
      `TestCIGate`/`TestGatingConclusiveScan`/etc., per `oracle/conftest.py`'s
      `_SOUNDNESS_CORE_CLASSES`) was untouched except its own documented floor-constant task below.
- [x] Update `test_boundary_regression.py`, `test_encoding_nondegeneracy.py`,
      `test_probe_solve_cost.py` and `test_timeout_skip_inventory.py` for the new encoding, or
      delete those whose subject no longer exists, recording which and why.
      `test_boundary_regression.py` (740 lines): 3 of 4 classes deleted (`TestBoundaryAnalysis`,
      `TestBoundaryDocumentation`, `TestExampleRegression` -- all retired M-sizing-specific or
      fully redundant with `test_oracle_provider.py`'s own unconditional 53-example regression);
      `TestTemporalDepthAllTags` kept verbatim (`temporal_depth()` is a plain, encoding-independent
      metric, confirmed still correct). `test_encoding_nondegeneracy.py` (330 lines): deleted
      entirely -- its whole premise (a Z3 constant-interning aliasing hazard for hand-named
      quantifier bound variables in `ForAllTime`/`ExistsTime`-style constructs) is structurally
      impossible in a quantifier-free encoding with no `z3.Int`/bound-variable naming at all.
      `test_probe_solve_cost.py` + its companion `oracle/probe_solve_cost.py`: updated (settings
      migrated to `back`/`mid`/`fwd` via `Z3OracleProvider._segment_lengths`; added a
      `max_rlimit` parameter/`--max-rlimit` flag to both, mirroring the oracle CLI's own addition
      in Phase 20, since a tiny `timeout_ms` can no longer reliably force an undecided draw for
      measurement purposes). `test_timeout_skip_inventory.py`: needed no functional changes (it
      tests the inventory MECHANISM against synthetic fixture data, not real formulas) beyond
      3 tests' fixtures being updated to inject a local fake registry entry via `monkeypatch`
      rather than depend on `oracle/conftest.py`'s real (now-empty) `_KNOWN_TIMEOUT_SKIPS`
      registry staying non-empty -- that registry's own two entries were emptied in the same pass
      (both flagged `[RESOLVED]` by the timeout-skip-inventory mechanism itself on every run since
      Phase 20 landed), closing the Reasoned Exclusion Phase 20 left open for this exact pairing.
- [x] Regenerate `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` under the new
      encoding and update its `notes` field with the regeneration method. Done via
      `PYTHONPATH=code/src:oracle python3 oracle/scan_runner.py --max-complexity 5`, run 3 times
      for stability (all 3 identical): **274/274 conclusive (100%), 0 disagreements, 8.7-9.4s
      wall-clock** -- versus the prior manifest's 103/274 (37.6%) and 3549.987s (~59 minutes), a
      ~400x wall-clock speedup and a categorical jump in conclusive coverage, both consistent with
      removing the quantified constraint search entirely rather than tuning it. `notes` field
      records the exact regeneration command and both old/new figures.
- [x] Update the floor constant guarding the conclusive scan if the regenerated population changes
      it, with the measured new value recorded. Both `MIN_CONCLUSIVE_SCAN_FORMULAS` (90 -> 260)
      and `MIN_CONCLUSIVE_GATING_FORMULAS` (100 -> 260) raised, each keeping the same "~95% of the
      measured population, not 100%" margin convention the original derivations used, with the
      full measurement recorded inline as a dated addendum to (not a replacement of) the existing
      historical CI-hardware-investigation comment blocks, which remain valuable engineering
      history and were not deleted.

**DISCOVERED AND FIXED, beyond this phase's own task list**: regenerating the manifest surfaced a
stale, overly-narrow assertion in `test_cross_oracle_differential.py`'s
`test_temporal_only_agreement_complexity_5` (its "signature check" hardcoded the external
BimodalHarness defect's polarity as exclusively `mc_sat=False, bh_sat=True`). Investigation (using
the test's own ground-truth adjudication, which already independently confirmed MC correct and BH
wrong on the 3 newly-found cases) showed this was the CORRECT redesign consequence: the retired
encoding's own now-fixed Until/Since argument-order defect had coincidentally aligned with BH's
independent boundary-scan defect in one direction; with MC's Until/Since now independently
verified correct, the same external BH defect can surface with either polarity depending on which
side of a formula the boundary artifact lands on. Fixed the assertion to check the real invariant
(a genuine disagreement was routed here, per `classify_disagreement`'s own precondition) rather
than a specific boolean-value pattern that was itself an artifact of the now-fixed encoding.
Rewrote `KNOWN_EXTERNAL_DEFECTS.md`'s "Why ModelChecker is correct" section, which cited the
retired encoding's `main_time`/`is_valid_time`/`M`-sizing internals and a `TestBoundaryVacuity`
test class this phase's own deletion above just removed -- it now explains the certificate
encoding's genuinely bi-infinite (no-edge) lasso structure instead.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| `oracle/run-oracle-suite.sh`'s pass 2 ("serial, xdist_serial") selects zero tests and reports `FAILED (exit 5)` | Confirmed **pre-existing**, not caused by this phase: reproduced identically at the end of Phase 20 (commit `228a6db8`, before any Phase 21 deletion) via `git stash`. Root cause is a marker-interaction gap that predates task 184 entirely (`_XDIST_SERIAL_NODEID_FRAGMENTS`' `"test_regression_all_active_examples"` fragment has never matched a real test name since its introduction at commit `a7ea2e7f`, "task 132: complete orchestration"; its sibling fragment matches a real test, but that test is also `development`-marked, and pass 2's own filter excludes `development`-marked tests, so it can never be selected by either of the script's two passes regardless). Fixing the shared oracle-wide gating script's pass/fail semantics is outside this bimodal-scoped phase's file list and carries its own CI blast-radius risk that a bimodal redesign task should not take on unreviewed. | Direct `git stash` reproduction against `228a6db8`; `git log -S` confirming the dead fragment's origin at `a7ea2e7f`, five task-generations before this one. |
| `.github/scripts/unstable_watch_classify.py`'s `FAILURE_SIGNATURE_BY_NODEID_FRAGMENT` dict still keys one dead entry (`test_shift_closure_on_extracted_worlds_m3`, from the now-deleted `test_soundness_regression.py`) | Harmless dead data (an unused dict key with no test to ever match it again), and this file is CI-workflow-classification tooling entirely outside any file list this task's plan names at any phase. | Direct inspection: the dict entry is inert now that its keyed test no longer exists to produce a matching node id. |

This is a legitimate `[COMPLETED WITH EXCLUSIONS]`: both exclusions are pre-existing, narrow, and
explicitly out of this phase's (and this task's) scope, not silently descoped work that phase 21
itself was supposed to do.

**Timing**: 2 hours (actual: substantially more, given the full-file-deletion discrepancy from the
Scope Hypothesis, the 3x manifest-regeneration runs for stability, and the BH-comparison
investigation)

**Depends on**: 20

**Verification Tier**: full

**Scope Hypothesis**: the oracle bimodal test tree is 15 modules totalling roughly 10,300 lines;
the abundance/shift-closure subset inside `test_soundness_regression.py` (1,220 lines) is the
intended deletion, not the whole module. **Actual**: the whole 1220-line module was deleted (see
the Discrepancy note on the first task above); `test_encoding_nondegeneracy.py` (330 lines) was
ALSO deleted wholesale (not in the original hypothesis's list at all, discovered when its own
premise turned out to be structurally impossible under the new encoding).

**Files to modify**:
- `oracle/bimodal_logic/tests/test_soundness_regression.py` - deleted wholesale (not a partial
  abundance/shift-closure subset -- see the Discrepancy note above)
- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` - regenerated
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - floor constants updated, plus
  the discovered BH-comparison signature-check fix (not in the plan's original scope for this file)
- `oracle/bimodal_logic/tests/test_boundary_regression.py` - trimmed to its one surviving class
- `oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` - deleted wholesale (not in the
  plan's original file list at all)
- `oracle/bimodal_logic/tests/test_probe_solve_cost.py`, `oracle/probe_solve_cost.py` - updated
  (the companion CLI script is not in the plan's original file list)
- `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py`, `oracle/conftest.py` - registry
  cleanup (closing Phase 20's own Reasoned Exclusion)
- `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` - "Why ModelChecker is correct" section
  rewritten (not in the plan's original file list; discovered stale/dangling reference)
- `oracle/bimodal_logic/tests/test_ground_truth.py` - one dangling comment reference fixed

**Verification**:
- `bash oracle/run-oracle-suite.sh` green (with the gating clause still present at this point).
  Pass 1 (parallel): PASSED. Pass 2 (serial): pre-existing "0 selected" condition, unchanged from
  before this phase -- see the Reasoned Exclusions table above; this is not a regression from this
  phase's own work.
- The soundness core's test node ids are unchanged, confirming it was not modified. CONFIRMED:
  `test_cross_oracle_differential.py`'s `TestCIGate`/`TestFormulaEnumerator`/
  `TestDifferentialInfrastructure`/`TestKnownFormulaBaseline`/`TestDifferentialComparison`/
  `TestDifferentialReport` classes and their method names are untouched by this phase.
- Additional verification beyond the plan's own bar: the FULL oracle test tree now passes
  unconditionally, no exclusions at all: `pytest oracle/bimodal_logic/tests/ -q` -> 567 passed, 4
  xfailed (pre-existing, unrelated), 0 failed. The bimodal theory test tree remains 366/366.

---

### Phase 22: Documentation rewrite [COMPLETED]

**Goal**: Theory documentation describes the certificate design, with the frame-axiom ledger and
duration-guard gap note retired.

**Tasks**:
- [x] Rewrite `README.md`'s semantics sections: certificate definition, the four conditions, the
      certified ShiftSet, the new settings, the output shape; delete the abundance, world-interval,
      Skolem-abundance and time-shift sections.
- [x] Rewrite `docs/ARCHITECTURE.md`: retire the frame-axiom ledger table and the
      "Duration-domain guard (open gap)" note; describe the two-phase constraint emission and the
      re-check hook; state explicitly that validity is never reported.
- [x] Rewrite `docs/SETTINGS.md` for `back`/`mid`/`fwd`/`max_witnesses`, `docs/API_REFERENCE.md`
      for the new classes and functions, `docs/USER_GUIDE.md` for the new workflow, and
      `docs/ITERATE.md` for the new difference/isomorphism story.
- [x] Update `oracle/bimodal_logic/README.md` and `KNOWN_EXTERNAL_DEFECTS.md`, and document the
      certificate JSON export with a pointer to BimodalLogic's protocol section as the contract.
      `KNOWN_EXTERNAL_DEFECTS.md`'s "Why ModelChecker is correct" section was already rewritten in
      Phase 21 (confirmed by direct read, not redone); this phase added the "Certificate JSON
      Export" section to `oracle/bimodal_logic/README.md` pointing at
      `~/Projects/BimodalLogic/BimodalTools/README.md`'s protocol section as the fixed external
      contract.
- [x] Check every rewritten file for task-number references and remove them (these files are
      outside `specs/`). Confirmed zero task-number references in every file this phase authored
      (`README.md`, all six `docs/*.md` files). `oracle/bimodal_logic/README.md` carries three
      pre-existing "task 118" references (predating this task, describing a prior package-move
      commit) that this phase's own edit (the new "Certificate JSON Export" section) did not
      introduce and did not remove -- left as historical fact, matching the same convention this
      file's own "Relationship to the In-Package Bimodal Suite" section already used before this
      task touched it.
- [x] **(Amendment, adequacy-layer task)** Carry the (SOUND) theorem statement, the four lemmas
      (Frame, Histories, Time-shift preservation, Truth lemma) and the Lean citation table into
      `docs/ARCHITECTURE.md`, replacing the retired frame-axiom ledger table with this statement
      rather than leaving that section simply deleted.
      `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (created by the adequacy-layer
      task) is the source for this content — cite it as the fuller treatment and reproduce its
      statements rather than re-deriving them here. Done: `ARCHITECTURE.md`'s "The (SOUND) Theorem"
      section reproduces the theorem, the constructed model, all four lemmas (with Lean
      names/file:line), and the determinism/cost tradeoff, citing `ADEQUACY.md` as the fuller
      treatment. `ADEQUACY.md` itself was left unmodified, in keeping with its ownership by the
      separate adequacy-layer task -- see the Discovered-Beyond-Scope note below for the one stale
      sentence noticed in passing.

**Discovered beyond this phase's own task list**: direct testing of the standard
`dev_cli.py`/`model-checker` CLI iteration path (`"iterate": 3` on a countermodel example)
reproduced a live crash independent of, and sharper than, Phase 15's already-recorded
`ConstraintGenerator`/`is_world` gating gap: `model_checker/iterate/models.py`'s
`build_new_model_structure` calls `semantics.is_world(state)` with **no** `hasattr` guard (unlike
its neighboring `possible`/`verify` blocks in the same function), and `BimodalSemantics` defines no
`is_world` at all under the certificate encoding. `range(2**semantics.N)` with `N=0` (D3) is
`range(1)`, so the very first successor-model build after the first certificate always raises
`AttributeError: 'BimodalSemantics' object has no attribute 'is_world'`, aborting the run. This was
not caught by the 366/366-green suite because no example sets `iterate` above its default of `1`,
which short-circuits before this code path runs. Documented (not fixed, for the same cross-theory
shared-framework-scope reason Phase 15 gave for its own related exclusion) in
`docs/ITERATE.md`'s "A Live Limitation" section, with pointers added from `README.md`,
`ARCHITECTURE.md`, and `USER_GUIDE.md`. **Also noticed in passing, left unfixed as out of this
phase's file list**: `docs/ADEQUACY.md`'s own "Scope and status" section still describes
`semantic/core.py`/`operators.py` "as they stand today" as the retired window-and-abundance
encoding -- stale now that Phases 9-14 landed the certificate rewrite in those exact files;
`ADEQUACY.md` is owned by the separate adequacy-layer task per this phase's own Amendment note
above, so this phase did not edit it, but the discrepancy is recorded here for that task to pick
up.

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

### Phase 23: Remove the development marker and re-enable gating [COMPLETED]

**Goal**: Bimodal is a gating theory again, with every quarantine mechanism removed rather than
left inert.

**Tasks**:
- [x] Delete the `pytest_collection_modifyitems` hook from
      `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` (its own docstring names this
      as the exit path).
- [x] Delete the `development` half of `oracle/conftest.py`'s hook and the marker registration in
      `code/pyproject.toml`. The `xdist_serial` half of the same hook, and its
      `_SOUNDNESS_CORE_CLASSES`/`_is_soundness_core` exemption machinery (now dead, deleted with
      the `development` half it existed only to support), were the two things touched; the
      `xdist_serial` marking itself is unaffected.
- [x] Remove `and not development` from every gating invocation: `flake.nix` (2), `.github/workflows/tests.yml` (2),
      `packaging.yml` (1), `release.yml` (2), `pypi-smoke.yml` (1), `oracle/run-oracle-suite.sh` (2),
      and the documentation strings in `code/run_tests.py`. `code/tests/ci/test_workflow_parity.py`
      (byte-for-byte parity between `flake.nix` and `tests.yml`) verified green after the edit.
- [x] Retire or rewrite the CI contract tests that assert the marker's application:
      `test_development_marker_application.py`, `test_oracle_development_marker_application.py`,
      `test_gating_selection_bimodal_decoupling.py` deleted outright (their entire subject
      evaporated with the mechanisms they tested -- bimodal's solve cost is no longer something to
      decouple from). `test_run_tests_markers.py`'s illustrative `MARKER_EXPR` constant updated
      `"not development"` -> `"not unstable"`. `test_unstable_deselection_wiring.py` narrowed from
      asserting both `not unstable` and `not development` to `not unstable` alone, with the
      now-dead `_INVOCATION_COUNT_ANCHORS` mechanism (and its `test_invocation_count_anchor_is_current`
      test) removed -- `EXPECTED_GATING_MARKER_INVOCATIONS` stays `10` unchanged, since the
      invocation *count* did not change, only each expression's content.
- [x] Update `code/docs/core/TESTING_GUIDE.md` section 8.14 to record that the marker's single
      subject has exited development, and update `code/tests/README.md` and
      `bimodal/tests/README.md` accordingly. Section 8.14 rewritten in full as a retirement
      record (what it meant, what was removed, what was deliberately left alone, and a
      guidance note for a future theory needing the same pattern) rather than left as
      ~310 lines of now-dead procedure; two cross-references (8.9's own mention, and the
      "oracle suite" section's stale "49-item soundness core"/timing claim) updated alongside it.
      `code/tests/README.md` needed no change (its own "development" mentions are the unrelated
      "software development" sense, not the marker). `bimodal/tests/README.md`'s "This Suite Is
      Non-Gating" section rewritten to "This Suite Is Gating".
- [x] Re-assess the `test_example_budget_floor.py` comments that cite bimodal exclusions as
      justification, since those exclusions no longer exist. Confirmed directly (not assumed):
      `KNOWN_TIMEOUT_EXAMPLES`/`UNSTABLE_EXAMPLES` in `test_bimodal.py` are both empty sets, and
      `MD_TH_2`/`TN_CM_1`/`MF_MODAL_FUTURE_TH`/`BM_TH_5` are all now collected in `unit_tests`.
      The stale paragraph naming these four as uncollected was rewritten to record the historical
      state and the correction, rather than silently deleted.

**Discovered beyond this phase's own task list**: two extra real consumers of the `development`
marker, not named anywhere in the plan's Phase 23 task list, would have been left broken (an
unregistered-marker warning) or semantically wrong (still claiming a cost that no longer exists)
had they not been updated: `code/src/model_checker/builder/tests/unit/test_example.py`'s
`test_build_example_bimodal_theory_countermodel` (marker removed; its settings dict's retired
`N`/padded `max_time: 30` also updated to the certificate encoding's own fast default, verified
green both before and after at 0.18-0.19s) and
`code/tests/packaging/test_generate_then_execute.py`'s `_DEVELOPMENT_THEORIES` (emptied from
`{"bimodal"}`, kept as an empty set rather than deleted, matching this codebase's own
empty-registry convention). A `code/CHANGELOG.md` entry was added under `[Unreleased]` (Keep a
Changelog convention: never rewrite an already-published version's entry) recording the redesign
and the marker's retirement, since the 1.3.8 entry that introduced the marker is a published,
immutable historical record.

**A pre-existing bug from Phase 21's own Reasoned Exclusions table is naturally resolved as a side
effect, not separately fixed**: `oracle/run-oracle-suite.sh`'s pass 2 ("serial, xdist_serial")
previously reported "FAILED (exit 5)" because its one real `xdist_serial`-matching test was also
`development`-marked, and pass 2's own filter excluded `development`-marked tests -- so it could
never be selected by either pass, root-caused in Phase 21 to a marker-interaction gap dating to
commit `a7ea2e7f`. With `development` retired, that test is no longer marked, and a live
`bash oracle/run-oracle-suite.sh` run now shows pass 2 selecting and passing 5 tests (previously
0, exit 5). This was not a deliberate fix in this phase -- the blocking condition just no longer
exists -- but it closes a gap Phase 21 explicitly left open as pre-existing and out of scope.

**Timing**: 2 hours

**Depends on**: 19, 21

**Verification Tier**: full

**Scope Hypothesis**: ten gating invocations carry `and not development` across seven files, and
five CI contract tests assert the marker. **Confirmed exactly**: `grep -rn "not development"`
across the repository (excluding `specs/`) found precisely 10 invocations across `flake.nix` (2),
`.github/workflows/tests.yml` (2), `packaging.yml` (1), `release.yml` (2), `pypi-smoke.yml` (1),
`oracle/run-oracle-suite.sh` (2), plus documentation strings in `code/run_tests.py` (the 7th file,
no gating invocation of its own); and precisely 5 CI contract tests
(`test_development_marker_application.py`, `test_oracle_development_marker_application.py`,
`test_gating_selection_bimodal_decoupling.py`, `test_run_tests_markers.py`,
`test_unstable_deselection_wiring.py`). No discrepancy from the hypothesis.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py`
- `oracle/conftest.py`
- `code/pyproject.toml`
- `flake.nix`
- `.github/workflows/tests.yml`, `packaging.yml`, `release.yml`, `pypi-smoke.yml`
- `oracle/run-oracle-suite.sh`
- `code/run_tests.py`
- `code/tests/ci/test_development_marker_application.py`, `test_oracle_development_marker_application.py`,
  `test_gating_selection_bimodal_decoupling.py` -- all three deleted
- `code/tests/ci/test_run_tests_markers.py`, `test_unstable_deselection_wiring.py` -- edited
- `code/docs/core/TESTING_GUIDE.md`
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` (not in the plan's original list;
  named explicitly in this phase's own task text above)
- `code/tests/ci/test_example_budget_floor.py` (not in the original list; the phase's own
  re-assessment task above)
- `.github/workflows/README.md` (not in the original list; carried the same `and not development`
  phrasing in prose form as `tests.yml`/`flake.nix`)
- `code/src/model_checker/builder/tests/unit/test_example.py`,
  `code/tests/packaging/test_generate_then_execute.py` (not in the original list; two real
  marker consumers discovered during implementation, see the Discovered note above)
- `code/CHANGELOG.md` (not in the original list; a new `[Unreleased]` entry, not an edit to the
  1.3.8 entry that introduced the marker)

**Verification**:
- `grep -rn "not development"` outside `specs/` returns nothing except historical mentions in
  `code/CHANGELOG.md`'s published 1.3.8 entry and this phase's own retirement-record prose in
  `test_unstable_deselection_wiring.py` and `TESTING_GUIDE.md` section 8.14. **CONFIRMED.**
- `pytest code/tests/ci -v` green. **CONFIRMED**: 136 passed (down from more before three files'
  deletion, none newly red).
- The gating expression now collects bimodal's tests: verify with `--collect-only` that the count
  rises by the bimodal tree's size. **CONFIRMED**: `pytest src/model_checker/theory_lib/bimodal -m
  "not packaging and not performance and not unstable and not xdist_serial" --collect-only -q`
  collects all 366; the same 366 previously collected 0 under the `and not development` form.
- Additional verification beyond the plan's own bar: `pytest src/model_checker/theory_lib/bimodal/tests/
  -q` -> 366 passed; `pytest oracle/bimodal_logic/tests/ -q` -> 567 passed, 4 xfailed (identical to
  Phase 21's own figures, confirming the retirement changed gating wiring, not test outcomes);
  `bash oracle/run-oracle-suite.sh` -> both passes PASSED (pass 2 now genuinely selects and passes
  5 tests, see the Discovered note above).

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
