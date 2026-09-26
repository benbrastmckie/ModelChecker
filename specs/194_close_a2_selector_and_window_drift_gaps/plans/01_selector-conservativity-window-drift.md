# Implementation Plan: Close the A2 selector and window-drift gaps

- **Task**: 194 - Close the two residual encoder-versus-specification gaps in the A2
  encoding-completeness argument
- **Status**: [IMPLEMENTING]
- **Effort**: 4.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/194_close_a2_selector_and_window_drift_gaps/reports/01_selector-conservativity-window-drift.md`
- **Artifacts**: plans/01_selector-conservativity-window-drift.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/context/standards/status-markers.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
  - `code/docs/core/TESTING_GUIDE.md`
- **Type**: z3
- **Lean Intent**: false

## Overview

Two residual encoder-versus-specification gaps in the bimodal A2 (encoding completeness) argument
are closed here, both behavior-preserving. First, the one-hot target selector (`sel`/
`target_constraints`, `witness_constraints.py`) is structure that (C1)-(C4) do not themselves
contain; research established it is a *lossless Skolemization* of (C4)'s existential target time
(periodicity of `LabelledLasso.label` plus `target_window()` being exactly one representative
position per slot), so the work is to record that argument and to pin it with a direct test that
cross-checks the Z3 side against `certificate._target_holds` rather than against a hand-derived
expectation. Second, `WitnessRegistry.target_window()` is the last independently-defined window in
the encoder; it is made to delegate to `certificate._box_window`, joining the three bounds
`witness_constraints.py` already imports, so encoder and re-checker cannot drift on it by
construction. Definition of done: the delegation is in place, two new test groups (window
agreement across a swept `(nb, nm, nf)` range; selector conservativity against the re-checker)
pass, the four affected prose/docstring locations record the argument, and both the full bimodal
suite and the four-theory gate are green with no behavioral change.

### Research Integration

Report `01_selector-conservativity-window-drift.md` is integrated as follows:

- **F1** (selector conservativity is a short algebraic fact: window = one representative per slot,
  `sel[t]`'s implications read the same Z3 terms `_target_holds` reads, periodicity means no target
  time is lost) supplies the argument Phase 4 records and the equivalence Phase 3 tests.
- **F2** (no existing test isolates the selector from (C1)-(C3) *and* cross-checks the re-checker;
  `TestTargetConstraints` spot-checks clauses, `test_certificate_a2_triangle.py` is aggregate-only)
  defines Phase 3's shape: isolation like `TestTargetConstraints`, expectations computed by
  `certificate._target_holds`, never re-derived inline.
- **F3** (drift is real but latent; `target_window()` is load-bearing for `target_constraints`,
  `extract_certificate`'s slot-ordered label reconstruction, `symmetry.py`, `iterate.py`,
  `proposition.py`, and the A2-triangle test's candidate sizing) drives Phase 2's choice of
  delegation over assert-agreement, and its `full` verification tier.
- The report's **Decisions** section's recommendation (share one definition *and* add the swept
  agreement test as a supplement, not a replacement) is adopted verbatim: Phase 1 pins the sweep,
  Phase 2 delegates.
- Confirmed during planning, beyond the report: `certificate.py` imports only `.formula`, so
  `witness_registry.py` importing `_box_window` from `.certificate` introduces no cycle. Also
  found: `docs/TRUST_PIPELINE.md` states both gaps in prose twice (its Stage-2 "Two gaps remain"
  paragraph and its "What remains" table row "Selector conservativity, and the last unshared
  window"); those are additional locations Phase 4 must update, which the report did not name.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation was requested for this dispatch (no `roadmap_path` in the delegation
context).

## Goals & Non-Goals

**Goals**:
- `WitnessRegistry.target_window()` delegates to `certificate._box_window`, so exactly one
  definition of `[-nb, nm+nf)` exists in the codebase.
- A swept-range regression pins `target_window() == _box_window(registry) == range(-nb, nm+nf)`
  across the configured range of `nb`, `nm`, `nf` (including `mid == 0`), so a future
  reintroduction of an independent body fails loudly.
- A direct, (C1)-(C3)-isolated test establishes the selector-conservativity equivalence: with only
  `target_constraints` asserted, `sel[t]` is satisfiable exactly for those `t` where
  `certificate._target_holds` holds of the corresponding hand-built `WitnessFamily`.
- The periodicity corollary (`_target_holds` at `t` equals `_target_holds` at its in-window
  representative `t'`) is tested directly, with no Z3 solve.
- The conservativity argument and the now-shared window are recorded in `docs/ADEQUACY.md` §7.3,
  `docs/TRUST_PIPELINE.md` (both gap statements), and the relevant docstrings/comments.
- Full bimodal suite and four-theory gate green; no behavioral change.

**Non-Goals**:
- Widening the A2-triangle grid to `nb = nf = 2` (a separate, measured item in
  `TRUST_PIPELINE.md`'s "What remains").
- Any change to (C1)-(C3)'s constraint generators, to `_coherence_window`/`_scan_*_bound`, or to
  the re-checker's own logic.
- Discharging A1, A0, or S4, or touching the Lean side.
- Formalizing the conservativity argument in Lean; it is recorded as prose plus a test, matching
  how the report frames it.
- Changing `WitnessRegistry`'s public API shape (`target_window()` keeps its name, signature, and
  `range` return type).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Delegation is read as conflating two concepts that share a formula only by coincidence, inviting a future one-sided edit | M | M | Phase 2's docstring/comment text states *why* both require exactly `[-nb, nm+nf)`: F1's window-completeness argument for the selector, ADEQUACY.md §5.2's proved `mem_all_iff_window` bound for box faithfulness. Phase 1's sweep is the mechanical backstop. |
| Phase 3's test degenerates into a hand-derived expectation (re-implementing C4 inline) — exactly the weakness F2 names in the existing tests | H | M | Phase 3's task list requires the expected satisfying-`t` set to be computed by calling `certificate._target_holds` on a constructed `WitnessFamily`. A review read of the diff confirming no inline premise/conclusion membership logic is part of the phase's verification, not an aspiration. |
| A new `from .certificate import _box_window` in `witness_registry.py` creates an import cycle | H | L | Already falsified during planning: `certificate.py`'s only intra-package import is `.formula`. Phase 2 re-confirms with a bare `python -c` import of `witness_registry` before proceeding. |
| Label-bit fixing in Phase 3 desynchronizes from the hand-built lasso (Z3 bits say one thing, the `LabelledLasso` segments another), making a green test vacuous | M | M | Phase 3 derives *both* sides from one source: build the `LabelledLasso` segments first, then set `registry.bit(0, t, f)` for each window `t` and closure `f` from `family.main.label(t)` membership. A deliberate mismatch case (flip one bit, expect disagreement) guards against vacuity. |
| Swept range too large, making the unit test slow | L | L | Sweep stays at `DEFAULT_EXAMPLE_SETTINGS` order of magnitude: `nb` in 1..3, `nm` in 0..3, `nf` in 1..3 (36 combinations, no Z3 solve). |
| A sibling task dispatched this same cycle edits a bimodal file concurrently, so an unexpected failure is misattributed | M | M | Per the dispatch's concurrency note: re-read every file immediately before editing; stage only this task's own hunks with explicit file lists (never `git add -A`, never a directory pathspec); treat an unexplained failure outside this task's file set as possibly a sibling's in-flight edit and report rather than "fix" it. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 1 and 3 touch disjoint test files
(`tests/unit/test_witness_registry.py` and `tests/unit/test_witness_constraints.py`) and no
production file, so they are genuinely parallel-safe.

### Phase 1: Pin the window agreement with a swept-range regression [COMPLETED]

**Goal**: Before any production edit, pin the current behavior of `target_window()` against
`certificate._box_window` across the configured range of segment lengths, so Phase 2's refactor has
a behavioral baseline and a future reintroduction of an independent body fails loudly.

**Tasks**:
- [x] Re-read `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py`
      immediately before editing (sibling-concurrency discipline).
- [x] Extend the existing `TestTargetWindow` class (it already holds
      `test_target_window_length_equals_slots_per_lasso` and
      `test_target_window_hits_every_slot_exactly_once`) with a swept-range test asserting, for
      `back` in `1..3`, `mid` in `0..3`, `fwd` in `1..3` (36 combinations; `back`/`fwd` must be
      `>= 1` and `mid >= 0` per `WitnessRegistry.__init__`'s own validation):
      `registry.target_window() == _box_window(registry)` and
      `registry.target_window() == range(-back, mid + fwd)`.
- [x] Import `_box_window` from `...semantic.certificate` in that test module (the sibling module
      `test_witness_constraints.py` already establishes this exact import precedent).
- [x] Add a short docstring on the new test recording its purpose: it is the mechanical backstop
      against re-divergence once `target_window()` delegates, not a claim that two independent
      formulas happen to agree.
- [x] Run the module: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v`.
      (46 passed)
- [x] Commit (`task 194 phase 1.1: pin target_window/_box_window agreement across swept segment lengths`).

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Note on TDD ordering**: this test passes both before and after Phase 2, because the refactor is
behavior-preserving by construction (the two formulas are already textually identical). That is
the honest characterization — it is a pinned baseline plus a drift guard, not a RED-then-GREEN
cycle. Do not manufacture an artificial failure to simulate one.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` - add the swept
  agreement test to `TestTargetWindow`; add the `_box_window` import.

**Verification**:
- The new test passes, and `TestTargetWindow`'s two pre-existing tests still pass.
- The sweep actually executes 36 parameter combinations (assert or print the count once during
  development; do not leave a print in the committed test).

---

### Phase 2: Delegate `target_window()` to `_box_window` [NOT STARTED]

**Goal**: Remove the last independently-defined window in the encoder, so encoder and re-checker
share exactly one definition of `[-nb, nm+nf)` and cannot drift.

**Tasks**:
- [ ] Re-read `semantic/witness_registry.py` and `semantic/certificate.py` immediately before
      editing.
- [ ] Confirm no import cycle: `cd /home/benjamin/Projects/ModelChecker && PYTHONPATH=code/src python -c "from model_checker.theory_lib.bimodal.semantic import witness_registry; print('ok')"`
      after adding the import (`certificate.py`'s only intra-package import is `.formula`, so this
      is a confirmation, not an open question).
- [ ] In `semantic/witness_registry.py`: add `from .certificate import _box_window` alongside the
      existing `from .formula import Box, Formula`, and change `target_window()`'s body to
      `return _box_window(self)`.
- [ ] Rewrite `target_window()`'s docstring: it is now the *shared* definition, identical to box
      faithfulness's proved `mem_all_iff_window` bound (`docs/ADEQUACY.md` §5.2), reused for the
      one-hot selector because F1's completeness argument requires exactly one representative
      position per slot — state that both uses require exactly `[-nb, nm+nf)`, so sharing is the
      technically correct outcome rather than a convenience.
- [ ] In `semantic/certificate.py`, update the four-window-helpers comment block (the paragraph
      beginning "These four window helpers are deliberately duck-typed"): remove the
      "`WitnessRegistry.target_window` is independently defined" language, which is no longer
      accurate, and record that all four helpers are now shared by import, `_box_window` serving
      both box faithfulness and the encoder's selector/extraction window.
- [ ] Update `semantic/witness_registry.py`'s module docstring where it describes the position-slot
      model, if it asserts an independent target window (re-read to confirm before editing; do not
      edit speculatively).
- [ ] Run the two directly affected unit modules plus the extraction/iterate consumers:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_symmetry.py -v`.
- [ ] Run the full bimodal suite (this phase's tier is `full`):
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v`.
- [ ] Commit (`task 194 phase 2.1: share one window definition between encoder and re-checker`).

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: `target_window()` is consumed by five production modules
(`semantic/witness_constraints.py`, `semantic/core.py`, `semantic/symmetry.py`,
`semantic/proposition.py`, `iterate.py`) and four test modules, all of which call it through the
unchanged `registry.target_window()` interface and so require no edit. Confirm at implementation
time with `grep -rn "target_window" code/src/model_checker/theory_lib/bimodal/ | grep -v '\.pyc'`
and verify every hit is either a call site through the unchanged interface, a prose/comment
mention, or one of the two files this phase edits — if any hit turns out to be a second *definition*
or a direct re-derivation of the formula, treat it as a scope expansion and record it rather than
silently absorbing it.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` - add the `_box_window`
  import; `target_window()` delegates; docstring rewritten; module docstring touched only if it
  asserts independence.
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - the four-window-helpers
  comment block updated (comment only; no code change).

**Verification**:
- `target_window()`'s body contains no arithmetic — it is exactly `return _box_window(self)`.
- Phase 1's swept agreement test still passes (now trivially, by delegation).
- Full bimodal suite green, including the `slow`-marked `test_certificate_a2_triangle.py` cases.
- `grep -c "range(-" semantic/witness_registry.py` shows the formula no longer appears there.

---

### Phase 3: Direct selector-conservativity test against the re-checker [NOT STARTED]

**Goal**: Pin F1's equivalence — with only (C4) asserted, `sel[t]` is satisfiable exactly for the
`t` at which `certificate._target_holds` holds of the corresponding family — so a future
A2-triangle disagreement cannot be wrongly attributed to the selector mechanism.

**Tasks**:
- [ ] Re-read `tests/unit/test_witness_constraints.py` immediately before editing.
- [ ] Add a new test class (e.g. `TestSelectorConservativity`) after the existing
      `TestTargetConstraints`, importing `LabelledLasso`, `WitnessFamily` and `_target_holds` from
      `...semantic.certificate` (`_box_window`/`_coherence_window` are already imported in that
      module, establishing the private-helper import precedent).
- [ ] Write a small helper in the test module that, given `back`/`mid`/`fwd` label tuples and a
      closure, builds the `LabelledLasso` + single-lasso `WitnessFamily` **and** returns the
      corresponding bit assignment: for each `t` in `registry.target_window()` and each `f` in the
      closure, `registry.bit(0, t, f) == (f in family.main.label(t))`. Both sides must be derived
      from the one `LabelledLasso`, never written out twice by hand.
- [ ] Parametrize over at least four explicit label assignments crossing premise-present/absent
      and conclusion-present/absent (e.g. premises `[P]`, conclusions `[Q]`, with: no position
      satisfying C4; exactly one; several; and every position), at `back=2, mid=1, fwd=2`
      (`DEFAULT_EXAMPLE_SETTINGS`' own lengths) and at `back=mid=fwd=1` (the A2-triangle grid).
- [ ] For each assignment: assert only `generator.target_constraints(premises, conclusions)` plus
      the derived bit equalities into a fresh solver — no local coherence, no fulfilment, no box
      faithfulness — and assert
      (a) `solver.check() == sat` iff `{t in window : _target_holds(family, premises, conclusions, t)}`
      is non-empty, and
      (b) per-position, for every `t` in the window: pushing `generator.sel(t)` yields `sat` iff
      `_target_holds(family, premises, conclusions, t)`, and `unsat` otherwise (use
      `solver.push()`/`solver.pop()` around each `t`; this is the crisp form of "every model has
      `sel[t]` true only for `t` in the expected set").
- [ ] Add one deliberate-mismatch guard against vacuity: take a satisfying assignment, flip a
      single premise bit at the only satisfying position, and assert the solver flips to `unsat`
      while `_target_holds` on the *unflipped* family still reports that position — confirming the
      test is actually reading the bits it thinks it is.
- [ ] Add the periodicity-corollary test, with no Z3 at all: for a hand-built `LabelledLasso`, pick
      several `t` outside `registry.target_window()` and their in-window representatives `t'`
      (`registry.wrap(t) == registry.wrap(t')`), and assert
      `_target_holds(family, premises, conclusions, t) == _target_holds(family, premises, conclusions, t')`.
      Cover both `t < -nb` and `t >= nm + nf`.
- [ ] Give the new class a docstring stating what it establishes and why the expectation is computed
      by `_target_holds` rather than derived inline (F2's named weakness in the existing tests).
- [ ] Run: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -v`.
- [ ] Commit (`task 194 phase 3.1: test selector conservativity against the re-checker`).

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` - new
  `TestSelectorConservativity` class, the family/bit-assignment helper, and the periodicity test.

**Verification**:
- Every new test passes; the pre-existing `TestTargetConstraints` tests are untouched and still
  pass.
- Diff read-through confirms **no inline re-implementation** of C4's premise/conclusion membership
  logic: every expected verdict traces to a `_target_holds` call.
- The deliberate-mismatch guard fails when the flip is removed (check once during development,
  then restore) — evidence the assertions are not vacuous.
- The periodicity test performs no `z3.Solver()` call.

---

### Phase 4: Record the conservativity argument and the shared window [NOT STARTED]

**Goal**: Move F1 from tribal knowledge into the documents that A2 is argued in, and retire the
now-inaccurate "two gaps remain" prose.

**Tasks**:
- [ ] Re-read each target file immediately before editing.
- [ ] `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` §7.3: add a short paragraph
      (after the A2-triangle test block, before §7.4) stating that the one-hot selector `sel[t]` is
      a *lossless Skolemization* of (C4)'s existential target time — conservative because
      `target_window()` supplies exactly one representative position per slot and
      `LabelledLasso.label` is exactly periodic, so restricting `sel`'s domain to the window can
      discard only duplicate representations of an in-window target time, never a satisfying one —
      and therefore that "exactly the conjunction of (C1)-(C4)" is not weakened by the selector's
      presence. Name the deciding unit test for this claim (`TestSelectorConservativity` in
      `tests/unit/test_witness_constraints.py`) the way §7.3 already names the A2-triangle test.
- [ ] `docs/TRUST_PIPELINE.md`, Stage-2 "What is nonetheless known about the encoder" paragraph:
      change "Three of the four window bounds are shared by import" to all four, and replace the
      "Two gaps remain" sentence with the closed state — the window is now shared by construction,
      and the selector's conservativity is argued in ADEQUACY.md §7.3 and pinned by
      `TestSelectorConservativity`.
- [ ] `docs/TRUST_PIPELINE.md`, "What remains" -> "In this repository" table: remove or rewrite the
      row "**Selector conservativity, and the last unshared window**" to reflect that both halves
      are discharged (keep the separate "Widen the A2 grid to `nb = nf = 2`" row untouched — that is
      an explicit non-goal here).
- [ ] `semantic/witness_constraints.py`: extend `sel`'s and `target_constraints`' docstrings with a
      reference to the conservativity argument, mirroring how the module docstring already carries
      the corresponding reasoning for local coherence's wide window.
- [ ] `semantic/witness_constraints.py` module docstring, the sentence describing
      `registry.target_window()`: note it is now the shared `_box_window` definition.
- [ ] Verify no task-number references were introduced into any file outside `specs/**` (per
      `.claude/rules/no-task-references-in-deliverables.md`): cite ADEQUACY.md section numbers,
      test class names, and file names as anchors, never "task 194". Pre-existing phrasings in
      these files are left as they are.
- [ ] Diff read-through confirming every changed hunk lies inside markdown prose or a docstring —
      zero code or signature changes in this phase.
- [ ] Commit (`task 194 phase 4.1: record selector conservativity and the shared window`).

**Timing**: 1 hour

**Depends on**: 2, 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: four documentation locations are asserted here — `docs/ADEQUACY.md` §7.3,
two separate statements in `docs/TRUST_PIPELINE.md` (the Stage-2 paragraph and the "What remains"
table row), and the `sel`/`target_constraints`/module docstrings in
`semantic/witness_constraints.py`. Confirm the list is complete at implementation time with
`grep -rn "independently defined\|unshared window\|Two gaps remain\|target_window" code/src/model_checker/theory_lib/bimodal/docs/ code/src/model_checker/theory_lib/bimodal/semantic/*.py | grep -v '\.pyc'`
(note `docs/ARCHITECTURE.md` and `semantic/core.py` also mention `target_window` descriptively —
check whether either asserts independence; if so the count is five or six, and the extra locations
must be edited, not skipped).

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §7.3 conservativity paragraph.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - Stage-2 paragraph and the
  "What remains" table row.
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - `sel`/
  `target_constraints` docstrings and the module docstring's `target_window()` sentence.

**Verification**:
- Every changed hunk is inside prose or a docstring (diff read-through).
- No remaining assertion anywhere in `bimodal/` that `target_window` is independently defined:
  the grep in the Scope Hypothesis returns no such claim.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit -q` still passes
  (guards against a docstring edit that crossed a string boundary — `prose`'s named blind spot).

---

### Phase 5: Full-suite and four-theory-gate verification [NOT STARTED]

**Goal**: Confirm the task's explicit "no behavioral change is intended" claim against the full
bimodal suite and the repository's gating selection.

**Tasks**:
- [ ] Re-read `git status --short` and `git log --oneline -5` first: confirm no foreign
      uncommitted modification or foreign commit from a sibling task is in the tree. If one is
      present, STOP and report it rather than proceeding (dispatch concurrency note, item 5).
- [ ] Full bimodal suite, including the `slow`-marked A2-triangle cases:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v`.
- [ ] Four-theory gate, matching `.github/workflows/tests.yml`'s two-pass shape (parallel pass
      excluding `xdist_serial`, then the serial pass over exactly those):
      `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
      then
      `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread`.
      Run each in the background with a captured PID and a bounded waiter per
      `context/patterns/bounded-build-waiter.md`; do not poll unbounded.
- [ ] Spot-check the CLI path is unaffected: `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py`
      and confirm the countermodel/no-countermodel verdicts match what the examples' `expectation`
      settings declare (the certificate-encoding path runs through `target_window()` in
      `extract_certificate`, so this exercises the delegation end to end).
- [ ] Record the observed pass/fail counts for both passes in the implementation summary — actual
      numbers, not "all green".
- [ ] Commit any final doc/state touch-ups (`task 194: complete implementation`).

**Timing**: 0.75 hours

**Depends on**: 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None expected (verification only). Any file changed here is a defect fix and must be reported as
  a deviation from the plan.

**Verification**:
- Full bimodal suite: zero failures, zero errors.
- Both four-theory-gate passes: zero failures, zero errors (pre-existing `unstable`-marked
  deselections are expected and are not failures — confirm the deselection count matches the
  baseline rather than assuming it).
- `dev_cli.py` bimodal examples: every example's verdict matches its declared `expectation`.
- If any failure appears in a file outside this task's edited set, check `git log` before
  attributing it — it may be a sibling task's in-flight edit (dispatch concurrency note, item 4).

## Testing & Validation

- [ ] `TestTargetWindow`'s swept agreement test passes across all 36 `(nb, nm, nf)` combinations,
      including every `mid == 0` case.
- [ ] `TestSelectorConservativity` passes: per-position `sat`/`unsat` agrees with `_target_holds`
      for every parametrized label assignment, at both `back=2,mid=1,fwd=2` and `back=mid=fwd=1`.
- [ ] The periodicity-corollary test passes for `t < -nb` and `t >= nm + nf`, with no Z3 solve.
- [ ] The deliberate-mismatch guard confirms the conservativity assertions are non-vacuous.
- [ ] Pre-existing `TestTargetConstraints`, `TestTargetWindow`, `test_certificate.py`,
      `test_symmetry.py`, `test_iterate.py` all still pass unchanged.
- [ ] `test_certificate_a2_triangle.py` (both tiers, including `slow`) passes with the same verdicts
      as before the change — it consumes `target_window()` for candidate sizing, so a changed
      candidate count would be the loudest possible signal of an unintended behavioral change.
- [ ] Full bimodal suite green.
- [ ] Four-theory gate green, both passes.
- [ ] `dev_cli.py` bimodal examples produce verdicts matching their `expectation` settings.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` - `target_window()`
  delegating to `_box_window`, docstring rewritten.
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - four-window-helpers comment
  block updated (comment only).
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - `sel`/
  `target_constraints`/module docstrings reference the conservativity argument.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` - swept-range
  window-agreement regression.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` -
  `TestSelectorConservativity` plus the periodicity-corollary test.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §7.3 selector-conservativity
  paragraph.
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - Stage-2 encoder paragraph and
  "What remains" row updated.
- `specs/194_close_a2_selector_and_window_drift_gaps/summaries/01_*-summary.md` - implementation
  summary with observed suite counts.

## Rollback/Contingency

Every phase commits independently and touches a small, disjoint file set, so rollback is
per-phase `git revert` of the named commit — no snapshot-then-reset is needed for the ordinary
case, and a whole-tree revert is inappropriate here because sibling tasks share this working tree
this cycle.

- **Phase 1 or 3 (test-only)**: revert the single commit; no production behavior is affected.
- **Phase 2 (delegation)**: revert the commit, restoring the independent `range(-self.nb,
  self.nm + self.nf)` body. Phase 1's agreement test continues to pass after the revert (it
  asserts equality, not delegation), so the revert is self-consistent; the task then closes as
  `[PARTIAL]` with the window gap still open and Phase 4's prose reverted along with it.
- **Phase 4 (prose)**: revert the commit; no code affected.
- **If Phase 5 finds a real behavioral change**: do not paper over it. The delegation is
  provably behavior-preserving for every valid `(nb, nm, nf)`, so a genuine behavioral difference
  means one of the planning premises is false — record the failing case, revert Phase 2, and report
  it as a finding rather than adjusting the test to match.
- **If a genuine whole-tree rollback becomes necessary** (it should not, given the per-phase
  commits): follow `context/contracts/recovery.md`'s rollback rung for the exact
  `git-snapshot.sh` invocation shape, including its out-of-scope override flag. Never emit a bare
  default-mode `git-snapshot.sh` call as a routine start-of-phase checkpoint; a defensive
  checkpoint before risky work uses `--no-revert`.
