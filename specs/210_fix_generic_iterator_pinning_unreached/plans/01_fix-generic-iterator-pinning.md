# Implementation Plan: Fix generic iterator pinning never reaching the rebuilt model's solve

- **Task**: 210 - Fix generic iterator pinning never reaching the rebuilt model's solve for logos, exclusion and imposition
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: `specs/210_fix_generic_iterator_pinning_unreached/reports/01_fix-generic-iterator-pinning.md`
- **Artifacts**: plans/01_fix-generic-iterator-pinning.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

`iterate/models.py`'s generic pinning loop in `ModelBuilder.build_new_model_structure` computes
`is_world`/`possible`/`verify`/`falsify` pins from the candidate Z3 model and asserts them only
into a local `temp_solver` that is never checked and never read again. The solver that actually
produces the rebuilt model is built by `models/structure.py`'s `_setup_solver` from the four
live constraint lists (`frame_constraints`, `model_constraints`, `premise_constraints`,
`conclusion_constraints`) — so for logos, exclusion and imposition (which have no
`_pin_theory_specific_values` override) the pins never reach the solve and every rebuild is an
independent, unpinned resolve. The fix appends each pin literal into
`model_constraints.frame_constraints` inline in the generic loop, alongside each existing
`temp_solver.add(...)` — the mechanism bimodal's own override already validates, applied one call
site up. Done when: a live, non-mocked, three-theory regression test asserts every rebuild's
solved predicate values equal the candidate model's, that test fails before the fix and passes
after, and the full four-theory gate is green with every changed iteration result reviewed.

### Research Integration

The research report is integrated as follows:

- **F2/F6 (root cause and precedent)** set the fix mechanism in Phase 3: append into
  `model_constraints.frame_constraints` at pin-computation time, keeping every existing
  `temp_solver.add(...)` call for interface parity with tests that assert against `temp_solver`.
- **F5 (rejected mechanism)** is recorded in Non-Goals: a `_pin_theory_specific_values` default
  that replays `temp_solver.assertions()` would re-append every base constraint a second time
  (they are copied into `temp_solver` at `models.py:93` before the pins are added), doubling
  solver size per rebuild and aliasing `_setup_solver`'s `constraint_dict` labels.
- **F3 (live confirmation for all three theories)** supplies the exact probe method, examples and
  settings that Phase 2's regression test is built from — `[] |- \neg A`/N=2 for logos,
  `EX_CM_6`/N=3 for exclusion, `IM_CM_0`/N=4 for imposition, each with a bounded `max_time`.
  SCOPE item 1 is already discharged by the research phase; Phase 2 converts that one-off probe
  into permanent coverage rather than re-confirming it.
- **F4 (no downstream consistency check)** is why the regression test asserts at the
  `build_new_model_structure` boundary rather than on final reported models: nothing in
  `iterate/core.py` would reject a divergent rebuild, so the invariant has to be checked where it
  is established.
- **F1/Decision 4** require the stale "Consequence, NOT fixed here" comment at
  `iterate/models.py:150-159` to be rewritten in the same edit as the fix.
- **F7/Decision 5** scope the bimodal docstring correction to a pure wording change (Phase 5).
- **Recommendation 5** shapes Phase 6: changed iteration results for `iterate > 1` examples in
  the three theories are expected fallout to be inspected individually, never blanket-suppressed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided for this dispatch; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Make the generic pinning loop's `is_world`/`possible`/`verify`/`falsify` pins actually reach
  the solve that produces the rebuilt model, for every theory without a
  `_pin_theory_specific_values` override (logos, exclusion, imposition).
- Add live, non-mocked, shared-engine regression coverage over all three affected theories that
  fails before the fix and passes after, and is agnostic to which live list a future refactor
  chooses for pins.
- Add a `frame_constraints`-presence assertion mirroring bimodal's existing
  `TestPinTheorySpecificValues` shape, for symmetry with the bimodal coverage.
- Correct the two stale in-code documentation claims (the `iterate/models.py` "NOT fixed here"
  comment and the bimodal `_ensure_frame_constraints_in_search_solver` docstring).
- Run and pass the full four-theory gate, with every changed iteration result reviewed.

**Non-Goals**:
- A `_pin_theory_specific_values` default that replays `temp_solver.assertions()` — rejected per
  F5; unsound (duplicates every base constraint).
- Any change to `_pin_theory_specific_values`'s signature, call site, or contract, or to
  bimodal's override behavior.
- Any change to `ModelConstraints.all_constraints` or its computed-property form — that defect is
  already fixed upstream and this task's gap is distinct (F1).
- Adding a fifth constraint-group list, or changing `_setup_solver`, display routines, or
  anything that assumes exactly four constraint-group lists (Decision 3).
- Adding a post-rebuild consistency check in `iterate/core.py`'s loop. F4 documents the absence;
  the regression test covers the invariant from the test side. A production-side guard is a
  larger design change and is out of scope here.
- Changing the recorded `expectation` values of any example to make a test pass.

## Decisions Carried Into This Plan

- **Pin destination: `frame_constraints`, confirmed.** The research flagged Decision 3 for
  planning-phase confirmation. Confirmed as written. The side effect is display-only: for model
  2+ of the three theories, `print_constraints`/`--save` output will list concrete pin literals
  under the "frame constraints" heading rather than under "model constraints". This is the same
  severity class as a previously accepted display-ordering finding, is not a soundness concern,
  and the alternative (a fifth list) would require touching `_setup_solver`, the display
  routines, and every site that assumes four groups — a materially larger diff for a cosmetic
  gain. Phase 6 includes an explicit look at one `print_constraints` rendering to confirm the
  output is still well-formed, not merely longer.
- **Sequencing: baseline before behavior change.** Because this changes iteration *results*, the
  gate is only interpretable against a recorded pre-fix baseline. Phase 1 captures it before any
  production edit lands.
- **In-code text must not cite task numbers.** The rewritten `iterate/models.py` comment and the
  bimodal docstring describe the mechanism and its resolution in durable terms only — no "task N"
  references in any file outside `specs/**`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Four-theory gate surfaces genuine result changes in `expectation`-asserting example tests | M | H | Expected per Recommendation 5. Phase 1's baseline makes each diff attributable; Phase 6 inspects every diff individually and records the verdict. Never blanket-suppress, never loosen the regression test, never edit an `expectation` to force green. |
| Pins land under the "frame constraints" display heading for rebuilt models | L | H | Accepted per Decisions above; display-only. Phase 6 confirms the rendering is still well-formed. |
| A rebuild becomes UNSAT once genuinely pinned (a candidate the search found is not actually realizable under the full constraint set) | H | L | `build_new_model_structure` already returns `None` on `not z3_model_status` and the loop handles it. Phase 3's verification watches for a collapse in model counts; Phase 6 treats a theory that can no longer find model 2 at all as a blocking finding, not expected fallout. |
| The regression test is slow enough to burden the default suite (three live iterating solves) | M | M | Use the small, fast examples and bounded `max_time` the research probes used; measure the class's wall-clock in Phase 2 and mark `slow` if it exceeds roughly 30s, per the existing marker taxonomy. |
| Reviewer conflates this fix with the upstream `all_constraints` property change | L | M | The rewritten `iterate/models.py` comment states plainly that the read-side property change is separate and already landed, and that the pins now reach the solve via the four live lists. |
| Repeated appends to `frame_constraints` across many rebuilds grow the list unboundedly within one iteration run | M | M | Each rebuild constructs fresh `model_constraints` via `original_build`'s path; Phase 3 verifies this empirically by asserting `len(frame_constraints)` does not grow monotonically across successive rebuilds in one run. If it does, scope the append to a per-rebuild copy rather than the shared list. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 5 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 6 | 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Capture Pre-Fix Baseline [COMPLETED]

**Goal**: Record the current, unpinned behavior so every post-fix change is attributable to this
fix rather than to unrelated drift.

**Tasks**:
- [x] Create `specs/210_fix_generic_iterator_pinning_unreached/baselines/`.
- [x] Run the four-theory directory gate and save full output to
      `baselines/01_pre-fix-theory-suites.txt`:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -q`
      Result: `1 failed, 1694 passed in 280.42s`, the one failure being the pre-existing
      `bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`.
- [x] Run the shared-engine iterate suite and save to `baselines/01_pre-fix-iterate.txt`:
      `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q`
      Result: `238 passed in 1.26s`.
- [x] Record the pass/fail/skip counts and the identity of any already-failing test in a short
      `baselines/01_pre-fix-summary.md`, so Phase 6 can distinguish a pre-existing failure from a
      new one.
- [x] For one representative `iterate > 1` example per affected theory, run it through
      `./dev_cli.py` and save the printed model 2+ output to
      `baselines/01_pre-fix-{theory}-iteration.txt`. These are the diffs Phase 6 reviews.
      Logos (`[] |- \neg A`, N=2, iterate:3) and exclusion (`EX_CM_6`, N=3, iterate:3,
      max_time=40) each settled at 1/3 models found within the bounded search (matching the
      research report's caveat about bounded `max_time`); imposition (`IM_CM_0`, N=4, iterate:3,
      max_time=40) found 2/3 models. All three are valid baseline captures for Phase 6's diff.

**Timing**: 1 hour (mostly solver wall-clock).

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Three baseline iteration captures (logos, exclusion, imposition) plus two
suite captures. Confirm by listing `baselines/` and checking each file is non-empty and ends with
a pytest summary line or a completed model printout.

**Files to modify**:
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/*` - new baseline captures (new
  files only; no production source touched)

**Verification**:
- Every named baseline file exists and is non-empty.
- `01_pre-fix-summary.md` names every currently-failing test by node ID, or states explicitly
  that there are none.

---

### Phase 2: RED — Live Three-Theory Pinning Regression Test [NOT STARTED]

**Goal**: Add the permanent regression test that encodes the pinning invariant, and confirm it
fails today for all three theories (TDD RED).

**Tasks**:
- [ ] Add a real-`BuildExample` helper to `code/src/model_checker/iterate/tests/integration/test_models.py`,
      modeled on bimodal's `_real_build_example` (`theory_lib/bimodal/tests/integration/test_iterate.py:559`):
      only the surrounding `BuildModule` is a `Mock`; the semantics, solver and model-checking
      path are real. Parametrize the theory via `theory_lib.{logos,exclusion,imposition}`'s own
      `get_theory()`.
- [ ] Add `class TestGenericPinningReachesRebuiltSolve`, parametrized over the three theories
      with the research-confirmed cases: logos `([], [r"\neg A"], N=2)`, exclusion `EX_CM_6`
      (`N=3`), imposition `IM_CM_0` (`N=4`); `iterate: 2` or `3`, bounded `max_time` (40).
- [ ] Intercept every `ModelBuilder.build_new_model_structure` call (monkeypatch wrapping the
      real method) to capture each `(candidate_z3_model, returned_structure)` pair.
- [ ] For every captured pair, assert that `is_world`, `possible`, `verify` and `falsify`
      (each guarded by `hasattr`, matching the production loop's own guards) evaluated at every
      state — and, for `verify`/`falsify`, every sentence-letter atom — under
      `returned_structure.z3_model` equal the same predicate evaluated under
      `candidate_z3_model`, with `model_completion=True` on both sides.
- [ ] Assert at least one rebuild was actually intercepted, so a test that silently captures
      nothing cannot pass vacuously.
- [ ] Do NOT duplicate `TestAllConstraintsReflectsCertificateAfterSolve` per theory — its subject
      is a different attribute and would not catch a regression of this defect (Recommendation 2).
- [ ] Run the new class and record the failure output; confirm all three theory parametrizations
      fail with predicate mismatches, matching the research's F3 signatures.
- [ ] Time the class; if it exceeds roughly 30s, add the existing `slow` marker.
- [ ] Commit the RED test on its own (it is a green sub-step of this phase: the test exists and
      correctly fails).

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Exactly one new test file region (one helper + one test class) in
`iterate/tests/integration/test_models.py`, three parametrizations, all three failing pre-fix.
Confirm by running
`PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/integration/test_models.py::TestGenericPinningReachesRebuiltSolve -v`
and checking the output shows three failures and zero errors/skips — an error or a skip means the
test is not exercising the path and must be fixed before Phase 3.

**Files to modify**:
- `code/src/model_checker/iterate/tests/integration/test_models.py` - add real-example helper and
  `TestGenericPinningReachesRebuiltSolve`

**Verification**:
- All three parametrizations FAIL (not error, not skip) with predicate-value mismatches.
- The rest of `iterate/tests/` still passes unchanged.

---

### Phase 3: GREEN — Route Generic Pins Into the Live Constraint List [NOT STARTED]

**Goal**: Make the generic loop's pins reach `_setup_solver`, turning Phase 2's failing test
green without changing `_pin_theory_specific_values`.

**Tasks**:
- [ ] In `code/src/model_checker/iterate/models.py`'s `build_new_model_structure`, for each of the
      eight existing `temp_solver.add(...)` pin sites (is_world true/false, possible true/false,
      verify true/false, falsify true/false), add a matching
      `model_constraints.frame_constraints.append(<same literal>)`. Keep every existing
      `temp_solver.add(...)` call exactly as it is (interface parity with tests asserting against
      `temp_solver`, and with bimodal's own precedent).
- [ ] Preserve the existing `hasattr(semantics, 'is_world')` / `'possible'` / `'verify'` /
      `'falsify'` guards unchanged — bimodal must remain on its override path with no generic
      pins appended.
- [ ] Rewrite the stale comment block at `iterate/models.py:150-159`: state that
      `all_constraints` is a read-only computed property (so nothing is assigned here), that
      `_setup_solver` builds its solver from the four component lists, and that the generic pins
      are therefore appended into `frame_constraints` above so they reach the solve. Remove the
      "Consequence, NOT fixed here" claim entirely. No task-number reference in the comment text.
- [ ] Run Phase 2's test class; confirm all three parametrizations now pass.
- [ ] Verify the list-growth risk empirically: instrument a single live run to log
      `len(model_constraints.frame_constraints)` at the top of each `build_new_model_structure`
      call and confirm it does not grow monotonically across successive rebuilds (i.e. each
      rebuild gets fresh `model_constraints`). Record the observed numbers in the phase notes. If
      it does grow, stop and scope the append to a per-rebuild copy before proceeding.
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q` and compare against
      Phase 1's `01_pre-fix-iterate.txt`.
- [ ] Confirm each of the three theories still finds more than one model on its Phase 1
      representative example (a collapse to a single model is a blocking finding, not expected
      fallout — see Risks).

**Timing**: 1 hour

**Depends on**: 1, 2

**Verification Tier**: full

**Scope Hypothesis**: Exactly one production file changed (`iterate/models.py`), with 8 added
append calls plus one rewritten comment block. Confirm with
`git diff --stat code/src/model_checker/iterate/models.py` (one file) and
`git diff code/src/model_checker/iterate/models.py | grep -c '^+.*frame_constraints.append'`
returning 8 — a different count means a pin site was missed or double-added and must be
reconciled against the eight `temp_solver.add` sites before the phase closes.

**Files to modify**:
- `code/src/model_checker/iterate/models.py` - append each pin literal into
  `model_constraints.frame_constraints`; rewrite the stale consequence comment

**Verification**:
- All three parametrizations of `TestGenericPinningReachesRebuiltSolve` pass.
- `iterate/` suite is no worse than the Phase 1 baseline.
- `frame_constraints` length does not accumulate across rebuilds within one run (recorded
  measurement, not assumption).
- Each affected theory still yields more than one model on its baseline example.

---

### Phase 4: Pin-Presence Assertion Mirroring Bimodal Coverage [NOT STARTED]

**Goal**: Add the symmetric structural assertion that pins land in `frame_constraints`, not only
in `temp_solver` — the shape bimodal's `TestPinTheorySpecificValues` already establishes.

**Tasks**:
- [ ] In `iterate/tests/integration/test_models.py`, add a test asserting that after a
      `build_new_model_structure` call for a theory with no `_pin_theory_specific_values`
      override, `model_constraints.frame_constraints` contains the generic pin literals (length
      grew by the expected pin count, and a representative `is_world`/`verify` literal is present).
- [ ] Mirror the assertion style of `theory_lib/bimodal/tests/integration/test_iterate.py`'s
      `TestPinTheorySpecificValues` (line ~297) rather than inventing a new shape.
- [ ] Add a companion assertion that bimodal is unaffected: its rebuild path still routes through
      its override and the generic loop adds no generic pins for it (its `hasattr` guards do not
      fire for `is_world`).
- [ ] Run the full `iterate/tests/` suite plus bimodal's `tests/integration/test_iterate.py`.

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: One test file changed, two tests added. Confirm with
`git diff --stat code/src/model_checker/iterate/tests/integration/test_models.py`.

**Files to modify**:
- `code/src/model_checker/iterate/tests/integration/test_models.py` - add pin-presence and
  bimodal-unaffected assertions

**Verification**:
- Both new tests pass.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q`
  is unchanged from the Phase 1 baseline.

---

### Phase 5: Correct the Bimodal Docstring Wording [COMPLETED]

**Goal**: Remove the present-tense claim that `all_constraints` "permanently misses" the
certificate encoding, which stopped being true when `all_constraints` became a read-only computed
property — without touching the method's still-necessary defensive design.

**Tasks**:
- [x] In `code/src/model_checker/theory_lib/bimodal/iterate.py`, edit
      `_ensure_frame_constraints_in_search_solver`'s docstring (the paragraph around lines
      145-157 describing the `all_constraints` snapshot). Replace the present-tense "permanently
      misses" claim with an accurate statement: `all_constraints` was formerly an eager
      construction-time snapshot that missed post-construction mutations; it is now a read-only
      computed property recomputed from the same four live lists on every access.
- [x] Add one sentence clarifying that reading the four component lists directly remains required
      for the separate, still-live `stored_solver`/`_setup_solver` reassignment bug documented
      earlier in the same docstring — not as a workaround for the now-resolved `all_constraints`
      staleness.
- [x] Leave the method body, the four-list read, and every other docstring section unchanged.
- [x] No task-number reference in the docstring text.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: One file, docstring-only. Confirm with
`git diff code/src/model_checker/theory_lib/bimodal/iterate.py` — every changed hunk must lie
inside the triple-quoted docstring; a hunk touching executable lines means the edit overran and
must be reverted and redone.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - docstring wording correction only

**Verification**:
- Diff read-through confirms every changed hunk is inside the docstring.
- `PYTHONPATH=code/src python -c "import model_checker.theory_lib.bimodal.iterate"` succeeds
  (the docstring is not malformed).

---

### Phase 6: Full Four-Theory Gate and Fallout Review [NOT STARTED]

**Goal**: Run the complete gate, and adjudicate every changed iteration result against the Phase 1
baseline individually.

**Tasks**:
- [ ] From `code/`, run the parallel pass:
      `PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
- [ ] Run the serial `xdist_serial` second pass with no `-n` flag.
- [ ] Run each theory directory explicitly:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -v`
- [ ] Diff each run against Phase 1's baseline capture. For every test that changed state,
      classify it as (a) pre-existing failure, (b) expected pinning-result change, or (c) genuine
      regression, and record the classification with evidence.
- [ ] Re-run the Phase 1 representative `./dev_cli.py` examples and diff the printed model 2+
      output against `baselines/01_pre-fix-{theory}-iteration.txt`. Inspect each diff; confirm the
      new model 2+ is self-consistent with the candidate the search intended.
- [ ] Run one example with `print_constraints` enabled and confirm the rendering is well-formed
      with the pin literals now listed under the frame-constraints heading (the accepted
      display-only side effect).
- [ ] Do not edit any `expectation` value, loosen any regression assertion, or add a skip to make
      the gate green. A category (c) regression blocks the phase.

**Timing**: 1.5 hours

**Depends on**: 3, 4, 5

**Verification Tier**: full

**Scope Hypothesis**: The set of tests whose state changes is expected to be small and confined
to `iterate > 1` example tests in logos/exclusion/imposition. Confirm by diffing the Phase 6 run
against the Phase 1 baseline and enumerating every changed node ID — a change outside those three
theories' iteration paths is unexpected and must be explained before the phase closes.

**Files to modify**:
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/01_post-fix-*.txt` - post-fix gate
  captures (new files)
- Any test or example file found to need a genuine correction during fallout review (not
  anticipated; if one is needed, record the reasoning)

**Verification**:
- Parallel pass, serial `xdist_serial` pass, and the four theory directories are all green, or
  every remaining failure is classified as a pre-existing failure identified in Phase 1's summary.
- Every changed iteration result is enumerated with an explicit classification and evidence.
- `print_constraints` output renders correctly.

---

## Testing & Validation

- [ ] `TestGenericPinningReachesRebuiltSolve` fails for all three theories before Phase 3 and
      passes after (RED then GREEN, per the project's mandatory TDD requirement).
- [ ] The pin-presence test and the bimodal-unaffected test pass.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q` is green.
- [ ] Four-theory directory run is green.
- [ ] `code/` parallel pass with the standard marker exclusions is green.
- [ ] `xdist_serial` serial pass is green.
- [ ] Bimodal's `tests/integration/test_iterate.py` is byte-for-byte unchanged in outcome from
      the Phase 1 baseline (this fix must not touch bimodal's behavior).
- [ ] No `expectation` value was changed and no skip was added to obtain a green gate.

## Artifacts & Outputs

- `code/src/model_checker/iterate/models.py` — generic pins appended into
  `model_constraints.frame_constraints`; stale consequence comment rewritten.
- `code/src/model_checker/iterate/tests/integration/test_models.py` — real-example helper,
  `TestGenericPinningReachesRebuiltSolve` (3 parametrizations), pin-presence test,
  bimodal-unaffected test.
- `code/src/model_checker/theory_lib/bimodal/iterate.py` — docstring wording correction.
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/` — pre- and post-fix gate and
  iteration captures plus the classification summary.
- `specs/210_fix_generic_iterator_pinning_unreached/summaries/01_*-summary.md` — implementation
  summary (written at implement postflight).

## Rollback/Contingency

Each phase commits independently, so rollback is a targeted `git revert` of the offending commit
rather than a working-tree discard:

- **Phase 5 (docstring)** is fully independent — revert it alone with no effect on anything else.
- **Phase 3 (the fix)** is a single-file change; reverting its commit restores the pre-fix
  behavior exactly. Phases 2 and 4's tests will then fail again, which is the correct signal, not
  a second defect to chase.
- If a genuine regression is found in Phase 6 that cannot be resolved within this task, revert
  Phase 3's commit, leave Phases 2/4's tests in place marked `xfail` with the specific blocking
  reason cited, and record the finding — the failing test is more valuable retained than deleted.
- If an intentional whole-tree rollback is ever required while the tree is dirty, take a snapshot
  first per `context/contracts/recovery.md`'s rollback rung (including its out-of-scope override
  flag for the deliberate whole-tree case) before running any destructive git command.
