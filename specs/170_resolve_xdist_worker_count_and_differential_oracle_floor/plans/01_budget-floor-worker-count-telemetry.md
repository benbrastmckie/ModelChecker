# Implementation Plan: Task #170

- **Task**: 170 - Resolve xdist worker count and differential oracle floor
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/reports/01_ci-budget-questions-a-c-d-and-b-confirmation.md`
- **Artifacts**: plans/01_budget-floor-worker-count-telemetry.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The task carries four items. Research settled B outright, measured C conclusively, measured A
strongly but partially, and left D's root cause open with a concrete instrumentation
recommendation. This plan lands C (extend the example solve-budget floor to `bimodal`,
`exclusion`, `imposition`), runs the bounded full-selection `-n 6` vs `-n 4` screen for A and
then decides A on the screen's outcome under an explicitly stated evidence limitation, adds the
peak-RSS-per-worker telemetry for D without attempting a speculative fix, and closes with
documentation and a final gate. B is closed and is protected by a Non-Goal below.

### Research Integration

- **(B) closed, no work.** Research verified in-tree that
  `test_known_conclusive_population_self_consistent` carries `@pytest.mark.unstable`,
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` is 40000, `MIN_CONCLUSIVE_GATING_FORMULAS` is 100, and
  `unstable-watch.yml`'s classifier was extracted to the unit-tested
  `.github/scripts/unstable_watch_classify.py`. No residue. No phase in this plan touches any of
  it; see Non-Goals.
- **(C) measured, conclusive.** All 22 flagged `max_time: 2`/`3` examples measured 0.01s-0.37s
  isolated and up to 0.80s under 6-worker/4-core contention: 5x-300x headroom, categorically
  unlike the ~3x margin that produced the `CL_TH_12`/`CL_TH_13` failures. Phase 1 lands the
  `_COVERED` extension the research recommends. **See the scope correction under Phase 1 — the
  "22" figure is incomplete.**
- **(A) measured, partial.** `-n 4` vs `-n 6` under `taskset -c 0,1,2,3` produced byte-identical
  outcomes across 554 tests (bimodal 301, exclusion+imposition 253), covering every
  countermodel-expected example in those three theories. The full 2321-test gating selection
  (logos, `code/tests/`) was not covered. Phases 1-2 execute the report's bounded design to
  close that gap; Phase 3 decides on the result.
- **(D) root cause open.** The named test is a confirmed innocent bystander (the replacement
  worker re-ran it in 0.23s). Both incidents show a silent gap (123s, ~17min) before the worker
  was detected dead — a process-death signature, not a hang-inside-one-test signature. No memory
  telemetry exists in CI to separate the three live hypotheses. Phase 4 adds that telemetry and
  nothing else. **This plan does not attempt a fix for D and does not claim a root cause.**

### Prior Plan Reference

No prior plan for task 170. Effort calibration and process constraints are drawn instead from
the sibling tasks in this batch (159/160/167), whose handoffs establish the long-running-command
discipline encoded in the Process Constraints section below.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not supplied as `roadmap_path` in this dispatch's delegation
context, so it was not loaded and no roadmap phases are included. No roadmap items are claimed
or annotated by this plan.

## Goals & Non-Goals

**Goals**:

- Extend `code/tests/ci/test_example_budget_floor.py`'s `_COVERED` to `bimodal/examples.py`,
  `exclusion/examples.py`, and `imposition/examples.py` at the unchanged `_MIN_MAX_TIME = 10`,
  raising every below-floor budget in those files, and record the measurement basis in both the
  guard's docstring and `TESTING_GUIDE.md` section 8.13.
- Run the bounded full-gating-selection `-n 6` vs `-n 4` screen, twice per worker count, under
  `taskset -c 0,1,2,3`, and diff sorted node-id outcome lists.
- Decide the `-n` value on that screen's outcome, changing `.github/workflows/tests.yml` and
  `flake.nix` together (parity-guarded) if and only if the screen is clean — and recording the
  known limitation of the local instrument either way.
- Add peak-RSS-per-worker telemetry to the Python 3.12 `general-tests` job, as an importable,
  unit-tested module, so a future task can decide D on data instead of log archaeology.

**Non-Goals**:

- **Re-tuning `GATING_RECHECK_SOLVE_TIMEOUT_MS` (40000) or `MIN_CONCLUSIVE_GATING_FORMULAS`
  (100).** Item B is closed. Any edit to either constant is a regression against task 160's
  landed disposition and against those constants' own comment blocks. No phase in this plan
  touches `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`.
- Lowering `_MIN_MAX_TIME` below 10, or lowering any existing above-floor budget. The floor only
  raises; `BM_CM_1` (60s) and `BM_CM_4` (120s) and every other above-floor value are untouched.
- Attempting a fix, a workaround, or a local reproduction for D. Root cause is open, and this
  plan says so.
- Adding `max_rlimit` plumbing to `ModelDefaults` / `utils.testing.run_test()`. Research names
  this as the natural stronger instrument but places it out of scope; TESTING_GUIDE 8.13 records
  the deliberate decision not to adopt `max_rlimit` for this failure class.
- Triggering a CI run to gather evidence. Consistent with task 160's posture, evidence is
  gathered locally or from already-archived runs.
- Creating a pull request or pushing to remote (`.claude/rules/pr-prohibition.md`).

## Process Constraints (binding on every phase)

These cost four dispatches in this batch. They are execution rules, not advice.

1. **The Bash tool auto-moves a foreground command to the background once it exceeds its wait
   window. `timeout` does NOT prevent this.** Any command expected to exceed ~2 minutes must be
   launched with `run_in_background: true` (or treated as auto-backgrounded) and then polled with
   `BashOutput` **in the same turn**. Never end a turn waiting for a completion notification.
2. **Known costs.** `oracle/bimodal_logic/tests/` non-slow selection is ~46 minutes — no phase
   here requires it. The full 2321-test gating selection is the expensive item in this plan; the
   research measured 554 tests in under ~4 minutes across both `-n` values under `taskset -c0-3`,
   which extrapolates to roughly 8-12 minutes per single full-selection draw.
3. **Every phase below carries a wall-clock ceiling. A timeout is a recorded data point, not a
   blocker.** On hitting a ceiling: record what completed, narrow the selection and label the
   narrowing honestly in the phase's verification notes, and continue. Do not silently retry.
4. **Mandatory TDD** per `code/docs/core/TESTING_GUIDE.md`: the failing check comes first. Each
   phase below states its RED step explicitly.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The `_COVERED` extension flags far more examples than the researched 22 (planning-time AST scan found 57 below-floor dicts; 35 sit at `max_time: 5` and were never measured) | M | H (already observed at planning time) | Phase 1 re-runs the scan first and treats the count as a hypothesis; raising a budget is monotone-safe at runtime, and Phase 1 additionally measures the previously-unmeasured `max_time: 5` cohort so the widening is evidence-backed rather than assumed |
| A clean local `-n 4` vs `-n 6` diff is weak evidence of CI safety — TESTING_GUIDE 8.13 already records that `taskset -c 0-3` at `-n 6` passes cleanly locally (2292 passed) while the same selection failed on CI | H | H (established, not speculative) | Phase 2 is framed as a **falsification screen**, not a safety proof: a non-empty diff is decisive against `-n 4`; an empty diff only clears the screen. Phase 3's decision rule and the residual-risk record both state this in the artifact and in the workflow comment |
| `-n 4` lengthens the `general-tests` job and could approach `timeout-minutes: 20` | M | M | Phase 3 measures the `-n 4` full-selection wall clock from Phase 2's own draws and explicitly decides whether `timeout-minutes` must rise alongside; it is a named phase task, not an afterthought |
| Changing `-n` in only one of `tests.yml` / `flake.nix` | H | L | `code/tests/ci/test_workflow_parity.py::test_worker_count_matches` enforces it; Phase 3 deliberately demonstrates the guard going RED on a one-sided edit before completing the two-sided one |
| Losing the documented `-n 6`-over-`auto` rationale while rewording the comment | M | M | The rationale is about *fixed `-n` vs `auto`* and survives any fixed value. Phase 3 requires the reworded comment to retain the `BM_CM_1` contention-flake reference verbatim and adds the new evidence beneath it rather than replacing it |
| D telemetry adds CI complexity for an intermittent issue | L | M | Scoped to the Python 3.12 matrix leg only, `continue-on-error`/non-gating, and documented as removable once the hypothesis resolves |
| Phase 2's four full-selection draws exhaust the dispatch budget | M | M | Ceiling of 60 minutes total for Phase 2 with a defined degraded outcome: fewer draws completed is a recorded, honestly-labelled partial result that feeds Phase 3's decision rule as "inconclusive" |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 1, 3, 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential by
construction; the sequencing rationale is stated per phase rather than left implicit.

**Why C before A.** C is the conclusively-evidenced item and its change is monotone-safe, so it
should land first and unconditionally. Landing it first also means Phase 1's own full-gate run
doubles as the first `-n 6` draw of Phase 2's screen, so the screen measures the tree that will
actually ship rather than a superseded one — no duplicated cost, no confounded comparison.

**Why A before D, and why D is still done if A lands.** Research recommendation 4 sequences A
first because fewer workers means more memory headroom per worker, so `-n 4` may retire D as a
side effect. This plan follows that order but does **not** treat "D stopped recurring" as
equivalent to "D was understood": if `-n 4` ships and the crash disappears, the memory-ceiling
hypothesis is *consistent with* that outcome but not confirmed by it, and the ABI hypothesis is
not excluded. Phase 4's telemetry records the worker count alongside peak RSS precisely so the
data remains diagnostic under whichever `-n` value ships. Phase 4 is sequenced after Phase 3
rather than in parallel because both edit `.github/workflows/tests.yml`.

---

### Phase 1: Extend the example solve-budget floor to bimodal, exclusion, imposition [COMPLETED]

**Goal**: `code/tests/ci/test_example_budget_floor.py` covers the three non-logos example files
at the unchanged 10s floor, every below-floor budget in them is raised to at least 10, and the
guard's docstring records the measurement that justifies the widening.

**Tasks**:

- [x] Re-run the below-floor AST scan over the three files and record the actual counts. Do not
      carry the research report's "22" forward as fact — see the Scope Hypothesis below.
      **Confirmed**: re-scan found exactly 57 (bimodal 21, exclusion 26, imposition 10), matching
      the Scope Hypothesis, not the research report's 22.
- [x] For any below-floor budget **not** covered by the research report's measurements (the
      `max_time: 5` cohort), measure isolated solve times for those examples before raising them,
      so the widening is measurement-backed exactly as the guard's own docstring demands. Record
      the measured range in the commit and in the docstring.
      **Measured**: all 35 `max_time: 5` examples (11 bimodal, 24 exclusion), isolated,
      single-process: 0.012s-1.549s.
- [x] **RED**: add the three `examples.py` paths to `_COVERED` and run
      `pytest code/tests/ci/test_example_budget_floor.py -v`. Confirm it fails, and confirm the
      violation count matches the scan. A passing test here means the scan or the edit is wrong.
      **Confirmed RED**: 21 + 26 + 10 = 57 violations, exactly matching the scan.
- [x] **GREEN**: raise every flagged `max_time` in the three files to 10. Raise only below-floor
      values — leave `BM_CM_1` (60), `BM_CM_4` (120), and every other at-or-above-floor value
      byte-identical. Re-run the guard; confirm green.
      **Confirmed GREEN**: 8/8 tests pass; `git diff` audit confirms every removed value was <10
      and every added value is exactly 10, with 57 changes total across the three files.
- [x] Rewrite the guard docstring's final scope paragraph (currently "Scope is the four
      `logos/subtheories/*/examples.py` files ... do not simply add them to `_COVERED` without
      re-measuring"). It must now record: the measurement that was performed, the actual number
      of budgets raised, and an explicit note that the floor does not touch and does not conflict
      with bimodal's `BM_CM_1`/`BM_CM_4` per-example recalibration record.
- [x] Note in the docstring or commit that `MD_TH_2` is separately excluded from
      `test_bimodal.py`'s collected suite via `KNOWN_TIMEOUT_EXAMPLES` for reasons unrelated to
      its budget, so its raised budget is not exercised in CI today.
      **Extended**: docstring also notes `TN_CM_1`/`MF_MODAL_FUTURE_TH` (same exclusion
      mechanism) and `BM_TH_5` (never added to `unit_tests` at all) share this property.

**Timing**: 1.25 hours (of which ~15 minutes is the backgrounded full-gate run).

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The task description and the research report both assert 22 below-floor
example settings dicts across the three files (20 at `max_time: 2`, 2 at `max_time: 3`). A
planning-time AST scan of the current tree found **57** dicts below the 10s floor — bimodal 21,
exclusion 26, imposition 10 — because 35 of them sit at `max_time: 5`, a value neither the task
description nor the research report enumerated or measured. The 22 figure counts only the `2`/`3`
cohort and is therefore an undercount of what extending `_COVERED` will actually flag. **Confirm
at implementation time** by re-running the AST scan (`ast.walk` for `Dict` nodes with a
`'max_time'` key, exactly as `_budgets()` does) over the three files on the working tree, and
reconcile against the RED-step violation count before raising anything. Raising the `max_time: 5`
cohort is monotone-safe at runtime — a larger budget can only turn an inconclusive result into a
conclusive one, never the reverse — but shipping it unmeasured would repeat the pattern-matching
the guard's own docstring forbids, which is why measuring that cohort is a task above rather than
an optional extra.

**Commit-mode justification**: the declared batch is
`code/tests/ci/test_example_budget_floor.py` plus the three `examples.py` files. Extending
`_COVERED` without raising the budgets is red; raising the budgets without extending `_COVERED`
is green but unguarded. The intermediate per-file states are expected red and must not be
committed. This is a pre-declared batch, not a retroactively widened one.

**Files to modify**:

- `code/tests/ci/test_example_budget_floor.py` — add three paths to `_COVERED`; rewrite the
  closing scope paragraph of the module docstring to record the measurement basis and the
  recalibration-record distinction. `_MIN_MAX_TIME` stays 10.
- `code/src/model_checker/theory_lib/bimodal/examples.py` — raise below-floor `max_time` values
  to 10; leave 60/120 and all other at-or-above-floor values untouched.
- `code/src/model_checker/theory_lib/exclusion/examples.py` — same.
- `code/src/model_checker/theory_lib/imposition/examples.py` — same.

**Verification**:

- `pytest code/tests/ci/ -q` — all CI guards green, including the widened floor and its own
  liveness test `test_floor_guard_detects_a_below_floor_budget`.
- `git diff` review confirming no `max_time` value was *lowered* anywhere and that
  `BM_CM_1`/`BM_CM_4` are unchanged.
- Full gate (this is the `full` tier's obligation, and it is also Phase 2's `-n 6` draw 1):
  from `code/`, with `PYTHONPATH=src`, run
  `taskset -c 0,1,2,3 pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 6 -q --timeout=300 --timeout-method=thread -rA`
  backgrounded, polled with `BashOutput` in the same turn. Save the sorted `PASSED`/`FAILED`/
  `ERROR` node-id list to the task directory as the `-n 6` draw-1 baseline.
- **Ceiling**: 20 minutes for the full-gate run. On timeout, record the partial result, narrow to
  `theory_lib/{bimodal,exclusion,imposition}` plus `code/tests/ci/`, label the narrowing in the
  phase notes, and carry the timeout forward as an input to Phase 2's ceiling planning.

---

### Phase 2: Bounded full-selection `-n 6` vs `-n 4` falsification screen [COMPLETED]

**Goal**: Produce sorted per-test outcome lists for the full gating selection at `-n 6` and
`-n 4`, two draws each, under `taskset -c 0,1,2,3`, and diff them — yielding either a decisive
finding against `-n 4` or a cleared screen.

**Outcome**: **CLEAN**. All four draws passed 2323/2323 (1 skip, 0 failed, 0 errors) and all four
pairwise diffs (cross-`-n` x2, within-`-n` x2) were empty. See
`specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/evidence/phase2-screen-results.md`
for the full table, diffs, wall clocks, and the required evidence-limitation statement.

**Tasks**:

- [x] Reuse Phase 1's `-n 6` draw-1 list. Run the remaining three draws — `-n 4` draw 1, `-n 6`
      draw 2, `-n 4` draw 2 — each with the identical command shape, changing only the `-n` value,
      each backgrounded and polled with `BashOutput` in the same turn.
      **Deviation (process, not scope)**: backgrounded via explicit shell `&`/`disown` and polled
      with `kill -0`/`tail` loops rather than the harness's `BashOutput` tool, because the
      Bash-tool poll commands themselves were repeatedly killed at their own 2-minute wall-clock
      limit (not auto-backgrounded) before the underlying pytest process finished; the disowned
      process survived each such kill and was recovered on the next poll. All four draws still
      ran sequentially, each to completion, with identical command shape.
- [x] Normalize each run's output to a sorted list of `PASSED`/`FAILED`/`ERROR` node-id lines and
      store all four under the task directory (not under `code/`), so the evidence outlives the
      dispatch. Stored as `evidence/{n6,n4}-draw{1,2}-outcomes.txt`.
- [x] Diff `-n 6` draw 1 vs `-n 4` draw 1, and `-n 6` draw 2 vs `-n 4` draw 2. Also diff the two
      same-`-n` draws against each other — a non-empty *within*-`-n` diff means the local
      instrument is itself noisy and the cross-`-n` diff cannot be read as a worker-count effect,
      which is a distinct and important outcome.
      **All four diffs empty** — see `evidence/phase2-screen-results.md`.
- [x] Record explicitly, in the phase notes, which of the three outcomes obtained: **clean**
      (both cross-`-n` diffs empty and both within-`-n` diffs empty), **dirty** (any cross-`-n`
      diff non-empty), or **inconclusive** (fewer than the planned draws completed, or a
      within-`-n` diff is non-empty).
      **CLEAN**, recorded in `evidence/phase2-screen-results.md`.
- [x] Record each draw's wall clock. Phase 3 needs the `-n 4` timing to decide the
      `timeout-minutes` question.
      **Recorded**: `-n 6` 240.63s/280.14s, `-n 4` 307.19s/238.35s — no systematic `-n 4`
      slowdown observed on this host; see the wall-clock note in `evidence/phase2-screen-results.md`
      for why this host's seconds should not be extrapolated directly to CI's `timeout-minutes`.

**Timing**: 1.25 hours (three backgrounded draws plus diffing and recording).

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: The gating selection is asserted to collect 2321 of 2443 tests, and a
single draw is estimated at 8-12 minutes by extrapolation from the research's 554-test
measurement. Both are hypotheses. **Confirm at implementation time** by reading the collected
count off draw 1's own output and the elapsed time off the first completed draw, then re-check
the Phase 2 ceiling against the observed per-draw cost before launching the remaining draws.

**Files to modify**: none. This phase writes only measurement artifacts under
`specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/`.

**Verification**:

- Four outcome lists exist under the task directory, each with a recorded collected-test count
  and wall clock.
- The three diffs are recorded verbatim (including empty ones, as explicit `diff exit 0` notes).
- The obtained outcome is named as exactly one of clean / dirty / inconclusive.
- **Ceiling**: 60 minutes for the whole phase. On timeout, the phase closes with the draws that
  completed, the outcome is recorded as **inconclusive**, and Phase 3 takes its inconclusive
  branch. A timeout here is a data point about measurement cost, not a failure.

**Evidence limitation to record in the phase notes** (this is required output, not commentary):
`TESTING_GUIDE.md` section 8.13 already establishes that restricting the development host with
`taskset -c 0-3` and running the full gating selection at `-n 6` **passes cleanly (2292 passed)**
while the same selection failed on real CI — core-count restriction does not reproduce a per-core
clock/IPC gap or a virtualized neighbour, and the oracle suite reached the same conclusion
independently. This screen therefore cannot prove `-n 4` safe on CI. It can only falsify it. Say
so in the artifact.

---

### Phase 3: Decide and apply (or decline) the `-n 6` -> `-n 4` change [COMPLETED]

**Goal**: The `-n` value is settled by an explicit, written decision rule applied to Phase 2's
recorded outcome, with both files changed together and the documented rationale preserved — or
with `-n 6` retained and the residual risk recorded.

**Branch taken**: **Clean** (Phase 2's recorded outcome). Changed `-n 6` to `-n 4` in both
`.github/workflows/tests.yml` and `flake.nix`. `timeout-minutes: 20` left unchanged, with the
comparison and rationale recorded in a comment (no systematic slowdown observed; see below).

**Decision rule** (apply exactly; do not improvise):

- **Clean** -> change to `-n 4` in both files. The change ships on a cleared falsification screen
  plus the research's 554-test result, **not** on a safety proof, and the workflow comment and
  the summary must both say that.
- **Dirty** -> do **not** change. `-n 6` stands. Record the specific flipping node ids as the
  actionable finding; this is the strongest possible result from this instrument and should be
  written up as such.
- **Inconclusive** -> do **not** change. `-n 6` stands. Close this phase
  `[COMPLETED WITH EXCLUSIONS]` enumerating the draws that did not complete, and record what a
  future dispatch would need to finish the screen.

**Tasks** (the change tasks apply only on the **clean** branch):

- [x] Read Phase 2's recorded outcome and state the branch taken before editing anything.
      **CLEAN** (see above).
- [x] Compare the `-n 4` draw wall clock against the `-n 6` draw wall clock and against
      `general-tests`' `timeout-minutes: 20`. If the projected CI-side `-n 4` duration leaves less
      than a comfortable margin, raise `timeout-minutes` in the same edit and justify the new
      value in a comment. Do not ship a `-n` reduction that silently narrows the backstop margin.
      **Decision: left at 20, not raised.** `-n 6` averaged 260.4s, `-n 4` averaged 272.8s (~5%
      difference, inside the ~70s draw-to-draw spread; the single fastest draw overall was an
      `-n 4` draw) — no systematic slowdown to project forward. Rationale recorded in a comment
      directly above `timeout-minutes: 20`.
- [x] **RED**: change `-n 6` to `-n 4` in `.github/workflows/tests.yml` **only**, then run
      `pytest code/tests/ci/test_workflow_parity.py -v`. Confirm `test_worker_count_matches`
      fails. This demonstrates the parity guard is live before relying on it.
      **Confirmed RED**: `AssertionError: -n worker count diverged ... ('4') and ... ('6')`.
- [x] **GREEN**: make the matching change in `flake.nix`. Re-run the parity module; confirm all
      of it green. **Confirmed GREEN**: 5/5 passed.
- [x] Reword the inline rationale comment in `tests.yml`. **Retain verbatim** the existing
      `-n 6`-over-`auto` reasoning and its `BM_CM_1` contention-flake reference — that reasoning
      is about fixed `-n` versus `auto` and is preserved under any fixed value. Append the new
      evidence beneath it: the measured screen, the number of tests compared, and the explicit
      statement that the local instrument is known not to reproduce the CI contention class.
      Update `flake.nix`'s cross-reference comment so it still points at `tests.yml`'s comment as
      the full rationale.
      **Done.** `BM_CM_1-example_case7` citation and the never-`-n auto` argument survive verbatim
      in both files (only the literal `6`->`4` digit updated where the sentence describes this
      job's own current value); new paragraph appended in `tests.yml` with the screen's four-draw
      result, the corroborating 554-test prior measurement, and the explicit "can only falsify,
      cannot prove CI-safe" statement (citing `TESTING_GUIDE.md` 8.13). `flake.nix`'s comment
      updated to point at `tests.yml`'s step comment as the full rationale.
- [x] Record a named revert trigger in the comment: the first CI run in which a
      countermodel-expected example stops finding a countermodel, or a new contention-shaped
      failure appears, restores `-n 6` in both files.
      **Done**, in `tests.yml`'s new paragraph, naming `test_workflow_parity.py`'s
      `test_worker_count_matches` as the two-sided-revert guard.

**Timing**: 0.75 hours.

**Depends on**: 2

**Verification Tier**: full

**Files to modify** (clean branch only):

- `.github/workflows/tests.yml` — `-n` value in the parallel gating pass; the inline rationale
  comment; possibly `timeout-minutes`.
- `flake.nix` — `-n` value in `checks.default`'s `checkPhase` parallel pass; cross-reference
  comment.

**Verification**:

- `pytest code/tests/ci/ -q` green, with `test_workflow_parity.py` specifically confirmed.
- `git diff` shows the `-n` value changed in exactly two places and that the `BM_CM_1`/`auto`
  rationale text survives in `tests.yml`.
- `nix flake check --dry-run` or at minimum a `nix flake show` parse to confirm `flake.nix` is
  still syntactically valid after the edit. Do **not** run a full `nix flake check` — it rebuilds
  the closure and runs the whole suite again; the parity guard plus Phase 2's measurement already
  cover what a full check would tell us here.
- **Ceiling**: 15 minutes. On timeout of any verification command, record it and narrow to
  `pytest code/tests/ci/ -q` alone, labelled.

---

### Phase 4: Peak-RSS-per-worker telemetry for the Python 3.12 job [COMPLETED]

**Goal**: The Python 3.12 `general-tests` leg records peak RSS per xdist worker alongside the
worker count, as an importable and unit-tested module, so a future task can decide D's memory
hypothesis on data. This phase adds instrumentation only — no fix, no claimed root cause.

**Tasks**:

- [x] **RED**: write `code/tests/ci/test_worker_rss_sampler.py` first, against the module's
      intended interface, using synthetic `/proc/<pid>/status`-shaped fixtures written to
      `tmp_path` rather than live processes, so the tests are hermetic and run on any host.
      Confirm it fails on the missing module. Mirror the existing
      `test_unstable_watch_classifier.py` + `.github/scripts/unstable_watch_classify.py`
      structure — that pairing is the in-tree precedent for an importable, unit-tested CI helper
      and it should be followed rather than reinvented.
      **Confirmed RED**: `FileNotFoundError` naming the missing script path, at collection time.
- [x] **GREEN**: implement the sampler as `.github/scripts/worker_rss_sample.py` — a small
      polling loop that discovers the pytest worker processes, samples `VmRSS` on an interval,
      tracks a per-worker peak, and emits a compact summary (per-worker peak, aggregate peak,
      worker count, sample count, interval). Prefer reading `/proc/<pid>/status` directly with a
      `psutil` path only if `psutil` genuinely buys something; a `/proc`-only implementation
      avoids adding a CI dependency at all, and the choice must be stated in the module docstring
      either way. If `psutil` is used, add it to the Python 3.12 leg's `pip install` line only.
      **Implemented `/proc`-only** (choice stated in the module docstring); no new CI dependency.
      20/20 unit tests green; live smoke-tested against a real `pytest -n 2` process (nonzero
      per-worker RSS discovered correctly, e.g. 55424/55208 KB).
- [x] Wire it into `.github/workflows/tests.yml` gated to the 3.12 matrix leg
      (`if: matrix.python-version == '3.12'`), running alongside the gating pass and printing its
      summary in a dedicated step. The step must be non-gating — a sampler failure must never
      turn a green suite red.
      **Deviation (documented, not silent)**: the sampler runs inline within the existing "Run
      general test suite" step (bash-conditional on `${{ matrix.python-version }}`), not as a
      separate GH Actions step, because true "alongside" execution requires the sampler and
      pytest to share one shell/process tree — a separate step cannot observe a process
      backgrounded by an earlier step without either not waiting for it (which would silently
      stop that step from reflecting pytest's own pass/fail) or moving the pass/fail check into
      the telemetry step (which would make the "non-gating" telemetry step gating in practice).
      The parallel-pass `pytest ...` invocation is backgrounded unconditionally (not only under
      3.12) specifically so the file keeps exactly **one** literal copy of that line —
      duplicating it per branch was tried first and broke
      `test_workflow_parity.py::test_parallel_pass_marker_expression_matches` /
      `test_worker_count_matches` ("expected exactly one parallel (`-n`) pass, found 2"), exactly
      the class of regression this phase's own Verification bullet warns is "a real finding, not
      a test to adjust." Confirmed non-gating and gating-preserving by two smoke tests: a passing
      `pytest -n 2` run's exit code 0 propagates through `wait`, and a deliberately failing run's
      exit code 1 also propagates through `wait` unchanged by the sampler's `|| true`.
- [x] Record the effective `-n` worker count in the sampler's own output, so the data stays
      diagnostic regardless of which value Phase 3 shipped. This is the mechanism by which the
      memory hypothesis can be confirmed or refuted even if `-n 4` makes the crash stop recurring.
      **Done**: `--workers 4` passed explicitly (not inferred from live process count, which is
      transiently unstable during worker replacement); recorded verbatim in the summary's
      `workers` field.
- [x] Document in the workflow comment: what this is for, that D's root cause is **open**, the
      three live hypotheses in one line each, and that this instrumentation is **removable** once
      the hypothesis resolves.
      **Done**, in the new comment block above the (now-conditionally-sampled) parallel pass.

**Timing**: 1.5 hours.

**Depends on**: 3

**Verification Tier**: interface

**Scope Hypothesis**: The two crash incidents are asserted to be memory-related (research's
favored but unconfirmed hypothesis 1), and a 16GB runner ceiling is assumed. Neither is
established. **Confirm at implementation time only** that the sampler's output would in fact
distinguish the hypotheses — i.e. that it records absolute peak RSS, not a ratio, and records it
per-worker and in aggregate — since a reading that cannot be compared against a ceiling is not
evidence. Do not encode the 16GB figure as a threshold or an assertion anywhere in the sampler.

**Files to modify**:

- `.github/scripts/worker_rss_sample.py` — new; the importable sampler.
- `code/tests/ci/test_worker_rss_sampler.py` — new; hermetic unit tests over synthetic fixtures.
- `.github/workflows/tests.yml` — new 3.12-gated, non-gating telemetry step; possibly the 3.12
  leg's dependency install line.

**Verification**:

- `pytest code/tests/ci/test_worker_rss_sampler.py -v` green.
- `pytest code/tests/ci/ -q` green — in particular `test_workflow_parity.py` must still pass,
  since a new step in `tests.yml` must not perturb the two `pytest ...` invocation lines the
  parity regex extracts. If it does perturb them, that is a real finding, not a test to adjust.
- A local smoke run of the sampler against a short backgrounded `pytest -n 2` invocation,
  confirming it emits a plausible non-zero per-worker peak.
- YAML validity of `tests.yml` (parse it, e.g. via `python -c "import yaml"` if available, or a
  targeted structural read if not — note that PyYAML is deliberately absent from both CI
  toolchains, so a parse check is a local-only convenience).
- **Ceiling**: 10 minutes for the smoke run. On timeout, record and fall back to asserting the
  sampler's behaviour through its unit tests alone, labelled.

---

### Phase 5: Documentation, final gate, and honest close-out [COMPLETED]

**Goal**: `TESTING_GUIDE.md` reflects what actually landed, the full gate set runs, and the
task's written record states plainly which items are closed, which shipped on partial evidence,
and which remain open.

**Tasks**:

- [x] Rewrite section 8.13's closing paragraph ("Coverage is deliberately partial. `bimodal`,
      `exclusion`, and `imposition` still carry 20 settings dicts at `max_time: 2` and 2 at `3`
      ...") to record the widened coverage, the actual number of budgets raised, the measurement
      that backed it, and the preserved distinction from bimodal's per-example recalibration
      record. Do not delete the "Raise the budget; never lower the floor" discipline paragraph.
      **Done**; discipline paragraph confirmed still present (grep-verified).
- [x] If Phase 3 took the clean branch, add a short note in 8.13 or 8.11 recording the `-n` change,
      its evidence basis, and the named revert trigger. If Phase 3 declined, record the decline
      and why — a declined change with a written reason is a better artifact than silence.
      **Done** (clean branch): added as a second paragraph directly after the widened-coverage
      paragraph in 8.13.
- [x] Add a brief D subsection (or extend 8.11, which already narrates the worker-hang incident
      and the `--timeout-method=thread` guard) stating: root cause **not determined**; the named
      test is a confirmed innocent bystander; the three live hypotheses; the telemetry that now
      exists; and that this is deliberately left open for a future task rather than guessed at.
      **Done**: extended 8.11 with a new subsection before 8.12.
- [x] Run the full gate set and record exactly what ran versus what was narrowed.
      **Full, no narrowing needed** (see Verification below): `code/tests/ci/` 58/58,
      `code/tests/` 439 passed/1 skipped (0 failed), full gating selection at the settled `-n 4`
      two-pass split: parallel 2343 passed/1 skipped in 230.44s, serial 9 passed in 2.26s. All
      within their ceilings; no timeout hit.
- [x] Write the implementation summary under `summaries/01_...-summary.md`, and the orchestrator
      handoff, both stating item-by-item: B closed (untouched), C landed, A decided-with-branch,
      D instrumented-not-fixed.
      **Done.**

**Timing**: 0.75 hours.

**Depends on**: 1, 3, 4

**Verification Tier**: full

**Files to modify**:

- `code/docs/core/TESTING_GUIDE.md` — section 8.13 (and 8.11 if the D note lands there).
- `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/summaries/01_budget-floor-worker-count-telemetry-summary.md` — new.
- `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/plans/01_budget-floor-worker-count-telemetry.md` — phase markers.

**Verification**:

- `pytest code/tests/ci/ -q` green.
- `pytest code/tests/ -q` green.
- Full gating selection, backgrounded and polled in the same turn, at whatever `-n` value Phase 3
  settled on:
  `taskset -c 0,1,2,3 pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n {settled} -q --timeout=300 --timeout-method=thread`
- Hard-constraint gate: `git diff` over the whole task's changes confirms
  `MIN_CONCLUSIVE_GATING_FORMULAS`, `GATING_RECHECK_SOLVE_TIMEOUT_MS`, and `_MIN_MAX_TIME` are
  all unchanged, and that no `max_time` was lowered.
- **Ceiling**: 25 minutes for the full gating run. On timeout, record the partial result, narrow
  to `code/tests/` plus the three theory suites, and label the narrowing explicitly in the
  summary — the summary must name which gates ran in full and which were narrowed.

---

## Testing & Validation

- [ ] `pytest code/tests/ci/test_example_budget_floor.py -v` — green after Phase 1, with the
      guard's own liveness test passing.
- [ ] `pytest code/tests/ci/test_workflow_parity.py -v` — green after Phase 3, and demonstrated
      RED on the deliberate one-sided edit before that.
- [ ] `pytest code/tests/ci/test_worker_rss_sampler.py -v` — green after Phase 4.
- [ ] `pytest code/tests/ci/ -q` — green at the end of every phase that touches `.github/` or
      `code/tests/ci/`.
- [ ] Full gating selection green at the settled `-n` value.
- [ ] No `max_time` lowered anywhere; `BM_CM_1` (60) and `BM_CM_4` (120) byte-identical.
- [ ] `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` untouched (item B).

## Artifacts & Outputs

- `code/tests/ci/test_example_budget_floor.py` — widened `_COVERED`, rewritten scope docstring.
- `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition}/examples.py` — below-floor
  budgets raised to 10.
- Four full-selection outcome lists plus their diffs, stored under the task directory as the
  durable evidence for the A decision.
- `.github/workflows/tests.yml` and `flake.nix` — `-n` value and rationale comments (clean branch
  only), plus the 3.12-gated telemetry step.
- `.github/scripts/worker_rss_sample.py` and `code/tests/ci/test_worker_rss_sampler.py` — new.
- `code/docs/core/TESTING_GUIDE.md` — updated 8.13 (and 8.11 if the D note lands there).
- `specs/170_.../summaries/01_budget-floor-worker-count-telemetry-summary.md` — item-by-item
  disposition including the open D root cause.

## Rollback/Contingency

Each phase is an independent, separately-committed unit, so rollback is per-phase.

- **Phase 1**: revert the single atomic-batch commit. The floor extension and the budget raises
  go back together; nothing else depends on them.
- **Phase 3**: revert the two-file `-n` commit. The named revert trigger recorded in the workflow
  comment is the operational form of this — restoring `-n 6` in both files is a one-line change
  in each, and `test_workflow_parity.py` catches a one-sided revert.
- **Phase 4**: the telemetry step is non-gating and 3.12-scoped by construction; removing the
  workflow step plus the two new files fully retires it, which is exactly the removability the
  research recommends.
- **Phase 5**: documentation-only; revert the commit.

If a later CI run shows a contention-shaped regression after Phase 3's change, revert Phase 3
first and leave Phases 1, 4, and 5 in place — they are independent of the `-n` value, and Phase
4's telemetry becomes more valuable, not less, in that scenario.
