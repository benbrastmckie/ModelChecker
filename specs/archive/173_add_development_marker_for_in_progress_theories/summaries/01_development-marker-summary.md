# Implementation Summary: Add `development` pytest marker for in-progress theories

- **Task**: 173 - Add development marker for in progress theories
- **Status**: [COMPLETED] — all six phases verified green, including a clean full-suite gating
  run obtained after task 153 landed (see "Plan Deviations" below for the resolved account)
- **Started**: 2026-08-31T00:00:00Z
- **Completed**: 2026-08-31T23:59:00Z
- **Effort**: ~6.5 hours estimated; delivered at estimate across two dispatches (Phase 6 resumed
  once its blocking precondition cleared)
- **Dependencies**: Task 158, Task 172, Task 175 (all landed; this plan built directly on their
  four `-m` drivers and `unstable_watch_classify.py` baseline)
- **Artifacts**: plans/01_development-marker.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Introduced a `development` pytest marker for theories still under active construction (bimodal
today), deselected from every gating pytest invocation, with a non-gating `DEV_STATUS`
observability path in the unstable-watch classifier and a new TESTING_GUIDE.md section (8.14)
documenting the whole category. No `theory_lib` test was marked as part of this task's own
edits — the category was created without being applied, per the plan's explicit non-goal. (By
the time this task's Phase 6 closed, a downstream task, 153, had legitimately begun using the
category by marking bimodal's whole test tree — see "Plan Deviations" below.)

## What Changed

- `code/pyproject.toml`: registered the `development` marker, including the deliberate
  non-mirroring note (unlike `xdist_serial`, it is not mirrored into `oracle/conftest.py`).
- Six gating pytest invocations across four drivers now carry `and not development`:
  `.github/workflows/tests.yml` (parallel + serial), `.github/workflows/differential-tests.yml`
  (first invocation), `flake.nix`'s `checks.default` (parallel + serial), and
  `oracle/run-oracle-suite.sh` (both passes, defensive since the marker is unregistered there).
- `code/tests/ci/test_unstable_deselection_wiring.py`: extended in place — renamed
  `TestGatingInvocationsDeselectUnstable` to `TestGatingInvocationsDeselectQuarantineMarkers`,
  added a second assertion (`not development`) alongside the existing `not unstable` check on
  the same parsed marker expression, and updated the module/class docstrings. Bite confirmed by
  a temporary-revert check (documented, not committed).
- `.github/scripts/unstable_watch_classify.py`: added a third, optional `dev_junit_path` input
  to `run()` (default `/tmp/watch-development.xml`, inert until a deferred workflow step exists);
  every collected dev testcase is recorded with `classification == "DEV_STATUS"` and its true
  outcome, never feeding `any_new` or `any_failure`, and excluded from the `currently_unstable`
  fragment-matching loop so it can never corrupt an `unstable` test's promotion streak.
  Generalized `fetch_past_classifications` with a defaulted `field` selector (default
  `"classification"` unchanged; `field="outcome"` feeds the new pass-rate path) and added
  `compute_dev_pass_rate`, wired into a new `## Development Watch` step-summary section
  (informational per-node-id pass rate, deliberately not using `READY TO PROMOTE` wording or the
  20-run framing).
- `code/tests/ci/test_unstable_watch_classifier.py`: 13 new tests across four groups
  (`TestDevStatusClassification`, `TestFetchPastClassificationsFieldSelector`,
  `TestComputeDevPassRate`, `TestDevelopmentWatchSummary`), all pre-existing tests unchanged.
- `code/docs/core/TESTING_GUIDE.md`: new section 8.14 (meaning, per-test granularity, entry
  criteria, what it must not hide, wiring, observability including the deferred producing step,
  exit path, four-marker decision table, "currently marked: none"); one appended sentence in
  8.9's wiring paragraph pointing to 8.14.

## Decisions

- **`file_scope` widened by exactly one file** (`.github/scripts/unstable_watch_classify.py`),
  per the orchestrator's Scope Decision 1: the declared `file_scope` already contained the test
  file that loads this module by absolute path and names it as its subject; excluding the module
  itself was a task-creation oversight, not a deliberate boundary.
- **`.github/workflows/unstable-watch.yml` NOT edited** (Scope Decision 2): the observability
  design's third JUnit input is inert (`parse_junit` returns nothing for a missing file) until a
  deferred workflow step adds the producing step. See "Follow-ups" below.
- **`.github/workflows/release.yml` NOT edited** (Scope Decision 3): its `test-and-release`
  no-op comment and `build` job's defensive filter would benefit from naming `development` too,
  and the task text asks for it by name, but it is out of `file_scope` and belongs to the tasks
  already owning that file. Flagged, deliberately not done here.
- **`oracle/conftest.py` NOT edited, deliberately, by this task** (Scope Decision 4): as landed
  by this task's own Phases 1-5, the marker was not mirrored there, so no oracle-tree test could
  register or claim `development`. (Factual update at Phase 6 closure: a later, separate,
  non-task-173 commit — `65f9de0e "update testing"`, outside this task's `file_scope` and not
  authored by this dispatch — has since mirrored the marker into `oracle/conftest.py` with an
  explicit exemption for the differential/soundness core classes. That change is not evaluated or
  endorsed here; it is noted only so this summary stays accurate against the current repo state.)
- Per-test marker granularity (mirroring `bimodal`'s `UNSTABLE_EXAMPLES` set-membership idiom),
  not a theory-level `pytestmark` blanket — documented explicitly in 8.14 with the reasoning
  (a blanket would hide a real regression in an already-passing test).
- `fetch_past_classifications` was generalized with a defaulted `field` selector rather than
  duplicated for the pass-rate path, per the delegation instruction; its default behavior is
  unit-tested explicitly to confirm it is unchanged.
- "A failing development test must not zero an unstable test's streak via `any_failure`" is an
  explicit named test (`test_failing_dev_test_does_not_feed_any_failure_via_legacy_streak`),
  plus a second, stronger test
  (`test_dev_nodeid_overlapping_unstable_fragment_does_not_corrupt_streak_matching`) covering the
  fragment-matching-loop exclusion specifically.

## Plan Deviations

- **Phase 6, first dispatch: closed `[PARTIAL]`.** `cd code && PYTHONPATH=src pytest tests/ci/ -v`
  (83 tests) and `pytest --collect-only -m development -q` (0 collected) both verified green as
  planned. Collection-level equivalence of the new `-m` filter was verified two ways: identical
  `--collect-only -q` counts (2392/2527 both with and without `and not development`) AND a full
  sorted diff of both `--collect-only -q` outputs was byte-identical/empty (3055 lines each).
  However, an actual execution run of the full gating parallel-pass command was attempted twice
  under a 580s `timeout` wrapper and both times exited **124**, confounded by task 153's then
  in-flight, uncommitted changes to `bimodal/semantic/core.py` and `test_frame_constraints.py` in
  the same shared working tree. An xdist worker crash excerpt (`[gw0] node down: Not properly
  terminated`) was captured and offered as evidence for task 174
  (`root_cause_xdist_worker_crash`), not investigated here.
- **Phase 6, second dispatch (this one): resolved, closed `[COMPLETED]`.** Task 153 had landed
  (confirmed via `git log`) and the working tree was clean of its prior uncommitted bimodal
  changes. Re-running the same full gating parallel-pass command produced a genuinely clean pass:
  `2132 passed, 1 skipped, 2 warnings in 82.21s (0:01:22)` — no timeout, no failure, no xdist
  worker crash. `code/tests/ci/ -q` was re-confirmed green (136 passed).
- **Downstream change discovered during closure, not made by this task**: between the two
  dispatches, task 153 phase 8 (`74e6eb08`) applied `development` to the whole bimodal test tree
  via a new `bimodal/tests/conftest.py` collection hook — the marker's designed exit path, per
  this plan's own Scope Decisions and TESTING_GUIDE.md 8.14 — and a separate, later,
  non-task-numbered commit (`65f9de0e "update testing"`) mirrored the same blanket into
  `oracle/conftest.py` with an exemption for the differential/soundness core. Neither edit was
  made by this task or is in its `file_scope`. Consequence: the plan's "identical collected
  count with/without `and not development`" verification bullet, true at the moment this task's
  own Phases 1-5 landed, is no longer literally true — the gating expression now legitimately
  deselects 447 tests (vs. 135 without `and not development`), all attributable to bimodal, not
  to any defect in this task's six `-m` edits. `pytest --collect-only -m development -q` now
  collects 313 tests (all bimodal) rather than 0. Both plan-level `Testing & Validation` items
  affected are annotated as `DEVIATION (downstream, not this task's edit)` in place, with the
  full account in the plan's Phase 6 Findings.
- **xdist worker crash**: not reproduced in the clean re-run. The original excerpt remains
  recorded as task 174 evidence; no further action taken here, per the delegation's explicit
  instruction.
- **CI run 32996446859's two failures**: not marked `development`, not touched, and not
  encountered in the clean re-run.

## Impacts

- No production behavior change from this task's own six `-m` edits, the marker registration, or
  the classifier's `DEV_STATUS` path in isolation — all verified inert/no-op at the time this
  task's own Phases 1-5 landed (exact, empty collection diff).
- `bimodal` (and any future in-progress theory) now has a documented, tested, structurally-gated
  mechanism to mark known-incomplete tests without turning CI red or losing observability — and
  that mechanism is now in active use: task 153 has applied it to bimodal's whole test tree, and
  a separate later commit extended the mirroring into `oracle/conftest.py`. The full code-tree
  gating command now runs clean (2132 passed, 1 skipped) with bimodal correctly excluded.
- An xdist worker crash was observed once during the first dispatch's confounded full-suite
  attempt and is recorded as evidence for task 174; it did not recur in the clean re-run and is
  not attributable to this task.

## Follow-ups

- **Deferred `/spawn` candidate** (recorded in the plan, not implemented here): add a third
  watch step to `.github/workflows/unstable-watch.yml` mirroring `watch_code`, selecting
  `-m development` and writing `--junitxml=/tmp/watch-development.xml` with the same `exit 0`
  tolerance for pytest exit codes 0 and 5; then extend
  `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`'s
  `-m unstable` count assertion to also confirm the new `-m development` step.
- **Flagged, deliberately unmade**: `.github/workflows/release.yml`'s `test-and-release` no-op
  comment and the `build` job's defensive filter should eventually name `development` alongside
  `unstable`; out of `file_scope` for this task.
- **Task 174 evidence**: the xdist worker-crash excerpt recorded in the plan's Phase 6 Findings
  section and in "Plan Deviations" above should be folded into task 174's own investigation.

## References

- `specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md`
- `specs/173_add_development_marker_for_in_progress_theories/reports/01_development-marker-design.md`
- `code/pyproject.toml`
- `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`, `flake.nix`,
  `oracle/run-oracle-suite.sh`
- `code/tests/ci/test_unstable_deselection_wiring.py`
- `.github/scripts/unstable_watch_classify.py`
- `code/tests/ci/test_unstable_watch_classifier.py`
- `code/docs/core/TESTING_GUIDE.md`
