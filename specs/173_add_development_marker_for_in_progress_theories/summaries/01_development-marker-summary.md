# Implementation Summary: Add `development` pytest marker for in-progress theories

- **Task**: 173 - Add development marker for in progress theories
- **Status**: [IN PROGRESS] — Phases 1-5 complete and verified green; Phase 6 is `[PARTIAL]`
  (a clean, unconfounded full-suite gating run was not obtained — see "Plan Deviations" below)
- **Started**: 2026-08-31T00:00:00Z
- **Completed**: not yet — resumable at Phase 6 once the blocking condition below clears
- **Effort**: ~6.5 hours estimated; Phases 1-5 delivered at estimate, Phase 6 blocked
- **Dependencies**: Task 158, Task 172, Task 175 (all landed; this plan built directly on their
  four `-m` drivers and `unstable_watch_classify.py` baseline)
- **Artifacts**: plans/01_development-marker.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Introduced a `development` pytest marker for theories still under active construction (bimodal
today), deselected from every gating pytest invocation, with a non-gating `DEV_STATUS`
observability path in the unstable-watch classifier and a new TESTING_GUIDE.md section (8.14)
documenting the whole category. No `theory_lib` test was marked as part of this task — the
category is created without being applied, per the plan's explicit non-goal.

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
- **`oracle/conftest.py` NOT edited, deliberately** (Scope Decision 4): the marker is not
  mirrored there, so no oracle-tree test can register or claim `development`, keeping the
  differential/soundness harness categorically, unconditionally gating.
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

- **Phase 6 deviated: closed `[PARTIAL]`, not `[COMPLETED]`.** `cd code && PYTHONPATH=src pytest
  tests/ci/ -v` (83 tests) and `pytest --collect-only -m development -q` (0 collected) both
  verified green as planned. Collection-level equivalence of the new `-m` filter was verified
  two ways: identical `--collect-only -q` counts (2392/2527 both with and without
  `and not development`) AND a full sorted diff of both `--collect-only -q` outputs is
  byte-identical/empty (3055 lines each) — this is the definitive answer that the filter
  deselects nothing beyond the four pre-existing filters. However, the plan's second
  verification bullet — an actual execution run of the full gating parallel-pass command
  (`pytest tests/ src/model_checker -m "... and not development" -n 4 -q --timeout=300
  --timeout-method=thread`) — was attempted twice under a 580s `timeout` wrapper and both times
  exited **124** (killed at the bound), never producing a clean pass. The first attempt's tail
  showed, at ~93-96% collected: 4 `F`s and an xdist worker crash (`[gw0] node down: Not properly
  terminated`, `replacing crashed worker gw0`) — this excerpt is recorded verbatim as evidence
  for task 174 (`root_cause_xdist_worker_crash`, not_started), not investigated or fixed here. A
  targeted rerun scoped to the two bimodal files nearest the failure signal
  (`test_frame_constraints.py`, `test_frame_class_mapping.py`) was itself confounded: task 153
  is concurrently mid-flight on those exact two files plus uncommitted changes to
  `bimodal/semantic/core.py` in the same shared working tree (153 landed `b7bc19c3` "failing
  tests for Seriality and Interpolation (RED)" — four intentionally-red test classes — during
  this task's own Phase 6 window), so no clean attribution was possible from that run either. No
  failure attributable to this task's own scope (marker registration, the six `-m` edits, or the
  classifier) was observed, and the collection-equivalence result above makes one implausible —
  but an unconfounded, clean full-suite green run was not obtained in this dispatch.
  **Continuation condition**: re-run the full gating command once task 153 lands its in-flight
  `bimodal/semantic/core.py` work (or otherwise vacates the shared tree), and confirm the
  F's/crash resolve or are independently attributable to task 174.

## Impacts

- No production behavior changes from this task's own edits: zero tests carry `development`, so
  the six new `-m` filters are no-ops at the collection level (verified as an exact, empty diff —
  see "Plan Deviations" above), and the classifier's new dev-input path is inert until the
  deferred workflow step lands.
- `bimodal` (or any future in-progress theory) now has a documented, tested, structurally-gated
  mechanism to mark known-incomplete tests without turning CI red or losing observability.
- An xdist worker crash was observed during full-suite verification and is recorded as evidence
  for task 174; it is not attributable to this task (see "Plan Deviations").

## Follow-ups

- **Deferred `/spawn` candidate** (recorded in the plan, not implemented here): add a third
  watch step to `.github/workflows/unstable-watch.yml` mirroring `watch_code`, selecting
  `-m development` and writing `--junitxml=/tmp/watch-development.xml` with the same `exit 0`
  tolerance for pytest exit codes 0 and 5; then extend
  `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`'s
  `-m unstable` count assertion (currently 2) to also confirm the new `-m development` step.
- **Flagged, deliberately unmade**: `.github/workflows/release.yml`'s `test-and-release` no-op
  comment and the `build` job's defensive filter should eventually name `development` alongside
  `unstable`; out of `file_scope` for this task.
- **Deliberate, permanent**: `oracle/conftest.py` is never updated to mirror this marker — that
  is the intended, structural boundary keeping the oracle suite fully gating, not a gap to close.
- **Phase 6 resumption**: re-run the full gating parallel-pass command
  (`pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and
  not xdist_serial and not development" -n 4 -q --timeout=300 --timeout-method=thread`) once task
  153 has landed its in-flight `bimodal/semantic/core.py` work, to obtain the clean execution-level
  confirmation this dispatch could not get cleanly.
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
