# Implementation Summary: Fix unstable watch classifier laundering guard

- **Task**: 175 - Fix unstable watch classifier laundering guard
- **Status**: [COMPLETED]
- **Started**: 2026-08-31T10:03:00Z
- **Completed**: 2026-08-31T18:18:00Z
- **Effort**: ~4 hours (plan estimate: 8 hours)
- **Dependencies**: None
- **Artifacts**: plans/01_laundering-guard-fix.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`.github/scripts/unstable_watch_classify.py`'s gating-branch negative guard matched
`_assert_scan_report`'s own source listing (which pytest embeds verbatim in every `<failure>`
body), misclassifying every genuine gating-floor TIMING failure as NEW and failing the nightly
Unstable Watch job. All seven plan phases landed: the guard now discriminates the rendered
disagreement count from the source listing via an anchored regex, a real-pytest-subprocess
regression test proves both directions, the promotion streak is computed per node id from the
already-uploaded per-run JSONL artifacts, and two findings were recorded (the zero-contention
`xdist_serial` closure; two `TESTING_GUIDE.md` section 8.9 edits).

## What Changed

- `DISAGREEMENT_SIGNATURE` converted from a bare substring to a compiled anchored regex
  (`r"Self-comparison produced \d+ disagreements"`), requiring a literal rendered digit; the
  sibling `has_zero_disagreements` check was tightened alongside it to a `scan report:`-anchored,
  `re.DOTALL` pattern, validated against real captured text from a subprocess-pytest run (not a
  hand-typed string).
- Added `TestRealPytestJunitRoundTrip` to `code/tests/ci/test_unstable_watch_classifier.py`: a
  self-contained fixture (no `oracle`/`bimodal_logic`/Z3 import) reproducing
  `_assert_scan_report`'s exact two-assertion shape, driven through a real
  `subprocess.run([sys.executable, "-m", "pytest", ...])` invocation and the real
  `parse_junit`/`classify`. Confirmed the documented RED (`NEW` against the pre-fix guard) and the
  GREEN (`TIMING` after the fix) directly against real pytest output, plus a synthetic companion
  test pinning the source listing does not match the new pattern.
- Added `compute_per_test_promotion_streak` (a network-free pure function alongside the existing
  `compute_promotion_streak`) and `fetch_past_classifications` (bounded `gh run download` +
  JSONL parse per marked node id, each fetch independently wrapped in try/except). Wired both into
  `run()` via injectable `past_runs_fn`/`fetch_past_classifications_fn` parameters, so
  `READY TO PROMOTE` now names only the node id(s) that individually reached a 20-run streak, and
  the step summary carries a per-test breakdown table. The prior global per-run streak is
  retained and relabelled as a legacy, job-level upper bound; it no longer drives promotion.
- Recorded a new comment item at `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`'s
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` block: five consecutive `unstable-watch.yml` nightly runs under
  true zero-sibling-worker single-process execution reproduced the identical 96/103 shortfall,
  retiring the sibling-worker-contention sub-hypothesis while leaving the runner-hardware-capacity
  hypothesis open.
- Rewrote `TESTING_GUIDE.md` section 8.9's "Promotion-streak limitation" paragraph to describe the
  new per-node-id mechanism and its residual bounds, and added a caution to the
  "classifier lives in an importable module" paragraph for whoever adds a third `unstable`
  marking.

## Decisions

- Remedy (a) (anchor the classifier's own regex) chosen over remedy (b) (a machine-readable
  signature line from `_assert_scan_report`) on blast-radius grounds: that helper has at least
  five other call-site groups that pin its current message text. Recorded in-code at the
  `DISAGREEMENT_SIGNATURE` definition site.
- `has_zero_disagreements` tightened alongside the fix for consistency, not because it shared the
  exact defect (the report confirmed empirically it was never exposed to the source-listing echo).
- `FAILURE_SIGNATURE` surveyed and left unchanged: it is the last statement of a single-assertion
  test, so no sibling assertion can leak it into an unrelated failure. Recorded as a comment.
- Per-test promotion streak built as a real fix (report's recommended path) rather than the
  documented-deferral fallback, since the per-run artifact already carries everything needed and
  the marked set is only 2 node ids today.

## Plan Deviations

- None (implementation followed plan).

## Impacts

- The nightly Unstable Watch job will no longer misclassify a genuine gating-floor TIMING failure
  as NEW, so it will stop exiting 1 for the known, documented instability.
- BM_CM_1's promotion path is no longer coupled to the gating test's own (currently failing)
  history — its streak can now individually reach 20 and trigger `READY TO PROMOTE` regardless of
  the gating test's state.
- Hard-constraint audit (Phase 7): `MIN_CONCLUSIVE_GATING_FORMULAS` (100) and
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` (40000) are byte-identical to their pre-change values; the
  `unstable` marker is untouched; no `continue-on-error` was added to the classify step;
  `.github/workflows/unstable-watch.yml` is unmodified (confirmed via `git diff --stat`); the
  classifier imports stdlib only (`json`, `os`, `re`, `subprocess`, `sys`, `tempfile`, `time`,
  `xml.etree.ElementTree`); no existing test was deleted or weakened.
- **Final CI confirmation is user-only.** This implementation authored and committed the fix
  locally; it did not push, dispatch the workflow, or open a PR (per
  `.claude/rules/pr-prohibition.md`). The exit condition's last step — the fix actually preventing
  a `NEW` misclassification on the next real nightly run, or a user-initiated
  `workflow_dispatch` — lands only once the user pushes/dispatches.
- **Unrelated, pre-existing failures observed and explicitly out of scope**: the Phase 7 full
  `code/tests/` run (560 passed, 5 skipped, 3 failed) showed 3 failures in
  `code/tests/cli/test_flag_matrix.py` and `code/tests/cli/test_parse_file_flags.py`, caused by
  a concurrently-implemented task's own commit (`74f578f6`, "task 158 phase 1: non-interactive
  project generation") adding a `project_name` CLI flag not yet accounted for in the flag-matrix
  test. Confirmed via `git diff --stat` that none of this task's four `file_scope` files
  (`.github/scripts/unstable_watch_classify.py`, `code/tests/ci/test_unstable_watch_classifier.py`,
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`, `code/docs/core/TESTING_GUIDE.md`)
  were touched by that commit or vice versa. Not fixed here — outside this task's scope and
  ownership.

## Follow-ups

- User-only: push/dispatch to confirm the fix on real CI (next nightly run, or a manual
  `workflow_dispatch`).
- Not opened as a task here (out of scope for this task, flagged for the user/owning task): the 3
  pre-existing `code/tests/cli/` failures from task 158's `project_name` flag need their own fix.

## References

- `specs/175_fix_unstable_watch_classifier_laundering_guard/plans/01_laundering-guard-fix.md`
- `specs/175_fix_unstable_watch_classifier_laundering_guard/reports/01_laundering-guard-fix-design.md`
- `.github/scripts/unstable_watch_classify.py`
- `code/tests/ci/test_unstable_watch_classifier.py`
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `code/docs/core/TESTING_GUIDE.md`
