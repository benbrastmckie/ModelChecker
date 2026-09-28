# Implementation Summary: Fix logos subtheory-orchestration meta-test timeout

- **Task**: 208 - Fix logos subtheory meta test timeout
- **Status**: [COMPLETED]
- **Started**: 2026-09-27T17:25:00-07:00
- **Completed**: 2026-09-27T17:41:00-07:00
- **Effort**: ~2.25 hours (four phases, two full-gate runs)
- **Dependencies**: None
- **Artifacts**: plans/01_delete-duplicate-subtheory-meta-test.md, baselines/01_gate-before.md,
  baselines/01_gate-after.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`TestSubtheoryOrchestration::test_all_subtheory_tests_pass`, in
`code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`,
re-executed all four Logos subtheory test suites (418 Z3-backed tests) a second time via a serial
`subprocess.run` loop of nested `pytest` invocations. Those same 418 tests are already collected
and run directly by the same repository-wide gate (`code/pyproject.toml`'s `testpaths`), and the
meta-test carried no pytest markers, so CI's marker expression selected it unconditionally. Its
measured wall time (162.94s-320.90s across runs) straddled CI's 300s per-test timeout, producing
the intermittent pass/fail behavior the task described. Research established complete coverage
overlap and no unique isolation property, so this task deleted the meta-test outright rather than
optimizing or relocating it, bracketed by measured before/after full-gate runs under CI's exact
invocation shape.

## What Changed

- Deleted `test_all_subtheory_tests_pass` (the `subprocess.run` nested-pytest loop and its
  `pytest.fail` reporting) from `TestSubtheoryOrchestration` in
  `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`.
- Removed the now-unused `import subprocess` and `import sys` from the same file (`Path` stays;
  it is used by `test_type_hint_coverage`).
- Extended the module docstring recording that each subtheory's own `tests/` directory is already
  collected directly by the repository-wide pytest selection, so a nested-`pytest`
  re-execution meta-test would duplicate that coverage with worse diagnostics and is deliberately
  absent, citing durable anchors (`testpaths`, `test_no_operator_conflicts`,
  `test_dependency_resolution`) rather than an ephemeral task identifier.
- Captured measured before/after full-repository-gate numbers under CI's exact invocation shape
  in `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-before.md` and
  `01_gate-after.md`.
- Mechanically audited `bimodal`, `exclusion`, and `imposition` for the same nested-pytest
  pattern (Phase 2, read-only; no files changed by that phase).

## Decisions

- **Deletion, not optimization or relocation.** The task's own "What to decide" section required
  stating plainly if deletion is the honest outcome. Research found complete coverage overlap
  (the 418 subtheory tests are already directly collected) and that the one property re-execution
  could additionally guard — no cross-subtheory operator conflict — is already asserted
  in-process by `test_no_operator_conflicts` and `test_dependency_resolution`. Raising the
  timeout, marking `xdist_serial`/`slow`, and parallelising the subprocess loop were all
  explicitly rejected per the task's constraints and research Finding 6 (each either hides the
  cost, relocates rather than removes the timeout risk, or keeps the duplicate compute).
- **No replacement in-process test was written.** Writing one would duplicate
  `test_no_operator_conflicts`/`test_dependency_resolution`, which already assert the one
  non-duplicated property (cross-subtheory load compatibility).
- **Sibling-theory audit is report-only.** Mechanically confirmed (via grep, not inherited from
  research) that no sibling theory shares the nested-pytest-via-subprocess pattern; `bimodal`'s
  only `subprocess` user (`_lean_check.py`) invokes an external Lean tool (`lake exe
  check_certificate`), not pytest. No follow-up task was needed.
- **Node-count verification used a full node-id diff, not raw totals.** Two sibling tasks (197,
  207) were concurrently dispatched on this same shared tree per this cycle's disclosed territory.
  Sibling task 197 landed 5 new bimodal nodes between the before and after gate runs, so the raw
  collect-only totals moved +4 (3099→3103) rather than the naively-expected -1. A full sorted
  node-id diff isolated this task's own effect to exactly the expected -1 (only the meta-test
  node removed, nothing else); the sibling's +5 was verified attributable to sibling commit
  `ae3584d0` and is unrelated to this deletion. This is recorded explicitly in the plan's Testing
  & Validation checklist rather than silently rounded to "differs by exactly one."

## Plan Deviations

- Testing & Validation checklist item "`--collect-only -q` node count differs by exactly one
  between before and after" — the raw totals differed by +4 due to a concurrent sibling's
  commits landing mid-task (see "Decisions" above and `baselines/01_gate-after.md`'s "Node-count
  reconciliation" section for the full node-id diff). This task's own isolated contribution is
  exactly -1 as the plan intended; the deviation is in the raw-count arithmetic only, caused by
  disclosed concurrent-dispatch activity outside this task's control, not by any defect in the
  deletion itself. Annotated inline on the plan's Phase 4 tasks and Testing & Validation
  checklist rather than silently checked off.
- One before-run failure
  (`bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`)
  was observed in Phase 1's baseline, outside this task's edit target
  (`logos/tests/integration/test_subtheory_orchestration.py`). Per territory discipline it was
  recorded, not fixed, and attributed to transient contention from sibling task 197's in-flight
  edits at the time; it was absent (passing) in the after-run, consistent with that attribution.
  No plan step was skipped in response — this was anticipated by the plan's own risk table.

## Impacts

- The full-repository gate's parallel pass selects one fewer node from this task's own change,
  and no longer contains any item near the 300s timeout ceiling attributable to this meta-test
  (the deleted test's 162.94s-320.90s duration is gone from the durations report entirely).
- Parallel-pass wall time moved from 334.27s (before) to 251.45s (after), directionally
  consistent with removing a contention-prone serial item, though not offered as a precise
  isolated measurement given ambient host load and the sibling's concurrent commits between runs.
- No coverage was lost: the same 418 subtheory tests remain directly collected and run by the
  gate (spot-checked via `grep -c "logos/subtheories/"` on the after-run's collect-only output,
  returning 418), and the one property re-execution could have additionally guarded remains
  asserted by two still-passing in-process tests.
- `.github/workflows/tests.yml`, `code/pyproject.toml`, and no timeout value were touched, per
  the task's explicit constraint.

## Follow-ups

- None. The sibling-theory audit (Phase 2) found no analogous pattern elsewhere requiring a
  follow-up task.

## References

- `specs/208_fix_logos_subtheory_meta_test_timeout/reports/01_logos-subtheory-meta-test-timeout.md`
- `specs/208_fix_logos_subtheory_meta_test_timeout/plans/01_delete-duplicate-subtheory-meta-test.md`
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-before.md`
- `specs/208_fix_logos_subtheory_meta_test_timeout/baselines/01_gate-after.md`
- `code/src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py`
