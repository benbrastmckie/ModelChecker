# Implementation Summary: Bimodal In-Development Status and CI Non-Gating

- **Plan**: `specs/177_bimodal_in_development_status_and_ci_non_gating/plans/01_bimodal-in-development-ci-non-gating.md`
- **Status**: COMPLETED (all six phases)

## What Changed

**Phase 1 — Executable gating-invocation count, six -> seven.** Added
`EXPECTED_GATING_MARKER_INVOCATIONS = 7` and a real assertion deriving the count from the four
scanned CI drivers, plus a parametrized docs-consistency test asserting each of seven
documentation/docstring anchors states "seven" and no longer states the stale "six". Corrected
all seven anchors: `code/docs/core/TESTING_GUIDE.md` (four sites plus a new sentence naming
`oracle/run-oracle-suite.sh` as a manual, non-workflow driver),
`code/src/model_checker/theory_lib/bimodal/tests/conftest.py`,
`code/src/model_checker/theory_lib/bimodal/tests/README.md`, and
`code/tests/ci/test_development_marker_application.py`.

**Phase 2 — Retained oracle soundness gate (GAP 1), pinned and documented.** Added
`TestOracleSoundnessGateStaysUnconditionallyGating` (3 assertions) to
`code/tests/ci/test_unstable_deselection_wiring.py`: no `continue-on-error` on the "Run CI gate
tests explicitly" step, `TestCIGate` still node-id-selected, and the `paths:` trigger unnarrowed
on both `push` and `pull_request`. Added a comment block above that step in
`.github/workflows/differential-tests.yml` and a paragraph in TESTING_GUIDE.md section 8.14
distinguishing this soundness check from the `development` marker's completeness quarantine.

**Phase 3 — `-m development` producing step wired (GAP 3).** Added a `watch_development` step
to `.github/workflows/unstable-watch.yml`, mirroring `watch_code`'s shape exactly: selects
`-m development`, writes `/tmp/watch-development.xml`, `continue-on-error: true`, tolerates
exit codes 0 and 5. No changes to `.github/scripts/unstable_watch_classify.py` — its `main()`
already resolves the unspecified `dev_junit_path` argument to `DEFAULT_DEV_JUNIT_PATH`.

**Phase 4 — `run_tests.py --markers`/`-m` passthrough (GAP 2).** Created
`code/tests/ci/test_run_tests_markers.py` (new module) and wired `--markers`/`-m` through
`create_argument_parser()` and all five command-building sites in `code/run_tests.py`
(`ExampleTestRunner._run_logos_example_tests`, `_run_standard_example_tests`,
`UnitTestRunner._run_logos_unit_tests`, `_run_standard_unit_tests`,
`PackageTestRunner._build_pytest_command`). `code/pyproject.toml` untouched. Also added
`_normalize_markers_deselection_exit_code` (see Plan Deviations below).

**Phase 5 — False claims corrected.** `.github/workflows/README.md`: replaced the stale
single-clause `-m "not packaging"` / `-n 6` claims (four passages) with the real five-clause
expression and `-n 4`, and added a pointer to `test_worker_count_matches`. `.github/workflows/tests.yml`:
reworded the self-contradicting "this job deliberately does NOT exclude bimodal" comment to
state accurately that bimodal's tests still execute and report but are gating-excluded via the
`development` marker.

**Phase 6 — Documentation and criteria proofs.** Documented the two canonical `run_tests.py`
invocations in `code/src/model_checker/theory_lib/bimodal/tests/README.md` and
`code/docs/core/TESTING_GUIDE.md` section 8.14. Proofs below.

## Task 173 Pointer Note

`specs/173_add_development_marker_for_in_progress_theories/plans/01_development-marker.md` was
deliberately NOT edited, per this plan's explicit instruction and task 153's precedent (do not
rewrite another task's historical plan record). That file's Phase 6 criteria at lines 501, 529,
and 588 each state "`pytest --collect-only -m development -q` collects zero tests" as the
graduation/completion signal. That criterion is now stale: it predates bimodal's declared
theory-wide `development` blanket (TESTING_GUIDE.md section 8.14's "Currently marked"
paragraph, already the correct, current source of truth), under which
`PYTHONPATH=src pytest -m development -q --collect-only` collects 313 tests today, not zero.

**If task 173 is ever resumed to close its own Phase 6**, that dispatch must either strike this
criterion or re-scope it to "zero tests outside the authorized bimodal blanket" (which is exactly
what `code/tests/ci/test_development_marker_application.py`'s containment property already
enforces) before checking it off as-is.

## Criteria Proofs

**Criterion (a) — scoped to completeness checks: a bimodal-only change cannot turn any required
CI check red, except the one named, tested exception.**

- `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" --collect-only -q`
  → 2117/2564 collected, **0 bimodal node ids** (`grep -c theory_lib/bimodal` on the collected
  list returns 0).
- `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable and not development" --collect-only -q`
  → 9/2564 collected, **0 bimodal node ids**.
- Real (non-collect-only) execution of both passes, run after the above:
  - Parallel pass (`-n 4 -q --timeout=300 --timeout-method=thread`): 2114 passed, 1 skipped, 2
    failed — the same two CPU-contention-affected classifier tests noted below (not bimodal, not
    a regression; both pass in isolation).
  - Serial pass: 9 passed, 0 failed, exit 0.
- The one deliberate, named, tested exception: `.github/workflows/differential-tests.yml`'s "Run
  CI gate tests explicitly" step, which still runs unconditionally on a bimodal-only push/PR
  because `TestCIGate::test_oracle_baseline_agreement` is a soundness check (fails only on a real
  semantic disagreement, never a timeout), pinned by Phase 2's three assertions.
- `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/logos src/model_checker/theory_lib/exclusion src/model_checker/theory_lib/imposition -q`
  → 699 passed, exit 0 — no other theory weakened by this work.

**Criterion (b) — bimodal stays runnable with failures visible (non-gating, not hidden).**

- `cd code && ./run_tests.py bimodal` (bare, no `--markers`) → runs the full suite (267 example
  + 267+46 unit collected across the two passes) and reports a real, non-zero exit: 2 known
  example failures (`BM_CM_1`, `BM_CM_4`) and 3 known unit failures
  (`TestBoundVarCounterOrderIndependence::test_bm_cm_4_independent_of_prior_counter_state`,
  parametrized ×3) — 5 known failures total, exactly matching the plan's risk-table statement.
  `Test Summary` prints `FAILED` for both theory-test rows; overall runner exit is non-zero. This
  is intended, pre-existing behavior, not a regression, and is exactly what "runnable with
  failures visible" means.
- `cd code && ./run_tests.py bimodal --markers "not development"` → both passes report
  "313 deselected" / 0 selected, and the runner's overall summary is `SUCCESS: All tests passed!`
  (exit 0) — the exit-code-5-normalization addition (Plan Deviations) makes this genuinely exit
  0 rather than pytest's raw exit 5.
- `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m development --collect-only -q`
  → 313/2564 collected (non-zero, matching the research report's figure).
- `cd code && ./run_tests.py logos --unit` → unchanged behavior, no `-m` token emitted, exit 0
  (positive control: the new flag does not alter behavior for a target that never uses it).

**Criterion (c) — the GAP 1 decision is enforced by a test, not merely documented.**

Phase 2's three assertions in `TestOracleSoundnessGateStaysUnconditionallyGating`
(`code/tests/ci/test_unstable_deselection_wiring.py`), each independently RED-verified via a
targeted mutation of `.github/workflows/differential-tests.yml` (add `continue-on-error: true`;
remove the `::TestCIGate` node id; delete one `paths:` entry), then reverted (confirmed
byte-identical to the pre-mutation original via `diff`).

## Containment and Regression Checks

- All three containment tests still exist and were extended, not narrowed:
  `test_development_marker_application.py`, `test_unstable_deselection_wiring.py`,
  `test_workflow_parity.py`.
- `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`'s
  `assert len(matches) == 2` is byte-for-byte unchanged (confirmed via `git show` against the
  pre-Phase-1 commit and the current file).
- `git diff` confirms `code/pyproject.toml`, `.github/scripts/unstable_watch_classify.py`, and
  `specs/173_add_development_marker_for_in_progress_theories/` are all unmodified.
- `PYTHONPATH=code/src pytest code/tests/ci/ -v` — 118-120 passed across repeated runs. Two
  tests in `test_unstable_watch_classifier.py::TestRealPytestJunitRoundTrip` intermittently
  failed only while long-running, CPU-heavy background verification runs (`./run_tests.py
  bimodal`, `./run_tests.py bimodal --markers development`, both spanning the full ~2500-test
  bimodal suite) were active on the same host under a measured host load average of 8-14 and
  7.7GB swap in use; both pass cleanly in isolation (confirmed repeatedly) and this module's
  full suite passes cleanly (39/39) once contention subsides. This is the documented
  CPU-contention flake class (TESTING_GUIDE.md section 8.13), not a regression introduced by
  this work.

## Plan Deviations

- **Added `_normalize_markers_deselection_exit_code` to `code/run_tests.py`** (Phase 4), with
  new TDD coverage (`TestExitCodeFiveNormalizedOnlyWhenMarkersSupplied`, 5 tests). Not an
  explicit task in the plan's Phase 4 task list, but necessary to satisfy the plan's own stated
  Phase 4 verification bullet and the top-level Testing & Validation checklist item
  ("`./run_tests.py bimodal --markers "not development"` — zero bimodal tests, exit 0"), which
  would otherwise be false: pytest exits 5 ("no tests ran"), not 0, when an `-m` expression
  collects but fully deselects a suite. The normalization converts a markers-caused exit 5 to 0
  and leaves an unmarked exit 5 untouched (so a genuine "nothing collected" problem is still
  surfaced). No Non-Goal is affected by this addition.
- All other phases followed the plan's task lists exactly, with no other additions, omissions,
  or altered scope.
