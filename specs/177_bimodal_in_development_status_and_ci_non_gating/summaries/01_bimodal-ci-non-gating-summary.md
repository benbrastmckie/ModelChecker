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
- Real (non-collect-only) execution of both passes, run after the `subprocess.run`-corruption
  bug below was fixed:
  - Parallel pass (`-n 4 -q --timeout=300 --timeout-method=thread`): 2116 passed, 1 skipped,
    exit 0.
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
- A full, non-collect-only `./run_tests.py bimodal --markers development` end-to-end run was
  also launched as a redundant confirmatory spot-check, but was terminated by the host before
  completion (>50 minutes elapsed under the same host contention documented below). Since
  `development` is a theory-wide blanket covering bimodal's entire tree today (TESTING_GUIDE.md
  8.14's "Currently marked"), this invocation selects the identical node-id set the bare
  `./run_tests.py bimodal` run above already executed to completion with recorded results — no
  additional evidence would have been produced beyond what is already recorded, so the
  incomplete run is not treated as a gap in this proof.

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
- `PYTHONPATH=code/src pytest code/tests/ci/ -v` — a real, self-caused bug was found and fixed
  during this verification, not a host flake. `test_unstable_watch_classifier.py::
  TestRealPytestJunitRoundTrip`'s two tests failed consistently (not intermittently) whenever
  run as part of the full `code/tests/ci/` battery, while passing in isolation. Root cause:
  `code/tests/ci/test_run_tests_markers.py`'s subprocess-mocking tests originally patched
  `run_tests_mod.subprocess.run` by hand (`run_tests_mod.subprocess.run = <stub>`, restored in a
  `finally` block via `run_tests_mod.subprocess.run = __import__("subprocess").run`). Because
  `run_tests.py` does a plain `import subprocess`, `run_tests_mod.subprocess` IS the same global
  `subprocess` module every other test module imports, and the "restore" line re-read `.run`
  *after* it had already been overwritten -- so it captured the stub, not the original, and left
  the real global `subprocess.run` permanently patched to the last-used stub for the rest of the
  pytest session. `test_run_tests_markers.py` sorts alphabetically before
  `test_unstable_watch_classifier.py`, so by the time the classifier's real-subprocess
  round-trip tests ran, `subprocess.run` had been silently replaced. Fixed by switching every
  patch site to pytest's `monkeypatch.setattr(run_tests_mod.subprocess, "run", ...)` fixture,
  which guarantees teardown regardless of test outcome. After the fix,
  `PYTHONPATH=code/src pytest code/tests/ci/ -q` passed 120/120 across three consecutive full
  runs.

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
