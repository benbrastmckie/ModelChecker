# Phase 3 Handoff: Wire the `-m development` producing step in unstable-watch.yml (GAP 3)

**Status**: COMPLETED

## What was done

- Added `test_watch_development_step_selects_development_and_writes_junit` to
  `TestGatingInvocationsDeselectQuarantineMarkers` in
  `code/tests/ci/test_unstable_deselection_wiring.py`, using a step-boundary split (not
  `_extract_pytest_invocations`) to isolate the new step and assert its shape: `-m development`,
  `--junitxml=/tmp/watch-development.xml`, `continue-on-error: true`, and the same
  `[ "$code" -eq 0 ] || [ "$code" -eq 5 ]` tolerance shape as `watch_code`/`watch_oracle`.
- Confirmed RED (0 matching steps found) before the workflow edit.
- Did NOT modify `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable`'s
  `assert len(matches) == 2` — confirmed still passing unchanged after the new step landed.
- Added the `watch_development` step to `.github/workflows/unstable-watch.yml`, positioned
  after `watch_oracle` and before the classify step, mirroring `watch_code`'s exact shape and
  indentation character-for-character.
- Made no changes to `.github/scripts/unstable_watch_classify.py` — confirmed by `git diff`
  (empty) and by reading `main()`, which already resolves the unspecified `dev_junit_path`
  argument to `DEFAULT_DEV_JUNIT_PATH = "/tmp/watch-development.xml"`.

## Verification

- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_deselection_wiring.py -v` — 20 passed,
  including the unchanged "exactly 2" test.
- `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m development --collect-only -q`
  — 313/2564 tests collected (2251 deselected), non-zero as expected.
- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_watch_classifier.py -q` — 39 passed
  (classifier untouched and its own contract still green).
- `git diff .github/scripts/unstable_watch_classify.py` — empty.

## Note on transient CI-suite flakes observed during this phase

Two unrelated tests in `test_unstable_watch_classifier.py`
(`TestRealPytestJunitRoundTrip::test_real_pytest_floor_failure_classifies_timing` and
`test_real_pytest_disagreement_failure_still_classifies_new`) intermittently failed when run as
part of the full `code/tests/ci/` battery while two long-running, CPU-heavy
`./run_tests.py bimodal` background verification runs (see Phase 4 handoff) were active on the
same host. Both pass cleanly in isolation and as part of the full suite once those background
runs finished. This is the documented CPU-contention flake class (TESTING_GUIDE.md section
8.13), not a regression from this phase's changes.

## Deviations from plan

None — followed Phase 3's task list exactly.

## Next phase

Phase 4 (`run_tests.py --markers` passthrough) is independent (wave 1) and was completed in
parallel with this phase in the same session. Phase 6 depends on Phases 1-5, all now complete
except Phase 5 (also complete) — Phase 6 is next.
