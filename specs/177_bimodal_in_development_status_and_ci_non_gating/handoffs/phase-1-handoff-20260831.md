# Phase 1 Handoff: Make the gating-invocation count executable and correct "six" to "seven"

**Status**: COMPLETED

## What was done

- Added `EXPECTED_GATING_MARKER_INVOCATIONS = 7` module constant and
  `test_total_gating_marker_expression_count_is_seven` to
  `code/tests/ci/test_unstable_deselection_wiring.py`, deriving the count from `_SCANNED_FILES`
  by counting invocations whose `-m` expression is present.
- Added `_SEVEN_COUNT_ANCHORS` (7 tuples) and a parametrized
  `test_seven_count_anchor_is_corrected` asserting each documentation/docstring anchor states
  "seven" and no longer states the stale "six".
- Recorded RED evidence: docs-consistency test failed 7/7 before the prose fix; the count test
  failed (`assert 7 == 6`) when the constant was temporarily set to 6, then restored to 7.
- Corrected "six" -> "seven" at all seven anchors: `TESTING_GUIDE.md` (lines ~972, 1388, 1394,
  and the "six gating `-m` expressions" line near 1487), `bimodal/tests/conftest.py` line 25,
  `bimodal/tests/README.md` line 10, `test_development_marker_application.py` line 13.
- Added the manual-driver sentence to TESTING_GUIDE 8.14's "Where the deselection is wired"
  paragraph noting two of the seven invocations live in `oracle/run-oracle-suite.sh`, a manual
  driver invoked by no workflow.
- Confirmed all edits lie strictly inside comment/docstring/markdown regions.
- Did NOT modify `test_scanned_invocation_counts_match_known_shape` or any existing assertion.

## Verification

- `PYTHONPATH=code/src pytest code/tests/ci/ -v` — 100 passed.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q`
  — 313 tests collected (unchanged from before the conftest.py comment edit).
- Repo-wide grep confirms no surviving stale "six" gating-invocation claim outside the test
  file's own `must_not_contain` guard strings (deliberate) and one unrelated "six-way CPU
  contention" mention in oracle test files.

## Deviations from plan

None — followed the plan's Phase 1 tasks exactly.

## Next phase

Phase 4 (`run_tests.py --markers` passthrough) and Phase 5 (README.md/tests.yml prose
corrections) are both unblocked (wave 1, no dependency on Phase 1 beyond shared-file
serialization already resolved). Phase 2 depends on Phase 1 and is unblocked next.
