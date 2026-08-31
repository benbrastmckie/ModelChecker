# Phase 2 Handoff: Record and enforce the retained oracle soundness gate (GAP 1)

**Status**: COMPLETED

## What was done

- Added `TestOracleSoundnessGateStaysUnconditionallyGating` (3 test methods) to
  `code/tests/ci/test_unstable_deselection_wiring.py`, with helper functions
  `_gate_step_block` and `_trigger_block` for regex-based extraction of the "Run CI gate tests
  explicitly" step and the `push`/`pull_request` trigger blocks:
  1. `test_gate_step_has_no_continue_on_error`
  2. `test_gate_step_still_selects_test_ci_gate` (positive complement of the existing
     `test_differential_tests_yml_gate_step_has_no_marker_expression`, which only asserts
     `TestGatingConclusiveScan` is absent)
  3. `test_paths_trigger_unnarrowed` (parametrized over `push`/`pull_request`)
- Recorded RED evidence for all three by temporarily mutating
  `.github/workflows/differential-tests.yml`: (a) added `continue-on-error: true` to the gate
  step, (b) removed the `::TestCIGate` node id, (c) deleted the bimodal `paths:` entry from the
  `push` trigger. Each mutation failed only its matching assertion. Reverted all three; `diff`
  against a saved original confirmed byte-identical revert before the GREEN edit.
- Added a comment block directly above the "Run CI gate tests explicitly" step in
  `.github/workflows/differential-tests.yml` recording the by-design decision, the three
  guardrails, and the enforcing test class name.
- Added a paragraph to `code/docs/core/TESTING_GUIDE.md` section 8.14 ("Why a bimodal-only edit
  can still legitimately gate on `differential-tests.yml`") distinguishing the soundness check
  from the completeness blanket and stating criterion (a)'s scoped reading explicitly.

## Verification

- `PYTHONPATH=code/src pytest code/tests/ci/test_unstable_deselection_wiring.py -v -k
  TestOracleSoundnessGate` — 4 passed.
- `git diff .github/workflows/differential-tests.yml` — comment lines only; no change to any
  `run:`, `paths:`, or step key.

## Deviations from plan

None — followed Phase 2's task list exactly.

## Next phase

Phase 3 (wire the `-m development` producing step in `unstable-watch.yml`) depends on Phase 2
and is now unblocked.
