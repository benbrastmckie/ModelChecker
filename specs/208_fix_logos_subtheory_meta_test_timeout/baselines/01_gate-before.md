# Baseline: full repository gate, before deletion

- **Date**: 2026-09-27 (host-local timestamps below are PDT)
- **Host-load caveat**: this is a shared, ambient-load host, not an isolated CI runner. Two
  sibling tasks (197, 207) had in-progress uncommitted implementation work on this same tree
  during this run (see "Concurrent-sibling observation" below). Wall-clock numbers below should
  be read as one data point under real contention, not a clean-room measurement.

## Invocation shape (verified against `.github/workflows/tests.yml` immediately before this run)

Both `-m` expressions and both flag sets match the current workflow file exactly (no drift from
research's recorded shape):

- Parallel pass: `pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`
- Serial pass: `pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread`

Run from `code/` with `PYTHONPATH=src`, matching the workflow's `working-directory: code` /
`env.PYTHONPATH: src`. `--durations=10` was added to the parallel pass only (as CI's own comment
documents doing manually for measurement), never a value governed by the gate itself.

## Selected-node count (`--collect-only -q` under the parallel pass's marker expression)

**3099 / 3237 tests collected (138 deselected)** — matches research Finding 2's ~3099 exactly.
The node
`src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass`
is present in the collected set (confirmed via direct grep of the collect-only output).

## Parallel pass result

`1 failed, 3083 passed, 15 skipped, 5 warnings in 334.27s (0:05:34)`

- Wall time: **334.27s (5m34.849s per `time`)**.
- `test_all_subtheory_tests_pass` duration this run: **162.94s** (2nd-slowest item; well under
  the 300s ceiling this run — consistent with research's boundary-case description: the same test
  measured 320.90s in isolation and reportedly failed on at least one other CI run of this exact
  gate shape, so its position relative to the ceiling varies with load rather than being a fixed
  quantity).
- Slowest 10 durations (raw, in descending order):
  1. 176.78s call — `bimodal/tests/integration/test_certificate_a2_triangle.py::TestExhaustiveTriangleWithBox::test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`
  2. 162.94s call — `logos/tests/integration/test_subtheory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass`
  3. 31.30s setup — `logos/subtheories/counterfactual/tests/test_candidate_structure.py::test_populations_match_the_research`
  4. 27.08s setup — `logos/subtheories/counterfactual/tests/test_candidate_structure.py::test_n3_exhaustive_failure_counts[I]`
  5. 24.96s call — `bimodal/tests/integration/test_certificate_a2_triangle.py::TestExhaustiveTriangleWithBox::test_boxed_closure_enumeration_agrees_with_z3`
  6. 19.68s call — `logos/subtheories/counterfactual/tests/test_candidate_logic.py::test_constitutive_countermodel_is_confirmed_by_the_oracle[ILC]`
  7. 18.61s call — `models/tests/unit/test_semantic.py::TestSemanticDefaultsNBounds::test_max_n_itself_is_constructible`
  8. 14.26s call — `logos/subtheories/counterfactual/tests/test_candidate_logic.py::test_constitutive_comparison_outcome[ILMC-4]`
  9. 14.02s call — `logos/subtheories/counterfactual/tests/test_candidate_logic.py::test_constitutive_comparison_outcome[ILC-4]`
  10. 14.02s call — `logos/subtheories/counterfactual/tests/test_candidate_logic.py::test_constitutive_countermodel_is_confirmed_by_the_oracle[ILMC]`

- **FAILED**: `bimodal/tests/integration/test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`
  This is NOT `test_all_subtheory_tests_pass` and is unrelated to this task's target file. See
  "Concurrent-sibling observation" below.

## Serial pass result

`9 passed, 3232 deselected in 4.08s` — wall time 5.626s (`time`). No failures.

## Concurrent-sibling observation (territory discipline)

Before this run, `git status --short` showed uncommitted modifications to
`code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`,
`code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`, and
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py`. `git log` confirms
these are not this task's own commits. This dispatch's `## Territory` section names task 197
("harden certificate wire proof carrying" — bimodal certificate work) and task 207 as concurrent
siblings scheduled this same cycle with undeclared `file_scope`, so uncommitted bimodal-certificate
work in flight is the expected shape of that disclosed concurrency, not a surprise. The one
parallel-pass failure is in `bimodal/tests/integration/test_iterate.py`, in the same theory as
task 197's in-flight edits, and is plausibly attributable to that concurrent, mid-edit state
rather than to anything this task changes. This baseline captures the failure as-is (per this
plan's Phase 1/4 contract: the after-run comparison only needs to show no *additional* newly
failing node beyond what is recorded here); it is not investigated or fixed here, as it falls
outside `logos/tests/integration/test_subtheory_orchestration.py`, this task's sole edit target.

## Files

- Raw log: `baselines/01_gate-before.log`
