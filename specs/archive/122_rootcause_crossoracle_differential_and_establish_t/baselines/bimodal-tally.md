# In-Package Bimodal Suite Tally (Phase 4)

## Definitive result

`PYTHONPATH=<pylibs>:code/src pytest code/src/model_checker/theory_lib/bimodal/tests -n 6
--junitxml=baselines/junit-bimodal.xml -q`

**286 collected, 286 passed, 0 failed, 0 errored, 0 skipped. 43.43s wall-clock (6 workers).**

vs. task-118 baseline: 818 tests, 813 passed, 5 failed (all 5 in
`test_cross_oracle_differential.py`, relocated out by task 118 -- see
`collection-counts.txt` for the 818->286 count explanation: task 118 phase 5 relocated 7
oracle-dependent files, not just the 1 differential file). The in-package suite is confirmed
fully green without `BimodalHarness` on the path.

## `-n auto` (12-worker) CPU-contention flake -- investigated, not a regression

Two consecutive `-n auto` (12-worker, machine has 24 logical cores) full-suite runs each
produced exactly 1 failure: `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]`
(a Z3 solve that normally completes in ~10s, ran 15.16s and 15.20s respectively in the two
failing runs -- both times the single slowest `call` duration in the whole 286-test suite next
to two unrelated ~20s tests). Investigation:

- Isolated single-test runs (no xdist): 3/3 passed, consistently ~10.0-10.8s each.
- The 43-test `test_bimodal.py` file alone under `-n auto`: 43/43 passed (including BM_CM_1),
  22.70s.
- Full 286-test suite under `-n 6` (reduced worker count): 286/286 passed, 43.43s.

This isolates the cause to CPU contention specific to running the *full* 286-test suite at
12-way parallelism on this development machine: BM_CM_1's Z3 solve sits close to whatever
internal timeout budget applies, and full-suite 12-way contention (many concurrent Z3 solves
across workers) intermittently pushes its wall-clock past that budget. It is not a semantic
regression (the formula's assertion is unaffected -- only solve completion time varies), not
sensitive to test *file* parallelism (passes at `-n auto` for the 43-test file), and not
sensitive to whether xdist is involved at all (passes in isolation). Per the plan's own risk
mitigation ("if flakiness appears, pin the affected tests to -n 0 or a single worker and record
the reason"), the adopted resolution is to run the full bimodal suite at `-n 6` rather than
`-n auto` -- this keeps meaningful parallelism (43.43s vs. ~70 min single-threaded per the
task-118 baseline) while removing the contention that only manifests at full-suite 12-way
parallelism on this 24-core machine. The two `-n auto` attempts are preserved for the record as
`junit-bimodal-attempt1-flaky.xml`/`bimodal-run-attempt1-flaky.txt` and
`junit-bimodal-attempt2-flaky.xml`/`bimodal-run-attempt2-flaky.txt`; the `-n 6` green run
(`junit-bimodal.xml`/`bimodal-run.txt`) is the definitive Phase 4 record.
