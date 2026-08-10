# Repeat-Sample Validation Results

Evidence record for Phase 4 of `plans/01_single-threaded-construction-guard.md`.

- **Date**: 2026-08-08
- **Commit under test**: `d1fdbb63` (guard wired through Phases 1-3, incl. the `Syntax.__init__`
  extension from the Phase 2 amendment)
- **Python**: 3.13.13 | **pytest**: 9.0.3 | **Z3**: 4.16.0
- **Machine**: 24 cores. Load average during sampling: 4.6 -> 4.0 (1-min).
- **Concurrent activity**: the oracle suite (`oracle/run-oracle-suite.sh`, PID 405013) was
  running for the entire duration of all three batches. This is recorded deliberately: none of
  the three batches asserts wall-clock, so external CPU contention cannot skew the result, and
  running under contention is if anything a *stronger* test for a scheduling-dependent race than
  running on an idle machine.

## Methodology

A segfault kills the interpreter, so in-process pytest repetition cannot detect it. Each sample
is its own `python -m pytest` subprocess, judged solely by exit code:

| Exit code | Meaning |
|-----------|---------|
| 0 | pass |
| 139 (128+SIGSEGV) | segfault |
| 134 (128+SIGABRT) | abort |
| other non-zero | test failure or other error |

Samples run strictly serially — the harness never parallelizes them.

### Commands (verbatim, from repo root)

```bash
# Batch 1 -- 3-thread contract test
bash specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh 20 \
  "code/tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent"

# Batch 2 -- 5-thread contract test
bash specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh 20 \
  "code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building"

# Batch 3 -- both in one pytest invocation (cross-test guard-leak detection)
bash specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh 20 \
  "code/tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent" \
  "code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building"
```

Each sample the harness executes is:

```bash
PYTHONFAULTHANDLER=1 PYTHONPATH=code/src python -m pytest <node-ids> -q
```

## Results

### Batch 1 — `test_sequential_vs_concurrent` (3 threads)

| Run | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|-----|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|----|----|----|----|----|
| exit | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

**20/20 exit code 0.** Harness exit 0. Raw log: `evidence/phase4-batch1.txt`.

### Batch 2 — `test_concurrent_model_building` (5 threads)

| Run | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|-----|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|----|----|----|----|----|
| exit | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

**20/20 exit code 0.** Harness exit 0. Raw log: `evidence/phase4-batch2.txt`.

### Batch 3 — both node IDs in one invocation

| Run | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|-----|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|----|----|----|----|----|
| exit | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

**20/20 exit code 0.** Harness exit 0. Raw log: `evidence/phase4-batch3.txt`.

No run in any batch produced exit 139, exit 134, or any other non-zero code. No faulthandler
output was emitted.

**Total: 60/60 subprocess runs at exit code 0.**

## Contrast with the pre-fix baseline

Measured before the guard (from `reports/01_concurrent-segfault.md`):

| Configuration | Pre-fix result | Pre-fix crash rate | Post-fix result |
|---------------|----------------|--------------------|-----------------|
| 3 threads (`test_sequential_vs_concurrent`) | 5 crashes / 8 runs | 62.5% | 0 crashes / 20 runs |
| 5 threads (`test_concurrent_model_building`) | 6 crashes / 6 runs | 100% | 0 crashes / 20 runs |

The pre-fix crash site migrated across Z3 C API entry points (`Z3_get_sort_kind`, `Z3_mk_gt`,
`Z3_mk_func_decl`, `AstRef.__del__`) — the signature of shared-structure memory corruption.

## Statistical reading

20 clean runs against the measured 62.5% 3-thread rate drive the probability that a defect of
that magnitude survived undetected below 1e-8 (0.375^20). Against a hypothetical *residual* 10%
rate — far weaker than what was measured — 20 runs still give ~88% detection power
(1 - 0.9^20). The 5-thread configuration was 100% reproducible pre-fix, so a single clean run
there would already be significant; 20 makes it conclusive.

Batch 3 additionally rules out cross-test guard leakage: if either test left the guard held on
exit, the second test in the same interpreter would have raised `ConcurrentConstructionError`
from its first construction and failed the run. It did not, in 20 consecutive attempts.

## Conclusion

Phase 4's acceptance criterion — 60 total subprocess runs, all exit code 0 — is met. The
intermittent C-level segfault is not reproducible under the guard.
