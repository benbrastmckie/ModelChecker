# Research Report: `-n 4` Worker-Count Verification on Real CI

- **Task**: 171 - Verify xdist worker count on real ci
- **Started**: 2026-08-26T17:36:00Z
- **Completed**: 2026-08-26T18:05:00Z
- **Effort**: ~30 minutes (observation and log analysis; the CI run itself was user-triggered)
- **Dependencies**: None
- **Sources/Inputs**:
  - CI run `32995122897` (Tests, sha `cf60b1c8`) — the `-n 4` run under verification
  - CI run `32915763636` (Tests, sha at v1.3.6) — the `-n 6` baseline for comparison
  - CI run `32995122906` (Differential Oracle Tests, sha `cf60b1c8`) — same push
  - `.github/workflows/tests.yml`, `flake.nix`, `.github/scripts/worker_rss_sample.py`
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  - `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/reports/01_ci-budget-questions-a-c-d-and-b-confirmation.md`
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **Items (1), (2), (3) DISCHARGED.** The Tests workflow ran on real CI against `cf60b1c8`
  (which carries `-n 4`) across Python 3.10/3.11/3.12 plus `nix flake check`. All four jobs
  green. No example flipped. No timeout pressure.
- **Item (4) revert trigger DID NOT FIRE.** No flip, no timeout. `-n 4` stands in both
  `tests.yml` and `flake.nix`; `timeout-minutes` stays at 20 and was not widened.
- **`-n 4` is not slower on CI hardware.** It was marginally *faster* than the `-n 6` baseline
  (202.4s vs 204.5s average), a better outcome than the local screen predicted.
- **Python 3.12 worker-crash telemetry COLLECTED, item D NOT CLOSED.** The `[gw2] node down`
  crash did not recur, and the sampler produced its first real-CI reading. The numbers argue
  *against* the memory-ceiling hypothesis but do not close item D — see the caveats below.
- **The same push turned Differential Oracle Tests green for the first time ever, but NOT
  because the shortfall was fixed.** The failing test is quarantined. This is the documented
  `unstable` fallback working as designed, not a resolution. See "Do Not Misread" below.

## Findings

### (2) No example flipped outcome

| Job | `-n 6` baseline (`32915763636`) | `-n 4` (`32995122897`) |
|-----|--------------------------------|------------------------|
| Python 3.10 | 2043 passed, 255 skipped | 2089 passed, 255 skipped |
| Python 3.11 | 2043 passed, 255 skipped | 2089 passed, 255 skipped |
| Python 3.12 | 2043 passed, 255 skipped | 2089 passed, 255 skipped |
| nix flake check | success | success |

Zero failures. Skip count identical at 255 across both worker counts and all three Pythons.

The `+46` pass delta is **new tests, not behavior change**: `git diff 1e501592..cf60b1c8`
over `*test_*.py` adds 55 test functions and removes 0. The ~9 not reflected in this suite's
count live under `oracle/`, which `differential-tests.yml` owns and this selection does not
reach.

This is a genuine no-flip result rather than an absence of evidence: a countermodel-expected
example that stopped finding a countermodel would **fail its assertion**, not silently change
count. Green across the matrix is the finding.

The serial (`xdist_serial`) pass also went green on all three Pythons: `9 passed, 2457
deselected` in ~2.3s.

### (3) Timeout headroom — comfortable, no widening needed

Parallel gating pass wall clock:

| Python | `-n 6` baseline | `-n 4` |
|--------|-----------------|--------|
| 3.10 | 206.73s | 208.16s |
| 3.11 | 202.23s | 198.64s |
| 3.12 | 204.40s | 200.26s |
| **average** | **204.5s** | **202.4s** |

`-n 4` averaged **2.1s faster** than `-n 6` on the 4-vCPU runner. The local screen had
measured `-n 4` ~5% *slower* (272.8s vs 260.4s), inside the ~70s draw-to-draw spread; real CI
shows no slowdown at all. The decision to leave `timeout-minutes: 20` unchanged is confirmed
by measurement rather than assumption.

Whole-job durations against the 20-minute ceiling:

| Job | Duration |
|-----|----------|
| General Suite / Python 3.10 | 3m56s |
| General Suite / Python 3.11 | 3m46s |
| General Suite / Python 3.12 | 3m47s |
| nix flake check | 6m12s |

Worst case is under a third of the budget.

### Python 3.12 worker-crash telemetry (first real-CI collection)

`worker_rss_sample.py` produced its first CI reading on the 3.12 job:

```json
{
  "sample_count": 101,
  "distinct_worker_pids_observed": 24,
  "per_worker_peak_kb": 3766144,
  "aggregate_peak_kb": 4344196,
  "per_pid_peak_kb": {
    "2304": 226184, "2313": 268596, "2307": 379928, "2310": 3766144,
    "2436": 80920, "2438": 35100, "2636": 42664, "2663": 78816,
    "2667": 11224, "2717": 79528, "2718": 44564, "2836": 80952,
    "2981": 81060, "3002": 80188, "3018": 42516, "3251": 80944,
    "3260": 45624, "3262": 67748, "3263": 69192, "3277": 78952,
    "4513": 14196, "4704": 83080, "4709": 145872, "4738": 128380
  }
}
```

Sampling covered ~202s at a 2s interval (101 samples), matching the run length.

**The headline is the asymmetry.** Of the four `-n 4` workers, three peaked at 226 MB, 269 MB,
and 380 MB. The fourth (pid 2310) peaked at **3.59 GiB** — roughly 10x its siblings. Aggregate
peak was 4.14 GiB, only ~0.55 GiB above the single largest worker, meaning the peaks are **not
simultaneous**.

Against a 16 GB runner, aggregate peak is **~26% of available memory**.

The `[gw2] node down: Not properly terminated` crash **did not recur** on this run.

## Do Not Misread: the Differential Oracle green

`differential-tests.yml` run `32995122906`, on the same push and same sha, completed
**success** — the first green in the workflow's history (all six prior runs failed).

**This is not the 96/103 conclusiveness shortfall being resolved.** The gating test carries
`@pytest.mark.unstable` at
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py:2412`, and the run's
`-m "not unstable"` selection deselected it:

```
62 passed, 10 deselected in 294.94s   (main pass)
49 passed in 193.82s                  (CI gate pass)
```

`test_known_conclusive_population_self_consistent` appears **zero times** in the run log as
either PASSED or FAILED. The green is the documented `unstable` quarantine route from the
CI-budget work operating exactly as designed — an honest, declared narrowing of the gate, not
a silent weakening, and not evidence about the seven shortfall formulas.

Recording this explicitly because "Differential Oracle Tests: success" is the single most
misreadable signal produced by this push. `MIN_CONCLUSIVE_GATING_FORMULAS` remains 100 and
`GATING_RECHECK_SOLVE_TIMEOUT_MS` remains 40000; neither was touched.

## Open Questions

**Item D remains OPEN. Do not close it on this run.**

Three reasons, in order of force:

1. **One clean run against a crash seen twice is not a negative result.** The task's own
   instruction is explicit: a non-recurrence is *consistent with* the memory-ceiling hypothesis
   but does not confirm it and does not exclude the Z3/Python-3.12 ABI hypothesis.
2. **A 2s sampling interval cannot see the event of interest.** An OOM kill or a native-layer
   segfault follows a transient allocation spike, which is precisely the shape a 2s sampler
   misses. The telemetry bounds *steady-state* memory, not the peak that would kill a worker.
3. **But the steady-state numbers do argue against the memory ceiling.** At 4.14 GiB aggregate
   on a 16 GB runner, extrapolating this shape to `-n 6` lands nowhere near exhaustion. The
   memory-ceiling hypothesis is *weakened* by this data, which shifts weight toward the
   Z3/Python-3.12 ABI hypothesis without establishing it.

Follow-on questions this run raises:

- **What is pid 2310 doing?** A single worker holding 3.59 GiB while its siblings hold under
  400 MB is the most concrete lead item D has produced. Identifying which test group xdist
  assigned to that worker would narrow the search considerably. This run's telemetry does not
  map PIDs to test groups; wiring that correlation is the obvious next instrumentation step.
- **Does the asymmetry track a specific theory suite?** If the 3.59 GiB worker is consistently
  the one holding `theory_lib/bimodal`, that connects the memory profile to the same suite
  implicated in the original contention flake.
- **Would a shorter sampling interval catch a spike?** Dropping to 0.25s costs little on a
  non-gating step and would materially improve the odds of catching a pre-crash excursion —
  but only on a run where the crash actually recurs.

## Recommendations

1. **Keep `-n 4`.** Verified on real CI across the full matrix. No flip, no slowdown, no
   timeout pressure. The revert trigger did not fire and both files stay in sync.
2. **Leave `timeout-minutes` at 20.** Confirmed by measurement; worst job used under a third.
3. **Do not close item D.** Carry it forward with the telemetry recorded here as its first
   real-CI data point.
4. **Next instrumentation step for item D**: correlate worker PID to xdist test group so the
   3.59 GiB worker can be identified, and consider a tighter sampling interval. Both are
   non-gating changes to an already-non-gating step.
5. **Do not report the Differential Oracle green as a fix.** Any downstream summary of this
   push should carry the quarantine caveat from the section above.

## References

- CI run `32995122897` — Tests, `-n 4`, all four jobs green
- CI run `32915763636` — Tests, `-n 6` baseline
- CI run `32995122906` — Differential Oracle Tests, green via `unstable` deselection
- `.github/scripts/worker_rss_sample.py` — sampler contract in module docstring
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py:2412` — the `unstable` marker
- `code/tests/ci/test_workflow_parity.py::test_worker_count_matches` — the `-n` sync guard
- `code/docs/core/TESTING_GUIDE.md` section 8.13 — why local `taskset` screens are blind here

---

# ADDENDUM (2026-08-26T18:15Z): the crash recurred on Python 3.11

**This addendum falsifies a conclusion drawn above.** The body of this report states that the
`[gw2] node down` crash "did not recur." That was true of run `32995122897`. It is **not** true
in general: the very next Tests run, `32996446859` (sha `3dd6a985`, the version-bump commit),
reproduced it — **on Python 3.11, at `-n 4`**.

```
[gw2] node down: Not properly terminated
FAILED src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py
       ::TestFixtureSmoke::test_extract_world_histories_nonempty
       - worker 'gw2' crashed while running '...'
1 failed, 2088 passed, 255 skipped in 342.19s (0:05:42)
```

The same run also failed `nix flake check` on a *different* mechanism (see below).

## What this changes for item D

Three hypotheses were live. This incident moves all three:

1. **The Z3/Python-3.12 ABI hypothesis is substantially weakened.** The crash is not
   3.12-specific. It has now occurred on 3.11. The instrumentation comment in
   `.github/workflows/tests.yml` justifying the 3.12 gate — "the only leg the crash has been
   observed on" — is now **factually false** and must be updated.
2. **The memory-ceiling hypothesis is weakened, not strengthened.** `-n 4` gives more headroom
   per worker than `-n 6`, and the crash still occurred. Combined with the 4.14 GiB aggregate
   peak (26% of 16 GB) recorded above, memory exhaustion looks unlikely as the sole cause.
3. **The xdist/execnet worker-communication hypothesis gains relative weight** by elimination,
   though nothing here confirms it directly.

## The instrumentation is on the wrong job

`worker_rss_sample.py` is gated on `matrix.python-version == '3.12'`
(`.github/workflows/tests.yml:180`). The crash occurred on **3.11**, so the sampler collected
**nothing** for the one incident it was built to explain. This is the single highest-value
correction available: **remove the 3.12 gate and sample on all three legs.** The step is
already non-gating and costs almost nothing.

## A pattern the "innocent bystander" reading may have missed

Both confirmed `node down` incidents share two properties not previously connected:

| Run | Python | Worker | Test file |
|-----|--------|--------|-----------|
| `32910478240` | 3.12 | `gw2` | `test_frame_class_mapping.py::TestFrameClassDeclarationConsistency::test_three_taskframe_axioms_present_in_frame_constraints` |
| `32996446859` | 3.11 | `gw2` | `test_frame_class_mapping.py::TestFixtureSmoke::test_extract_world_histories_nonempty` |

Same worker id, same file, different tests and different Pythons. The prior analysis concluded
the *named test* is an innocent bystander, which the differing test names still support. But
two-for-two on the same **module** is a stronger signal than the bystander reading accounts
for, and warrants checking whether xdist's distribution consistently assigns
`test_frame_class_mapping.py` to `gw2` and whether that module's fixtures hold unusual native
state. Two incidents is a thin base for either conclusion — this is a lead, not a finding.

## Second, independent failure in the same run: `nix flake check`

```
FAILED src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py
       ::TestBimodalIteratorReal::test_iterate_example_generator_yields_models
       - AssertionError: First model was not satisfiable; cannot exercise iteration
1 failed, 2040 passed, 259 skipped, 3 warnings in 229.65s (0:03:49)
```

**This is a different mechanism from the worker crash** — a solve-budget overrun, not process
death — and must not be conflated with it.

The root cause is an **assertion-design flaw, not a budget number**. `solve()` in
`code/src/model_checker/models/structure.py:293` returns `_create_result(True, None, False,
start_time)` on `UNKNOWN`, i.e. `timeout=True` **and** `z3_model_status=False`. A genuine unsat
returns `timeout=False, z3_model_status=False`. The test asserts only `z3_model_status`, so a
contention-induced timeout is **indistinguishable from a real unsatisfiable result** and
inverts into a false negative.

This is why the recorded 30 -> 60 `max_time` widening did not fix it, and why 60 -> 120 would
not either: no budget value closes a hole in the discriminator. The structure already carries
the discriminator (`model_structure.timeout`); the test simply does not consult it.

**Recommended fix** (does not weaken the assertion — a genuine unsat still fails):

```python
if example.model_structure.timeout:
    pytest.skip("Z3 exceeded max_time under CI contention; timeout is not unsat")
assert example.model_structure.z3_model_status, (
    "First model was not satisfiable; cannot exercise iteration"
)
```

The sibling test `test_iterate_two_produces_distinct_models` already handles the analogous
budget-sensitivity gracefully in its docstring's terms; this test does not.

## Revised recommendations

Superseding items 3 and 4 of the body:

1. **Ungate the RSS sampler from 3.12** and correct the now-false "only leg observed on"
   comment. Highest value, lowest cost, non-gating.
2. **Fix the `test_iterate` assertion** to consult `model_structure.timeout` before asserting
   `z3_model_status`. This is a genuine fix, not a budget bump.
3. **Item D remains OPEN**, now with a corrected hypothesis ranking and one more incident.
4. **`-n 4` still stands.** Nothing here argues for reverting it: the crash predates it,
   occurred at `-n 6` twice, and the timing verification in the body is unaffected.
5. **Treat "green" on any single Tests run as weak evidence.** Runs `32995122897` (all green)
   and `32996446859` (two failures) are consecutive, on near-identical trees. The failure rate
   is what matters, not the last result.
