# Grounding the Wall-Clock Performance Budgets

**Task**: 136 — ground_wallclock_performance_budgets
**Session**: sess_1786211832_501137_136
**Date**: 2026-08-08
**Scope**: `code/tests/integration/test_performance.py`,
`code/tests/integration/test_timeout_resources.py`,
`code/src/model_checker/builder/tests/integration/test_performance.py`,
`code/pyproject.toml`

---

## 1. Executive Summary

The root cause of every one of these failures is a single structural fact that the task
description did not have, and it changes the recommended fix:

> **Every wall-clock quantity these tests measure is dominated by, and hard-capped at, the
> theory's `max_time` setting — which for `BimodalSemantics` defaults to `1` second.**
> The measured "elapsed" is `min(real_solve_time, max_time) + overhead`. Budgets of 0.5s and
> 1.0s are therefore compared against a distribution whose ceiling is ~1.0–1.25s and whose
> spread straddles the budget. They are not tight budgets — several are *arithmetically
> unreachable*, and the rest are coin flips by construction.

Three consequences:

1. **`test_small_model_generation_completes_quickly` (<500ms) can never pass.** Its measured
   floor is ~1.20s, of which 1.00s is the Z3 timeout wall. The example it runs genuinely needs
   ~1.6–1.8s of solve time. This is an authoring defect, confirmed by measurement, exactly as
   the task suspected. Same for `test_multiple_examples_process_efficiently` (5 × 1.2s = 6.2s
   against a 2.0s budget).
2. **`test_simple_model_performance` (<1.0s) and `test_scaling_with_n[2-1.0]` (<1.0s) have a
   budget numerically equal to the `max_time` cap.** They fail exactly when Z3 exhausts its
   budget. Observed failure rates across 5 samples: 2/5 and 4/5.
3. **The task's proposed alternative — asserting a relative scaling ratio between two N values
   — does not work in this codebase, and I recommend against it.** Section 5 gives the
   measurement. While `max_time` caps every solve at 1s, all of N=2/4/8 measure ≈1.0s, so any
   ratio is ≈1.0 and the assertion is vacuous; and if you raise `max_time` enough to measure
   real scaling, the underlying solve time varies by two orders of magnitude, and the ratio
   inherits variance from *both* numerator and denominator. A ratio is strictly worse here, not
   better.

**Recommended disposition: no timing assertion in these three files survives as a performance
guard.** 2 are deleted as unreachable, 15 are deleted as vacuous or noise, 7 have the timing
clause replaced by a behavioural assertion, and 4 are retained only as *hang guards* (budgets
20x+ above measured cost, where the assertion means "did not hang" rather than "was fast"). The
one genuinely well-built micro-benchmark
(`test_serialization_performance`) is pure-Python, Z3-free, 100-rep averaged, and is retained
as-is.

**A second, independent finding worth acting on** (Section 7): several of these tests are slow
*only* because they burn the full `max_time` waiting for a solve whose result they never
inspect. `test_memory_released_after_error` spends 11.0s to assert a garbage-collection fact;
10.0s of that is Z3 timing out ten times. Setting a small explicit `max_time` on such tests cuts
their cost by ~90% **and** removes their timing sensitivity, because a solve that is designed to
be truncated is deterministic in a way that one racing the cap is not.

---

## 2. Correction to the Task's Premise: Two of Three Files Are Already Narrowed

The task description says all three files carry a module-level `pytestmark = pytest.mark.slow`
quarantining 43 tests. **That is no longer true at HEAD** (`d1fdbb63`). Commit `aebf7a23`
("task 135 phase 3.1") already did most of workstream (1):

| File | Marker state at HEAD |
|------|----------------------|
| `code/tests/integration/test_performance.py` | Module-level mark **already replaced** by per-class marks. `TestConcurrentPerformance` is unmarked and runs in the default suite. |
| `code/tests/integration/test_timeout_resources.py` | Module-level mark **already replaced** by per-class marks, plus per-method marks inside `TestResourceLimits`. `test_concurrent_model_building` is unmarked and runs in the default suite. |
| `code/src/model_checker/builder/tests/integration/test_performance.py` | **Still module-level** `pytestmark = pytest.mark.slow` at line 31 — all 10 tests quarantined. |

Current collection: **41 tests selected by `-m slow`** (not 43), across the three files plus
`models/tests/unit/test_semantic.py::test_max_n_itself_is_constructible`.

**Verified against the task's cross-task note**: both concurrency tests have indeed been
rewritten to assert the single-threaded-construction contract, both are already unmarked, and
both passed in all 5 sample sweeps and in the in-progress unfiltered full run. They do **not**
need to stay marked. The task description's instruction to add `@pytest.mark.slow` to "the two
concurrency crashers" is superseded — re-marking them would be a regression against task 135's
completed work.

So workstream (1) reduces to: **narrow the one remaining module-level mark in the builder
file**, and unmark the many tests in the other two files that carry no timing assertion at all.

---

## 3. Measurement Method

All numbers below are measured on this machine at HEAD `d1fdbb63`, under the same background
load (a sibling oracle suite was running, per the task's coordination note — this is
representative of the conditions that produce the reported flakiness).

- **5 repeat samples** of `pytest -m slow -q --durations=0`, full quarantined set, cold cache
  (`-p no:cacheprovider`). Wall time 64.6s / 65.2s / 66.9s / 68.4s / 68.8s.
- **Targeted probes** of `create_test_model` at N ∈ {2,3,4,8} × `max_time` ∈ {default 1, 10, 30},
  both in-process (8 identical repeats) and one-per-fresh-process (3–6 repeats), recording
  elapsed, the model's `timeout` flag, and Z3's self-reported `z3_model_runtime`.
- **1 unfiltered full-suite run** (`-m ""`, 2195 collected, 0 deselected) — see Section 8.

Observed failure sets across the 5 samples (this alone demonstrates the instability):

| Sample | Failures |
|---|---|
| 1 | `test_scaling_with_n[2-1.0]`, `test_multiple_examples_process_efficiently`, `test_small_model_generation_completes_quickly` |
| 2 | `test_multiple_examples_process_efficiently`, `test_small_model_generation_completes_quickly` |
| 3 | `test_scaling_with_n[2-1.0]`, `test_multiple_examples_process_efficiently`, `test_small_model_generation_completes_quickly` |
| 4 | `test_simple_model_performance`, `test_scaling_with_n[2-1.0]`, `test_multiple_examples_process_efficiently`, `test_small_model_generation_completes_quickly` |
| 5 | `test_simple_model_performance`, `test_scaling_with_n[2-1.0]`, `test_multiple_examples_process_efficiently`, `test_small_model_generation_completes_quickly` |

Per-test failure rate: `test_small_model_generation_completes_quickly` **5/5**,
`test_multiple_examples_process_efficiently` **5/5**, `test_scaling_with_n[2-1.0]` **4/5**,
`test_simple_model_performance` **2/5**.

---

## 4. Root Cause: The `max_time` Cap Is the Thing Being Measured

`BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` is:

```python
{'N': 2, 'M': 2, 'contingent': False, 'disjoint': False,
 'max_time': 1, 'expectation': True, 'iterate': 1, 'solver': 'z3'}
```

Neither `create_test_model` (in `code/tests/utils/helpers.py`) nor the builder tests' generated
example modules override `max_time`, so every model construction in these three files runs with
a **1-second solver budget**.

### 4.1 Direct probe: elapsed is pinned to the cap

`create_test_model({'N': n})`, in-process, 5 repeats each:

| N | elapsed min | median | max | `timeout` flag | z3 runtime |
|---|---|---|---|---|---|
| 2 | 0.097 | 0.616 | 1.034 | True | 1.0002 |
| 3 | 0.176 | 1.007 | 1.031 | False | 0.3333 |
| 4 | 0.386 | 1.026 | 1.029 | True | 1.0009 |
| 8 | 1.027 | 1.030 | 1.031 | True | 1.0013 |

The maximum is ~1.03s for **every** N. N=8 is not "10x slower than N=2" — it is capped at the
same 1.0s wall. This is why `test_scaling_with_n[4-2.0]` and `[8-10.0]` always pass: their
budgets (2.0s, 10.0s) are 2x and 10x above a quantity that physically cannot exceed ~1.03s.
Those two assertions are vacuous.

### 4.2 The N=3 case: budget, cap, and true solve time all coincide at 1.0s

Fresh-process probe of `create_test_model({'N': 3})`, timing the construction only:

```
max_time=10:  elapsed 1.123 / 1.187 / 1.259 / 1.230 / 1.153   timeout=False  z3_runtime 0.902–1.012
max_time=1:   elapsed 1.227 / 1.265 / 1.200                   timeout=False,True,False
```

The genuine Z3 solve time for N=3 is **0.90–1.01s**, and the default cap is **1.0s**. The true
cost straddles the cap: 1 of 3 fresh runs timed out. Inside the warm pytest process (theory
already loaded, overhead ≈ 0) the measured elapsed is 0.85–1.01s.

`test_simple_model_performance` asserts `elapsed < 1.0` on exactly this quantity. **The budget
sits inside the measured distribution.** A 2/5 observed failure rate is the arithmetic
consequence, not bad luck.

Identical reasoning applies to `test_scaling_with_n[2-1.0]`: budget 1.0 = cap 1.0, measured
0.60–1.15, observed 4/5 failures.

### 4.3 The builder tests: unreachable, not tight

The failure output is explicit about what is happening:

```
TIMEOUT: Model search exceeded maximum time of 1 seconds
No model for example SMALL found before timeout.
EXAMPLE SMALL: there is no countermodel.
Solver Run Time: 1.0002 seconds
AssertionError: 1.1991400718688965 not less than 0.5
```

I ran the same example at increasing budgets:

| `max_time` | elapsed | outcome |
|---|---|---|
| 1 (default) | 1.225 | **TIMEOUT — "there is no countermodel"** |
| 5 | 1.843 | "there is a countermodel" |
| 20 | 2.005 | "there is a countermodel" |

Two findings:

1. The measured floor is **1.20s** (1.00s timeout wall + ~0.22s BuildModule/theory overhead).
   A 500ms budget cannot be met under any circumstance. Confirmed 5/5 failures at 1.199s,
   1.200s, 1.244s, 1.253s, 1.252s — a spread of only 5%, which is the signature of a *constant*,
   not a flake. The task's read was right: **authoring defect, not flakiness.**
2. **Latent correctness bug, outside this task's file scope but worth reporting**: the same
   example reports *"there is no countermodel"* at `max_time=1` and *"there is a countermodel"*
   at `max_time=5`. This is precisely the silent semantic inversion that
   `TESTING_GUIDE.md` §8.6 warns about ("a timeout is indistinguishable from a genuine 'no
   countermodel exists' outcome at the assertion site"). These tests do not assert on the
   verdict, so they do not catch it — but any *other* bimodal example sitting near the 1s
   boundary is silently at risk. See Section 9.

`test_multiple_examples_process_efficiently` is the same defect times five: 5 examples × ~1.24s
= 5.98–6.23s measured, against a 2.0s total budget and 0.5s average budget. 5/5 failures.

---

## 5. The Relative-Scaling Ratio Proposal: Measured, and Not Recommended

The task asked me to investigate asserting *relative scaling* between two N values instead of
absolute seconds, on the theory that a ratio is more load-stable. I measured it. **It is not,
and I recommend against it.** Two independent reasons:

### 5.1 Under the current `max_time`, every ratio is vacuous

As Section 4.1 shows, N=2, N=4 and N=8 all measure ≈1.03s because all three hit the same cap.
Any ratio between them is ≈1.0 regardless of the code under test. This is not hypothetical —
it is already happening. `test_constraint_generation_scales_linearly` in the builder file is
exactly this shape:

```python
self.assertLess(time_ratio, formula_ratio * formula_ratio)
```

All four of its cases hit the 1s cap, so `time_ratio ≈ 1.0` is compared against 4, 9, and 16.
The assertion is stable at 4.01–4.26s across all 5 samples — stable precisely because it
measures nothing. It would not detect a genuine quadratic blowup, because the cap truncates the
signal before the assertion sees it.

### 5.2 Lift the cap and the ratio becomes *more* volatile, not less

With `max_time=30` (in-process), the same construction:

| N | elapsed min | median | max |
|---|---|---|---|
| 2 | 0.213 | 1.311 | 5.130 |
| 3 | 0.233 | 1.000 | 30.090 |
| 4 | 0.472 | 30.084 | 30.090 |

N=3 ranges from 0.233s to a full 30s timeout **on identical input in the same process** — a
129x spread. A ratio N4/N2 built from these ranges from ~0.09 to ~141, a spread of three orders
of magnitude. The ratio compounds the variance of two noisy measurements rather than cancelling
it; cancellation would only occur if the two measurements' noise were correlated, and it is not.

### 5.3 The one condition under which timing here *is* reproducible

Worth recording, because it is the most useful positive finding: **one construction per fresh
process is highly stable.** Fresh-process, `max_time=10`, N=2 then N=4:

```
N2=0.578 N4=0.350 ratio=0.60
N2=0.571 N4=0.354 ratio=0.62
N2=0.580 N4=0.352 ratio=0.61
N2=0.563 N4=0.347 ratio=0.62
N2=0.581 N4=0.356 ratio=0.61
N2=0.596 N4=0.389 ratio=0.65
```

Spread: 6% on N=2, 11% on N=4, ratio stable to ±4%. Compare the 8-repeat *in-process* sequence
for N=3 at the default cap: `1.119, 0.616, 0.600, 0.340, 1.021, 0.137, 1.025, 1.026` — erratic,
non-monotonic, with the solver timing out on reps 4/6/7 and solving in 0.137s on rep 5, same
input.

So the instability is **not** primarily machine load, and **not** intrinsic per-call Z3
randomness — it is contamination from prior solver work accumulated in the same interpreter
process. (Consistent with the process-global Z3 context documented in
`model_checker/models/concurrency.py` and pinned by task 135's guard.) Note also that N=4 is
*faster* than N=2 here (ratio 0.6), which means even a clean ratio measurement would not encode
the monotonic "bigger N is slower" intuition a scaling guard is meant to express.

**Conclusion**: a trustworthy timing measurement in this codebase requires subprocess isolation
plus repeat sampling. That is a benchmark harness, not a unit test. If a genuine performance
regression guard is wanted, it belongs in a separate opt-in benchmarking job (e.g.
`pytest-benchmark` with `--benchmark-only`, run deliberately), not as an assertion inside the
functional suite. I recommend **not** building one as part of this task, and instead removing
the assertions that pretend to be one.

---

## 6. Per-Assertion Inventory and Disposition

Classification per the task's scheme: **(a)** real regression guard needing a grounded budget;
**(b)** correctness test wearing a stopwatch — assert behaviour, drop timing; **(c)** obsolete /
never-grounded — delete the assertion.

Measured columns are the 5-sample min–max of the pytest-reported call duration (which includes
a little setup, so it slightly overstates the assertion window).

### 6.1 `code/tests/integration/test_performance.py`

| Test | Budget | Measured (5 samples) | Fails | Class | Disposition |
|---|---|---|---|---|---|
| `test_simple_model_performance` | <1.0s | 0.85–1.01 | 2/5 | **(b)** | Budget == `max_time` cap. Delete the timing clause; assert the model was constructed and is well-formed (currently it asserts *nothing* about the model). Unmark. |
| `test_medium_model_performance` | <5.0s | 1.09–1.10 | 0/5 | **(c)** | Vacuous: 5x above a 1.03s ceiling. Delete timing clause; keep as a construction smoke test. |
| `test_complex_model_performance` | <20.0s | 5.81–6.19 | 0/5 | **(a)-ish** | The only test whose cost is real (N=16 Python-side constraint generation, ~6s, not solver-capped). 3.3x headroom. But `except Exception: assert elapsed < 30.0` makes it near-unfailable. **Retain as a hang guard** with the existing 20s budget, documented as such; do not treat as a perf guard. |
| `test_scaling_with_n[2-1.0]` | <1.0s | 0.60–1.15 | 4/5 | **(b)** | Budget == cap. Delete timing clause. |
| `test_scaling_with_n[4-2.0]` | <2.0s | 1.07–1.09 | 0/5 | **(c)** | Vacuous (2x cap). Delete timing clause. |
| `test_scaling_with_n[8-10.0]` | <10.0s | 1.08–1.09 | 0/5 | **(c)** | Vacuous (10x cap). Delete timing clause. |
| `test_memory_usage_simple` | 10MB | 0.35–1.10 | 0/5 | — | No wall-clock assertion. **Unmark.** |
| `test_memory_usage_complex` | 100MB | 1.33–1.37 | 0/5 | — | No wall-clock assertion. **Unmark.** |
| `test_memory_cleanup` | 500 objs | 3.16–4.76 | 0/5 | — | No wall-clock assertion. **Unmark** (see §7 for cost reduction). |
| `test_batch_small_examples` | <2.0s | **<0.005** | 0/5 | **(c)** | `validate_example` only does structural assertions — **no model checking at all**. The budget measures ~20 list constructions. Delete timing clause; unmark. |
| `test_batch_mixed_complexity` | <5.0s | **<0.005** | 0/5 | **(c)** | Same. Delete timing clause; unmark. |
| `TestConcurrentPerformance::test_sequential_vs_concurrent` | — | — | 0/5 | — | Already unmarked (task 135). **Leave alone.** |
| `test_repeated_operations` | ratio ≤1.5x | <0.005 | 0/5 | **(c)** | Ratio of two sub-millisecond parse times; passes only because the first is cold-start. Pure noise. Replace with a real caching assertion or delete. Unmark either way. |
| `test_theory_loading_performance` | ratio ≤1.1x | <0.005 | 0/5 | **(b)** | Intent is "the theory cache works". Assert that directly (`get_theory('bimodal') is get_theory('bimodal')`), drop the timing. Unmark. |
| `test_maximum_n_performance` | <35s | 0.05–0.07 | 0/5 | **(c)** | 500x headroom; fails fast at N=64. Vacuous. Unmark. |
| `test_many_propositions_performance` | <2.0s | <0.005 | 0/5 | **(c)** | Wrapped in `except Exception: pass` — cannot fail. Delete timing clause; unmark. |

### 6.2 `code/tests/integration/test_timeout_resources.py`

| Test | Budget | Measured | Fails | Class | Disposition |
|---|---|---|---|---|---|
| `test_z3_solver_timeout` | <5.0s | 0.07–0.09 | 0/5 | **hang guard** | 55x headroom; the assertion means "did not hang". **Retain, unmark.** |
| `test_cli_command_timeout` | <6.0s | 0.26–0.29 | 0/5 | **hang guard** | Backed by a real `subprocess` timeout=5. **Retain, unmark.** |
| `test_various_timeout_values[0.001/0.01/0.1]` | — | 0.07–0.18 | 0/5 | **(c)** | Asserts `settings['max_time'] == timeout_value` — i.e. that the dict it just built contains what it put there. Tautological. Rewrite to assert the setting reaches the solver, or delete. Unmark. |
| `test_large_state_space` | — | 0.16–0.22 | 0/5 | — | No timing assertion. **Unmark.** |
| `test_many_propositions` | — | 0.32–1.10 | 0/5 | — | No assertion **at all** (bare try/except with a comment). Either assert something or delete. Unmark. |
| `test_concurrent_model_building` | — | — | 0/5 | — | Already unmarked (task 135). **Leave alone.** |
| `test_keyboard_interrupt_cleanup` | — | <0.005 | 0/5 | — | Asserts only `module_path` is truthy; does not test interrupts. **Unmark** (and consider deleting as a stub). |
| `test_graceful_shutdown` | — | 0.94–1.09 | 0/5 | — | No timing assertion (has `@pytest.mark.timeout(10)`, which is the right mechanism). **Unmark.** |
| `test_performance_with_many_constraints` | <1.5s | 1.14–1.17 | 0/5 | **(b)** | **Margin only 0.33s over a cap-pinned 1.15s.** Has not failed yet but is the same shape as the ones that do. Delete timing clause. |
| `test_scaling_behavior[2-0.1]` | <0.3s | 0.26–0.29 | 0/5 | **(b)** | **Tightest margin in the entire set: as little as 0.01s.** This is the next flake. Delete timing clause. |
| `test_scaling_behavior[4-0.5]` | <1.5s | 0.79–1.09 | 0/5 | **(b)** | Margin 0.41s over a cap-pinned value. Delete timing clause. |
| `test_scaling_behavior[8-2.0]` | <6.0s | 4.08–4.10 | 0/5 | **(c)** | Margin 1.9s, but the 4.1s is pure cap-burn (`max_time` = 4.0). Delete timing clause; see §7. |
| `test_memory_released_after_error` | 1000 objs | **10.88–11.06** | 0/5 | — | No timing assertion. Most expensive test in the set; 10s of it is cap-burn. **Unmark + reduce cost (§7).** |
| `test_file_handles_closed` | — | 3.23–3.68 | 0/5 | — | No timing assertion. **Unmark.** |

### 6.3 `code/src/model_checker/builder/tests/integration/test_performance.py`

All 10 currently quarantined by the module-level mark at line 31.

| Test | Budget | Measured | Fails | Class | Disposition |
|---|---|---|---|---|---|
| `test_small_model_generation_completes_quickly` | <0.5s | 1.199–1.253 | **5/5** | **(c)** | **Arithmetically unreachable** (floor 1.20s). Delete the timing assertion; keep as a "small example runs end-to-end" integration test. |
| `test_medium_model_generation_completes_within_timeout` | <2.0s | 1.18–1.24 | 0/5 | **(b)** | Margin 0.76s over a cap-pinned value. Delete timing clause. |
| `test_large_model_generation_completes_within_timeout` | <5.0s | 1.19–1.25 | 0/5 | **(c)** | Identical settings to the "medium" test (both N=5) — the "large" case is a copy-paste duplicate. Delete timing clause; consider merging the two tests. |
| `test_multiple_examples_process_efficiently` | avg<0.5s, total<2.0s | 5.98–6.23 | **5/5** | **(c)** | Unreachable (5 × 1.24s). Delete both timing assertions; keep as a multi-example integration test. |
| `test_comparison_mode_performance` | <2.0s | 0.12–0.14 | 0/5 | **(c)** | Vacuous, **and the test does not do what it says**: `bimodal.get_theory(['extensional'])` and `get_theory(['counterfactual'])` return the *identical* operator collection (verified: `is` comparison True, same 17 operators). It compares bimodal against itself. Delete timing clause; fix or delete the test. |
| `test_module_loading_performance` | <0.1s | <0.005 | 0/5 | **hang guard** | Z3-free, 20x headroom, genuinely cheap. **Retain, unmark.** |
| `test_serialization_performance` | <1ms avg | <0.005 | 0/5 | **(a)** | **The one well-built timing assertion here**: pure Python, no Z3, averaged over 100 iterations. **Retain as-is, unmark.** |
| `test_constraint_generation_scales_linearly` | ratio<n² | 4.01–4.26 | 0/5 | **(c)** | Vacuous — all four cases hit the 1s cap so `time_ratio ≈ 1.0` (see §5.1). Delete or re-scope to count constraints rather than seconds. |
| `TestMemoryUsage::test_memory_usage_stays_within_bounds` | — | <0.005 | 0/5 | **(c)** | Body is `self.assertTrue(True, "placeholder")`. Delete or implement. Unmark. |
| `TestMemoryUsage::test_no_memory_leaks_in_iteration` | — | <0.005 | 0/5 | **(c)** | Same placeholder. Delete or implement. Unmark. |

### 6.4 Summary of dispositions

| Disposition | Count |
|---|---|
| Delete timing assertion as **arithmetically unreachable** | 2 (both builder) |
| Delete timing assertion as vacuous / never grounded (c) | 15 |
| Delete timing clause, assert the behaviour instead (b) | 7 |
| Retain as an explicit **hang guard** (budget ≥20x measured) | 4 |
| Retain as-is (real, Z3-free, averaged micro-benchmark) | 1 |
| No timing assertion at all — simply unmark | 9 |
| Already correct, leave alone (task 135's two contract tests) | 2 |
| **Total** | **40** (+ `test_max_n_itself_is_constructible` = 41 collected) |

**Zero timing assertions require a re-grounded p95/p99 budget.** Every candidate for category
(a) either measures the `max_time` cap rather than the code, or needs subprocess isolation to be
meaningful (§5.3). This is the substantive answer to the task's central question.

---

## 7. Independent Win: Stop Paying for Timeouts Nobody Reads

Several expensive tests never inspect the solve result — they assert a garbage-collection fact,
a file-handle count, or merely that no exception escaped. They nonetheless wait the full
`max_time` for a solve that is guaranteed to be discarded:

| Test | Cost | Cap-burn component | Fix |
|---|---|---|---|
| `test_memory_released_after_error` | 11.0s | 10 × 1.0s | Set `max_time` ≈ 0.05 in its settings dict — it asserts only `gc` object growth |
| `test_scaling_behavior[8-2.0]` | 4.1s | `max_time`=4.0 | Timing clause deleted anyway; shrink the cap |
| `test_file_handles_closed` | 3.6s | 5 CLI subprocesses | Reduce iteration count |
| `test_memory_cleanup` | 3.2–4.8s | 5 × ~0.7s | Set a small `max_time` — asserts only object growth |
| `test_constraint_generation_scales_linearly` | 4.2s | 4 × 1.0s | Deleted or re-scoped per §6.3 |

Estimated saving: **~20s of the ~65s** quarantined-set runtime, with no loss of assertion power.
This matters for the definition of done, because un-quarantining adds this cost to every default
run. It also *reduces* flakiness: a solve deliberately truncated at 50ms is deterministic,
whereas one racing a 1s cap is not.

---

## 8. What Must Be True to Delete the `-m "not slow"` Clause

The `addopts` note in `code/pyproject.toml` names two blockers. Status:

| Blocker | Status |
|---|---|
| 1. Concurrent model building segfaults the interpreter (exit 139) | **Resolved by task 135.** Both concurrency tests are rewritten, unmarked, and passed in all 5 sample sweeps plus the unfiltered run. No exit-139 abort observed in any run performed for this research. |
| 2. Wall-clock budgets tighter than real Z3 variance | **This task.** Addressed by the §6 dispositions. |

Path to deletion, in order:

1. **Narrow the last module-level mark.** Replace `pytestmark = pytest.mark.slow` (builder
   file, line 31) with per-test marks. Cheap, independent, and unblocks visibility on 10 tests.
2. **Apply the §6 dispositions** — delete or rewrite the timing assertion on 24 tests (2
   unreachable + 15 vacuous + 7 converted to behavioural assertions).
3. **Reduce cap-burn** per §7 so the un-quarantined cost is acceptable.
4. **Leave exactly one test marked `slow`**: `models/tests/unit/test_semantic.py::test_max_n_itself_is_constructible`
   (measured 9.56–10.27s, allocates ~3.5GB; per the task description it stays marked to keep
   `MAX_N` honest). Note this means the marker survives, so the `slow` marker *definition* in
   `[tool.pytest.ini_options].markers` must stay — only the `-m "not slow"` clause in `addopts`
   is deleted. The marker's description string should also be rewritten: it currently says
   "Quarantined pending fixes… expected to rejoin the default run", which will no longer be
   true.
5. **Delete the `-m \"not slow\"` clause** from `addopts` and rewrite the long TEMPORARY comment
   block above it.
6. **Verify with ≥5 repeat unfiltered full sweeps**, requiring an identical pass set each time —
   not merely 5 green runs, since the defect being fixed is *set instability*, and comparing
   failure sets is what exposed it in the first place.

**Cost estimate for the default run**: the quarantined set costs ~65s, of which ~10s
(`test_max_n_itself_is_constructible`) stays marked, and ~20s is recoverable per §7. Net
addition to the default run: **~35s** on a current filtered baseline of ~5:37 — roughly +10%.

### Unfiltered full-run evidence

An unfiltered run (`-m ""`, 2195 collected, 0 deselected) was executed as part of this research;
its result is recorded in §10 below. Note that the pre-existing failures it surfaces are the
same three/four timing tests catalogued in §6 — no *new* class of failure appears when the
filter is lifted, and critically **no interpreter abort occurred**, which is the key change
since the `addopts` note was written.

---

## 9. Findings Outside This Task's File Scope (Report, Do Not Fix Here)

1. **Bimodal's default `max_time: 1` is below the real solve time for its own simple examples.**
   N=3 solves in 0.90–1.01s against a 1.0s cap; the builder's N=2 example needs ~1.6–1.8s. Per
   `TESTING_GUIDE.md` §8.6 this silently inverts semantic conclusions ("there is no
   countermodel" vs "there is a countermodel", demonstrated in §4.3). Any bimodal example
   sitting near the boundary is at risk. Worth a separate task to audit bimodal example
   `max_time` values against the guide's 30s convention.
2. **`bimodal.get_theory(subtheories)` ignores its argument.** `get_theory(['extensional'])` and
   `get_theory(['counterfactual'])` return the same object with all 17 operators. Either the
   parameter is unimplemented or the tests using it are misleading. Affects
   `test_comparison_mode_performance` and the builder tests' generated modules.
3. **`tests/utils/base.py::BaseExampleTest.validate_example` does no model checking** — it calls
   `assert_example_structure`, a pure type/shape check. Any test named "batch performance" built
   on it measures list construction. Not a bug, but the naming actively misleads.
4. **Timing is only reproducible with one construction per process** (§5.3). If a real benchmark
   is ever wanted, this is the constraint it must respect.

---

## 10. Verification Evidence

- 5× `pytest -m slow` sweeps: failure sets and per-test durations recorded in §3 and §6.
- Targeted `create_test_model` probes: §4.1, §4.2, §5.2, §5.3.
- Builder example at `max_time` ∈ {1, 5, 20}: §4.3.
- `get_theory` subtheory identity check: §9.2.
- Unfiltered full-suite run (`-m ""`, 2195 collected): see the appended result below.

### Unfiltered run result

```
$ PYTHONPATH=src python -m pytest -q -p no:cacheprovider -m ""
collected 2195 items          # 0 deselected -- filter genuinely disabled

FAILED tests/integration/test_performance.py::TestExecutionPerformance::test_simple_model_performance
FAILED src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerformance::test_multiple_examples_process_efficiently
FAILED src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerformance::test_small_model_generation_completes_quickly
================== 3 failed, 2192 passed in 373.77s (0:06:13) ==================
```

Compare against the baseline recorded in the `addopts` comment block, which was measured before
task 135 landed:

| | `addopts` baseline (before task 135) | This run (HEAD `d1fdbb63`) |
|---|---|---|
| Unfiltered result | 5 failed / 2173 passed in 6:36 | **3 failed / 2192 passed in 6:13** |
| Interpreter abort (exit 139) | intermittent, aborted runs with no summary | **none observed** |
| Failure set stability | "differing failure set run to run" | still unstable — see below |

Two conclusions:

1. **Blocker 1 of the `addopts` note is resolved.** The unfiltered run completed normally with a
   full failure summary. No exit-139 abort occurred in this run, in any of the 5 `-m slow`
   sweeps, or in any targeted probe performed for this research.
2. **Blocker 2 is confirmed still live, and this run is itself fresh evidence of it.** The
   failure set here (3) is a strict *subset* of the `-m slow` sweeps' (4) —
   `test_scaling_with_n[2-1.0]` failed in 4 of 5 sweeps but **passed** in this full run, at the
   same commit on the same machine. That is exactly the set-instability the task was opened to
   fix, reproduced once more. The two builder failures appear in all 6 runs without exception,
   consistent with their being unreachable constants rather than flakes.

---

## 11. Recommended Implementation Phasing

| Phase | Content | Files |
|---|---|---|
| 1 | Narrow the builder file's module-level `pytestmark` to per-test marks | builder `test_performance.py` |
| 2 | Delete the 2 unreachable + 15 vacuous timing assertions | all three test files |
| 3 | Convert the 7 category-(b) tests to behavioural assertions | all three test files |
| 4 | Reduce cap-burn on the 5 expensive tests (§7) | `test_timeout_resources.py`, `test_performance.py` |
| 5 | Remove all remaining `slow` marks from the three files; keep only `test_max_n_itself_is_constructible` marked | all three test files |
| 6 | Delete the `-m "not slow"` clause from `addopts`; rewrite the TEMPORARY comment and the `slow` marker description | `code/pyproject.toml` |
| 7 | Verify: ≥5 repeat unfiltered full sweeps with an **identical** pass set | — |

Phases 1 and 4 are independent of the rest and can land first.
