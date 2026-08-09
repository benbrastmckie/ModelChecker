# Oracle Gating-Suite Baseline: STATUS

**Date:** 2026-08-09
**Verdict:** RED. The gating oracle suite does not pass. No baseline was promoted.
**Rubric category:** (c) — a failure that reproduces on a quiet machine.

This file is the honest record that the re-baselining effort produced instead of a green
baseline. It exists because the alternative — quietly widening a solve budget, lowering a floor,
or adding an `xfail` until the suite went green — is the single outcome the baselining work exists
to prevent. **Nothing was weakened.** `git diff --stat -- oracle/bimodal_logic/` is empty: no test
file, assertion, timeout budget, `MIN_CONCLUSIVE_*` floor, marker, or guard was touched.

## What was run

Canonical gating suite, via the canonical runner, from the repository root inside `nix develop`:

```
ORACLE_JUNIT_DIR=<staging> bash oracle/run-oracle-suite.sh
```

No flags, no marker overrides, no budget overrides. 2026-08-09, 13:29:58 → 13:54:26 (24m28s),
runner exit code 1. Full output: `oracle-run-RED-2026-08-09.txt` (Section 1).

```
== oracle suite summary (gating: slow deselected on both passes) ==
pass 1 (parallel, -n 6, not xdist_serial and not slow, budget 1300s): FAILED (exit 1)
pass 2 (serial, xdist_serial and not slow, budget 900s):             TIMED OUT (exit 124)
```

Collection matched the pinned counts exactly: 606 total = 594 gating-parallel + 10 `xdist_serial`
+ 2 `slow`. No collection-count disagreement.

### Machine quietness for this run

| | 1-min load | Foreign process >50% CPU, `z3`, or `lean` |
|---|---|---|
| Before (4 samples, 13:28:40–13:29:25) | 0.34–0.56 | none |
| After (3 samples, 13:54:50–13:55:14) | 1.85–2.22 | none |

Quiet by both criteria. The after-run load figures are the decay tail of this run's own six
workers, sampled 24 seconds after they exited; the criterion that matters — no foreign CPU
consumer, and specifically no `pytest`, `z3`, or `lean --worker` — held at every sample. **This
run is adjudicable, and it is the sole basis for the verdict below.**

## Per-test findings

### 1. Pass 1 — `test_oracle_interface.py::TestMixedFormulas::test_mixed_and_box_next`

- **Failure mode:** `bimodal_logic.errors.OracleTimeoutError` — "Z3 solver did not decide the
  formula within 60000 ms (temporal_depth=1, time_bound M=3); treat as inconclusive, not as a
  proof of validity". Raised at `oracle/bimodal_logic/provider.py:271`.
- **Observations on a quiet machine:** two, independent.
  1. An earlier gating run the same day (13:06–13:16): `1 failed, 586 passed, 3 skipped,
     4 xfailed in 579.39s`, this test the sole failure.
  2. The adjudicable run above (13:29–13:39): `1 failed, 586 passed, 3 skipped, 4 xfailed in
     567.62s`, this test the sole failure.
  The two verdicts are identical down to the counts. This is not a flake signature.
- **Prior evidence:** recorded as failing before, in
  `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/summaries/01_record-external-bh-boundary-defect-summary.md`,
  where it appeared in a `-m "not slow"` pass alongside three others and *did* pass on an isolated
  re-run. That is no longer the picture: it now fails reproducibly under the gating runner on a
  quiet machine.
- **Not done:** the budget was not widened. `TEMPORAL_SOLVE_TIMEOUT_MS`,
  `ATEMPORAL_SOLVE_TIMEOUT_MS`, and the 60000 ms call-site budget are untouched.

### 2. Pass 2 — TIMED OUT at its 900 s budget

Pass 2 completed 7 of its 10 `xdist_serial` tests and was then SIGTERM'd by the runner's
`timeout --kill-after=60s 900` wrapper while executing the 8th.

| # | Test | Verdict in the adjudicable run |
|---|---|---|
| 1 | `test_boundary_regression.py::TestExampleRegression::test_regression_all_active_examples[BM_CM_1-example_case7]` | PASSED |
| 2 | `test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` | **FAILED** |
| 3 | `test_oracle_interface.py::TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement[some_past]` | PASSED |
| 4 | `test_oracle_interface.py::TestMixedFormulas::test_mixed_or_diamond_prev` | PASSED |
| 5 | `test_oracle_interface.py::TestSpotCheckCrossSignal::test_spot_check_individual_countermodels` | **FAILED** |
| 6 | `test_soundness_regression.py::TestStateIsolationRegression::test_100_calls_mixed_temporal_depths` | PASSED |
| 7 | `test_soundness_regression.py::TestStateIsolationRegression::test_sat_unsat_interleaving_stability` | PASSED |
| 8 | `test_soundness_regression.py::TestStateIsolationRegression::test_temporal_propositional_interleaving` | **HUNG → SIGTERM at the 900 s budget** |
| 9 | `test_soundness_regression.py::TestStateIsolationRegression::test_no_semantics_reference_leak_with_temporal` | never reached |
| 10 | `test_soundness_regression.py::TestOracleMFormulaBoundarySafe::test_oracle_m_formula_depth1_boundary_safe` | never reached |

A `TIMED OUT` pass on a verified-quiet machine is itself a listed category (c) trigger, and it is
met here. **The 900 s budget was not raised**, and `ORACLE_PASS1_TIMEOUT` / `ORACLE_PASS2_TIMEOUT`
are unchanged.

Failure *reasons* for tests 2 and 5 are not recoverable from this run: pytest emits tracebacks in
its summary section, which the SIGTERM pre-empted. No JUnit file exists for pass 2 for the same
reason — `--junitxml` is written at session teardown.

### 3. Strict-xfail integrity

No strict-xfail XPASSed. Pass 1's JUnit records `{'pytest.skip': 3, 'pytest.xfail': 4}` — all four
strict xfails in `test_oracle_interface.py` still xfailed, and the sole failure was the
`OracleTimeoutError` above. (A strict-xfail XPASS is reported by pytest as a failure, so it could
not have hidden inside the pass count.)

## Runs that were performed but are NOT evidence

Two further runs were performed and are **excluded from the adjudication** because the machine was
not quiet. Under the plan's protocol a failing run on an unverified-quiet machine "is not evidence
of anything and must not be promoted, triaged, or reported as a result". They are listed only so
the attempts are on the record and so the next dispatch does not repeat them blind.

| Run | Window | Contention found | Outcome (not evidence) |
|---|---|---|---|
| Pass-2 re-run (verbatim runner pass 2, budget unchanged) | 13:58:06–14:13:07 | `lean` at 61.7% and 110% CPU in the before-capture | TIMED OUT again at test 8; tests 1, 2, 5 FAILED |
| Isolated re-run of the 4 failing node IDs, one serial invocation | 14:17–14:28:48 | `lean` at 493% before; `runLinter` at 770–776% plus `lean --worker` at 121–190% after | all 4 FAILED in 662.33 s |

The contender is a Lean lint job in a sibling project
(`cslib/.lake/packages/batteries/.lake/build/bin/runLinter` and its `lean --worker` processes) —
the exact `lean --worker` contention the plan names as documented on this machine.

An earlier revision of the working notes described the pass-2 re-run as running on a verified-quiet
machine. That was a reading error: the live display filter used to inspect the capture files
selected only their section labels and hid the CPU-hog lines the captures had correctly recorded.
The captures were right; the reading was not. The conclusions were revised rather than left
standing.

**Consequence:** `test_spot_check_individual_countermodels`,
`test_known_conclusive_population_self_consistent`, and
`test_regression_all_active_examples[BM_CM_1-example_case7]` are **not** adjudicated here. The
first of these is nonetheless pre-registered in the plan as category (c) "by definition" should it
recur, on the strength of the prior finding in
`specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/summaries/01_record-external-bh-boundary-defect-summary.md`
that it "still times out at a 180000 ms budget even alone".

## What this means for the regression gate

- The committed partial `baselines/oracle-run.txt` was **not** overwritten. It remains the only
  record of the prior state.
- No `baselines/junit-oracle.xml` was written. Pass 1's 594-test JUnit exists in staging, but
  publishing it under that name would misrepresent a partial as the 604-test gating report.
- `code/scripts/verify-refactor.sh` was repaired independently and is committed: Step 3's oracle
  count is re-pinned from a stale 550 to the measured 606 with three new per-marker sub-count pins,
  Step 5 is re-scoped from stale line numbers onto content-matched guard checks (demonstrated to
  fail under all four required mutations), and Step 6 now invokes `oracle/run-oracle-suite.sh`
  instead of an unfiltered pytest that silently dragged the 60–90 minute exhaustive sweep into
  every gating run.
- **The gate is therefore expected to FAIL at Step 6**, and that failure is the honest state of the
  gate, not something to be engineered away. `--skip-oracle` remains the fast path for Steps 1–5
  and 7.

## Follow-up required (not performed here, and deliberately so)

Diagnosing or repairing any of these failures is out of scope for a baselining effort — repairing
a defect inside the task that certifies the baseline is how a "green" baseline stops meaning
anything. A follow-up task should, on a machine with no Lean or Z3 workload:

1. Re-run the gating suite to re-confirm the two adjudicated findings.
2. Adjudicate the three currently-unadjudicated pass-2 failures on a quiet machine.
3. Diagnose why `test_temporal_propositional_interleaving` does not terminate within 900 s, and
   why `test_mixed_and_box_next` no longer decides within 60000 ms at temporal_depth=1, M=3.
4. Only then decide whether any budget is genuinely mis-calibrated — with the measurement to
   justify it, not to rescue a red run.

## Addendum: an in-package failure surfaced by the repaired gate

Running the repaired gate's fast path, `bash code/scripts/verify-refactor.sh --skip-oracle`,
inside `nix develop` on 2026-08-09 gave **exit 1**, with the repaired steps all green and two
untouched steps red:

```
OK: 298 tests collected (baseline 289)                     <- Step 1
OK: 2177 tests collected (baseline 2100)                   <- Step 2
OK: oracle total = 606 (pinned 606)                        <- Step 3, re-pinned
OK: oracle gating-parallel = 594 (pinned 594)
OK: oracle xdist_serial = 10 (pinned 10)
OK: oracle slow = 2 (pinned 2)
OK: sub-counts partition the suite (594 + 10 + 2 = 606)
FAIL: bimodal suite failed on both attempts                <- Step 4, NOT modified
OK (5a): KNOWN_EXTERNAL_DEFECTS.md present and non-empty   <- Step 5, re-scoped
OK (5b): all five guard assertions present exactly once, in the required order
OK (5c): all four floor/budget constants hold their pinned values
OK (5d): all 4 xfail( markers are strict=True
=== Step 6: gating oracle suite run SKIPPED (--skip-oracle) ===
FAIL: compare_bimodal_baseline.sh reported regressions     <- Step 7, NOT modified
2 check(s) FAILED
```

Steps 4 and 7 were deliberately left untouched by the gate repair, so their failures are not
caused by it. Step 4 fails on **both** attempts (the retry allowance for the documented Z3-timing
flake did not absorb it), on the same test each time, with a fast deterministic assertion rather
than a timeout:

```
FAILED code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases[BM_CM_1-example_case7]
>       assert result, f"Test failed for example: {example_name}"
E       AssertionError: Test failed for example: BM_CM_1
E       assert False
code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py:73: AssertionError
1 failed, 297 passed in 138.47s
```

**This is very likely the same underlying defect as the oracle-side failure.** The oracle's
`test_boundary_regression.py::TestExampleRegression::test_regression_all_active_examples[BM_CM_1-example_case7]`
names the same example case, `BM_CM_1` / `example_case7`. The in-package failure is deterministic
and fast, which makes it the better handle on the defect than the oracle-side observation, and it
is independent of any Z3 timing budget.

It was not repaired here: fixing a defect discovered during triage is an explicit non-goal, and
repairing it inside the task that certifies the baseline is how a "green" baseline stops meaning
anything. It is reported as a blocker for a follow-up task.

## Second adjudicable run: the full gate with Step 6 live (2026-08-09, 23:16:57–23:45:56Z)

An independent run of the repaired gate — `nix develop --command bash -c 'bash
code/scripts/verify-refactor.sh'`, no `--skip-oracle`, no `PYTEST_ADDOPTS` — completed in 28m59s
with **exit 1** and **3 check(s) FAILED** (Steps 4, 6, 7). Step 6 *executed*; it was not `SKIPPED`.
Full output: `specs/127_close_oracle_suite_regression_baseline/run2/verify-refactor.txt`.

This is a second, independent observation of the gating suite on a verified-quiet machine, and it
**strengthens the category (c) verdict rather than softening it**. Nothing was weakened to obtain
it: `git diff --stat -- oracle/bimodal_logic/` is still empty.

### Machine quietness for this run

| | 1-min load | Foreign compute job |
|---|---|---|
| Before (3 samples, 23:16:28–23:16:38) | 1.09–1.11 | none; no instantaneous CPU above 12.9%, all Claude sessions |
| During (continuous 60s sampling, 23:27:18–23:45:59, plus a manual capture at 23:26:55) | 2.51–7.97 | none |
| After (3 samples, 23:47:04–23:47:15) | 3.38–4.39 | none |

The load figures above 6 between 23:23 and 23:28 are **this run's own** pass-1 `-n 6` workers: the
23:26:55 capture records four `python3` xdist workers at 99.7% CPU each, with every `lean` process
at ≤5.9% lifetime-average CPU and none appearing in the instantaneous top-20. Raw captures:
`run2/machine-before-phase7.txt`, `run2/machine-during-phase7.txt`, `run2/machine-after-phase7.txt`,
`run2/contention-watch.log`. **This run is adjudicable.**

Deviation recorded: idle cslib `lean --worker` LSP processes were present throughout, which the
quietness rule names categorically. They were adjudicated non-contending on measurement — ≤5.9%
lifetime-average CPU, absent from every instantaneous top-20 sample — not waived by assumption.
This is the same class of deviation Phase 1 recorded for its load-average threshold: a departure
from a numeric convenience criterion, not from any pinned test value or assertion.

### Step 6, pass 1 — a NEW failure alongside the adjudicated one

```
2 failed, 584 passed, 4 skipped, 4 xfailed in 549.76s (0:09:09)
FAILED oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_box_next
FAILED oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_all_future_neg
```

- `test_mixed_and_box_next` — the already-adjudicated failure, reproducing a **third** time, same
  failure mode: `OracleTimeoutError`, 60000 ms, `temporal_depth=1`, `M=3`, raised at
  `oracle/bimodal_logic/provider.py:271`.
- `test_mixed_and_all_future_neg` — **NEW. Not present in any earlier record.** It does not appear
  anywhere in `oracle-run-RED-2026-08-09.txt` (verified: zero occurrences). Identical failure mode
  and identical budget to the above.

The pass-1 verdict has therefore moved from `1 failed, 586 passed, 3 skipped, 4 xfailed` (the
13:29 run) to `2 failed, 584 passed, 4 skipped, 4 xfailed` (this run). Totals reconcile: 594 in
both. **The gating suite is not stable at its current solve budget** — the failing set grew by one
test between two quiet-machine runs on an unchanged tree. The budget was not widened in response.

### Step 6, pass 2 — TIMED OUT again, and it adjudicates two previously-unadjudicable failures

Pass 2 `TIMED OUT (exit 124)` at its unchanged 900 s budget, as in the first adjudicable run.
pytest's summary was again pre-empted by SIGTERM, so per-test IDs are not printed directly; the
per-file progress line is:

```
oracle/bimodal_logic/tests/test_boundary_regression.py F                 [ 10%]
oracle/bimodal_logic/tests/test_cross_oracle_differential.py F           [ 20%]
oracle/bimodal_logic/tests/test_oracle_interface.py ..F                  [ 50%]
oracle/bimodal_logic/tests/test_soundness_regression.py .
```

Mapped against the collection order and per-file grouping already established in the pass-2 table
above (1 boundary + 1 cross-oracle + 3 oracle-interface + 5 soundness = 10) — this is an inference
from ordering, not from printed node IDs:

| # | Test | This run | First adjudicable run |
|---|---|---|---|
| 1 | `test_regression_all_active_examples[BM_CM_1-example_case7]` | **FAILED** | PASSED |
| 2 | `test_known_conclusive_population_self_consistent` | **FAILED** | **FAILED** |
| 3 | `test_enriched_vs_primitive_sat_agreement[some_past]` | PASSED | PASSED |
| 4 | `test_mixed_or_diamond_prev` | PASSED | PASSED |
| 5 | `test_spot_check_individual_countermodels` | **FAILED** | **FAILED** |
| 6 | `test_100_calls_mixed_temporal_depths` | PASSED | PASSED |
| 7 | `test_sat_unsat_interleaving_stability` | in flight at SIGTERM | PASSED |
| 8 | `test_temporal_propositional_interleaving` | never reached | **HUNG → SIGTERM** |
| 9–10 | (remaining) | never reached | never reached |

**Consequence for the three previously-unadjudicated failures.** Two of them are now adjudicated on
a verified-quiet machine, which the earlier record explicitly left open:

- `test_known_conclusive_population_self_consistent` — FAILED on a quiet machine. Adjudicated:
  category (c).
- `test_spot_check_individual_countermodels` — FAILED on a quiet machine. Adjudicated: category
  (c). This also confirms the pre-registration noted above.
- `test_regression_all_active_examples[BM_CM_1-example_case7]` — FAILED here, having PASSED in the
  first adjudicable run. It is now consistent with the deterministic in-package Step 4 failure on
  the same example case, reinforcing that these are one defect and that the in-package test is the
  better handle on it.

`known_conclusive_complexity5.json` was **not** re-derived and `SELF_SCAN_SOLVE_TIMEOUT_MS` was
**not** adjusted in response to any of this.

### Step 4 and Step 7 in the full run

Step 4 failed on both attempts on exactly `test_example_cases[BM_CM_1-example_case7]`
(`1 failed, 297 passed` in 124.96s and 153.23s) — the already-adjudicated defect and no other test.

### `--skip-oracle`: run, exit code recorded, failure confirmed to be the adjudicated one

```
bash code/scripts/verify-refactor.sh --skip-oracle   ->  exit 1, "2 check(s) FAILED"
```

Steps 1, 2, 3 and all of Step 5 (5a–5d) pass. The two failures are Steps 4 and 7, neither of which
the gate repair touched. Step 4's sole failing test on both attempts is again exactly
`test_example_cases[BM_CM_1-example_case7]` (`1 failed, 297 passed` in 133.24s and 140.20s). Full
output: `run2/phase7-verify-refactor-skip-oracle.txt`. Exit 1 here is the **expected** outcome under
the standing category (c) determination; it was recorded, not engineered away.

**Step 7's failure is a consequence of the same defect, not an independent regression finding.**
`code/scripts/compare_bimodal_baseline.sh` runs under `set -euo pipefail`, and its first action is
a pytest pipeline over the same bimodal test file. That pytest exits non-zero because of
`BM_CM_1-example_case7`, `pipefail` propagates it, and `set -e` aborts the script immediately —
its captured output is the single line `Running bimodal test suite...`, before any comparison
logic runs. The gate's message "compare_bimodal_baseline.sh reported regressions" is therefore
misleading in this specific case: nothing was compared. This is recorded, not repaired — Step 7
was deliberately left untouched by the gate repair, and fixing a defect found during triage is an
explicit non-goal.

### Net effect on the verdict

The category (c) verdict stands and is now supported by two independent adjudicable runs. The
gating suite is RED, the gate correctly reports it as RED, and the failing set is **larger** than
first recorded, not smaller.
