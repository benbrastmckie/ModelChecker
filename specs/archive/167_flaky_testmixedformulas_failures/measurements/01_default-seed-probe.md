# Measurement Log: Default-Seed Solve-Cost Probe

Task 167 Phase 2. Determines whether the default-seed Z3 work quantity (measured via `rlimit`,
Z3's load-independent resource-unit counter) for the two flaky `TestMixedFormulas` formulas is
run-to-run deterministic. See the plan's Phase 2/3 for the campaign design and decision rule.

Tool: `oracle/probe_solve_cost.py` (built in Phase 1).

Hard ceiling: 45 minutes of campaign wall clock. A probe hitting its own `timeout` is a recorded
data point, not a blocker.

## Ambient conditions -- before first draw

- Timestamp (UTC): 2026-08-26T07:58:45Z
- `uptime`: `00:58:45 up 1 day 14:50, 1 user, load average: 4.25, 4.30, 5.64`
- `nproc`: 24
- `z3.get_version_string()`: 4.16.0
- `PYTHONHASHSEED`: unset (ambient shell default -- matches production, which never sets it)

## Draws 1-3: `and(neg(A), next(B))` (test_mixed_and_all_future_neg's formula)

`--formula-name mixed_and_all_future_neg --timeout-ms 180000`, default seed, each invocation
prefixed `timeout 240`, foreground, one at a time.

<!-- draws appended below as they complete -->

- Draw 1: `{"formula_name": "mixed_and_all_future_neg", "timeout_ms": 180000, "seed": "default", "wall_s": 105.8135, "decided": true, "rlimit": 363423989, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`
- Draw 2: `{"formula_name": "mixed_and_all_future_neg", "timeout_ms": 180000, "seed": "default", "wall_s": 105.4953, "decided": true, "rlimit": 363423989, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`
- Draw 3: `{"formula_name": "mixed_and_all_future_neg", "timeout_ms": 180000, "seed": "default", "wall_s": 104.6969, "decided": true, "rlimit": 363423989, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`

**Summary for `mixed_and_all_future_neg`**: rlimit = 363423989 on all 3 draws (0% spread, exact
match). wall_s = 105.81 / 105.50 / 104.70 (tight spread here, but that is host-load-dependent, not
Z3-dependent -- the rlimit identity is the signal that matters).

## Draws 4-6: `or(diamond(A), prev(B))` (test_mixed_or_diamond_prev's formula)

`--formula-name mixed_or_diamond_prev --timeout-ms 240000`, default seed, each invocation
prefixed `timeout 300`, foreground, one at a time.

- Draw 4: `{"formula_name": "mixed_or_diamond_prev", "timeout_ms": 240000, "seed": "default", "wall_s": 69.2333, "decided": true, "rlimit": 250005414, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`
- Draw 5: `{"formula_name": "mixed_or_diamond_prev", "timeout_ms": 240000, "seed": "default", "wall_s": 68.5269, "decided": true, "rlimit": 250005414, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`
- Draw 6: `{"formula_name": "mixed_or_diamond_prev", "timeout_ms": 240000, "seed": "default", "wall_s": 70.7327, "decided": true, "rlimit": 250005414, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`

**Summary for `mixed_or_diamond_prev`**: rlimit = 250005414 on all 3 draws (0% spread, exact
match). wall_s = 69.23 / 68.53 / 70.73.

**Conditional PYTHONHASHSEED=0 control**: SKIPPED. Both formulas' rlimit values agree exactly
(0% spread) across all 3 draws each -- the plan's conditional step only fires "if rlimit disagrees
across draws of the same formula", which did not happen for either formula.

## Step 5: Forced repro (verbatim failure texts)

Both target formulas share `temporal_depth=1, M=3`, so both produce a structurally identical
`OracleTimeoutError` message (only `timeout_ms` varies with the budget given).

**Provider-level (`OracleTimeoutError.__str__()`)**, captured via a direct
`Z3OracleProvider().find_countermodel(formula, timeout_ms=2000)` call for each formula
(`timeout 60`-bounded, `python3 -c` one-liner, not committed -- exploratory only):

```
STR: Z3 solver did not decide the formula within 2000 ms (temporal_depth=1, time_bound M=3); treat as inconclusive, not as a proof of validity | Suggestion: Increase timeout_ms, or reduce the formula's temporal_depth, and retry; a timeout is not evidence the formula is valid.
CONTEXT: {'timeout_ms': 2000, 'temporal_depth': 1, 'M': 3}
```

Identical for both `mixed_and_all_future_neg` and `mixed_or_diamond_prev` (both have
`temporal_depth=1`, `M=3`).

**pytest-level (JUnit `<failure>` text)**, captured by temporarily lowering
`test_mixed_and_all_future_neg`'s `timeout_ms` from `60000` to `100` (single-line scratch edit),
running `timeout 120 env PYTHONPATH=code/src pytest
"oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_all_future_neg"
-v`, capturing the failure verbatim, then reverting the scratch edit immediately (confirmed via
`git diff --stat` showing no change):

```
>                   raise OracleTimeoutError(
                        timeout_ms=timeout_ms,
                        temporal_depth=depth,
                        M=M,
                    )
E                   bimodal_logic.errors.OracleTimeoutError: Z3 solver did not decide the formula within 100 ms (temporal_depth=1, time_bound M=3); treat as inconclusive, not as a proof of validity | Suggestion: Increase timeout_ms, or reduce the formula's temporal_depth, and retry; a timeout is not evidence the formula is valid.

oracle/bimodal_logic/provider.py:271: OracleTimeoutError
```

This confirms: the pytest-level failure text does NOT contain the string `Test failed for
example:` (`FAILURE_SIGNATURE` in `.github/scripts/unstable_watch_classify.py`) -- the
plan's stated defect in the naive `MAX_TIME_BY_NODEID_FRAGMENT` fallback is confirmed directly
from real captured text, not assumed. The stable, matchable substring across any budget is
`bimodal_logic.errors.OracleTimeoutError: Z3 solver did not decide the formula within`.

Scratch-edit revert confirmed: `git diff --stat oracle/bimodal_logic/tests/test_oracle_interface.py`
produced no output (byte-identical to the pre-edit committed state).

## Step 6: CI history query (bounded, non-blocking)

`timeout 60 gh auth status` -- authenticated (benbrastmckie). `timeout 60 gh run list
--workflow=tests.yml --limit 20` and `timeout 60 gh run list --workflow=unstable-watch.yml
--limit 30` both succeeded within budget.

**Structural finding (more precise than a raw run count)**: neither `test_mixed_and_all_future_neg`
nor `test_mixed_or_diamond_prev` can have a recorded CI **serial** failure at all, because no
GitHub Actions workflow currently invokes `oracle/bimodal_logic/tests/test_oracle_interface.py`'s
regular (non-`unstable`) selection:
- `.github/workflows/tests.yml`'s `general-tests` job runs `pytest tests/ src/model_checker`
  (rooted at `code/`) -- it never reaches `oracle/`. Its own comment at line 120 only draws an
  analogy to `oracle/run-oracle-suite.sh`'s two-pass structure; it does not invoke that script.
- `.github/workflows/differential-tests.yml` runs only
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`'s specific classes -- not
  `test_oracle_interface.py`.
- `.github/workflows/unstable-watch.yml` runs `oracle/bimodal_logic/tests/ -m unstable` -- would
  only pick up either target test if it were already `unstable`-marked, which neither is as of
  this campaign.
- No workflow file greps for `run-oracle-suite`, confirming `oracle/run-oracle-suite.sh` (the
  script `test_mixed_and_all_future_neg`'s docstring refers to when it says "If this test ever
  fails SERIALLY") is not wired into any GitHub Actions trigger.

Confirms directly (not merely records unavailability): the "if this test ever fails SERIALLY"
watch item in `test_mixed_and_all_future_neg`'s docstring can only have been observed from a
**local** developer serial run, never from CI -- there is no CI serial-run history to mine because
no CI job runs this selection. This does not block the phase; it is itself the answer to the
open item ("was CI flake-rate history available and did it confirm a serial failure").

## Ambient conditions -- after last draw

- Timestamp (UTC): 2026-08-26T08:10:13Z
- `uptime`: `01:10:13 up 1 day 15:01, 1 user, load average: 4.39, 4.57, 5.12`
- Campaign wall clock elapsed: ~11.5 minutes (well within the 45-minute ceiling; no ceiling event).

## Campaign completion

All 6 primary draws completed (3 per formula), plus Step 5 (both verbatim failure texts) and
Step 6 (CI history query). No draw hit its per-invocation `timeout`. The conditional
`PYTHONHASHSEED=0` control was not needed (no rlimit disagreement observed). Proceeding to
Phase 3's decision gate with a complete, non-partial campaign.

## ROUTE DECISION

**Route A** is selected.

**Rule applied**: "Route A if, for both formulas, the rlimit values across draws agree within 5%
of their minimum."

**Deciding numbers**:

| Formula | rlimit draws | min | max | spread |
|---|---|---|---|---|
| `mixed_and_all_future_neg` | 363423989, 363423989, 363423989 | 363423989 | 363423989 | 0% |
| `mixed_or_diamond_prev` | 250005414, 250005414, 250005414 | 250005414 | 250005414 | 0% |

Both formulas' spread (0%) is well under the 5% threshold, and both have 3 (>= 2) completed
draws. Neither Route B trigger condition (>5% spread after PYTHONHASHSEED=0 control, or <2
completed draws) applies. Route A is the unambiguous outcome of the decision rule -- not a close
call.

**Excluded route**: Route B (Phase 6, the `unstable` fallback) is not taken. Phase 6 closes
`[COMPLETED WITH EXCLUSIONS]` in the plan file, with a `#### Reasoned Exclusions` record naming
this measurement (0% rlimit spread on both formulas, well under the 5% Route B threshold).
