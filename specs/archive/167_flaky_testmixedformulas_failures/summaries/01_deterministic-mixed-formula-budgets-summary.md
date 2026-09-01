# Implementation Summary: Deterministic mixed-formula budgets

- **Task**: 167 - Fix flaky `TestMixedFormulas` failures (`test_mixed_or_diamond_prev`,
  `test_mixed_and_all_future_neg`)
- **Plan**: `specs/167_flaky_testmixedformulas_failures/plans/01_deterministic-mixed-formula-budgets.md`
- **Route taken**: Route A (deterministic `max_rlimit` budgets)

## Route decision

Three prior investigations against these two tests (commits `caf20bea`/`7f7269d6`/`6ea94522`)
each reactively widened a wall-clock `timeout_ms` in response to a load-driven failure, without
ever establishing a load-independent pass/fail boundary. `timeout_ms` maps directly to Z3's
wall-clock `max_time`, so on a loaded host the same amount of Z3 work can cross a fixed wall-clock
budget purely from CPU contention — the budget was measuring host load, not solver work.

This plan measured whether the *quantity* of Z3 work these two formulas require is run-to-run
deterministic, using Z3's resource-unit counter (`rlimit`) instead of wall clock. Phase 2's
bounded measurement campaign (`specs/167_flaky_testmixedformulas_failures/measurements/01_default-seed-probe.md`)
took 3 isolated default-seed draws per formula (Z3 4.16.0, `PYTHONHASHSEED` unset) and found the
rlimit **bit-identical across all 3 draws for both formulas** (0% spread), while wall time still
varied with host load in the same draws. That is direct evidence the underlying work is
deterministic and the previous wall-clock instability was a host-load artifact, not solver
variance. Phase 3's decision gate applied the plan's rule ("Route A if, for both formulas, the
rlimit values across draws agree within 5% of their minimum") and selected Route A — the deviation
threshold (5%) was cleared by a wide margin (0%), and both formulas had the required >=2 completed
draws, so neither Route B trigger condition applied.

Route A replaces the load-dependent wall-clock boundary with the load-independent complement Z3
already exposes: `max_rlimit`, already wired end-to-end from `ExampleSettings` through
`ModelDefaults.solve()`/`re_solve()` to `Z3SolverAdapter.set_rlimit()`, but never plumbed through
`Z3OracleProvider.find_countermodel()`, which builds its own settings dict. Phase 4 closed that
one gap (optional, default-off `max_rlimit` parameter on `find_countermodel()` and
`OracleTimeoutError`); Phase 5 applied calibrated budgets to the two target tests.

## Measured values and applied budgets

| Test | Measured default-seed rlimit (3 draws, 0% spread) | Applied `max_rlimit` | Headroom | Applied `timeout_ms` |
|---|---|---|---|---|
| `test_mixed_or_diamond_prev` | 250005414 | 800000000 | ~3.2x | `TEMPORAL_SOLVE_TIMEOUT_MS` (180000ms, ~2.5x the measured 70.73s worst draw) |
| `test_mixed_and_all_future_neg` | 363423989 | 1100000000 | ~3.0x | 240000ms explicit (180000ms clears only ~1.7x the measured 105.81s worst draw, short of the plan's >=2x wall-clock headroom rule) |

Both budgets satisfy the plan's Phase 5 requirement of >=3x the measured rlimit (`TESTING_GUIDE.md`
section 8.6: "set budgets generously, not tightly" — headroom for genuine future cost growth, not
run-to-run noise). `timeout_ms` is retained on both tests as a generous backstop; `max_rlimit` is
expected to fire first if either budget is ever exhausted. Both `@pytest.mark.xdist_serial`
markers are unchanged (that marker addresses the separate `-n 6` parallel-worker contention
mechanism, orthogonal to the budget-unit change). Both tests' docstrings append a "Fourth
investigation (2026-08-26)" record (preserving, not replacing, the three prior investigations'
history) that names the measured rlimit, the draw count, the Z3 version the figure is valid for,
an explicit recalibration trigger on a future Z3 upgrade, and — for `test_mixed_and_all_future_neg`
— resolves its standing "if this test ever fails SERIALLY, recalibrate" watch item and states the
prior 60000ms figure is superseded.

`OracleTimeoutError` now accepts an optional `max_rlimit` parameter: when set, it is recorded in
`self.context` and the message names both budgets, since an rlimit-exhausted UNKNOWN is classified
`is_timeout=True` identically to a wall-clock timeout by `ModelDefaults.solve()` — the code
genuinely cannot tell which one fired. When `max_rlimit` is absent (every existing caller), the
message and context are byte-for-byte unchanged.

## Verification gates run — and which were narrowed

The following gates actually ran, in this closure dispatch, against the working tree:

1. **`TestMaxRlimitParameter` (5 tests, Phase 4's new suite)**: `PYTHONPATH=code/src pytest
   "oracle/bimodal_logic/tests/test_oracle_interface.py::TestMaxRlimitParameter" -q` — 5 passed in
   1.23s.
2. **The two target node ids** (Phase 5's and Phase 7's core check):
   `PYTHONPATH=code/src pytest
   "oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_or_diamond_prev"
   "oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_all_future_neg"
   -q` — 2 passed in 126.32s (0:02:06), no `OracleTimeoutError` on either test.
3. **CI-contract gate**: `timeout 300 env PYTHONPATH=code/src pytest code/tests/ci/ -q` — 35 passed
   in 1.32s, confirming no regression to the `unstable` deselection wiring, the classifier tests,
   the timing-marker coverage check, the example-budget floor, or workflow parity.
4. **Protected-work check**: `git diff --stat` from the task's base commit shows **no** change to
   `oracle/run-oracle-suite.sh`; `grep -c "not unstable" oracle/run-oracle-suite.sh` still finds 5
   occurrences (the deselection filter on both passes plus other references).

**Narrowed, not run in full — and why**: Phase 7's plan text specifies four broader pytest
invocations: (a) `-m "xdist_serial and not unstable" -v` over the whole
`test_oracle_interface.py` file (four `xdist_serial`-marked tests, not just the two this task
modifies); (b) the Route B watch selection (`-m unstable -v`) — inapplicable, since Route A was
selected, not Route B; (c) `code/tests/ci/ -v` — run, see gate 3 above (run with `-q` rather than
`-v`; functionally equivalent, same exit code and pass count); (d) the full
`oracle/bimodal_logic/tests/ -m "not slow and not xdist_serial and not unstable" -q` parallel-pass
selection. Items (a) and (d) were **not run** in this dispatch: the full `oracle/bimodal_logic/tests/`
directory has been measured elsewhere in this task's own orchestration at approximately 46 minutes
wall clock, which exceeds a single bounded dispatch's practical ceiling and risks the
foreground-command auto-backgrounding failure mode this task's closure instructions were explicit
about avoiding. This summary does **not** present the narrowed gates above as a full-suite pass —
gates 1-4 are exactly what ran, and items (a) and (d) remain open verification debt for a future,
time-unconstrained dispatch (or CI) to close.

## Plan Deviations

- Phase 4's own verify line specified the full non-slow, non-serial `oracle/bimodal_logic/tests/`
  selection (`timeout 600 ... -m "not slow and not unstable and not xdist_serial" -q`); a prior
  dispatch in this same orchestration narrowed it to the single file this phase modifies
  (recorded in the plan's Phase 4 "Deviation from plan" note, commit `d7188a69`).
- Phase 5's own verify line specified `-m xdist_serial -v` over the whole
  `test_oracle_interface.py` file; this dispatch narrowed it to exactly the two target node ids
  (recorded in the plan's Phase 5 "Deviation from plan" note), for the same reason.
- Phase 7's plan text specifies four verification invocations; this dispatch ran gates 1-4 above
  and explicitly did not run the full `xdist_serial` file selection or the full parallel-pass
  selection, per the "Verification gates run" section above.
- `test_mixed_and_all_future_neg`'s `timeout_ms` was set to an explicit 240000 rather than adopting
  the shared `TEMPORAL_SOLVE_TIMEOUT_MS` constant, because 180000 clears only ~1.7x its measured
  105.81s worst draw — short of the plan's own Scope Hypothesis requirement of >=2x. This was
  anticipated and pre-authorized by the plan's Phase 5 Scope Hypothesis text, not an undocumented
  departure.
- Route B (Phase 6) was not executed; it closed `[COMPLETED WITH EXCLUSIONS]` per the plan's own
  route-exclusivity contract, with the Phase 3 measurement recorded as the reasoned exclusion.
