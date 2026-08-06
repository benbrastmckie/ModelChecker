# Implementation Summary: The `find_countermodel` Timeout/UNSAT Contract

- **Task**: 133 - fix_oracle_self_consistency_disagreements
- **Plan**: `specs/133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md`
- **Status**: PARTIAL — Phases 1-6 complete and verified green; Phase 7 (full-suite verification)
  completed its verification work but the suite did not go green. See "What remains" below.

## What changed

`Z3OracleProvider.find_countermodel()` (`oracle/bimodal_logic/provider.py`) previously collapsed
two opposite outcomes — "formula is provably valid (UNSAT)" and "solver exhausted its budget" —
into the same `None` return. It now raises a dedicated `OracleTimeoutError`
(`oracle/bimodal_logic/errors.py`, new) when the solver does not decide, leaving `None` to mean
exclusively "proven no countermodel". Every caller and every test that encoded the old ambiguous
contract as correct behavior was migrated to the new three-valued one, per CLAUDE.md's
no-backwards-compatibility policy (clean break, no compatibility layer).

### Phase-by-phase

1. **Contract split** (`provider.py`, `errors.py`, `__init__.py`): `find_countermodel()` raises
   `OracleTimeoutError` on `structure.timeout`; `validate_self()` propagates it (gained an
   optional `timeout_ms` parameter, backward-compatible default) rather than catching it.
2. **CLI fix** (`cli.py`): `bimodal-logic check` no longer prints `{"result": "valid"}` for a
   solve it never completed. It now catches `OracleTimeoutError` and prints
   `{"result": "inconclusive", "countermodel": null}` with exit code 2.
3. **Interface/provider test migration** (`test_oracle_interface.py`, `test_oracle_provider.py`):
   every test in the plan's inventory migrated. **Five additional tests were found broken by the
   same root cause when the full suite was actually run** — the plan's "Bucket 1: small
   non-boundary formulas, unaffected by design" classification was wrong for these five, each of
   which constructs a formula that is not actually small/fast (an `all_future` primitive
   expansion that doesn't decide even at 180 s; three `ACTIVE_EXAMPLES` entries; all four
   documented-valid spot-check formulas F4/F7/F9/F10 individually; a discarded-result depth-2
   probe). All five fixed with the same classify-and-skip pattern.
4. **Differential harness** (`test_cross_oracle_differential.py`): introduced `_reference_verdict`
   (shared SAT/UNSAT/TIMEOUT classification), guarded `_generate_differential_report`'s
   previously-unguarded `reference_fn()` call (the plan's named highest-risk point), and fixed a
   counting inversion where a TIMEOUT reference against a decided subject was miscounted as a
   disagreement. Verified via a Z3-free stub oracle proving all three outcomes and both counting
   edge cases in milliseconds.
5. **Budget calibration**: measured conclusive rate at 10000/15000/20000 ms on a bounded
   30-formula sample: 53.3% / 50.0% / 56.7% — flat and noisy, no rung clears the 60% target and
   none shows a real improvement over the last. Extrapolating each rung's sample wall clock to the
   full 548-solve sweep showed 20000 ms alone risks exceeding the Phase 7 90-minute abort ceiling.
   **Kept `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000`** (best-measured, lowest-risk of the three rungs)
   rather than mechanically escalating to the hard ceiling. Added
   `MIN_CONCLUSIVE_SCAN_FORMULAS = 137` (the lowest measurement, 50%, floored and applied to 274)
   and a shared `_assert_scan_report` helper enforcing the two-tooth assertion (zero disagreements
   among conclusive results; a floor on conclusiveness), proven against stubs before being wired
   into the real scan test.
6. **xfail rewrite**: of the five `xfail(strict=True)` tests rooted in this cause, **four** now
   pass unconditionally (their non-agreements were entirely inconclusive, confirmed by observing
   `XPASS(strict)` with the decorator still in place before removing it).
   `test_temporal_only_agreement_complexity_5` is the plan's anticipated exception: 13 of 158
   temporal-only formulas at complexity<=5 have both MC and BH decide and genuinely disagree — a
   real, previously-masked soundness finding kept `xfail`'d with an accurate reason (not this
   task's to fix). All five `reason=` strings rewritten without task-number or `specs/` path
   citations.
7. **Full-suite verification**: see "What remains" below — this is where the session ends.

## What remains (Phase 7 did not achieve a green suite)

The scan-alone run (`test_complexity_5_scan_self_consistent`) completed in 60.1 minutes (well
under the 90-minute abort ceiling) with **zero disagreements** — the plan's central soundness
claim holds — but **failed the conclusiveness floor**: `agreements=106 disagreements=0
timeout_count=168`, i.e. 106/274 (38.7%) conclusive against a floor of 137 (50%). The floor was
calibrated in Phase 5 from a 30-formula sample that only reached complexity 4; the real,
representative full sweep came in lower, confirming a caveat already flagged in the Phase 5
handoff. The floor was deliberately **not** adjusted and re-run in this session (see the Phase 7
handoff for the reasoning) — reported honestly instead, per the coordinator's explicit
instruction to state the actual result rather than force green.

The full two-pass `oracle/run-oracle-suite.sh` run (~76.7 minutes) **FAILED both passes**. Beyond
the scan's floor miss, it surfaced **five additional failures in `test_soundness_regression.py`**
— a file never touched by any phase of this plan and not in its file list. All five share an
identical signature (`OracleTimeoutError` at `temporal_depth=2, M=4, 5000 ms`, raised out of a
test asserting `result is None`) and are the exact same root-cause bug this plan targets,
discovered in a third file the plan's inventory never enumerated. Per the plan's explicit Phase 7
instruction, these are reported here, not fixed — out of scope for this task.

**Recommended follow-up** (not part of this task):
1. A task scoped to `test_soundness_regression.py`'s five affected tests, using the same
   resolved-and-wrong/inconclusive bucketing pattern established in Phases 3 and 6.
2. A task or plan revision to recalibrate `MIN_CONCLUSIVE_SCAN_FORMULAS` from the real 274-formula
   measurement (106, or lower under `-n 6` parallel contention) rather than the optimistic
   30-sample estimate, then re-run `oracle/run-oracle-suite.sh` to confirm green.

## Exit criterion for the downstream regression-baseline task

**Necessary and sufficient to unblock the downstream baseline task**: one complete
`oracle/run-oracle-suite.sh` invocation in which both passes report PASSED and the script exits
0, with the scan's recorded `disagreements` and `timeout_count` captured alongside it. **This
criterion was NOT met in this session.**

**What the actual (non-green) result proves**: at the moment this scan ran, under this machine's
load, no formula in the complexity-5 sweep produced two *conclusive* solves that contradicted
each other (`disagreements=0` over 106 conclusive formulas, real Z3 solving, 60 minutes wall
clock). Because a budget-exhausted solve now raises instead of returning `None`, this is a real
agreement count — which was not true of any previous run of this suite. The suite as a whole is
not yet green because of (a) a floor calibrated from an unrepresentative sample, and (b) five
pre-existing failures in a file outside this plan's scope.

**What it does not prove**: that the disagreement count is stably zero across runs, or that the
suite is currently runnable end to end. Both remain open until the follow-up work above lands.

**Annotation the promoted baseline must carry** (once achieved): the calibrated
`SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` and the (likely-revised) `MIN_CONCLUSIVE_SCAN_FORMULAS`
floor, alongside the actual measured counts. A future failure of
`test_complexity_5_scan_self_consistent` on the *conclusiveness floor* is a budget/performance
regression; a failure on *disagreements* is a semantic regression — these have different causes
and different fixes, and this session's own floor-miss (with zero disagreements) is a clean,
concrete example of that distinction holding up under real, adversarial-scale verification.

## Calibration data reference

- Conclusive rate at 10000/15000/20000 ms (30-formula sample, complexity<=4 only): 53.3% / 50.0%
  / 56.7%. Flat and noisy — the ~50% inconclusive rate is a real limit of what this oracle
  decides in reasonable time at any of these budgets, not an artifact of the specific budget
  chosen.
- Full 274-formula sweep at 10000 ms: 38.7% conclusive (106/274), 0 disagreements, 60.1 min wall
  clock (serial).
- Raw data: `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl`,
  `scan_15s_sample.jsonl`, `scan_20s_sample.jsonl`.

## Plan Deviations

- **Phase 1 sequencing**: created `errors.py` and its `__init__.py` export before writing the RED
  test (rather than strictly "RED first" as the task list's literal ordering implies), so the RED
  failure would be `DID NOT RAISE` (behavior) rather than `ImportError` (wiring), matching the
  plan's own stated success criterion. Content unchanged from what the plan specifies.
- **Phase 2 manual verification**: the plan's `python -m bimodal_logic.cli check ...` command is a
  no-op — `cli.py` has no `if __name__ == "__main__":` guard (pre-existing, out of scope). Used an
  equivalent direct call to `main()` instead.
- **PYTHONPATH throughout**: the plan's verification commands literally set `PYTHONPATH=code/src`.
  `test_oracle_interface.py` hard-imports `bimodal_harness` at module level, which needs
  `../BimodalHarness/src` on the path too (nix's devShell already exports it); a bare override
  drops it and causes `ModuleNotFoundError`. Used `PYTHONPATH="code/src:$PYTHONPATH"` (append, not
  replace) throughout Phases 3-7. `scan_instrumented.py`'s own import needs `oracle/` on the path
  specifically; used `PYTHONPATH="code/src:oracle"` for calibration runs.
- **Phase 3 scope**: five tests outside the plan's stated call-site inventory were found broken by
  the same root cause and fixed using the same pattern (see "Phase-by-phase" above and the Phase 3
  handoff for full detail, including a one-line additive change to `provider.py`'s
  `validate_self()` signature, also outside Phase 3's stated file list but required to carry out
  its own explicit instruction).
- **Phase 5 budget decision**: kept `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` rather than mechanically
  advancing to `20000` at the end of the escalation ladder, based on an extrapolated runtime-risk
  calculation the plan's escalation-rule text does not itself spell out (see the Phase 5 handoff).
- **Phase 7 tool-call mechanics**: per the coordinator's mid-task correction, switched from
  `run_in_background: true` tool calls for every verification to foreground commands tracked by
  PID with bounded waits, reserving the background-with-abort-rule discipline for Phase 7's
  genuinely multi-hour runs (the scan-alone and full-suite runs).
- **Phase 7 outcome**: did not achieve the plan's stated success criterion (green suite). Reported
  honestly per the coordinator's explicit instruction rather than adjusting the floor to force a
  green result that would not have reflected the real, representative measurement, and would not
  have addressed the independent `test_soundness_regression.py` failures regardless.

## Artifacts

- `oracle/bimodal_logic/errors.py` (new)
- `oracle/bimodal_logic/__init__.py`
- `oracle/bimodal_logic/provider.py`
- `oracle/bimodal_logic/cli.py`
- `oracle/bimodal_logic/tests/test_oracle_provider.py`
- `oracle/bimodal_logic/tests/test_oracle_interface.py`
- `oracle/bimodal_logic/tests/test_cli.py`
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl`,
  `scan_15s_sample.jsonl`, `scan_20s_sample.jsonl` (calibration measurements)
- `specs/133_fix_oracle_self_consistency_disagreements/handoffs/phase-{1..7}-handoff-*.md`
- `specs/133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md`
  (annotated in place, phase headings and task checkboxes updated)
