# Implementation Summary: The `find_countermodel` Timeout/UNSAT Contract

- **Task**: 133 - fix_oracle_self_consistency_disagreements
- **Plan**: `specs/133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md`
- **Status**: COMPLETED — all 7 phases complete. The plan's substantive claim is verified green
  against the correct vehicle; the gating suite is separately RED on three timeout-shaped,
  out-of-scope failures. Both outcomes are documented precisely below.

## The original premise was wrong, and that is the headline result

The task was created to fix "N disagreements" in the oracle's self-consistency scan — a
self-comparison returning contradictory verdicts for the same formula, which would be a real
correctness defect. **There were never any disagreements.** Three full 274-formula sweeps have now
measured `disagreements=0`. What the scan had been reporting as disagreements were solver
*timeouts* being laundered into false verdicts.

`Z3OracleProvider.find_countermodel()` collapsed two opposite outcomes — "formula is provably
valid (UNSAT)" and "solver exhausted its budget" — into the same `None` return, discarding the
`structure.timeout` signal that `model_checker.models.structure` deliberately keeps separate. Two
solves of a boundary formula could land on opposite sides of "finished", and the scan would score
that as a semantic contradiction. The disagreement count was a load-dependent quantity wearing a
soundness claim's clothing.

The fix makes the contract three-valued: `None` now means exclusively "proven no countermodel",
and an undecided solve raises `OracleTimeoutError`. Per CLAUDE.md's no-backwards-compatibility
policy this was a clean break with no compatibility layer, so every caller and every test
encoding the old contract was migrated.

## What changed, by phase

1. **Contract split** (`provider.py`, new `errors.py`, `__init__.py`): raises `OracleTimeoutError`
   on `structure.timeout`; `validate_self()` propagates rather than catching, since a spot check
   that cannot obtain a verdict is a tooling problem, not evidence of unsoundness.
2. **Live CLI bug fixed** (`cli.py`): `bimodal-logic check` no longer prints
   `{"result": "valid"}`, exit 0, for a solve it never completed. It emits
   `{"result": "inconclusive", "countermodel": null}` with exit code 2 — a distinct code so a
   consuming script can tell "we don't know" from both "valid" and "bad input". This was a
   user-facing correctness bug, not just a test-harness one.
3. **Interface/provider test migration**: every test in the plan's inventory. **Five additional
   tests outside that inventory were found broken by the same root cause** once the suite was
   actually run — the plan's "small non-boundary formulas, unaffected by design" bucket was wrong
   for them (an `all_future` primitive expansion that does not decide even at 180 s; three
   `ACTIVE_EXAMPLES`; all four documented-valid spot-check formulas; a discarded-result depth-2
   probe). All fixed with the same classify-and-skip pattern.
4. **Differential harness**: added `_reference_verdict` (shared SAT/UNSAT/TIMEOUT classification),
   guarded `_generate_differential_report`'s previously-unguarded `reference_fn()` call (the
   plan's named highest-risk point), and fixed a counting inversion where a TIMEOUT reference
   against a decided subject was scored as a *disagreement* — the exact false-alarm inversion of
   the bug being fixed. Proven with a Z3-free stub oracle in milliseconds.
5. **Budget calibration and the two-tooth assertion**: kept `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000`
   after measuring that conclusiveness is essentially budget-independent in the 10-20 s range
   (53.3% / 50.0% / 56.7% on bounded samples — flat and noisy). Added `_assert_scan_report`,
   which separates the *soundness* claim (`disagreements == 0`, zero tolerance) from the
   *performance* claim (a floor on conclusiveness), so the scan can never degrade into
   "everything was inconclusive, therefore zero disagreements, therefore pass".
6. **xfail rewrite**: four of five `xfail(strict=True)` tests now pass unconditionally (their
   non-agreements were entirely inconclusive). `test_temporal_only_agreement_complexity_5` stays
   `xfail` on a genuine, separate soundness finding: 13 of 158 temporal-only formulas have both
   oracles decide and disagree. All five `reason=` strings rewritten without task-number or
   `specs/` path citations.
7. **Verification** — below.

## Verification: what is green and what is not

### Green — the plan's actual claim

`oracle/run-oracle-exhaustive-scan.sh` completed against HEAD
(`oracle/scan-results/20260807T155847Z/`, `SCAN_COMPLETE` marker present):

| Metric | Value |
|---|---|
| Total formulas | 274 |
| Conclusive (both sides decided) | 103 |
| **Disagreements among conclusive results** | **0** |
| Inconclusive | 171 |
| Wall clock | 3651.2 s (60.9 min), serial |

Counts were recomputed independently from the 274 raw `report.json` entries rather than trusted
from its summary fields, and reproduce exactly. Against the deployed floor,
`conclusive = 103 >= 90`: both teeth of the assertion pass, so
`test_complexity_5_scan_self_consistent` passes at HEAD.

Zero disagreements now holds across three full sweeps (101/274 at 5000 ms pre-fix; 106/274 and
103/274 at the deployed 10000 ms). The 106-vs-103 spread at an identical budget is the run-to-run
variance the floor of 90 was deliberately set *below*.

### Not green — the gating suite, on three timeout-shaped failures

`oracle/run-oracle-suite.sh` is RED on both passes (pass 1: 1 failed / 557 passed / 2 skipped /
4 xfailed, 671.62s; pass 2: 2 failed / 8 passed, 740.90s). **Every failure is a timeout or
conclusiveness failure. Not one is a disagreement.** Each was isolated in its own pytest session
rather than guessed at:

| Test | Isolated | Disposition |
|---|---|---|
| `TestTernarySerializationAll::test_all_sat_task_relation_ternary` | PASSED, 26.35s vs 180 s budget | Contention artifact — a 26 s solve cannot exhaust 180 s absent severe external load. |
| `TestSpotCheckCrossSignal::test_spot_check_individual_countermodels` | PASSED, 131.42s vs 180 s budget | The known same-session Z3-state flake, already classified pre-existing/environmental by the quantifier-aliasing work; `xdist_serial` does not close it. |
| `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` | FAILED 99/103, then 98/103, then **PASSED 100/103** | Straddles its floor. See below. |

**The run was measurably contended, not presumed so.** A `ps` check immediately before launch was
clean, but a sibling task's `pytest code/tests/integration/...` appeared mid-run at ~100% CPU, and
an unrelated `pytest -m slow` was still at 84-94% CPU afterwards. Pass 2 — nominally the
contention-free serial pass — ran 66% over its measured basis (740.90s vs ~446s), the signature of
load originating outside the suite. `run-oracle-suite.sh`'s own header anticipates this and states
the required response: *"Never widen these timeouts, or `MIN_CONCLUSIVE_GATING_FORMULAS`/
`MIN_CONCLUSIVE_SCAN_FORMULAS`, to paper over a contended run -- re-run when the machine is idle
instead."* **No constant was touched.**

### The one reproducing failure is a calibration finding worth acting on

`TestGatingConclusiveScan` was run three further times alone: conclusive counts of **99, 98, and
100** against a floor of exactly **100**, with `disagreements=0` every time. It passes only when it
lands at the very top of its own observed range — a coin-flip gate.

This is the same mistake this plan already corrected once for its own constant, where
`MIN_CONCLUSIVE_SCAN_FORMULAS` moved from 137 (set at an optimistic sample's level, permanently
failing) down to 90 (below every real measurement, stable). `MIN_CONCLUSIVE_GATING_FORMULAS = 100`
against an observed `{98, 99, 100}` needs the same re-floor. Consistent with that reading, the
constant's own comment records that the manifest population's slowest conclusive solve was
**10.094s against a 10000 ms budget — about 0.9% *over* nominal**, leaving under 1% headroom on its
slowest member.

It was deliberately **not** changed: it is another task's constant guarding another task's
manifest, and its own comment directs an investigator to "investigate instead" of raising it.
Recommending the re-floor is in scope; performing it is not.

## Exit criterion for the downstream regression-baseline task

**The criterion as originally written is stale and must not be applied verbatim.** It names
`oracle/run-oracle-suite.sh` as the vehicle. That script now deselects `slow` on *both* passes and
does not execute the scan at all, so a green run of it confirms nothing about this plan's claim and
a red one does not refute it. `oracle/run-oracle-exhaustive-scan.sh` is the correct and only
vehicle (`code/docs/core/TESTING_GUIDE.md` section 8.8).

**Against the correct vehicle the criterion is met**: a complete run reaching `SCAN_COMPLETE` with
`agreements=103 disagreements=0 timeout_count=171`, counts recorded here and in
`evidence/verification-results.md` — satisfying the criterion's own rule that a green run whose
counts were not captured does not count.

**What that proves**: no formula in the complexity-5 sweep produced two conclusive solves that
contradicted each other. Because a budget-exhausted solve now raises instead of returning `None`,
an agreement in that run is a real agreement — which was not true of any previous green run of this
suite.

**What it does not prove**: that the conclusive count is stable run to run (it is not — 101, 103,
106 across three sweeps), or that the gating suite is currently green (it is not).

**Annotation the promoted baseline must carry**: `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` and
`MIN_CONCLUSIVE_SCAN_FORMULAS = 90`, alongside the measured counts. A future failure on the
*conclusiveness floor* is a budget/performance regression; a failure on *disagreements* is a
semantic regression. These have different causes and different fixes, and conflating them is what
consumed four consecutive triage efforts in this line of work. Everything observed in Phase 7 —
across two dispatches, three sweeps, and three gating failures — landed cleanly in the budget
bucket, which is the contract fix working as designed.

## Recommended follow-up (not this task)

1. **Re-floor `MIN_CONCLUSIVE_GATING_FORMULAS`** from the real observed distribution `{98, 99,
   100}` to a value below it, mirroring the 137 -> 90 correction made here. Owned by the
   gating-manifest work, not this task.
2. **Decide the disposition of `test_spot_check_individual_countermodels`'s same-session Z3-state
   sensitivity**, which `xdist_serial` demonstrably does not close.
3. **Investigate the 13 genuine temporal-only disagreements** kept `xfail`'d in
   `test_temporal_only_agreement_complexity_5` — a real soundness finding this contract fix
   surfaced by removing the noise that had been hiding it.

## Plan Deviations

- **Phase 1 sequencing**: created `errors.py` and its export before writing the RED test, so the
  RED failure would be `DID NOT RAISE` (behavior) rather than `ImportError` (wiring), matching the
  plan's own stated success criterion.
- **Phase 2 manual verification**: the plan's `python -m bimodal_logic.cli check ...` command is a
  no-op — `cli.py` has no `if __name__ == "__main__":` guard (pre-existing, out of scope). Used an
  equivalent direct `main()` call.
- **PYTHONPATH throughout**: the plan's literal `PYTHONPATH=code/src` drops `../BimodalHarness/src`,
  which `test_oracle_interface.py` hard-imports, causing `ModuleNotFoundError`. Used
  `PYTHONPATH="code/src:$PYTHONPATH"` (append, not replace).
- **Phase 3 scope**: five tests outside the plan's inventory were found broken by the same root
  cause and fixed with the same pattern, plus a one-line additive `timeout_ms` parameter on
  `validate_self()` required to carry out Phase 3's own instruction.
- **Phase 5 budget decision**: kept 10000 ms rather than mechanically advancing to the 20000 ms
  ceiling, based on a runtime-risk extrapolation the plan's escalation rule does not itself spell
  out.
- **Phase 7 vehicle correction**: the plan's stated verification vehicle
  (`oracle/run-oracle-suite.sh`) became stale mid-task when the gating/exhaustive split moved the
  scan to `oracle/run-oracle-exhaustive-scan.sh`. Verified against the correct vehicle and
  annotated the stale instruction in place rather than reporting a false green from a script that
  no longer runs the test in question.
- **Phase 7 blockers already closed**: the two soft blockers carried into the final continuation
  (recalibrate the floor from 137; migrate `test_soundness_regression.py`) were already resolved at
  HEAD by commit `c8087c4d`. Verified directly rather than assumed, and attributed to that commit
  rather than claimed as this dispatch's work.
- **Phase 7 out-of-scope failures not fixed**: three gating failures were classified with isolation
  and repeat runs but not fixed, per the plan's own "report it and stop" instruction and the
  suite's explicit prohibition on adjusting constants to paper over a contended run.
- **`grep -c "if result is not None"` returns 1, not 0**, in `test_oracle_interface.py`. The
  survivor is inside a `try/except OracleTimeoutError` that already classifies the inconclusive
  case, so it is a genuine assertion branch rather than a masking guard. The grep was a proxy for
  "no masking guards remain"; that property holds.

## Artifacts

- `oracle/bimodal_logic/errors.py` (new), `__init__.py`, `provider.py`, `cli.py`
- `oracle/bimodal_logic/tests/test_oracle_provider.py`, `test_oracle_interface.py`, `test_cli.py`,
  `test_cross_oracle_differential.py`
- `specs/133_fix_oracle_self_consistency_disagreements/evidence/verification-results.md`
  (consolidated measurements), `scan_10s_sample.jsonl`, `scan_15s_sample.jsonl`,
  `scan_20s_sample.jsonl`
- `specs/133_fix_oracle_self_consistency_disagreements/run/gating-suite-head-1786212046.log`,
  `isolate-1786213644.log`, `gating-conclusive-repeats-*.log` — **local-only, not committed**
  (`.gitignore:7` excludes `*.log`). Every number drawn from them is transcribed into this summary,
  `evidence/verification-results.md`, and the Phase 7 handoff, which are tracked.
- `specs/133_fix_oracle_self_consistency_disagreements/handoffs/phase-{1..7}-handoff-*.md`
- `specs/133_fix_oracle_self_consistency_disagreements/plans/02_find-countermodel-contract.md`
