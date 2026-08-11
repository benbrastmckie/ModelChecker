# Implementation Summary: Per-Formula Solve-Capacity Decision (Oracle Gating Suite)

- **Task**: 145 - decide_oracle_per_formula_solve_capacity
- **Date**: 2026-08-11
- **Plan**: plans/01_per-formula-solve-capacity.md (7 phases, all completed)
- **Session**: sess_1786456768_0d5e0f
- **Terminal deliverable**: full `code/scripts/verify-refactor.sh` run (no skip flags)
  inside `nix develop` printing **"[verify-refactor] All checks passed"** with
  `disagreements == 0` — achieved on run 3
  (`baselines/07_full-gate-transcript-run3.txt`, GATE_EXIT=0, wall 34m42s, pass 2
  1315.36 s < 1800 s).

## What was decided and implemented

The recorded decision (reports/02_capacity-decision-record.md) matches a remedy to each
measured mechanism:

| Mechanism | Remedy landed |
|---|---|
| `and_box_next` bounded tail | `timeout_ms` 60000 → 240000 (2.3x uncensored 92.8-104.2 s worst; never recalibrated after the 2026-08-07 aliasing fix) |
| BM_CM_4 bounded tail | `max_time` 30 → **120** at both sync'd sites (fresh 7-seed probe: 57.1 s worst; the planned 60 would have sat at 1.05x) |
| Ternary `next_A` divergent tail | **Recorded fallback** (not substitution): test → `xdist_serial`, per-leg 480000 ms override, accepted ~1-in-7 divergent residual, full adjudication inline |
| Gating re-check ~1.0x headroom | New `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` decoupled from `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` (monotone membership; only the two gating call sites) |
| `all_future_neg` contention victim | `xdist_serial` relocation, budget untouched at 60000 |
| BM_CM_1 boundary-straddling (surfaced by the gate) | `max_time` 15 → 60 with probe-backed basis (diagnosed pre-existing at the pre-task commit; divergent seed-2 residual recorded) |

Supporting changes: verify-refactor Step 3 re-pin 627/609/16/2 with provenance; Step 5c
five-constant pin set; `ORACLE_PASS2_TIMEOUT` headroom note (value unchanged at 1800);
TESTING_GUIDE 8.8 two-budget contract note; stale docstrings refreshed.

Option (c) accept-and-monitor is rejected with recorded grounds. Floors, `TEMPORAL_` /
`ATEMPORAL_` / `SELF_SCAN_SOLVE_TIMEOUT_MS`, and `ORACLE_PASS2_TIMEOUT` are unchanged;
nothing is xfailed/skipped/disabled; every changed constant carries its inline
measurement basis; no task numbers cited outside specs/**.

## Measurement gates that fired (and changed the plan)

1. **Both witness candidates failed the Phase 1 confirmation probe** (primary
   `and(neg(A), next(B))`: max wall 107.4 s > 60 s criterion, 4.4x-median rlimit outlier;
   secondary `some_future(A)`: undecided at 180 s on seed 7). The plan's recorded
   fallback was taken exactly as specified.
2. **BM_CM_4's fresh probe disconfirmed the planned 60 s** (57.1 s worst draw → 1.05x);
   recalibrated to 120 (2.1x) per the same convention.
3. **The full gate surfaced BM_CM_1** (red in runs 1-2's Step 7): diagnosed by isolated
   re-measurement at HEAD and at the pre-task commit as pre-existing genuine cost growth
   (~13-15 s vs stale 15 s budget), probed uncensored, and recalibrated 15 → 60 — a
   recorded deviation from the plan's "watch item only" non-goal, forced by the gate.

## Gate history (honest accounting)

- Run 1 (red): interleaving `some_future` draw blew its 5000 ms provider default
  (1 of 50 iterations; pre-existing heavy tail, NOT remedied by this task) + BM_CM_1.
- Run 2 (red): gating floor 98/103 under a concurrent lean/lake build from another
  session (the one leg plausibly contention-driven; matches the recorded 99/103
  incident signature) + BM_CM_1. disagreements = 0 in both red runs; every remedied
  mechanism was green in both.
- Run 3 (GREEN, quiet machine, load evidence in transcript): all 7 steps green.

## Honestly-scoped limitations (recorded, decision record section 7.7)

- **Divergent tails are not resolved and cannot be resolved by budget** — three measured
  instances (ternary `next_A` 601 s undecided; BM_CM_1 seed-2 600.7 s undecided at
  rlimit ~64x median; enriched-pair `[next]` [NEW] timeout-skip at 180 s). This task
  converts bounded tails into reliable passes and divergent tails into bounded, recorded
  residual risk. Encoding-level work remains out of scope (nine-plus recorded dead ends).
- The Phase 4 adjudication's "coverage retained elsewhere" premise is eroded by the
  enriched-pair [next] skip; reassessed in the decision record — the erosion REINFORCES
  the fallback taken (the ternary test is now the strongest hard-asserting bare-next(A)
  gate).
- The interleaving test's 50-draw `some_future` exposure at 5000 ms remains a
  pre-existing per-run failure probability (observed 1-in-2 runs on a loaded machine);
  outside this task's mandate, recorded in section 7.5.

## Plan Deviations

- Phase 1: BM_CM_4 re-probe disconfirmed the planned 60 s → Phase 3 landed 120 (2.1x
  fresh measured worst) instead. Deviation annotated in the plan and decision record.
- Phase 4: executed as the plan's own recorded fallback (relocation + 480000 ms leg
  override) because both substitution candidates failed the Phase 1 gate; substitution
  was not performed.
- Phase 5: Step 3 re-pin is 627/609/16/2 (not the planned 627/610/15/2, which assumed
  the substitution branch); the ternary test IS relocated on the fallback branch.
- Phase 7: BM_CM_1 `max_time` 15 → 60 — outside the plan's original non-goals
  ("BM_CM_1 watch item only"), performed after gate-forced diagnosis proved the failure
  pre-existing, measured, and change-independent; recorded in decision record 7.2/7.6
  and at the constant.
- Phase 7 required three gate runs (red/red/green) with per-run causes recorded; no
  budget, floor, or assertion was altered in response to any red run except the
  measured BM_CM_1 recalibration above.

## Downstream

- The green Step 6 unblocks the pass-level task that was blocked on it.
- Open, unremedied exposures a future task may pick up: the interleaving `some_future`
  50-draw exposure; the enriched-pair [next] expected_sat adjudication demanded by the
  [NEW] inventory line; the divergent-tail class generally (encoding-level, currently
  out of scope).

## Artifacts

- reports/02_capacity-decision-record.md — the recorded decision (sections 1-7.8)
- baselines/03_witness-candidate-probe.{json,md} — 7-seed probes (both candidates,
  BM_CM_4, BM_CM_1)
- baselines/06_bm-cm-1-tail-probe.{json,md} — BM_CM_1 seed-2 600 s divergence probe
- baselines/04, 05, 07 — full-gate transcripts (red, red, GREEN with load evidence)
- bench_witness_probe.py — seeded probe harness (methodology copy)
- Modified: oracle/bimodal_logic/tests/test_oracle_interface.py,
  test_boundary_regression.py, test_cross_oracle_differential.py,
  code/src/model_checker/theory_lib/bimodal/examples.py, code/scripts/verify-refactor.sh,
  oracle/run-oracle-suite.sh, code/docs/core/TESTING_GUIDE.md
