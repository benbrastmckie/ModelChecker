# Phase 4 Contingency Triage Record

**Date**: 2026-08-10
**Session**: sess_1786427090_297889
**Outcome**: Branch (iii) — genuine failure. Stopped. Edits left uncommitted.

## What Phase 3 Produced

Two complete end-to-end runs of `nix develop --command bash code/scripts/verify-refactor.sh`
now exist. Both reached Step 6 and both failed there. Neither reached
`[verify-refactor] All checks passed`.

| | Contended attempt | Quiet attempt |
|---|---|---|
| Started | 2026-08-10 16:23 | 2026-08-10 22:46 |
| Load average during run | 5.36 / 6.72 / 7.47 | 1.57 / 2.25 |
| Steps 1-5, 7 | all OK | all OK |
| Step 4 | green first attempt | green first attempt |
| Pass 1 (parallel, budget 1300s) | **PASSED** in 793.91s | **FAILED** in 771.35s |
| Pass 2 (serial, budget 1800s) | **FAILED** in 958.58s | **FAILED** in 847.38s |
| Transcript | `baselines/oracle-suite-step6-contended-attempt.txt` | `baselines/oracle-suite-step6-quiet-attempt.txt` |

## Classification: Why This Is Branch (iii), Not Branch (i)

Branch (i) (environmental contention) predicts that failures disappear when the machine is
quiet. The opposite happened. At load 1.57 — well inside the plan's preferred "~4 or below"
window, and roughly a quarter of the contended run's load — the failure count went **up**, and
pass 1, which had passed under heavy contention, **failed**.

The failure set is also not stable between runs:

- **Contended attempt** — pass 2 only: `TestMixedFormulas::test_mixed_and_box_next`
  (`OracleTimeoutError` at 60000 ms) and `test_cross_oracle_differential.py:656`
  (conclusive floor miss, 99 of 103 against floor 100, `timeout_count=4`, `disagreements=0`).
- **Quiet attempt** — pass 1: `TestMixedFormulas::test_mixed_and_all_future_neg`
  (`OracleTimeoutError` at 60000 ms) and
  `TestTernarySerializationAll::test_all_sat_task_relation_ternary`
  (`OracleTimeoutError` at 180000 ms). Pass 2:
  `TestMixedFormulas::test_mixed_and_box_next` (`OracleTimeoutError` at 60000 ms).
- **Research-phase pass-2 remeasure** (`baselines/pass2-remeasure.txt`, 836.37s): 1 failed —
  the same conclusive floor miss, 99 of 103 against floor 100.

`test_mixed_and_box_next` is the one failure common to both full-gate attempts. Everything else
moves. That signature — a varying set of per-formula solve timeouts, load-independent, with
`disagreements=0` throughout — is a genuine budget/performance condition in the oracle's Z3
solves, not a machine-contention artifact.

Critically, **every failure is a per-formula solve timeout or its downstream conclusive-count
consequence**. There is not a single semantic disagreement in either run. Nothing here indicates
a correctness regression.

## What This Does NOT Invalidate

The capacity decision this task exists to make is **confirmed**, and confirmed twice:

- Pass 2 wall clock came in at **958.58s** (contended) and **847.38s** (quiet) against the new
  **1800s** budget. The budget was never approached, let alone exhausted. Both figures sit in
  the same 800-960s band as the three prior measurements (869.58s / 802.98s / 836.37s).
- Option (a) at 1800s carries roughly 840-950s of headroom over every measurement ever taken.
  The `~2x-of-measured` convention that produced 1800s is sound.

The collection-count re-pin is likewise **confirmed twice**: Step 3 reported OK on all four
pinned values and on the partition `611 + 14 + 2 = 627` in both runs.

Step 5 also reported OK on sub-check 5c — all four floor/budget constants hold their pinned
values — in both runs. That is independent confirmation that nothing was weakened to chase a
green.

## Action Taken

Stopped, per the plan's branch (iii) instruction and its explicit prohibitions.

Specifically **not** done, and deliberately so:

- `MIN_CONCLUSIVE_GATING_FORMULAS` was **not** lowered to accommodate the 99/103 result. A floor
  miss is a budget/performance signal per `code/docs/core/TESTING_GUIDE.md` sections 8.6 and 8.8,
  never a license to lower the floor.
- `SELF_SCAN_SOLVE_TIMEOUT_MS` and the 60000 ms / 180000 ms per-solve budgets were **not**
  raised. Widening a solve budget to clear a timeout is the exact move the suite's own inventory
  footer prohibits.
- The three failing tests were **not** xfailed, skipped, or otherwise neutralized.
- The Step 3 partition check and exact-equality pin semantics were **not** relaxed.
- `pass1_timeout` remains 1300; `BASELINE_FULL_COUNT` untouched.
- Phase 5 was **not** executed. The working-tree edits remain uncommitted, because the plan
  conditions the commit on Step 6 reaching green.

## The Open Question For The Next Session

The two working-tree edits are independently verified and strictly improve the gate — without
them Step 3 fails, which is the condition that originally motivated the re-pin. The gate at HEAD
is currently red at *both* Step 3 and Step 6; with these edits applied it is red at Step 6 only.

That makes a reasonable case for committing them as a strict improvement and opening a separate
task for the solve-timeout condition, which is pre-existing and outside this task's stated scope
(it is option (b) from the originating diagnosis — semantic work on the encoding).

The plan does not authorize that, so it was not done unilaterally. It is a scope decision for the
user.
