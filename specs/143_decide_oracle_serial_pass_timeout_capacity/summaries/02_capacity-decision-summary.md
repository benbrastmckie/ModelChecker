# Implementation Summary: Close the Serial-Pass Capacity Decision

- **Task**: 143 - Decide oracle serial pass timeout capacity
- **Plan**: `specs/143_decide_oracle_serial_pass_timeout_capacity/plans/02_close-capacity-decision.md`
- **Status**: COMPLETED
- **Prior summary**: `summaries/01_phase4-triage-record.md` (Phase 4 triage record; its "edits
  left uncommitted" claim is corrected below)

## The Decision

Option (a) was taken: `ORACLE_PASS2_TIMEOUT` raised 900 -> 1800s, at
`oracle/run-oracle-suite.sh:136`. The full reasoning is recorded inline at
`oracle/run-oracle-suite.sh:95-134` — three independent measurements of the (then) 14-test serial
population (869.58s, 802.98s, 836.37s wall clock, load average 4-11), converging on 800-870s
(89-97% of the superseded 900s budget); a genuine capacity increase from more/heavier scheduled
work, not primarily a load artifact; and the same "~2x of measured, applied to the highest
observed figure" convention used for pass 1, landing on 1800s. This was the task's explicit
precondition for option (a) being acceptable at all — a deliberate, recorded capacity decision,
not an incidental fix folded into unrelated work — and it was met. The edit landed in commit
`e3b09d4e` ("oracle: raise pass-2 budget to 1800s and re-pin gate collection counts").

## Why Option (b) Was Not Taken — and Was Subsequently Exhausted

Plan v1 ruled out option (b) (make the four slow solves faster at the encoding level) on effort
grounds: it is semantic work on the encoding, not a budget change, and out of scope for a capacity
decision. Task 144 subsequently attempted it directly and independently: all three encoding-level
cost-reduction candidates were implemented, measured paired-by-seed on Z3 rlimit, and rejected —
task 144 completed with **objective not achieved**. This is a stronger result than plan v1's
effort-based deferral: option (b) is not merely lower-priority, it is empirically exhausted as a
lever. That finding materially strengthens the case for option (a), since it establishes there was
no lower-effort or "more correct" alternative being passed over.

## Why Option (c) Was Not Taken

Option (c) (accept-and-monitor, treating a pass-2 timeout as a capacity signal rather than a
correctness regression) was not viable at the condition that originated this task: pass 2 was
measured at 96.6% of its 900s budget with 30.4s of slack — a pass already effectively failing.
Monitoring an exhausted budget is not a decision; it defers an already-arrived capacity problem.

## Re-Pin Provenance and Supersession

This task re-pinned all four `BASELINE_ORACLE_*` values together in `e3b09d4e`, per the gate's own
prescribed remedy ("re-pin all four BASELINE_ORACLE_* values together"), reflecting the
then-current distribution of 14 tests in the serial pass (606 total / 590 parallel / 14 serial / 2
slow).

**Those task-143-era values are now superseded.** Task 145 (`6ea94522`) relocated `all_future_neg`
and the ternary `next_A` serialization test into the serial pass as part of its composite
per-solve remedy, changing the distribution again. `code/scripts/verify-refactor.sh:65-68` now
holds the current, live pins:

- Total: **627** (was 606)
- Gating-parallel: **609** (was 590)
- `xdist_serial`: **16** (was 14)
- Slow: **2** (unchanged)
- Partition: `609 + 16 + 2 = 627` ✓

This task's own confirmation run (`baselines/01_full-gate-confirmation.txt`) re-verified all five
of these as `OK` at Step 3. Re-pinning to match an intentional, recorded redistribution is not a
weakening of the gate: the pins remain exact-equality checks, not floors or inequalities, and will
still fail on any future unintended change.

## Current Headroom — Superseding the Stale 840-950s Claim

`summaries/01_phase4-triage-record.md` recorded "roughly 840-950s of headroom" for pass 2. That
figure was derived from the pre-relocation, 14-test serial population and is **stale** — it
predates task 145's relocation of `all_future_neg` and the ternary test into the serial pass,
which changed the population to 16 tests.

Two current, post-relocation measurements exist:

- **Task 145's green run 3** (`specs/145_.../baselines/07_full-gate-transcript-run3.txt`): pass 2
  measured **1315.36s against the 1800s budget = 73.1% of budget, 485s slack**.
- **This task's own confirmation run** (`baselines/02_oracle-suite-step6-confirmation.txt`, copied
  from the ephemeral `/tmp/verify-refactor-oracle.txt` before it was overwritten): pass 2 measured
  **"16 passed, 611 deselected in 1140.24s (0:19:00)"** against the same 1800s budget = **63.3% of
  budget, 659.76s slack** (`1140.24 / 1800 = 0.6335`; `1800 - 1140.24 = 659.76`).

Both figures supersede the stale 840-950s claim and both are well inside budget; this run's own
figure sits comfortably below task 145's, consistent with the recorded run-to-run variance under
differing ambient load documented in `oracle/run-oracle-suite.sh:95-134` and in task 145's own
records. Contrasted against the 96.6% / 30.4s-slack condition that originated this task, the
capacity decision holds comfortably under both current measurements.

## Verification Status

The blocker this task was waiting on is discharged. Task 145's own confirmation
(`specs/145_.../baselines/07_full-gate-transcript-run3.txt`) reached `[verify-refactor] All checks
passed`, `GATE_EXIT=0`, wall 34m42s, including `Step 6: OK: gating oracle suite green across both
passes` — the exact line this task was blocked on.

This task's **own** confirmation run (`baselines/01_full-gate-confirmation.txt`), launched before
`plans/02_close-capacity-decision.md` was written and ingested per that plan's Phase 6, is
independently **GREEN**:

- `GATE_EXIT=0`, final line `[verify-refactor] All checks passed`.
- Wall clock: started `2026-08-11T21:26:59Z`, finished `2026-08-11T21:59:50Z` — 32m51s.
- Load average: 2.83/2.50/4.30 at start, 2.12/3.57/4.47 at end — this green was not obtained on an
  artificially idle machine.
- Step 3: all five `OK` lines confirmed (total 627, parallel 609, `xdist_serial` 16, slow 2,
  partition 609+16+2=627).
- Step 6: `OK: gating oracle suite green across both passes (a strict-xfail XPASS would have
  failed this run)`.
- All of Steps 1-7 report `OK`.

Per the plan's Phase 6, since this run was GREEN, Phase 7 (red triage) was **not triggered** — its
conditional branch does not apply. This is recorded here explicitly rather than silently skipped.

**Green is contention- and seed-sensitive, not guaranteed on any single run.** This one green
confirmation does not establish unconditional reliability. Task 145's own gate runs 1 and 2 were
red under contention, and it records two accepted, unresolved-by-budget residual conditions:

- A ternary `next_A` divergent tail (~1-in-7 draws exhausting its 480000ms leg override).
- A divergent BM_CM_1 seed-2 residual, observed after the 15 -> 60s recalibration.

This task's confirmation run happened to avoid both. It is one green run among a documented
history of runs that have also been red on these known, already-adjudicated residuals — it
corroborates that the tree is green-capable under the current constants; it does not prove every
future run will be green.

## What Was Refused

Across tasks 143, 144, and 145, and again in this closeout:

- No timeout or budget was widened beyond the one deliberate, recorded capacity decision itself
  (`ORACLE_PASS2_TIMEOUT` 900 -> 1800, with reasoning recorded inline before any gate run was
  attempted against it).
- No floor was lowered (`MIN_CONCLUSIVE_GATING_FORMULAS`, `MIN_CONCLUSIVE_SCAN_FORMULAS`, or any
  Step 5c pinned constant).
- No test was xfailed, skipped, or disabled to obtain a green. Step 6's own inventory in this
  run's ephemeral transcript reports only pre-adjudicated `[KNOWN]` budget/performance skips (2),
  not new ones.
- Neither the Step 3 partition check nor the suite total was relaxed; both remain exact-equality
  pins, confirmed `OK` in this run.
- This closeout made no edit to `code/scripts/verify-refactor.sh`, `oracle/run-oracle-suite.sh`,
  or `oracle/bimodal_logic/tests/test_oracle_interface.py` — `git status --short` and
  `git diff --stat -- oracle/ code/` both confirm zero changes to any file under those paths for
  the duration of this closeout.

## Correction to the Prior Summary

`summaries/01_phase4-triage-record.md` states that the working-tree edits (the `ORACLE_PASS2_TIMEOUT`
raise and the four-value re-pin) were "left uncommitted." That claim is **stale**: both edits were
subsequently committed as `e3b09d4e`. The prior summary is not being rewritten — it is an accurate
record of its own moment — but this summary supersedes it on that specific point.

## Artifacts Produced

- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/01_full-gate-confirmation.txt` —
  the task-143-owned full-gate confirmation transcript (green, `GATE_EXIT=0`).
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/02_oracle-suite-step6-confirmation.txt`
  — the ephemeral Step 6 oracle-suite transcript, copied before it could be overwritten by a future
  run; carries the direct pass-1 (596.38s / 1300s) and pass-2 (1140.24s / 1800s) wall-clock
  evidence for this specific run.
- This summary.

## Provenance Already Committed (Not Reproduced Here)

- `e3b09d4e` — `ORACLE_PASS2_TIMEOUT` 900 -> 1800 plus the four-value re-pin (task 143).
- `6ea94522` (task 145) — superseded the pin values by relocating `all_future_neg` and the ternary
  `next_A` test into the serial pass (627/609/16/2, current).
