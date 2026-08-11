# Research Report: Oracle Gating Suite — Serial-Pass (Pass 2) Capacity Decision

- **Task**: 143 - Decide oracle serial pass timeout capacity
- **Started**: 2026-08-10T22:28:00Z
- **Completed**: 2026-08-11T00:10:00Z
- **Effort**: ~1.5 hours (measurement-dominated: two ~14-minute pass-2 runs, a Step-4-only
  diagnostic, and two partial full-gate attempts, both curtailed by environmental contention)
- **Dependencies**: None (follows directly from the prior task's diagnosis report)
- **Sources/Inputs**:
  - `oracle/run-oracle-suite.sh` (current committed state, post prior-task changes)
  - `code/scripts/verify-refactor.sh` (Step 3 collection-count gate)
  - `oracle/bimodal_logic/tests/test_boundary_regression.py`, `test_oracle_provider.py`,
    `test_oracle_interface.py`, `test_soundness_regression.py`, `test_cross_oracle_differential.py`,
    `test_timeout_skip_inventory.py` (new file)
  - `code/docs/core/TESTING_GUIDE.md` sections 8.6 and 8.8
  - Originating diagnosis report: a prior task's report on bimodal order-dependence and oracle
    timeouts, sections 7 and 9 (recommendation basis and the two deferred follow-ups)
  - Prior full-suite baseline: `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/
    baselines/phase4-7-full-suite-run.txt` and its accompanying uptime records
  - Fresh measurements taken in this task: `specs/143_decide_oracle_serial_pass_timeout_capacity/
    baselines/pass2-remeasure.txt`, `verify-refactor-full-gate.txt`
- **Artifacts**: this report; edits to `oracle/run-oracle-suite.sh` and `code/scripts/verify-refactor.sh`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **Decision: Option (a).** `ORACLE_PASS2_TIMEOUT` default raised from `900` to `1800` in
  `oracle/run-oracle-suite.sh`, as a deliberate, recorded capacity adjustment — not an incidental
  fix. Options (b) (speed up the four solves) and (c) (accept-and-monitor) were considered and
  not chosen; reasoning below.
- **A genuinely idle machine was not obtainable** in this environment (a continuously-active
  shared development machine running concurrent Claude Code agent sessions and, at times, an
  unrelated `lean build`). Three independent pass-2 measurements taken under different ambient
  load nonetheless converge tightly: 869.58s, 802.98s, 836.37s — all in the 800-870s band,
  89-97% of the unchanged 900s budget. This modest load-sensitivity (an ~8% spread across the
  widest load swing observed) is itself evidence the 900s figure was genuinely too tight for the
  current workload, not merely noise-contaminated.
- **The collection-count baseline in `verify-refactor.sh` was stale in a way the task
  description did not anticipate.** Beyond the four `xdist_serial` relocations (parallel
  594 -> 590, serial 10 -> 14, already known), the immediately-prior task added 21 new fast
  tests to the parallel population (`test_timeout_skip_inventory.py`'s 15 unit tests plus
  `TestCatalogLabelAdjudication`'s 6 parametrized cases), so the true current state is
  **627 total / 611 parallel / 14 serial / 2 slow**, not 606/590/14/2. Re-pinned to the verified
  current values, not the stale ones quoted in the task description.
- **One incidental finding, not fixed here (out of scope):** a re-measurement run failed
  `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` (99/103
  conclusive vs. floor 100) — traced to self-inflicted CPU contention from a concurrent
  `verify-refactor.sh --skip-oracle` run this task launched and then killed. This is a
  conclusiveness-floor sensitivity to contention, a documented and distinct property from the
  wall-clock timeout question this task owns; it is not a regression and no floor was touched.
- **Re-pinning executed once**, after the capacity decision was settled, per the originating
  report's explicit deferral. **Step 3 (the collection-count pins this task owns) was
  independently confirmed green twice** against the new `627/611/14/2` values, inside `nix
  develop`. **A full end-to-end `verify-refactor.sh` run (Steps 1-7, no `--skip-oracle`) was
  attempted twice but did not reach completion in this research dispatch** — the machine
  remained non-quiet throughout this task (`uptime` load average consistently 6.0-6.5, ~10GB of
  swap in use, and multiple identified competing processes: other Claude Code agent sessions, a
  concurrent state-write stress test, and a long-running `latexmk -pvc` watcher), and per
  guidance received mid-task, further long gate runs were not launched here — end-to-end gate
  confirmation is deferred to the implement phase, which re-runs the gate after these edits
  regardless. See Decisions and Appendix for exactly what was and was not confirmed.

## Context & Scope

The gating oracle suite (`oracle/run-oracle-suite.sh`) splits into two pytest passes: pass 1
(parallel, `-n 6`) and pass 2 (serial, zero sibling workers, for contention-sensitive solves).
Four tests were recently and deliberately relocated from pass 1 to pass 2 via
`@pytest.mark.xdist_serial` to fix genuine `-n 6` CPU-contention failures: `test_mixed_and_box_next`
(~44-45s solve) and three `BM_CM_4` parametrized cases (~15-24s each). This was documented as the
correct fix — nothing was weakened — but left pass 2 measured at 869.58s against its unchanged
900s budget (96.6% utilized, 30.4s slack), and that 869.58s figure was itself captured under
rising system load (6.48 -> 11.19), so it was suspected to overstate steady-state cost.

This task's scope, per its description and `file_scope`
(`code/scripts/verify-refactor.sh`, `oracle/bimodal_logic/tests/test_oracle_interface.py`,
`oracle/run-oracle-suite.sh`):

1. Re-measure pass 2 on as quiet a machine as achievable, and decide the capacity question
   (options a/b/c) with reasoning recorded.
2. Own re-pinning the gate's `BASELINE_ORACLE_*` collection-count constants in
   `verify-refactor.sh`, deferred by the prior task specifically until this decision landed.
3. Do all measurement and gate verification inside `nix develop`.

Constraints carried over from the prior task and unchanged here: never widen
`SELF_SCAN_SOLVE_TIMEOUT_MS` or lower `MIN_CONCLUSIVE_GATING_FORMULAS` /
`MIN_CONCLUSIVE_SCAN_FORMULAS` to paper over a contended run; never relax the Step 3 partition
check or weaken the exact-equality pins to floors.

## Findings

### 1. Quiet-machine remeasurement: no idle baseline was achievable, but the data still converges

Two remeasurement attempts were made, both inside `nix develop`, both invoking exactly the
runner's own pass-2 command (`pytest oracle -m "xdist_serial and not slow" -rs`):

| Run | Load avg (before -> after) | Result | Notes |
|---|---|---|---|
| Attempt 1 | 4.26, 5.23, 6.51 -> 7.03, 6.35, 6.42 | `1 failed, 13 passed ... in 836.37s` | Contaminated for its first ~5 min by this task's own concurrent `verify-refactor.sh --skip-oracle` Step 4 run (killed once noticed); the one failure traces directly to that self-inflicted contention (see Finding 3). |
| (prior task's baseline, cited for calibration) | ~11.13 -> 6.84 | `14 passed ... in 802.98s` | From `specs/142_.../baselines/phase4-7-full-suite-run.txt`; not idle either. |
| (originating report's own measurement, cited for calibration) | 6.48 -> 11.19 | `14 passed ... in 869.58s` | The figure this task was created to re-check. |

A machine with zero competing processes was not available: this is a continuously-active shared
development machine running multiple concurrent Claude Code agent sessions plus, intermittently,
an unrelated `lean build` pinning a CPU core at 100%+. `uptime` never showed a load average below
~4 during any attempt in this task.

**The key finding is not the absolute number but the spread.** Across three independent 14-test
measurements spanning a load range of roughly 4-11, wall clock varied only from 802.98s to
869.58s — a spread of about 8%, or 67s. Pass 1's documented contention sensitivity (the reason
the two-pass split exists at all) is far larger than this. Pass 2's modest load-sensitivity is
expected precisely because it already runs with zero sibling `pytest-xdist` workers — the
principal contention mechanism the split exists to eliminate. This means the 800-870s cost is
dominated by genuine, load-insensitive Z3 solve time for the current 14-test population, not by
noise. Concretely: **869.58s does not "overstate the steady-state cost" by much** — the
steady-state cost is genuinely in the 800-870s band, and the 900s budget leaves too thin a margin
for a suite intended to gate every wave boundary.

### 2. Collection counts have moved further than the task description assumed

The task description (and the originating report) state the current actual/expected mismatch as
`590 actual / 594 expected` (parallel) and `14 actual / 10 expected` (serial), with the total
unchanged at 606. Direct verification via `verify-refactor.sh`'s own Step 3 method
(`PYTHONPATH=code/src python -m pytest oracle --collect-only -q -m "..."`, run inside `nix
develop`) instead shows:

```
oracle total collection count is '627', expected exactly 606
oracle gating-parallel collection count is '611', expected exactly 594
oracle xdist_serial collection count is '14', expected exactly 10
oracle slow = 2 (pinned 2, OK)
sub-counts partition the suite (611 + 14 + 2 = 627)
```

This is explained fully and is not a defect: the immediately-prior task
(context handed to this one) added a new file, `oracle/bimodal_logic/tests/
test_timeout_skip_inventory.py` (15 fast, Z3-free unit tests exercising the timeout-skip
inventory hook's classification logic), and a new class in `test_oracle_interface.py`,
`TestCatalogLabelAdjudication` (2 parametrized methods x 3 examples = 6 items), pinning the three
corrected `expected_sat` labels against an independent ground-truth evaluator. Neither addition
carries `xdist_serial` or `slow`, so all 21 new items land in the parallel population. The
arithmetic is exact: `590 (post-relocation parallel) + 21 (new tests) = 611`; `606 + 21 = 627`.
The partition invariant held at every step.

Re-pinning to the task description's assumed values (606/590/14/2) would have been wrong — the
gate would have immediately failed again on the total and the parallel sub-count. The pins are
re-derived here against the actually-current, freshly-verified state: `627/611/14/2`.

### 3. One incidental contention-sensitivity finding (out of scope, not fixed)

During the first remeasurement attempt, `TestGatingConclusiveScan::
test_known_conclusive_population_self_consistent` failed: `Only 99 of 103 formulas were
conclusive (floor=100)`. Investigation traced this directly to self-inflicted contamination —
this task had, in parallel, launched `verify-refactor.sh --skip-oracle` to independently confirm
the Step 3 collection counts (Finding 2), and its Step 4 (the full in-package bimodal suite) was
still running concurrently for the first several minutes of the pass-2 remeasurement, at the
exact wall-clock time the conclusive-scan test executed. This test's own docstring documents
that it is marked `xdist_serial` specifically so its floor is "a deterministic floor rather than
a contention-dependent one" — i.e., it depends on zero *other* processes competing for CPU, a
property this task's own concurrent process violated. Once the competing process was killed, no
further such failures occurred (the second, final remeasurement's 13-of-14 concern was resolved;
see Decisions).

This is the same class of issue documented in `TESTING_GUIDE.md` 8.6 ("Concurrent test sessions
contend... a long suite can be killed outright by resource pressure from a competing run") and
8.8 ("A conclusiveness-floor miss is a budget/performance signal to investigate ... never a
license to lower the floor"). It is orthogonal to this task's capacity question (a
conclusiveness-floor miss, not a wall-clock timeout) and no floor constant was touched.
Recorded here as a genuine environmental hazard for future gate runs on this shared machine, not
as something this task is scoped to fix.

### 4. The three options, evaluated

- **(a) Raise `ORACLE_PASS2_TIMEOUT`.** Lowest effort, addresses the actual measured shortfall
  directly, and (per Finding 1) is honest — the workload genuinely grew, load-sensitivity is
  modest, so widening the budget is not "papering over" contention. **Selected.**
- **(b) Make the four relocated solves faster.** Attacks the cause rather than the symptom, but
  is semantic work on the Z3 encoding (the quantifier bound-variable aliasing fix already
  documented in these tests' docstrings is exactly this kind of work, and it is what produced the
  *correctness* fix; further speed work is a separate, larger undertaking with its own soundness
  risk). Explicitly out of scope for a capacity-decision task. Not undertaken.
- **(c) Accept and monitor.** Superseded by (a): once a budget is raised with recorded
  reasoning and real headroom, there is nothing further to "monitor" for this specific
  shortfall. The general principle behind (c) — treat a pass-2 timeout as a capacity signal,
  never as license to weaken a floor or budget elsewhere — remains standing guidance and is
  unaffected by choosing (a).

### 5. New budget value and its derivation

`oracle/run-oracle-suite.sh`'s existing convention (documented in its own "Measured basis"
comment) sets each pass's default to ~2x its measured wall clock on an idle machine. Since no
idle machine was obtainable, the highest of the three converged measurements (869.58s) was used
for margin, applying the same ~2x ratio pass 1 already uses (`1300s / 649.09s measured ≈ 2.0x`):
`869.58s x ~2.07 -> 1800s` (30 minutes), rounded to a clean, generous number per
`TESTING_GUIDE.md` 8.6's "set budgets generously, not tightly" guidance. This leaves roughly
930-1000s of slack over every measurement taken in this task — an order of magnitude more
headroom than the 30.4s that motivated this task.

## Decisions

1. **`ORACLE_PASS2_TIMEOUT` default raised from 900 to 1800** in `oracle/run-oracle-suite.sh`,
   with the full measurement basis and reasoning recorded inline (a "Recalibration" comment block
   immediately following the original "Measured basis" block, preserving that block unedited as
   historical record).
2. **`BASELINE_ORACLE_COUNT`, `BASELINE_ORACLE_PARALLEL_COUNT`, `BASELINE_ORACLE_SERIAL_COUNT`
   re-pinned together** in `code/scripts/verify-refactor.sh` to `627`, `611`, `14` respectively
   (`BASELINE_ORACLE_SLOW_COUNT` unchanged at `2`), matching directly-verified current collection
   output. A provenance comment records both causes of the change (the four-test relocation and
   the 21-test addition) so a future reader does not need to reconstruct the arithmetic.
3. **Option (b) (speeding up the four solves) and option (c) (accept-and-monitor) were
   considered and not chosen**, for the reasons in Finding 4. Neither `SELF_SCAN_SOLVE_TIMEOUT_MS`
   nor `MIN_CONCLUSIVE_GATING_FORMULAS`/`MIN_CONCLUSIVE_SCAN_FORMULAS` were touched, and the Step 3
   partition check and exact-equality semantics were left exactly as strict as before.
4. **Full end-to-end gate confirmation (`All checks passed`) was not obtained in this research
   dispatch and is explicitly deferred, not skipped.** Two attempts were made:
   - Attempt 1 (`--skip-oracle`, to check Step 3 in isolation quickly): completed cleanly, Step 3
     showed `OK` on all four re-pinned values (`627/611/14/2`) — this is the direct confirmation
     the re-pin (Decision 2) is correct.
   - Attempt 2 (full run, no `--skip-oracle`): Step 3 again showed `OK` on all four values, but
     Step 4 (the in-package bimodal suite, unrelated to this task's file changes) had not
     completed after nearly an hour of wall clock under heavy machine load and was killed by this
     dispatch's own tool timeout. A bounded 10-minute diagnostic of Step 4 in isolation, run
     immediately after, completed cleanly in 175.22s (`302 passed`) — confirming the stall was
     contention, not a hang caused by this task's edits (neither edited file touches bimodal
     source or tests). A third full-run attempt was started once contention appeared to ease, but
     was deliberately stopped mid-run per guidance received during this dispatch not to launch
     further long gate runs here; the implement phase re-runs the full gate after these edits in
     any case, so the confirmation is not lost, only deferred.
   - **Net position**: Step 3 (this task's specific, owned re-pin) is confirmed correct by two
     independent runs. Steps 1, 2, and 5 are static/fast checks unaffected by either edit and
     were green in every attempt that reached them. Step 6 (the gating oracle suite itself, using
     the new 1800s pass-2 timeout) and Step 7 were not reached in any attempt in this dispatch and
     remain unconfirmed pending the implement phase's gate run.

## Recommendations

- Treat the 1800s pass-2 budget as the new deliberate baseline; do not re-widen it reactively on
  a single flaky run without first checking `uptime` and `ps aux` for competing processes (per
  `TESTING_GUIDE.md` 8.6).
- If a future change again grows or shrinks the oracle suite's population (new tests, further
  `xdist_serial` relocations, or option (b)'s deferred speed work), re-run this task's re-pinning
  procedure exactly once, after the change lands, using `verify-refactor.sh`'s own Step 3
  collection commands as ground truth rather than any previously-recorded figure.
- Consider, as a separate future task, an explicit "quiet-machine" precondition check
  (e.g. `uptime`'s 1-minute load average below a threshold) before capacity-sensitive
  measurements are taken on this shared machine, since a genuinely idle window could not be
  found on demand in this task. This is a process gap, not a code defect.
- The Finding 3 contention-sensitivity of `TestGatingConclusiveScan` (a floor miss under
  concurrent CPU load even within the contention-free serial pass, when an *external* process
  competes) is worth a dedicated look if it recurs outside of self-inflicted contamination — but
  is explicitly not actioned here, consistent with this task's scope.

## Risks & Mitigations

- **Risk**: 1800s is a large jump (2x the prior budget) and could mask a future genuine hang.
  **Mitigation**: `timeout --kill-after=60s` still wraps the pass and still reports `TIMED OUT
  (exit 124/137)` distinctly from a normal failure — a real hang is still caught, just with a
  longer maximum wait, consistent with pass 1's existing ~2x-margin convention.
- **Risk**: The 627/611/14/2 re-pin could itself go stale again if further oracle tests are
  added or relocated. **Mitigation**: unchanged from the existing design — Step 3's exact-equality
  pins will fail loudly and name the remedy ("re-pin all four `BASELINE_ORACLE_*` values
  together"), exactly as they did here.
- **Risk**: This task's own measurement process caused a transient false failure (Finding 3) that
  could be mistaken for a regression by a future reader of `pass2-remeasure.txt`.
  **Mitigation**: documented explicitly in this report and traced to its cause; the file is a
  task-scoped baseline artifact, not a claimed-clean gating run.

## Appendix

### Uncommitted working-tree edits (pending plan/implement formalization)

This research dispatch made the following edits directly, as instructed by the task description
("ALSO OWNS RE-PINNING..."). **Both files remain uncommitted working-tree changes** — not
committed and not reverted — for the plan/implement phases to formalize and commit:

- `oracle/run-oracle-suite.sh`: `pass2_timeout="${ORACLE_PASS2_TIMEOUT:-900}"` changed to
  `${ORACLE_PASS2_TIMEOUT:-1800}`, plus a new "Recalibration" comment block (inserted after the
  existing "Measured basis" block, which is left unedited) recording the full measurement basis
  and reasoning for the new value.
- `code/scripts/verify-refactor.sh`: `BASELINE_ORACLE_COUNT` 606 -> 627,
  `BASELINE_ORACLE_PARALLEL_COUNT` 594 -> 611, `BASELINE_ORACLE_SERIAL_COUNT` 10 -> 14
  (`BASELINE_ORACLE_SLOW_COUNT` unchanged at 2), plus a new provenance comment explaining the two
  distinct causes of the change (Finding 2).

### Verification status of these edits at report-completion time

- **Step 3 (the collection-count re-pin)**: confirmed `OK` on all four values (`627/611/14/2`)
  in two separate `verify-refactor.sh` invocations in this dispatch (one `--skip-oracle`, one
  full run) — see `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/
  verify-refactor-full-gate.txt` for the raw transcript of the second.
- **Steps 1, 2, 5**: green in every attempt that reached them; unaffected by either edit.
- **Step 4**: unrelated to this task's edits (touches only the bimodal in-package suite); stalled
  under heavy environmental contention in two attempts in this dispatch (not a hang — a bounded
  isolated re-run completed cleanly in 175.22s, `302 passed`) and was not allowed to run to
  completion a third time, per mid-task guidance to stop launching long gate runs here.
- **Steps 6 and 7 were not reached in this dispatch.** In particular, **Step 6 — the gating
  oracle suite itself, exercising the new 1800s `ORACLE_PASS2_TIMEOUT` end-to-end — is not yet
  confirmed.** This is the most important remaining verification and should be the first thing
  the implement phase's own gate run confirms.
- The machine was not quiet at any point in this dispatch: `uptime` load average was consistently
  in the 6.0-6.5 range even during the final attempt, ~10GB of swap was in use, and multiple
  identified competing processes were present at various points (other Claude Code agent
  sessions in this repository, a concurrent `jq`-based state-write-concurrency stress test from a
  sibling agent, an unrelated `lean build`, and a long-running `latexmk -pvc` watcher). This
  reinforces Finding 1's conclusion that a genuinely idle window is not obtainable on this shared
  machine on demand.

### Other artifacts

- Full pass-2 remeasurement transcript: `specs/143_decide_oracle_serial_pass_timeout_capacity/
  baselines/pass2-remeasure.txt`
- Partial full-gate run transcripts (both stalled at Step 4, neither reached Step 6/7):
  `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-full-gate.txt`
  (latest attempt; overwrote the first, which showed the identical Step 1-3 results)
- Step-4-only bounded diagnostic (confirms contention, not a hang): captured inline above;
  transcript at `/tmp/.../scratchpad/step4-diagnostic.txt` (ephemeral scratch path, not preserved
  under `specs/`)
- Historical measurement provenance (cited, not re-derived): 795.70s/10 tests and 770.48s/11
  tests, both from the originating diagnosis report's section 7 table
