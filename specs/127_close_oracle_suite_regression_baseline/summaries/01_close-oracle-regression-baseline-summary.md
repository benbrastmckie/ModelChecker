# Implementation Summary: Close the Oracle Suite Regression Baseline

- **Task**: 127 - Complete the oracle differential-suite regression baseline that the core/theory_lib refactor could not finish
- **Status**: [BLOCKED]
- **Started**: 2026-07-24T23:32:00-07:00
- **Completed**: 2026-07-25T00:50:00-07:00
- **Effort**: ~3.5 hours agent time; ~2.5 hours unattended wall-clock across five pytest invocations
- **Dependencies**: None (task 126 depends on this one)
- **Artifacts**: plans/01_close-oracle-regression-baseline.md, run/ (staged evidence, see below)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, summary-format.md

## Overview

The task set out to produce a complete, clean 550-test oracle differential-suite baseline and flip
the core/theory_lib refactor plan's Phase 2 markers to `[COMPLETED]`. Phases 1 and 2 completed
cleanly: a full run under `-n 6` finished in 44:33 (2673.06s), reaching `[100%]` with an exit code
and complete JUnit XML. Phase 3 triage found 7 failures. Systematic isolated re-runs overturned the
plan's own success-rubric premise in both directions and surfaced one genuine, refactor-introduced
regression. **The task cannot close in its current form**: rubric category (c) was reached, so no
baseline was promoted and no Phase 2 marker was flipped. Phases 4-6 did not run.

## What Changed

- Ran the full 550-test suite under `-n 6`, backgrounded (Phase 2): `7 failed, 534 passed, 9 xfailed
  in 2673.06s (0:44:33)`. Staged at `specs/127_close_oracle_suite_regression_baseline/run/oracle-run.txt`
  and `.../run/junit-oracle.xml` (`tests="550" failures="7" errors="0"`, no `xpassed`).
- Re-ran the 5 failures **not** on the plan's watch list together in one serial (no `-n`) invocation:
  `5 passed in 179.26s (2:59)`. These are `-n 6` parallel-execution artifacts — state-isolation and
  interleaving tests are not xdist-safe — not regressions.
- Re-ran both plan-designated "known contention flake" watch-list tests in isolation. **Both still
  failed**, falsifying the plan's Category-C premise for both:
  - `test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent`
    — 31:31, `AssertionError: Self-comparison produced 3 disagreements at complexity<=5` (`assert 3 == 0`).
  - `test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary`
    — 1:00, `AssertionError: Expected SAT for next_A` (`assert None is not None`).
- Built a read-only `git worktree` at pre-refactor commit `6cfb7f48` and re-ran both watch-list
  tests there together, serially: `1 failed, 1 passed in 1928.38s (32:08)`.
  - `test_all_sat_task_relation_ternary` **passed** at `6cfb7f48`. **This is a refactor-introduced
    regression** — the single blocking finding of this task.
  - `test_complexity_5_scan_self_consistent` **failed** at `6cfb7f48` too, with
    `AssertionError: Self-comparison produced 1 disagreements at complexity<=5` (`assert 1 == 0`).
    Pre-existing, refactor not implicated for this test.
- Removed the read-only baseline worktree after use (trivially recreatable via
  `git worktree add --detach <path> 6cfb7f48`; its output is preserved in
  `run/baseline-6cfb7f48-watchlist.txt`).
- No files under `oracle/` were modified. No baseline was promoted into
  `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/`. No marker was flipped in the
  refactor plan. `code/scripts/verify-refactor.sh` was not touched (Phase 5 did not run).

## Decisions

1. **Per-test verdicts (the decisive findings):**
   - `test_all_sat_task_relation_ternary`: **refactor-introduced regression.** Passes at `6cfb7f48`,
     fails on the current branch with `AssertionError: Expected SAT for next_A` /
     `assert None is not None` — `find_countermodel` returns no model for a `next_A` (temporal
     diamond over atom A) formula expected SAT. This is category (c) per the plan's rubric: a hard
     stop. No baseline promotion, no Phase 2 marker flip.
   - `test_complexity_5_scan_self_consistent`: **pre-existing defect, not refactor-introduced.**
     Fails at both `6cfb7f48` and the current branch with a self-vs-self oracle disagreement.
     **Open question, not resolved here**: the disagreement count differs (1 at baseline vs. 3 at
     HEAD), each from a single sample on a suite already demonstrated to have Z3-timing-dependent
     assertion outcomes (see methodology finding below). This difference is **not** reported as
     evidence of further degradation, nor as proof the count is stable — it is unresolved with the
     data collected. Resolving it would require repeated samples at both commits (multiple runs at
     each of `6cfb7f48` and HEAD), which was not run here to avoid an open-ended investigation
     beyond this task's scope.
   - The 5 non-watchlist failures under `-n 6`: **confirmed benign xdist artifacts**, not
     regressions of any kind.

2. **The pre-declared watch list was wrong in both directions and must not be relied on for future
   triage.** The plan's research had classified `test_complexity_5_scan_self_consistent` and
   `test_all_sat_task_relation_ternary` as "Category C: contention flakes, pass in isolation" and
   treated everything else as presumptively clean. The actual result inverted this: the five
   failures **outside** the watch list were the benign ones (parallel-execution artifacts, pass
   serially), while **both** tests the plan pre-declared safe-to-ignore are genuine failures (one
   pre-existing, one refactor-introduced). A watch list built from a single prior observation
   actively pointed away from the real failures. Any future oracle-suite triage must re-verify
   watch-list membership by isolated re-run rather than trusting a prior classification.

3. **`-n 6` is unsound for generating this task's regression baseline.** It manufactured five false
   failures (state-isolation and interleaving tests are not safe under xdist parallelism) in a run
   that also happened to surface the two watch-list tests' real failures — but a `-n 6` run's
   failure set cannot, on its own, be trusted to distinguish xdist artifacts from real failures
   without the serial re-run step this task performed. **Recommendation**: generate the actual
   regression baseline **serially** (no `-n`), accepting the ~90 minute wall clock implied by
   scaling the 5-test 2:59 serial subset and the two ~31-32 minute watch-list tests across the full
   550, rather than continuing to rely on `-n 6` plus after-the-fact triage. The alternative —
   adding explicit serialization markers (e.g. `pytest-xdist`'s `@pytest.mark.xdist_group` or a
   `-p no:randomly`-style scope lock) to the specific state-isolation/interleaving test classes —
   would let `-n 6` stay usable for the rest of the suite, but requires editing the affected test
   files, which is outside this task's non-goals (no test-file modification). Serial baseline
   generation is the safer near-term recommendation; the marker approach is a reasonable follow-up
   if `-n 6` wall-clock savings matter enough to justify a small test-infrastructure change.

4. **Is the task's stated goal achievable right now? No.** The definition of done required a
   complete run with no genuine failures, the refactor plan's Phase 2 at `[COMPLETED]`, and a green
   `verify-refactor.sh` with Step 6 live. `test_all_sat_task_relation_ternary`'s refactor-introduced
   regression makes a truthful clean baseline impossible until that regression is fixed. This task
   stays `[BLOCKED]`; the refactor plan's Phase 2 stays at whatever framing it already had (not
   touched by this task; Phase 4 did not run). A follow-up task to diagnose and fix the ternary
   regression is the correct next step, followed by re-running this task's Phase 2-3 once that
   fix lands.

## Impacts

- Task 126 (core/theory_lib refactor) remains blocked on this task; this task in turn is now
  blocked on a new, distinct defect (the ternary regression) rather than on sandbox contention.
- The `-n 6` recommendation in the original research/plan is now known to be unsound for baseline
  generation on this suite; any future attempt should default to serial or use the alternative
  design proposed above.
- The known-flake watch list documented in prior research (and referenced by the plan) is
  falsified and should not be treated as settled precedent by future tasks touching this suite.

## Follow-ups

- **Blocking**: diagnose and fix `test_all_sat_task_relation_ternary`'s regression
  (`find_countermodel` returns `None` for `next_A`, expected SAT) — likely a follow-up task against
  the core/theory_lib refactor's oracle-facing changes. Until fixed, this task cannot promote a
  clean baseline or flip the refactor plan's Phase 2 markers.
- **Non-blocking, informational**: the `test_complexity_5_scan_self_consistent` disagreement-count
  question (1 vs. 3) is open. If a future run wants to resolve it, take 3-5 repeated samples at
  both `6cfb7f48` and the current commit and compare distributions, rather than treating a single
  sample difference as signal.
- **Non-blocking, methodology**: decide between a serial baseline run (~90 min, no code change) or
  adding `xdist_group`/serialization markers to the affected state-isolation/interleaving test
  classes (requires editing `oracle/` test files, which is outside this task's scope) before the
  next baseline attempt.
- Once the ternary regression is fixed, resume this task starting from Phase 2 (re-run the full
  suite) rather than assuming Phases 1-2's artifacts are still representative — they predate the fix.

## Plan Deviations

- **Isolation strategy changed mid-execution** (Phase 3): the plan's literal text calls for
  re-running watch-list failures "one at a time, serially." The first one-at-a-time isolated run
  (`test_complexity_5_scan_self_consistent`, 31:31) demonstrated this was too slow to apply
  individually to all 7 failures (~3+ hours projected). Switched to running the 5 non-watchlist
  failures together in one combined serial invocation (2:59) — cheaper and equally decisive for
  answering "does this reproduce outside `-n 6` parallelism," at the cost of not being strict
  single-test isolation. Recorded explicitly rather than silently substituted.
- **Added a baseline-commit comparison step not present in the plan's Phase 3 text.** The plan's
  rubric treats "a watch-list test that fails in isolation" as automatically category (c) with no
  further attribution step. Both watch-list tests fell into this bucket, so a baseline-commit check
  against `6cfb7f48` was added (via a read-only `git worktree`, never checking out over the current
  branch) to distinguish pre-existing defects from refactor-introduced ones — materially different
  findings that change what a follow-up task needs to fix. This is additive evidence-gathering, not
  a relaxation of the rubric's stop-here action.
- **Phases 4, 5, and 6 were not executed.** Per the plan's own category (c) instruction ("stop the
  plan here"), no markers were flipped, `verify-refactor.sh` was not touched, and nothing was
  committed. This is not a skipped step but the rubric's mandated action for this outcome.
- **The Phase 6 cleanup step (remove `run/` staging directory) was intentionally not performed.**
  `run/` holds the only record of this task's five pytest invocations and is required evidence for
  whoever picks up the follow-up regression fix; deleting it would destroy that evidence for no
  benefit, since nothing was promoted or committed.

## References

- `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md`
  — this task's plan, with Phase 1-2 marked `[COMPLETED]` and Phase 3 marked `[BLOCKED]`
- `specs/127_close_oracle_suite_regression_baseline/run/oracle-run.txt` — full `-n 6` run (7 failed, 534 passed, 9 xfailed, 2673.06s)
- `specs/127_close_oracle_suite_regression_baseline/run/junit-oracle.xml` — JUnit XML for the same run
- `specs/127_close_oracle_suite_regression_baseline/run/isolated-complexity5-scan.txt` — isolated re-run, `test_complexity_5_scan_self_consistent`
- `specs/127_close_oracle_suite_regression_baseline/run/isolated-nonwatchlist-combined.txt` — combined serial re-run of the 5 non-watchlist failures
- `specs/127_close_oracle_suite_regression_baseline/run/isolated-ternary-sat.txt` — isolated re-run, `test_all_sat_task_relation_ternary`
- `specs/127_close_oracle_suite_regression_baseline/run/baseline-6cfb7f48-watchlist.txt` — both watch-list tests re-run at pre-refactor commit `6cfb7f48`
