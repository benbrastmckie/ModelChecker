# Implementation Summary: Re-baseline the Gating Oracle Suite and Repair the Regression Gate

- **Task**: 127
- **Plan**: `plans/02_rebaseline-gating-oracle-suite.md` (v2)
- **Date**: 2026-08-09
- **Session**: sess_1786307124_299f8c
- **Phases completed**: 1, 2, 3, 5, 6 of 8. Phases 4 and 7 not started (machine contention).
- **Rubric category reached**: **(c) — a failure that reproduces on a quiet machine.**

## Headline

The gating oracle suite was run to completion on a verified-quiet machine and **it is red**. No
baseline was promoted. The regression gate was repaired independently and is committed. Nothing
anywhere was weakened to make anything pass.

## Phase 2 — reuse decision

Attempt 1's artifacts were **not** reused; Phase 2 was relaunched in full. Attempt 1 had no
`exit-code.txt`, no runner summary block, and only one of two per-pass JUnit files — failing three
of Phase 2's five completeness clauses. Splicing its pass-1 XML onto a later pass-2 run would have
produced a "run" that never existed as a single execution, with two halves carrying different
machine provenance and no single runner exit code to classify. Attempt 1's files were retained
under an `attempt1-` prefix as corroborating evidence. Full reasoning:
`run2/phase2-reuse-decision.md`.

## What the suite actually returned

Main run, `bash oracle/run-oracle-suite.sh` inside `nix develop`, 13:29:58 → 13:54:26, exit 1:

```
pass 1 (parallel, -n 6, not xdist_serial and not slow, budget 1300s): FAILED (exit 1)
pass 2 (serial, xdist_serial and not slow, budget 900s):             TIMED OUT (exit 124)
```

- Pass 1: `1 failed, 586 passed, 3 skipped, 4 xfailed in 567.62s`. Sole failure
  `test_oracle_interface.py::TestMixedFormulas::test_mixed_and_box_next`, `OracleTimeoutError` at
  60000 ms (temporal_depth=1, M=3). Attempt 1 produced an identical verdict on the same test —
  two independent quiet-machine observations.
- Pass 2: SIGTERM'd at its 900 s budget after 7 of 10 tests, hanging in
  `test_soundness_regression.py::TestStateIsolationRegression::test_temporal_propositional_interleaving`.
  Two of the 7 completed tests failed.
- No strict-xfail XPASS: pass 1's JUnit records `{'pytest.skip': 3, 'pytest.xfail': 4}`.
- Collection matched the pins exactly: 606 = 594 + 10 + 2.

Per-test adjudication, all machine captures, and the follow-up list:
`specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-baseline-STATUS.md`.
The run itself: `baselines/oracle-run-RED-2026-08-09.txt`.

## Machine-quietness evidence, including a correction

| Run | Before | After | Adjudicable? |
|---|---|---|---|
| Main gating run | load 0.34–0.56, no foreign CPU consumer | load 1.85–2.22, no foreign CPU consumer | **yes** |
| Pass-2 re-run | `lean` at 61.7% / 110% | clean | **no** |
| Isolated re-run of 4 failing nodes | `lean` at 493% | `runLinter` at 770–776%, `lean --worker` 121–190% | **no** |

**A correction I made mid-task and am recording rather than hiding.** I initially reported the
pass-2 re-run as running on a verified-quiet machine. That was wrong. The live display filter I
used to read the capture files selected only their section-label lines, so it hid the CPU-hog
lines the captures had correctly recorded. On re-auditing the raw files I found a sibling
project's Lean lint job had been contending throughout. I retracted the "verified quiet" claim,
marked both re-runs unadjudicable, and re-derived the verdict from the main run alone — which
satisfies a category (c) trigger ("a pass classified `TIMED OUT` on a verified-quiet machine") by
itself, so the conclusion survives without them.

This matters beyond bookkeeping: three failures observed only in the contended runs
(`test_spot_check_individual_countermodels`,
`test_known_conclusive_population_self_consistent`, and
`test_regression_all_active_examples[BM_CM_1-example_case7]`) are explicitly **not** adjudicated,
and are handed to the next dispatch to re-derive on a quiet machine.

## Phase 5 — gate repair (committed, verified)

**Step 3** — re-pinned from a stale 550 to the measured 606, with three new exact-equality
sub-count pins (594 / 10 / 2) plus a partition check. A latent bug was caught while writing it:
pytest prints `594/606 tests collected (12 deselected)` once a marker deselects anything, so the
original `[0-9]+ tests? collected` extractor would have read the **total** back for every
sub-count and the new pins would have silently checked nothing. The extractor now takes the
numerator. Verified live: total 606, parallel 594, serial 10, slow 2.

**Step 5** — the `XFAIL_LINES=(767 942 1020 1133 1431)` line-number pin was deleted (the file it
pinned now contains zero `xfail(` markers) and replaced with content-matched checks: the defect
record exists and is non-empty (5a); the five guard assertions are each present exactly once and
in their required order (5b); the four floor/budget constants hold their pinned values (5c); all
four `xfail(` markers are `strict=True` (5d). Line numbers are used only to compare *relative*
order, never pinned.

**Step 6** — now runs `bash oracle/run-oracle-suite.sh` instead of an unfiltered
`pytest oracle/bimodal_logic/tests/ -q` that, with no reachable ini file to filter the `slow`
marker, silently dragged the 60–90 minute exhaustive sweep into every gating run. Any non-zero
runner exit increments `FAILURES`, including the xdist preflight refusal.

**Header prose** rewritten; Steps 1, 2, 4, 7 untouched.

### Negative test (all four mutations required, all four detected)

Run against scratch trees under `run2/negative/`. Control (unmodified copy): Step 5 **passes**.

| Mutation | Step 5 message |
|---|---|
| (i) delete `assert not unclassified` | `FAIL: Step 5b: guard assertion 'assert not unclassified' appears 0 time(s) in oracle/bimodal_logic/tests/test_cross_oracle_differential.py, expected exactly 1` |
| (ii) transpose `assert not mc_soundness_bug` / `assert not bad_signature` | `FAIL: Step 5b: guard assertion 'assert not unclassified' (line 1419) is out of order — it must follow 'assert not mc_soundness_bug' (line 1454); the ordering is what makes each failure self-diagnosing` and `FAIL: Step 5b: guard assertion 'assert not bad_signature' (line 1406) is out of order — it must follow 'assert external_bh_defect' (line 1436); …` |
| (iii) lower `MIN_CONCLUSIVE_GATING_FORMULAS` 100 → 1 | `FAIL: Step 5c: MIN_CONCLUSIVE_GATING_FORMULAS in oracle/bimodal_logic/tests/test_cross_oracle_differential.py is '1', expected exactly 100 — a floor or budget was changed` |
| (iv) remove one `strict=True` | `FAIL: Step 5d: only 3 of 4 xfail( markers in oracle/bimodal_logic/tests/test_oracle_interface.py are strict=True — a non-strict xfail silently absorbs an XPASS` |

## New finding: an in-package failure the repaired gate surfaced

`bash code/scripts/verify-refactor.sh --skip-oracle` exits **1**, not 0. Steps 1, 2, 3 and all of
Step 5 pass; Steps 4 and 7 — which the plan explicitly says to leave untouched — fail:

```
FAILED code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_cases[BM_CM_1-example_case7]
E       AssertionError: Test failed for example: BM_CM_1
1 failed, 297 passed in 138.47s
```

It fails on **both** attempts (the retry allowance for the documented Z3 flake does not absorb it),
deterministically and fast — an assertion, not a timeout. It names the same example case,
`BM_CM_1` / `example_case7`, as the oracle-side boundary-regression failure, so it is very likely
the same underlying defect with a much better handle on it: deterministic, fast, and independent
of any solve budget. It was not repaired (explicit non-goal) and is reported as a blocker.

## Phases not started

- **Phase 4** (exhaustive-scan coverage record, 60–90 min serial) — not started.
- **Phase 7** (independent `verify-refactor.sh` with Step 6 live, 25–40 min) — not started.

Both require an otherwise-idle machine. At the point they came due, a sibling project's Lean
toolchain was consuming 168–216% CPU, and earlier in the session up to 776%. The plan is explicit:
"Not quiet before: wait and re-check. Do not start", and "If the machine cannot be made quiet …
stop and report rather than running contended. Every result obtained under contention is
unadjudicable." Starting either would have consumed 60–90 minutes to produce something that could
not be promoted. Evidence: `run2/machine-before-phase7.txt`.

## Plan Deviations

1. **JUnit merge not performed.** `run2/merge-junit.py` was written as specified, but no pass-2
   JUnit exists — both pass-2 executions were SIGTERM'd mid-test and pytest writes `--junitxml`
   only at session teardown. Publishing pass 1's 594-test XML as `junit-oracle.xml` would
   misrepresent a partial as the 604-test gating report, so it was deliberately not done.
2. **Phase 2's "neither pass TIMED OUT" clause is not satisfied**, and this is the finding rather
   than a process failure: the plan pre-declares that a repeat timeout on a quiet machine "is a
   genuine finding for Phase 3 to record, never a reason to raise `ORACLE_PASS*_TIMEOUT`".
3. **Pass 2 was re-run alone** rather than by re-running the whole runner — the action Phase 2's
   verification clause specifies verbatim. The re-run then turned out to be contended and is
   excluded from the adjudication.
4. **Phase 3's isolated re-run is excluded from the adjudication** for the same contention reason,
   so three failures remain unadjudicated. Within the plan's cap (one isolated re-run, no
   confirming full pass); no further attempts were made, since repeating runs until a clean one
   appears is exactly what the standing prohibitions forbid.
5. **Phase 5's `--skip-oracle` exits 0 criterion is not met** — due entirely to Steps 4 and 7,
   which Phase 5 is instructed not to modify. Phase 5's own scope (Steps 3, 5, 6) is fully green.
6. **Phase 6's marker flip was not performed** — correct behaviour: its gate requires category (a)
   or a resolved (b). The category-(c) framing correction was done instead.
7. **Phases 4 and 7 not started** — machine contention, per the plan's own stop-and-report rule.
8. **A mid-task reporting error was corrected**, described under machine-quietness above.

## Nothing was weakened

- `git diff --stat -- oracle/bimodal_logic/` is empty. No oracle test file was modified.
- No `MIN_CONCLUSIVE_*` floor, no `*_SOLVE_TIMEOUT_MS`, no `ORACLE_PASS*_TIMEOUT`, no marker, no
  `xfail`, no `deselect`, and no `-m` filter was added, broadened, or retuned.
- Step 3's `!=` exact-equality comparison was kept and *extended* to three more counts, not
  relaxed to a `>=` floor.
- The committed partial `baselines/oracle-run.txt` was not overwritten.
- The only `oracle/` change is the additive, opt-in `ORACLE_JUNIT_DIR` hook in
  `run-oracle-suite.sh`, inert when the variable is unset.

## Session 2 (2026-08-09 evening / 2026-08-10): Phases 7, 4, and 8

The earlier "Phases 4 and 7 not started" and "Phases not started" statements above describe the
state at the end of session 1 and are superseded here. Nothing above was rewritten; this section
records what changed.

### Phase 7 — COMPLETED. The gate ran end to end and it is RED, more so than first recorded.

`nix develop --command bash -c 'bash code/scripts/verify-refactor.sh'`, 23:16:57-23:45:56Z
(28m59s), **exit 1, "3 check(s) FAILED"** (Steps 4, 6, 7). **Step 6 executed, not `SKIPPED`.**
`--skip-oracle` run separately: **exit 1**, 2 checks FAILED (Steps 4, 7). Machine verified quiet
before, during (continuous 60 s sampling), and after — **this run is adjudicable**.

Three findings, all recorded in `baselines/oracle-baseline-STATUS.md` with raw evidence in
`baselines/gate-run-2026-08-09/`:

1. **A new failure.** Step 6 pass 1 returned `2 failed, 584 passed, 4 skipped, 4 xfailed` where
   the first adjudicable run returned `1 failed, 586 passed, 3 skipped, 4 xfailed`.
   `test_mixed_and_all_future_neg` appears in **no earlier record** (verified: zero occurrences in
   `oracle-run-RED-2026-08-09.txt`), same mode as the adjudicated failure —
   `OracleTimeoutError`, 60000 ms, depth=1, M=3. The failing set grew on an unchanged tree
   between two quiet-machine runs. The budget was not widened in response.
2. **Two previously-unadjudicable failures are now adjudicated.** Pass 2's progress line, mapped
   against the established collection order, shows
   `test_known_conclusive_population_self_consistent` and
   `test_spot_check_individual_countermodels` both FAILING on a verified-quiet machine — the
   earlier record had to leave all three open. `test_regression_all_active_examples[BM_CM_1-example_case7]`
   FAILED here having PASSED before, now consistent with the in-package Step 4 failure on the same
   example. This obviated the separately-suggested re-derivation run.
3. **Step 7's failure is a consequence, not an independent finding.**
   `compare_bimodal_baseline.sh` runs under `set -euo pipefail`; its first pytest pipeline exits
   non-zero on `BM_CM_1-example_case7`, so it aborts after printing `Running bimodal test
   suite...` and never reaches its comparison logic. Its "reported regressions" message is
   misleading in this case — nothing was compared. Recorded, not repaired.

Step 4 failed on both attempts on exactly `test_example_cases[BM_CM_1-example_case7]`
(`1 failed, 297 passed`), in both the full run and the `--skip-oracle` run — the already
adjudicated defect and no other test, which is what the corrected `--skip-oracle` criterion asks
for.

### Phase 4 — BLOCKED. Exhaustive scan attempted twice, neither attempt adjudicable.

| Attempt | Window | Quiet at launch | Outcome |
|---|---|---|---|
| 1 | 22:54:17-23:06:28Z | load 1.05-1.14 | Contention at **+85 s** (cslib `lean --worker` 291-467%, `lake` 794.8%, load1 -> 11.52). Aborted at formula 14/274. |
| 2 | 23:57:44-~01:07Z | load 0.57-0.76, **zero** lean/lake | Clean ~46 min through formula ~215, then `lean --worker` 285%/205% transient and ~100% **sustained** from 00:47. Terminated at formula 234/274 (~85%). |

`SCAN_COMPLETE` and `report.json` never written in either attempt. Neither run's per-formula
outcomes were triaged or promoted: the scan's verdict per formula is decided by a 10 s wall-clock
solve budget, which is exactly what contention corrupts.

Marked `[BLOCKED]`, **not** `[COMPLETED]` via the red/incomplete branch: that branch requires the
quiet-machine captures, which an unadjudicable run cannot supply, and recording an environmental
non-result there would misrepresent it as a category (c) finding about the scan.
`baselines/exhaustive-scan/` was deliberately **not** created — the plan forbids manufacturing
anything to fill the gap. The 2 `slow` tests remain unaccounted for.

### Phase 8 — COMPLETED.

`run2/` removed (`run/` untouched); empty `baselines/serial-rebaseline/` removed; this session's
two gitignored `oracle/scan-results/` scratch dirs removed. Staged narrowly against concurrent
session activity in `specs/116`, `specs/129`, `specs/138`, `specs/events.jsonl`, and
`specs/.orchestrator-multi-state.json` — none staged.

### Session 2 deviations

1. **Phase 7 was run before Phase 4** — shorter run (25-40 min vs 60-90 min), and this host's
   quiet windows proved short. The phases are independent (7 depends on 5 and 6; 4 on 3), so this
   is ordering, not a dependency violation.
2. **Phase 7's "confirm the failure is ... not a new one" criterion is NOT met** — see finding 1
   above. Recorded as an enlargement of the category (c) result; nothing relaxed in response.
3. **Quietness deviation, recorded with reasoning.** Idle cslib `lean --worker` LSP processes were
   present at the Phase 7 launch, which the quietness rule names categorically. Adjudicated
   non-contending **on measurement** (<=5.9% lifetime-average CPU, absent from every instantaneous
   top-20 sample), not waived by assumption — the same class of deviation Phase 1 recorded for its
   load-average threshold.
4. **Evidence promoted before cleanup (addition, not omission).** `baselines/gate-run-2026-08-09/`
   was created to hold the raw evidence `oracle-baseline-STATUS.md` cites, because Phase 8 deletes
   the `run2/` staging area those citations pointed into. All `run2/` references in that file were
   repointed; zero remain.
5. **A monitor threshold was retuned mid-session, not a test threshold.** The contention watcher's
   load alarm was raised from 6.0 to 14.0 after verification that load above 6 during Phase 7 was
   this run's own `-n 6` workers (four `python3` at 99.7% each, every `lean` <=5.9%). No test
   budget, floor, or assertion was involved.

### Nothing was weakened in session 2 either

`git diff --stat -- oracle/bimodal_logic/` is still empty. No assertion, solve-timeout budget,
`MIN_CONCLUSIVE_*` floor, marker, guard, or `xfail` strictness was relaxed, retuned, or deleted.
`known_conclusive_complexity5.json` was not re-derived; `SELF_SCAN_SOLVE_TIMEOUT_MS` and
`ORACLE_EXHAUSTIVE_TIMEOUT` are untouched. `--skip-oracle` was not added to make the gate green,
and the gate is reported as failing because it fails.

## Follow-up required

1. Diagnose `test_example_cases[BM_CM_1-example_case7]` — deterministic, fast, and the best handle
   on what is probably also the oracle-side `BM_CM_1` failure.
2. On a machine with no Lean or Z3 workload: adjudicate the three currently-unadjudicated pass-2
   failures, and diagnose why `test_temporal_propositional_interleaving` does not terminate within
   900 s and why `test_mixed_and_box_next` no longer decides within 60000 ms.
3. Run Phase 4 (exhaustive scan) and Phase 7 (full gate with Step 6 live).
4. Only then consider whether any budget is genuinely mis-calibrated — with measurement to justify
   it, not to rescue a red run.
