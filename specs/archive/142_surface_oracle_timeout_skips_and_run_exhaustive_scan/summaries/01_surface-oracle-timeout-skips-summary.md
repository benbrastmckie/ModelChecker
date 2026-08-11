# Implementation Summary: Surface Oracle Timeout Skips and Record Scan Cadence

- **Task**: 142 - Surface the two timeout-conditional pytest.skip sites, adjudicate wrong
  expected_sat labels, record exhaustive-scan cadence, address get_theory(config)
- **Status**: [COMPLETED]
- **Started**: 2026-08-10T21:20:00Z
- **Completed**: 2026-08-10T22:35:00Z
- **Effort**: ~5.5 hours (dominated by three full-suite Z3 solver runs: a ~15-minute Phase 1
  baseline, a ~15-minute Phase 3 spot-check, and a ~30-minute Phase 4/7 full gating-suite run)
- **Dependencies**: None
- **Artifacts**: plans/01_surface-oracle-timeout-skips.md, this summary

## Overview

All 7 phases of the plan are complete and verified. The gating suite's pass/fail verdict is
unchanged (both passes still `PASSED`, exit code 0); the only externally visible behavioral
change is that skip reasons and a classified timeout-skip inventory now print in every gating
run, and three previously-wrong `expected_sat` labels are corrected. No skip was converted to a
failure and no solve budget was widened, per the task's explicit constraints.

## What Changed

- **Ground-truth hard gate (Phase 1)**: independently re-derived `bimodal_logic.ground_truth
  .ground_truth_verdict` for the unfolded forms of `all_future(some_past(A))` (`TN_TH_2`) and
  `all_future(A)` (`TN_CM_1`/`BM_TH_1`) at windows 4, 5, and 6 — `SAT` and stable at every
  window, matching the research report exactly. Recorded in
  `baselines/ground-truth-reconfirmation.txt`.
- **Pre-change baseline (Phase 1)**: captured the targeted subset run (`-k
  "TestOracleExampleRegressionViaAPI or TestEnrichedRoundTrip"`) before any code change: 74
  passed, 2 skipped (`TN_TH_2` at line ~635, `all_future` at line ~779), 32 deselected, 853s.
  Recorded in `baselines/phase1-baseline-run.txt` with `uptime` before/after.
- **`TestCatalogLabelAdjudication` (Phase 1)**: new test class in `test_oracle_interface.py`
  that independently re-derives the ground-truth verdict at test time and pins each corrected
  label against it — confirmed RED (3 distinct assertion failures) before the label edit.
- **Three label corrections (Phase 2)**: `EXAMPLE_JSON_CATALOG["TN_TH_2"]`,
  `["TN_CM_1"]`, and `["BM_TH_1"]` all corrected `expected_sat` from `False` to `True`, with
  comments recording the ground-truth provenance. `REGRESSION_TIMEOUT_EXAMPLES` left
  byte-identical — re-inclusion of `TN_CM_1`/`BM_TH_1` is an explicit follow-up (see below).
  `TN_TH_2` still reports `SKIPPED` after the correction (the solver does not decide it at 2x
  budget) — a visibility improvement, not a new green, exactly as the plan predicted.
- **Timeout-skip inventory (Phase 3)**: `oracle/conftest.py` gained
  `pytest_runtest_logreport`/`pytest_terminal_summary` hooks that classify every
  timeout-conditional skip in a session as `[KNOWN]` / `[NEW]` / `[RESOLVED]`, printed in a
  `== ORACLE TIMEOUT-SKIP INVENTORY ==` section. The session's *seen* node-id set is derived
  from logreport events (never a static list), so a two-pass run never reports one pass's known
  skip as "resolved" in the other pass's session. An opt-in `ORACLE_SKIP_REPORT` JSON artifact
  mirrors the printed classification. 15 new unit tests in
  `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py`, all passing.
- **Gating runner wiring (Phase 4)**: `oracle/run-oracle-suite.sh` now passes `-rs` on both
  passes and adds an `ORACLE_SKIP_REPORT_DIR` opt-in (mirroring `ORACLE_JUNIT_DIR`) that writes
  one JSON artifact per pass. Pass budgets, `-m` expressions, `-n 6`, and the
  `_classify`/exit-code logic are untouched.
- **Exhaustive-scan cadence decision (Phase 5)**: recorded in `TESTING_GUIDE.md` section 8.8 —
  scheduled, off-hours, never gating, backed by two independent code-current
  `SCAN_COMPLETE`-verified runs (both `disagreements: 0`, ~59-61 min). Shipped
  `oracle/check-scan-freshness.sh`, the staleness-alerting mitigation the research required;
  verified fresh (newest run 0.7 days old), stale (`ORACLE_SCAN_MAX_AGE_DAYS=0`), and no-marker
  (absent `scan-results/`) paths, all correct.
- **`get_theory(config)` documentation (Phase 6)**: expanded the docstring at
  `bimodal/__init__.py`, `imposition/__init__.py`, and `exclusion/__init__.py` to state the
  actual signature-uniformity-placeholder contract. Docstring-only diff; conformance suite (50
  tests) passes; `bimodal.get_theory(['extensional'])['operators'].operator_dictionary` still
  has the same 17 entries as before.
- **Full-suite verification (Phase 7)**: `ORACLE_SKIP_REPORT_DIR=... bash
  oracle/run-oracle-suite.sh` inside `nix develop` — both passes `PASSED` (605 passed / 2
  skipped / 4 xfailed in 964s; 14 passed / 613 deselected in 803s), exit code 0. The inventory
  named exactly the two known entries (`[KNOWN]` for `TN_TH_2` and `all_future`) with no `[NEW]`
  and no `[RESOLVED]` lines, in both the printed section and the two JSON artifacts. The 4
  xfails are pre-existing, unrelated entry-point-discovery markers (`strict=True`,
  `_ENTRY_POINT_XFAIL_REASON`), confirmed unrelated to this change. Added a timeout-skip
  inventory subsection to `TESTING_GUIDE.md` section 8.8 describing `[KNOWN]`/`[NEW]`/
  `[RESOLVED]` semantics.

## Decisions

- Combined the Phase 7 TESTING_GUIDE.md subsection (describing the timeout-skip inventory) into
  the same section-8.8 edit made for Phase 5's cadence decision, rather than as a second,
  separately-timed edit — both land in the same subsection of the same file and the plan's own
  phase-territory table already lists TESTING_GUIDE.md section 8.8 as Phase 5's territory. No
  content was omitted; this is a sequencing consolidation, not a scope change.
- Used `bimodal.get_theory(['extensional'])['operators'].operator_dictionary` (17 entries) to
  verify Phase 6's "17 operators" invariant instead of the plan's literal
  `len(bimodal.get_theory(...)['operators'])`, which raises `TypeError` because
  `OperatorCollection` has no `__len__`. The underlying claim (17 operators, unchanged) is
  identical; only the verification command needed correcting for the real API shape.
- Ran the Phase 4 full-suite verification (`ORACLE_SKIP_REPORT_DIR=... bash
  oracle/run-oracle-suite.sh`) once and used the same run to satisfy Phase 7's full-suite
  verification requirement, rather than running the ~18-30 minute suite twice. Both phases'
  verification criteria are checked against the single run's output.

## Plan Deviations

- None beyond the two consolidations noted under Decisions above (both documentation-adjacency
  and verification-command corrections, not scope or behavior changes). Every plan checklist
  item is checked off; no task was skipped, altered in substance, or deferred beyond what the
  plan's own Scope Boundary table already designated as follow-up work.

## Impacts

- Every future gating run of `oracle/run-oracle-suite.sh` now prints skip reasons and a
  classified timeout-skip inventory — a `[NEW]` line is the actionable signal that a future
  contributor needs to adjudicate before assuming an existing label is correct, and a
  `[RESOLVED]` line is the signal that a formula that used to time out now decides, which should
  prompt revisiting its label and its `REGRESSION_TIMEOUT_EXAMPLES` membership.
- `oracle/check-scan-freshness.sh` gives an operator (or a future scheduled job) a way to detect
  a silently-broken exhaustive-scan cadence before institutional memory is the only signal.
- The three corrected labels remove a latent trap: a future encoding improvement that made
  `TN_TH_2`, `TN_CM_1`, or `BM_TH_1` decide within budget would previously have hard-failed the
  regression assertion against a wrong label; it will now assert against the ground-truth-correct
  one.

## Follow-ups

Recorded in the research's priority order (none created as tasks by this implementation, per the
plan's Scope Boundary):

1. **Investigate the primitive `untl`-based expansion's performance for `all_future`-shaped
   formulas** (highest priority) — confirmed SAT with a two-atom witness, yet undecided at
   180000ms in primitive form vs. under 2s in enriched form; implicated in both the site-779 skip
   and `BM_TH_2`'s continued timeout.
2. **Re-examine `TN_CM_1`/`BM_TH_1`'s `REGRESSION_TIMEOUT_EXAMPLES` exclusion** now that their
   labels are corrected — both decide in ~1.79s in a live probe, so the exclusion looks stale,
   but re-inclusion needs fresh multi-run timing evidence on an idle machine, sequenced strictly
   after (not part of) this label fix.
3. **Investigate `BM_TH_2` (`all_past(A)`) vs. its Until-mirror `all_future(A)`** — correctly
   labeled but 60s+ timeout vs. ~1.79s for the structurally symmetric future-side formula.
4. **Add a scheduled (never gating) periodic exhaustive-scan run** — e.g. weekly or
   merge-to-main, off-hours, invoking `oracle/run-oracle-exhaustive-scan.sh` unmodified; this
   task recorded the cadence decision and shipped the freshness checker but did not wire an
   actual CI schedule, which needs its own runner-capacity evaluation.
5. **Make `get_theory` fail loudly on a non-`None` `config`** across `bimodal`, `imposition`,
   and `exclusion`, then fix the ~15 call sites currently passing a silently-ignored
   subtheory-shaped list — a breaking change disproportionate to fold into this task, per the
   research's own recommendation.
6. **Follow up on `MD_TH_2`'s exclusion-reason/payload mismatch** — its `EXAMPLE_JSON_CATALOG`
   JSON is a bare atom (trivially fast) but its `REGRESSION_TIMEOUT_EXAMPLES` comment says
   "timeout-prone"; not independently verified by the research or this task.
7. **Surface the 7 other `except OracleTimeoutError:` sites** in `test_oracle_interface.py`
   (silent `continue` at lines ~1181/1205/1233, silent `return` at ~826/930) — strictly worse for
   visibility than the two named `pytest.skip()` sites this task addressed, since they produce no
   signal in `-rs` output at all; deserves its own design pass rather than a drive-by fix.

## References

- `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/reports/01_oracle-timeout-skips-scan.md`
- `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/plans/01_surface-oracle-timeout-skips.md`
- `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/baselines/` (ground-truth
  re-confirmation, Phase 1 baseline, Phase 4/7 full-suite run and skip-report JSON artifacts)
- `oracle/bimodal_logic/tests/test_oracle_interface.py`
- `oracle/conftest.py`
- `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py`
- `oracle/run-oracle-suite.sh`
- `oracle/check-scan-freshness.sh`
- `oracle/run-oracle-exhaustive-scan.sh`
- `code/docs/core/TESTING_GUIDE.md` (section 8.8)
- `code/src/model_checker/theory_lib/{bimodal,imposition,exclusion}/__init__.py`
