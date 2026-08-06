# Implementation Summary: Make the oracle suite fast and observable

- **Task**: 138 - make_oracle_suite_fast_and_observable
- **Status**: [COMPLETED]
- **Started**: 2026-08-06T15:02:00Z
- **Completed**: 2026-08-06T19:41:00Z
- **Effort**: ~11 hours agent work, plus ~60.7 minutes unattended wall clock for the Phase 4
  exhaustive derivation run
- **Dependencies**: Task 133 (`find_countermodel`/`OracleTimeoutError` contract) — preserved
  unmodified throughout
- **Artifacts**: plans/01_oracle-suite-fast-observable.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Split the `oracle/` test suite into a fast gating variant and an explicitly-invoked exhaustive
variant, instrumented the shared scan core with progress streaming and a completion-marker
contract, persisted a known-conclusive baseline so the gating variant asserts soundness without
re-solving known timeouts, wrapped every long-running pass in a bounded `timeout`, and documented
the split in all three places that describe how to run the suite. All seven planned phases
completed; the two protected assertion primitives (`_assert_scan_report`,
`SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_SCAN_FORMULAS`) remain byte-for-byte unmodified in
the final diff.

## What Changed

- `_generate_differential_report()` (the single shared scan core both entry points call) gained
  three optional, default-off parameters: `progress_path` (flushed per-formula JSONL),
  `heartbeat_every` (stdout heartbeat/loud lines), and `artifact_dir` (writes `report.json` then a
  `SCAN_COMPLETE` completion marker, atomically, strictly after the report is closed). Default
  (unset) behaviour is unchanged from before instrumentation existed.
- New `oracle/scan_runner.py`: a thin CLI delegating entirely to the shared core (zero
  `find_countermodel` calls of its own) for bounded/ad-hoc scans.
- New `oracle/run-oracle-exhaustive-scan.sh`: drives `pytest oracle -m slow -s` under
  `timeout --kill-after=60s`, reports completion from the `SCAN_COMPLETE` marker (never process
  exit), and classifies exit 124/137 as `TIMED OUT` distinct from `FAILED`.
- `oracle/run-oracle-suite.sh` now deselects `slow` on both passes
  (`not xdist_serial and not slow` / `xdist_serial and not slow`), wraps both passes in
  `timeout --kill-after=60s` (`ORACLE_PASS1_TIMEOUT`/`ORACLE_PASS2_TIMEOUT`, calibrated to
  1300s/900s from real measurement), and classifies timeouts distinctly from failures.
- New `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`: a persisted baseline
  manifest (index + canonical `formula_json` per entry) re-derived from a fresh serial exhaustive
  run (274 formulas, 0 disagreements, 103 conclusive).
- New `TestGatingConclusiveScan` (xdist_serial, not slow): solves only the manifest's
  known-conclusive subset via the unmodified `_assert_scan_report`, gated by a new, separate
  `MIN_CONCLUSIVE_GATING_FORMULAS = 100` constant. A structural drift guard
  (`_verify_manifest_matches_enumeration`) re-enumerates and cross-checks the manifest before any
  solving.
- `test_report_writes_to_file` relocated out of the `slow`-marked `TestFullScanReport` into a new
  `TestComplexity3ScanReportWriting` (adds coverage to the gating pass at zero cost).
- New `code/docs/core/TESTING_GUIDE.md` section 8.8 ("Oracle Suite: Gating vs. Exhaustive Split")
  and an updated "Running the Test Suite" section in `oracle/bimodal_logic/README.md`.
- `oracle/.gitignore` added, ignoring `scan-results/`.

## Decisions

- Instrumentation lives inside the one shared scan function as default-off parameters (Decision
  D1), so the ~30 existing call sites are untouched and there is never a second solve loop to
  drift.
- The exhaustive runner drives `pytest -m slow -s` directly rather than reimplementing the scan
  (Decision D2); `test_complexity_5_scan_self_consistent` reads the `ORACLE_SCAN_OUT_DIR`
  environment variable to opt into artifact emission, defaulting to today's unset behaviour.
- Baseline manifest identity is (0-based index, canonical `formula_json`), never index alone
  (Decision D3), so an enumerator change fails loudly with an explicit re-derivation message rather
  than silently misaligning.
- `MIN_CONCLUSIVE_GATING_FORMULAS = 100` is a separate constant from
  `MIN_CONCLUSIVE_SCAN_FORMULAS`, derived from the manifest's `conclusive_count=103` minus slack
  for the 8.646s slowest observed conclusive solve against the 10000ms budget.

## Impacts

- The gating suite (`oracle/run-oracle-suite.sh`) runs in ~16.1 minutes on an idle machine (649.09s
  + 318.57s), a ~4.76x speedup over the ~76.7-minute pre-change baseline, while both assertion
  teeth (soundness, conclusiveness floor) remain live and unweakened.
- The exhaustive sweep (`oracle/run-oracle-exhaustive-scan.sh`) is no longer part of routine
  testing; it is invoked explicitly, primarily to re-derive the baseline manifest.
- Total collected test count: 572 (was 559), +13 net new tests, none removed or skipped.
- **Environmental finding, documented not remediated**: re-running the full gating suite three
  times during Phase 6 under sustained, externally-verified CPU contention (an unrelated
  `lean --worker` proof-search process at 300-1200% CPU on this shared machine) intermittently
  missed `MIN_CONCLUSIVE_GATING_FORMULAS` (98-99/103 vs. 103/103 clean), and two **pre-existing**
  `xdist_serial` tests this task never touched failed with the identical `OracleTimeoutError`
  pattern in the same runs — confirming this is the pre-existing "tight solve-budget headroom"
  sensitivity `oracle/conftest.py` and `TESTING_GUIDE.md` section 8.6 already document, not a
  regression this task introduced. `disagreements == 0` held in every single attempt. Per the
  task's hard constraint, no threshold was adjusted to force green; the clean idle-machine
  measurement stands as the recorded "green end to end" evidence, and the finding is documented in
  Phase 6 of the plan and in TESTING_GUIDE.md 8.8's cross-reference to 8.6.

## Follow-ups

- None required by this task. The environmental contention finding above is informational, not a
  blocker: it reflects a pre-existing, already-documented category of flakiness in tight-budget Z3
  solve tests under heavy unrelated machine load, orthogonal to this task's scope (`oracle/` +
  `TESTING_GUIDE.md`) and to the two follow-up tasks the prior oracle-contract work already spawned
  (MC/BH disagreement resolution and the oracle regression baseline).

## Plan Deviations

- None (implementation followed the plan). One clarification worth recording: Phase 3's task list
  did not explicitly enumerate wiring `test_complexity_5_scan_self_consistent` to
  `ORACLE_SCAN_OUT_DIR`, but Decision D2 requires it (the exhaustive script must get artifacts by
  driving pytest directly) and Phase 3's territory note explicitly scopes that phase to "only the
  `TestFullScanReport` class body" — exactly where that test lives — so the wiring was implemented
  there as the natural realization of D2 within the phase's own declared territory, not a
  deviation from it.

## References

- `specs/138_make_oracle_suite_fast_and_observable/plans/01_oracle-suite-fast-observable.md`
- `specs/138_make_oracle_suite_fast_and_observable/reports/01_oracle-suite-fast-observable.md`
- `specs/138_make_oracle_suite_fast_and_observable/baselines/derivation-run/` (raw JSONL, report,
  marker from the baseline-deriving run)
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `oracle/scan_runner.py`, `oracle/run-oracle-exhaustive-scan.sh`, `oracle/run-oracle-suite.sh`
- `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`
- `code/docs/core/TESTING_GUIDE.md` (section 8.8)
- `oracle/bimodal_logic/README.md`
