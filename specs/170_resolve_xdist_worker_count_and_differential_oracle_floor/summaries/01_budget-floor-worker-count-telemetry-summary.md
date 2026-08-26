# Implementation Summary: Resolve xdist worker count and differential oracle floor

- **Task**: 170 - Resolve xdist worker count and differential oracle floor
- **Status**: [COMPLETED]
- **Started**: 2026-08-26T09:00:00Z
- **Completed**: 2026-08-26T09:34:00Z
- **Effort**: ~3.5 hours (5 phases, all closed in one dispatch)
- **Dependencies**: None
- **Artifacts**: plans/01_budget-floor-worker-count-telemetry.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Implemented all 5 phases of the plan, resolving the task's four items (B/C/A/D) in evidence
order. B was already closed and untouched. C (the example solve-budget floor) landed on a
re-measured, larger scope than the research report assumed. A (the xdist worker count) was
decided via a bounded falsification screen, taking the clean branch. D (the Python 3.12 xdist
worker crash) received instrumentation only, with root cause explicitly left open.

## What Changed

- **Item C**: `code/tests/ci/test_example_budget_floor.py`'s `_COVERED` extended from the four
  `logos/subtheories/*/examples.py` files to seven (adding `bimodal`, `exclusion`, `imposition`).
  A re-scan at implementation time found **57** below-floor `max_time` dicts (bimodal 21,
  exclusion 26, imposition 10) — not the research report's 22. The extra 35 sit at `max_time: 5`
  and had never been measured; all 35 were measured isolated (0.012s-1.549s, 6.5x-800x headroom
  over the 10s floor) before being raised, alongside the already-measured 22-item `2`/`3` cohort.
  All 57 raised to exactly 10; `BM_CM_1` (60) and `BM_CM_4` (120) untouched.
- **Item A**: Ran a four-draw falsification screen (`taskset -c 0,1,2,3`, two draws each at
  `-n 6`/`-n 4` over the full 2323-test gating selection). All four pairwise diffs
  (cross-`-n` x2, within-`-n` x2) were empty — outcome CLEAN. Changed `-n 6` to `-n 4` in both
  `.github/workflows/tests.yml` and `flake.nix`, with `test_workflow_parity.py`'s
  `test_worker_count_matches` demonstrated RED on a one-sided edit first. `timeout-minutes: 20`
  left unchanged (no systematic `-n 4` slowdown observed: ~5% average difference, inside the
  draw-to-draw spread).
- **Item D**: Added `.github/scripts/worker_rss_sample.py`, a `/proc`-only (no new CI
  dependency) peak-RSS-per-xdist-worker sampler, unit-tested by 20 hermetic tests
  (`code/tests/ci/test_worker_rss_sampler.py`) and live-smoke-tested against a real
  `pytest -n 2` process. Wired into `tests.yml`'s existing "Run general test suite" step,
  3.12-gated and strictly non-gating (sampler failure never affects the step's own exit code,
  which is determined solely by `wait`ing on the backgrounded pytest process).
- **Item B**: No code change (closed prior to this task); the hard-constraint gate in Phase 5
  reconfirmed `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` has zero diff and
  both its constants (`GATING_RECHECK_SOLVE_TIMEOUT_MS`=40000, `MIN_CONCLUSIVE_GATING_FORMULAS`=100)
  are unchanged.
- Documentation: `code/docs/core/TESTING_GUIDE.md` section 8.13 rewritten to record the actual
  57-item widening and the `-n` change; section 8.11 extended with a full D subsection (root
  cause not determined, three live hypotheses, telemetry added, deliberately left open).

## Decisions

- Re-scanned rather than trusted the research report's "22" figure, per the plan's explicit
  Scope Hypothesis — confirmed 57 at RED, exactly matching the AST re-scan.
- Measured the previously-unmeasured `max_time: 5` cohort (35 examples) in isolation before
  raising it, using direct `run_test()` calls rather than pytest for three bimodal names not
  collected by any test suite (`TN_CM_1`, `MF_MODAL_FUTURE_TH` via `KNOWN_TIMEOUT_EXAMPLES`;
  `BM_TH_5` never added to `unit_tests`), since the AST-based floor guard scans the source file
  directly, independent of pytest collection.
- Applied the plan's three-branch decision rule to Phase 2's CLEAN outcome exactly as written:
  changed `-n` to 4, retained the `-n 6`-over-`auto`/`BM_CM_1` rationale verbatim, appended the
  new evidence and an explicit "falsifies, does not prove CI-safe" statement plus a named revert
  trigger.
- Chose a `/proc`-only sampler implementation over `psutil`, per the plan's stated preference,
  since `ubuntu-latest` always has `/proc` and this avoids a new CI dependency entirely.
- Backgrounded the parallel-pass pytest invocation unconditionally (not per-branch) in
  `tests.yml` so the file keeps exactly one literal `pytest ... -n 4 ...` line — a first,
  per-branch-duplicated attempt broke `test_workflow_parity.py`'s single-parallel-pass
  assertions, which the plan's own Verification section calls out as "a real finding, not a test
  to adjust."

## Plan Deviations

- **Process (Phase 2, not scope)**: Long-running full-selection draws were backgrounded via
  explicit shell `&`/`disown` and polled with `kill -0`/`tail` loops rather than the harness's
  `BashOutput` tool, because the poll commands issued through the Bash tool were themselves
  killed at a 2-minute wall-clock limit before the underlying (disowned) pytest process
  finished. The disowned process was unaffected and was recovered on the next poll. All four
  draws in Phase 2, and the final-gate draw in Phase 5, still ran to completion sequentially
  with the identical command shape each time.
- **Mechanism (Phase 4, not scope)**: The telemetry sampler is wired inline within the existing
  "Run general test suite" step rather than as a literal separate GH Actions step, because true
  "alongside" execution requires the sampler and pytest to share one shell/process tree across
  step boundaries, which GH Actions steps do not support without either breaking that step's own
  pass/fail reporting or making the "non-gating" telemetry step gating in practice. Every
  substantive requirement (3.12-gating, non-gating, worker-count recording, documentation) is
  still delivered; see the Phase 4 handoff for the full reasoning and the two smoke tests that
  confirm gating semantics are preserved.

## Impacts

- CI's example solve-budget floor now covers 7 files instead of 4, closing a previously latent
  (measured, not just theoretical) hazard class in `bimodal`/`exclusion`/`imposition`.
- CI's parallel gating pass now runs at `-n 4` instead of `-n 6`, on falsification-screen
  evidence rather than a safety proof; a named, two-sided-enforced revert trigger exists if a
  CI-only regression appears.
- The Python 3.12 leg now emits peak-RSS-per-worker telemetry on every run, giving a future task
  the data needed to actually decide (not guess at) the D memory hypothesis.
- No change to any constant this task was explicitly forbidden from touching (B's constants,
  the differential oracle test file).

## Follow-ups

- A future task should read the accumulated `worker-rss-summary.json` telemetry from Python 3.12
  CI runs (once several have run) and use it to either confirm or rule out the memory-exhaustion
  hypothesis for D; if ruled out, investigate the Z3/ABI or xdist/execnet hypotheses next.
- The named revert trigger for the `-n 4` change (a countermodel-expected example losing its
  countermodel, or a new contention-shaped failure) should be watched on the next several real
  CI runs, since this screen falsifies locally but cannot prove CI safety.

## References

- `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/plans/01_budget-floor-worker-count-telemetry.md`
- `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/handoffs/phase-{1,2,3,4,5}-handoff-*.md`
- `specs/170_resolve_xdist_worker_count_and_differential_oracle_floor/evidence/phase2-screen-results.md`
- `code/docs/core/TESTING_GUIDE.md` sections 8.11, 8.13
