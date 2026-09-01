# Implementation Summary: Decouple Release-Gating Tests from Bimodal Solve Cost

- **Task**: 181 - Audit and fix gating tests outside the bimodal test tree that still depend on bimodal solve cost
- **Status**: [COMPLETED]
- **Started**: 2026-09-01T05:31:00Z
- **Completed**: 2026-09-01T06:34:00Z
- **Effort**: ~8.5 hours planned; all 8 phases completed
- **Dependencies**: None
- **Artifacts**: plans/01_decouple-gating-tests-from-bimodal.md, baselines/before-wall-clocks.md, baselines/after-wall-clocks.md, baselines/before-after-comparison.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Executed the 8-phase plan decoupling release-gating pytest selections from bimodal's Z3 solve
cost: fixed a shared test helper's hardcoded bimodal default, swapped ten non-bimodal-specific
fixtures from bimodal to logos, quarantined two genuinely-bimodal completeness-claim tests via
per-test `@pytest.mark.development` markings, extended the packaging-suite CI wiring to actually
honor those markings, widened the containment contract, added a new standing executable guard
against future unclassified bimodal coupling, and recorded a paired, honest before/after
wall-clock comparison.

## What Changed

- `code/tests/utils/helpers.py::create_test_model()` now resolves `theory_name` via
  `model_checker.api.get_theory()` instead of hardcoding bimodal; default changed to `'logos'`.
  Five call sites across `test_performance.py`/`test_error_handling.py`/`test_timeout_resources.py`
  were pinned explicitly to `theory_name='bimodal'` after discovering logos's own
  `DEFAULT_EXAMPLE_SETTINGS` (N=16, four constraint flags all True) is not cheap the way
  bimodal's is — one uncontrolled run reached 13.6GB RSS before being manually killed.
- Ten fixtures across six files switched from bimodal to logos, preserving every assertion
  byte-for-byte: `builder/tests/unit/test_example.py` (6 tests), `tests/packaging/test_cli_console_script.py`,
  `tests/e2e/test_batch_output_real.py` (2 tests, renamed to drop the now-misleading "bimodal" in
  their names), `builder/tests/e2e/test_full_pipeline.py`
  (`test_print_impossible_flag_includes_impossible_states`), `tests/cli/test_flag_matrix.py`
  (`_MAXIMIZE_EXAMPLE`).
- A previously unaudited real-solve gating file discovered by Phase 7's own scan,
  `builder/tests/integration/test_performance.py` (distinct from `builder/tests/unit/test_example.py`),
  was also fixed (4 tests, bimodal → logos).
- Two completeness-claim tests marked `@pytest.mark.development` at per-test/per-parametrize
  granularity: `test_generate_then_execute[bimodal]` and (a third instance discovered mid-task,
  added by concurrent work) `test_generate_then_execute_cp1252[bimodal]`, plus
  `test_build_example_bimodal_theory_countermodel`.
- `packaging.yml`, `release.yml` (both packaging-suite steps), `pypi-smoke.yml` given
  `and not unstable and not development` in quoted form; `test_unstable_deselection_wiring.py`
  extended to scan them, `EXPECTED_GATING_MARKER_INVOCATIONS` 6 → 10.
- `test_development_marker_application.py`'s containment contract widened from "bimodal tree
  only" to an enumerated, exactly-matched allowlist of 3 authorized non-bimodal node ids.
- New `code/tests/ci/test_gating_selection_bimodal_decoupling.py`: standing guard asserting every
  bimodal-referencing file collected by a gating selection is classified in one of two enumerated
  constants (9 solve-free, 1 deliberate real-solve retention).
- `code/docs/core/TESTING_GUIDE.md` updated throughout (count anchors, driver lists, a new
  "Per-test markings" record, a cross-reference to the new contract).

## Decisions

- Where a logos swap would change a test's outcome (5 call sites in Phase 2, discovered via
  direct memory/time measurement rather than assumed safe), the call site was pinned to
  `theory_name='bimodal'` explicitly instead — preserving the exact original assertion, per the
  plan's own "genuinely needs bimodal" carve-out, rather than forcing a swap that would break the
  test or contaminate its neighbors.
- A genuinely new real-solve gating file found by Phase 7's own scan
  (`builder/tests/integration/test_performance.py`) was fixed in-phase rather than merely flagged,
  consistent with the plan's stated "Definition of done" and within all HARD CONSTRAINTS.
- A third `development` marking (beyond the plan's hypothesized two) was applied to
  `test_generate_then_execute_cp1252[bimodal]`, a test added by concurrent work in the same
  repository between plan authoring and Phase 6 landing, reusing the identical bimodal-cost
  pattern the plan already targeted.

## Plan Deviations

- Phase 2: 5 call sites pinned to `theory_name='bimodal'` explicitly (not anticipated by the
  plan's "none of the ~20 call sites needs bimodal" hypothesis) — see plan's Phase 2 deviation
  record and `handoffs/phase-2-handoff-*.md` for the full list and reasons.
- Phase 6: 3 non-bimodal `development`-marked node ids (not 2) — see plan's Phase 6 deviation
  record.
- Phase 7: the Scope Hypothesis's ~19-file seed list (report-derived) resolved to 11 real hits on
  the contract's own textual-fixture definition (most of the report's list used bimodal only as a
  string literal, out of scope by design — not a contradiction); one of the 11
  (`builder/tests/integration/test_performance.py`) was a genuine, previously-unaudited real-solve
  gating file, fixed rather than merely classified. See plan's Phase 7 deviation record.
- Phase 8: one transient CPU-contention flake was hit and re-verified clean on retry; three
  selections' collected-count deltas were traced to unrelated concurrent commits in this shared
  repository, not this task's changes. `nix flake check` deferred (not run; see Testing &
  Validation checklist).

## Impacts

- Packaging-suite gating wall clock: **105.80s → 19.82s (-81.3%)**.
- `test_example.py` gating wall clock: **36.13s → 10.66s (-70.5%)**.
- Exactly one gating test's wall clock still depends on bimodal solve cost by design:
  `test_theory_library_execution` (retained `max_time=10` unchanged; its `"World Histories"`
  assertion is not reproducible under any other theory).
- A standing executable contract now prevents a *new* bimodal-coupled fixture from silently
  re-entering a gating selection unclassified.

## Follow-ups

- `nix flake check`'s `checks.default` was not run in this dispatch (heavy, multi-minute
  operation on an already-contended shared host); a human should run it before relying on
  `flake.nix`'s gating shape as separately confirmed.
- The dead-code helpers noted by the original audit report (`tests/conftest.py::test_module_content`,
  `helpers.py::capture_model_output`/`run_example`) remain unaddressed — explicitly out of this
  task's cost scope per the plan's Non-Goals.

## References

- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/plans/01_decouple-gating-tests-from-bimodal.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/reports/01_gating-tests-coupled-to-bimodal.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/before-wall-clocks.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/after-wall-clocks.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/baselines/before-after-comparison.md`
- `specs/181_audit_gating_tests_coupled_to_bimodal_solve_cost/handoffs/phase-{1..8}-handoff-*.md`
