# Implementation Summary: Fix generic iterator pinning never reaching the rebuilt model's solve

- **Task**: 210 - Fix generic iterator pinning never reaching the rebuilt model's solve for
  logos, exclusion and imposition
- **Status**: [BLOCKED]
- **Started**: 2026-09-28T19:01:03Z
- **Completed**: 2026-09-28T19:36:57Z
- **Effort**: ~4.5 hours (plan estimated 6 hours across phases 1-3, 5)
- **Dependencies**: None
- **Artifacts**: plans/01_fix-generic-iterator-pinning.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Implemented the plan's core mechanism (Phases 1, 2, 3, 5): route the generic iterator's
`is_world`/`possible`/`verify`/`falsify` pins into `model_constraints.frame_constraints` so
they reach the Z3 solve that actually produces a rebuilt model, mirroring bimodal's own
`_pin_theory_specific_values` precedent. Discovered, during Phase 3's own verification, a
separate pre-existing defect that blocks the plan's stated Done-when criterion for 2 of 3
theories. Phases 4 and 6 (which depend on Phase 3) were not started.

## What Changed

- `code/src/model_checker/iterate/models.py`: `build_new_model_structure` now appends each
  computed pin literal into `model_constraints.frame_constraints` alongside the existing
  `temp_solver.add(...)` calls, for all four predicate types (is_world, possible, verify,
  falsify), guarded by the same `hasattr` checks as before. The stale "Consequence, NOT
  fixed here" comment was rewritten to describe the actual, now-correct mechanism.
- `code/src/model_checker/theory_lib/bimodal/iterate.py`: corrected
  `_ensure_frame_constraints_in_search_solver`'s docstring, which incorrectly still claimed
  in the present tense that `all_constraints` "permanently misses" the certificate encoding
  — no longer true since `all_constraints` became a read-only computed property. Clarified
  that reading the four component lists directly remains required for the separate,
  still-live `stored_solver`/`_setup_solver` reassignment bug the method actually works
  around.
- `code/src/model_checker/iterate/tests/integration/test_models.py`: added a real-`BuildExample`
  helper and `TestGenericPinningReachesRebuiltSolve` (parametrized over logos, exclusion,
  imposition), which monkeypatches `ModelBuilder.build_new_model_structure` to intercept
  every `(candidate_z3_model, returned_structure)` pair from a live `iterate:3` search and
  asserts the generic predicates agree between the two. Marked `@pytest.mark.slow` (92s
  total pre-fix).
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/`: pre-fix gate, iterate-suite,
  and per-theory representative-iteration captures for Phase 6 comparison (not yet used,
  since Phase 6 was not reached).

## Decisions

- Implemented the frame_constraints append using a shared `pinned = ... if ... else ...`
  variable per predicate (one `temp_solver.add`/`append` pair per predicate, covering both
  its true/false branches) rather than literally duplicating `temp_solver.add(...)` in each
  branch as the plan's literal wording suggested — this exactly matches bimodal's own
  `_pin_theory_specific_values` pattern, which the plan itself names as "the mechanism
  bimodal's own override already validates, applied one call site up." Documented inline in
  the plan as a reasoned deviation from the literal Scope Hypothesis append-count (4 call
  sites, not 8; functionally identical, confirmed no site missed or double-added).
- Confirmed empirically (not merely assumed) that `frame_constraints` does not grow across
  successive rebuilds within one run (constant length of 36 across 138 successful rebuilds
  in a live exclusion run), because each `build_new_model_structure` call constructs
  entirely fresh `model_constraints`.
- Fixed a transient `test_simplified_method_shorter` line-count-ceiling regression (this
  phase's comments pushed `build_new_model_structure` to 185 lines against a `<170` ceiling)
  by trimming comment verbosity only, to 169 lines — no behavior change.

## Plan Deviations

- **Phase 3 append-call-count** (see Decisions above): 4 append call sites instead of the
  literal reading of 8, functionally equivalent, documented inline in the plan.
- **Phases 4 and 6 not started**: both depend on Phase 3, which is `[BLOCKED]`. Not a skip or
  omission — phase-closure discipline forbids opening a phase whose dependency is not
  genuinely closed.
- **Phase 3 not closed as `[COMPLETED]`**: closed as `[BLOCKED]` instead, because 2 of its own
  stated verification criteria (all three regression-test parametrizations pass; each theory
  still finds more than one model) are not met, for a reason outside this phase's own edit
  (see Impacts below). This is a genuine scope-blocking discovery, not a reasoned exclusion
  of a mechanically-listed item, so `[COMPLETED WITH EXCLUSIONS]` was not used.

## Impacts

- **Exclusion is now genuinely fixed**: its live `iterate:3` regression test passes, finding
  2/3 models with pins correctly reaching the solve — a real improvement over the pre-fix
  state (pins silently discarded).
- **A separate, pre-existing, generic defect was discovered**: `models/structure.py`'s
  `solve()` unconditionally clears `model_structure.solver` in a `finally` block for every
  theory, and `ConstraintGenerator`'s `stored_solver` fallback (`iterate/constraints.py`)
  always points at the solver's pre-population (empty) state — confirmed by direct
  inspection (`len(iterator.constraint_generator.solver.assertions()) == 0`) for logos,
  exclusion, and imposition alike. This is the exact defect class bimodal's own
  `_ensure_frame_constraints_in_search_solver` already works around, but that workaround has
  never been generalized to the other three theories. With this task's fix now genuinely
  enforcing pins, a candidate drawn from an unconstrained search solver frequently cannot be
  reconciled with the real semantic constraints at rebuild time — confirmed via `unsat_core()`
  for logos (core: the `verify(_, A)` pins plus the conclusion constraint requiring the
  countermodel's evaluation world to verify `A`).
- **This blocks the plan's Done-when criterion** ("a live, non-mocked, three-theory
  regression test... passes after [the fix]") for logos and imposition. The defect is
  outside this plan's declared Non-Goals-bounded scope (which explicitly excludes
  `iterate/core.py`-adjacent consistency-guard changes).
- No regression to any other test: full `iterate/` suite (238 passed) and bimodal's own
  `tests/integration/test_iterate.py` (29 passed) both match or improve on the Phase 1
  baseline.

## Follow-ups

- **Decision needed** (recorded as `user_decision` in this dispatch's return metadata):
  whether to (a) expand task 210's scope to also generalize bimodal's
  `_ensure_frame_constraints_in_search_solver` workaround to the shared engine or to each of
  logos/exclusion/imposition, (b) spawn a new, dedicated task to fix the persistent-search-
  solver-empty defect first, then resume task 210's remaining phases against a corrected
  foundation, or (c) narrow task 210 permanently to the mechanical routing fix already
  landed (keep exclusion's coverage, mark logos/imposition's regression-test parametrizations
  `xfail` with the blocking reason cited, and accept a reduced Done-when scope).
- Once a path is chosen: complete Phase 4 (pin-presence assertion), then Phase 6 (full
  four-theory gate and fallout review), using the baseline captures already recorded in
  `baselines/`.

## References

- `specs/210_fix_generic_iterator_pinning_unreached/plans/01_fix-generic-iterator-pinning.md`
  (Phase 3 section carries the full diagnosis and `unsat_core()` evidence)
- `specs/210_fix_generic_iterator_pinning_unreached/reports/01_fix-generic-iterator-pinning.md`
- `specs/210_fix_generic_iterator_pinning_unreached/handoffs/phase-3-handoff-20260928T200500Z.md`
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/`
