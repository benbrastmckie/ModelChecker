# Implementation Summary: Fix generic iterator pinning never reaching the rebuilt model's solve

- **Task**: 210 - Fix generic iterator pinning never reaching the rebuilt model's solve for
  logos, exclusion and imposition
- **Status**: [COMPLETED]
- **Started**: 2026-09-28T19:01:03Z
- **Completed**: 2026-09-28T (this cycle)
- **Effort**: ~4.5 hours (prior cycle: Phases 1, 2, 3's routing fix, 5) + ~2.5 hours (this cycle:
  Phase 3 closure, 4, 6, against the corrected foundation)
- **Dependencies**: None (a separate, dedicated task fixed the shared-engine
  persistent-search-solver defect this task's own Phase 3 verification discovered; see Follow-ups
  in the prior cycle's record and Decisions below)
- **Artifacts**: plans/01_fix-generic-iterator-pinning.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Routed the generic iterator's `is_world`/`possible`/`verify`/`falsify` pins into
`model_constraints.frame_constraints` so they reach the Z3 solve that actually produces a
rebuilt model, mirroring bimodal's own `_pin_theory_specific_values` precedent. A prior cycle
implemented this fix (Phases 1, 2, 3's routing edit, 5) but discovered, during Phase 3's own
verification, a separate pre-existing defect in the shared engine (`models/structure.py`'s
`solve()`/`stored_solver`) that left the persistent search solver empty for logos, exclusion,
and imposition — causing 2 of 3 theories' regression tests to fail for a reason outside this
task's declared scope. Per the recorded `user_decision`, a dedicated task fixed that shared-engine
defect by generalizing bimodal's own re-assertion workaround into
`iterate/constraints.py`'s `ConstraintGenerator._ensure_original_constraints_in_solver`. This
cycle re-verified the routing fix against that corrected foundation (now passing for all three
theories), completed Phase 4 (pin-presence structural coverage), and completed Phase 6 (the full
four-theory gate and fallout review). All six plan phases are now `[COMPLETED]`.

## What Changed

- `code/src/model_checker/iterate/models.py`: `build_new_model_structure` now appends each
  computed pin literal into `model_constraints.frame_constraints` alongside the existing
  `temp_solver.add(...)` calls, for all four predicate types (is_world, possible, verify,
  falsify), guarded by the same `hasattr` checks as before. The stale "Consequence, NOT
  fixed here" comment was rewritten to describe the actual, now-correct mechanism. (Landed in
  the prior cycle; unchanged this cycle.)
- `code/src/model_checker/theory_lib/bimodal/iterate.py`: corrected
  `_ensure_frame_constraints_in_search_solver`'s docstring, which incorrectly still claimed
  in the present tense that `all_constraints` "permanently misses" the certificate encoding
  — no longer true since `all_constraints` became a read-only computed property. Clarified
  that reading the four component lists directly remains required for the separate,
  still-live `stored_solver`/`_setup_solver` reassignment bug the method actually works
  around. (Landed in the prior cycle; unchanged this cycle.)
- `code/src/model_checker/iterate/tests/integration/test_models.py`:
  - `TestGenericPinningReachesRebuiltSolve` (prior cycle): a real-`BuildExample` helper and a
    class parametrized over logos, exclusion, imposition, monkeypatching
    `ModelBuilder.build_new_model_structure` to intercept every `(candidate_z3_model,
    returned_structure)` pair from a live `iterate:3` search and asserting the generic
    predicates agree between the two. Re-verified this cycle against the corrected foundation:
    all three parametrizations now pass (`3 passed in 111.64s`).
  - `TestGenericPinAppendedToFrameConstraints` (this cycle, Phase 4): a structural pin-presence
    check mirroring bimodal's own `TestPinTheorySpecificValues` — asserts a rebuild's
    `frame_constraints` grew relative to a fresh, unpinned baseline and contains the pinned
    `is_world(0)` literal (via `.eq()` structural comparison), parametrized over the same three
    theories, plus a companion test confirming bimodal's `hasattr` guards never fire (`4 passed
    in 2.57s`).
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/`: pre-fix captures (prior cycle)
  plus post-fix gate, iterate-suite, and per-theory representative-iteration captures and a
  `01_post-fix-summary.md` fallout classification (this cycle, Phase 6).

## Decisions

- Implemented the frame_constraints append using a shared `pinned = ... if ... else ...`
  variable per predicate (one `temp_solver.add`/`append` pair per predicate, covering both
  its true/false branches) rather than literally duplicating `temp_solver.add(...)` in each
  branch as the plan's literal wording suggested — this exactly matches bimodal's own
  `_pin_theory_specific_values` pattern. Documented inline in the plan as a reasoned deviation
  from the literal Scope Hypothesis append-count (4 call sites, not 8; functionally identical).
- The prior cycle's `user_decision` ("spawn a new, dedicated task to fix the
  persistent-search-solver-empty defect first, then resume task 210's remaining phases against
  that corrected foundation") was acted on outside this task: a separate task generalized
  bimodal's `_ensure_frame_constraints_in_search_solver` re-assertion pattern into the shared
  `ConstraintGenerator._ensure_original_constraints_in_solver`, populating every theory's
  persistent search solver before the search loop pins against it. This task's own Phase 3 edit
  needed no change once that foundation landed — re-running the existing regression test against
  it was sufficient to confirm the routing fix now works for all three theories, not just
  exclusion.
- Phase 6's `print_constraints` rendering check was exercised via `print_grouped_constraints()`
  directly (on a live rebuilt model) rather than through the CLI's `-p`/`--print_constraints`
  flag: that flag's call site (`{logos,exclusion}/semantic/model.py`'s `print_to`) only invokes
  the rendering method when the top-level result is UNSAT, which a countermodel example's model 1
  never is. The rendering code path exercised is identical either way.

## Plan Deviations

- **Phase 3 append-call-count** (see Decisions above): 4 append call sites instead of the
  literal reading of 8, functionally equivalent, documented inline in the plan.
- **Phase 3 closed as `[COMPLETED]` in this cycle, not `[COMPLETED WITH EXCLUSIONS]`**: the prior
  cycle closed it `[BLOCKED]` because 2 of its own stated verification criteria were not met, for
  a reason outside this phase's own edit — a genuine scope-blocking discovery. That blocker is now
  resolved by the dedicated foundation task, so this cycle re-verified and closed the phase fully
  `[COMPLETED]` rather than recording an exclusion; the Done-when criterion the blocking finding
  cited as unmet is now met in full.
- None otherwise (this cycle's Phase 4 and Phase 6 work followed the plan as written).

## Impacts

- **All three theories are now genuinely fixed**: `TestGenericPinningReachesRebuiltSolve` passes
  for logos, exclusion, and imposition — pins computed from the candidate Z3 model now reach the
  solve that produces every rebuilt model.
- **No theory collapses to a single model**: logos unchanged (1/3 vs. the Phase 1 baseline's
  1/3), exclusion improved (2/3 vs. 1/3 — a genuinely pinned second model the pre-fix write-only
  pins never actually delivered), imposition unchanged (2/3 vs. 2/3).
- **`print_constraints`/`--save` display-only side effect confirmed well-formed**: pin literals
  now render correctly under the `FRAME CONSTRAINTS:` heading for a rebuilt model, per the
  Decisions Phase 3 already accepted.
- **No regression anywhere**: parallel pass (3204 passed, 1 pre-existing flake), serial
  `xdist_serial` pass (10 passed), four-theory directory pass (1695 passed, 0 failed), `iterate/`
  suite (251 passed), and bimodal's own `test_iterate.py` (29 passed — strictly better than the
  Phase 1 baseline, which recorded one pre-existing failure there). Full detail and per-command
  breakdown in `baselines/01_post-fix-summary.md`.
- **One pre-existing, load-sensitive flake remains**, by the same node ID recorded in the Phase 1
  baseline (`TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`,
  bimodal), unrelated to this task's changes — classified (a) in Phase 6's fallout review, not a
  regression.

## Follow-ups

None. All six plan phases are `[COMPLETED]`; the plan's Done-when criterion is met in full for
all three affected theories.

## References

- `specs/210_fix_generic_iterator_pinning_unreached/plans/01_fix-generic-iterator-pinning.md`
  (Phase 3's Resolution note records how the corrected foundation resolved the prior blocking
  finding; Phase 6 carries the full gate results)
- `specs/210_fix_generic_iterator_pinning_unreached/reports/01_fix-generic-iterator-pinning.md`
- `specs/210_fix_generic_iterator_pinning_unreached/handoffs/phase-3-handoff-20260928T200500Z.md`
- `specs/210_fix_generic_iterator_pinning_unreached/baselines/` (pre-fix and post-fix captures,
  `01_pre-fix-summary.md`, `01_post-fix-summary.md`)
