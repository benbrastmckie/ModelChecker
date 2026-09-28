# Phase 2 Handoff: Write the Failing Regression Tests (RED)

**Status**: COMPLETED

## What was done

Created `code/src/model_checker/iterate/tests/integration/test_search_solver_population.py`
with `TestPersistentSearchSolverPopulated`, parametrized over logos/exclusion/imposition:
- `test_persistent_solver_has_nonzero_assertions` (diagnostic only, documented as insufficient).
- `test_persistent_solver_model_satisfies_real_constraints` (the real acceptance criterion:
  checks the persistent solver, requires `sat`, and verifies the produced model satisfies every
  constraint in `model_constraints.frame_constraints/.model_constraints/.premise_constraints/
  .conclusion_constraints`).

Confirmed RED against the pre-fix engine (all 6 parametrized tests failed; output captured to
`baselines/02_red-search-solver-population.txt` during Phase 1's baseline pass, before Phase 3's
fix was written). Confirmed GREEN against the Phase 3 fix already drafted in
`iterate/constraints.py` (all 6 pass, 1.68s).

## Deviation

None beyond what's noted in the plan's Phase 2 task list: the strong test's failure mode
pre-fix is a constraint-violation assertion (not the `sat`-check), because an empty solver
trivially reports `sat`.

## Next phase

Phase 3: formalize/verify the already-drafted fix in `iterate/constraints.py`
(`_ensure_original_constraints_in_solver`, called from `ConstraintGenerator.__init__` after
`_create_persistent_solver`), and run the full `iterate/` suite to confirm no regressions.
