# Phase 5 Handoff: Document the Residual `stored_solver` Defect

**Status**: COMPLETED

## What was done

Added a `NOTE:` comment in `code/src/model_checker/models/structure.py` beside
`self.stored_solver = self.solver` (inside `solve()`), recording: the assignment precedes
`_setup_solver`'s reassignment (so `stored_solver` references the solver's pristine,
pre-population state); that reordering was deliberately rejected because `_setup_solver` uses
`assert_tracked`, whose `Implies(label, constraint)` assertions would be vacuously satisfiable
if copied into a fresh solver; and that the shared iterate engine no longer depends on this
value being populated, since `ConstraintGenerator._ensure_original_constraints_in_solver`
re-asserts the real constraint lists directly.

Confirmed via `git diff` that every changed hunk lies inside the added comment block (no
executable statement touched). Confirmed `iterate/README.md` does not document
`_create_persistent_solver`'s behavior (zero matches for `persistent`/`stored_solver`/
`_create_persistent_solver`), so no README update was needed.

## Verification

- `python -m py_compile code/src/model_checker/models/structure.py` succeeds.
- `git diff -- code/src/model_checker/models/structure.py` shows only added comment lines.
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q`: 247 passed (no regression
  from the comment addition).

## Next phase

Phase 6: review the iteration-result fallout against Phase 1's per-theory `dev_cli.py`
captures, confirm the out-of-scope boundary held, and close the task.
