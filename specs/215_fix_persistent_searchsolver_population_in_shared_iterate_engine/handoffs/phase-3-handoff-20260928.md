# Phase 3 Handoff: Generalize Re-Assertion into the Shared ConstraintGenerator (GREEN)

**Status**: COMPLETED

## What was done

Added `ConstraintGenerator._ensure_original_constraints_in_solver()` in
`code/src/model_checker/iterate/constraints.py`, called from `__init__` immediately after
`self.solver = self._create_persistent_solver()`. It reads the four component constraint lists
directly off `build_example.model_constraints` (`frame_constraints`, `model_constraints`,
`premise_constraints`, `conclusion_constraints`), guards each with `isinstance(value, list)`
(so a `Mock()` model_constraints in existing unit tests contributes nothing), and
`self.solver.add(...)`s each constraint.

`_create_persistent_solver` now records `self._reused_original_solver` (`True` on the CVC5
reuse branch, `False` on the Z3 copy branch); the new method returns early when the flag is
`True`, keeping the change a strict no-op for CVC5 (re-asserting there would duplicate
constraints already present on that exact solver object).

`theory_lib/bimodal/iterate.py` and `models/structure.py` are untouched (confirmed via
`git diff --stat`, no output for either path).

## Verification

- `test_search_solver_population.py`: 6/6 passed (GREEN).
- Full `iterate/` suite: **247 passed, 0 failed** (`baselines/03_post-fix-phase3-iterate.txt`),
  vs. the Phase 1 baseline of `2 failed, 239 passed`.
- `git diff --stat` on `code/`: only `iterate/constraints.py` changed (plus the pre-existing,
  unrelated `theory_lib/bimodal/semantic/__init__.py` whitespace-only diff that predates this
  dispatch and is not part of this task's scope).

## Notable observation (not this task's territory to act on)

The two previously-failing `TestGenericPinningReachesRebuiltSolve` tests (logos, imposition) in
`iterate/tests/integration/test_models.py` now pass as a side effect of the persistent solver
being genuinely populated -- exactly the expectation the task description recorded ("task 210's
already-correct pin-routing fix... will make the pinned candidate satisfiable rather than UNSAT
for logos and imposition"). No file in that test's territory was touched here; this is an
observed consequence, reported for Phase 6's review, not verified or claimed as this task's own
deliverable.

## Next phase

Phase 4: re-run bimodal's `test_iterate.py` standalone and the four-theory gate, diff against
Phase 1's actual (not stale) pre-fix baseline.
