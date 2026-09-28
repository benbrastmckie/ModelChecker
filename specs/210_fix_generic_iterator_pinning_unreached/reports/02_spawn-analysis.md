# Blocker Analysis: Task #210

**Parent Task**: #210 - Fix generic iterator pinning never reaching the rebuilt model's solve for logos, exclusion and imposition
**Generated**: 2026-09-28T19:47:13Z
**Blocker**: Phase 3's pin-routing fix is correct and lands cleanly for exclusion, but logos and imposition still fail the Phase 2 regression test because a separate, pre-existing, shared-engine defect leaves the live iteration loop's persistent search solver with zero real assertions — the "candidate" model being pinned was never actually constrained by real semantics during the search.

## Root Cause

Task 210's own Phase 3 verification (via `unsat_core()`, confirmed empirically for logos,
exclusion, and imposition) traced the failure to two interacting defects in the shared engine,
both outside task 210's declared file scope (`iterate/models.py` only):

1. `code/src/model_checker/models/structure.py`'s `solve()` assigns
   `self.stored_solver = self.solver` **before** calling `self._setup_solver(model_constraints)`
   (`structure.py:255-260`). `_setup_solver` is what actually populates constraints and
   *reassigns* `self.solver` to a new, populated solver object — so `stored_solver` is left
   permanently pointing at the pristine, pre-population `create_solver(...)` result, for every
   theory, not just bimodal.
2. `solve()`'s `finally` block unconditionally calls `_cleanup_solver_resources()`
   (`structure.py:298-300`), which sets `self.solver = None` for every theory. By the time
   `iterate/constraints.py`'s `ConstraintGenerator._create_persistent_solver()` runs
   (`constraints.py:56-98`), `model_structure.solver` is `None` and its `stored_solver` fallback
   is the empty solver from defect (1) — so the live loop's persistent search solver never
   receives `frame_constraints`/`model_constraints`/`premise_constraints`/`conclusion_constraints`
   at all. Confirmed directly: `len(iterator.constraint_generator.solver.assertions())` is `0`
   immediately after constructing a real `LogosModelIterator`/`ExclusionModelIterator`/
   `ImpositionModelIterator`.

Bimodal already works around this exact defect for itself: `theory_lib/bimodal/iterate.py`'s
`_ensure_frame_constraints_in_search_solver` (lines 105-196) re-asserts the four live constraint
lists onto `self.constraint_generator.solver` at iterator-construction time, and its own docstring
already names the root cause as "a bug in the shared engine (`models/structure.py`'s `solve()`)".
That workaround was never generalized to logos, exclusion, or imposition.

**Effect on task 210**: pre-fix, this was invisible — the write-only `temp_solver` pins were
discarded, so the rebuild simply re-solved the real, satisfiable base problem from scratch.
Post-Phase-3-fix, the rebuild is asked to satisfy the real base constraints **and** pinned literal
values taken from a candidate that was never actually a model of those real constraints. For
logos and imposition at the settings task 210's regression test and baseline use, that combination
is UNSAT on effectively every candidate. Exclusion happens not to hit this for its specific test
example, but the persistent solver is confirmed equally empty for it too — it is not evidence the
defect is absent for exclusion, only that this particular example doesn't expose it.

This is a genuine scope boundary, not a task 210 implementation defect: task 210's Non-Goals
already excluded "a production-side guard" / consistency-check work in `iterate/constraints.py`,
and the plan's own Risk table anticipated an occasional UNSAT-on-pin outcome, not a ~100% collapse
traced to a distinct, pre-existing generic-engine bug. The user has decided (recorded in
`specs/210_fix_generic_iterator_pinning_unreached/.decisions.json`) to spawn a dedicated follow-up
task for this defect, then resume task 210's remaining phases (3 closure, 4, 6) against the
corrected foundation.

## Proposed New Tasks

### New Item 1: Fix persistent search-solver population in the shared iterate engine
- **Effort**: 3-4 hours
- **Task Type**: z3
- **Rationale**: This is the single defect blocking task 210's Phase 3 closure for logos and
  imposition. It is a shared-engine change (affects every theory's live iteration loop, not one
  theory), matching the user's decision to scope it as its own task rather than expand task 210.
  The fix and its regression coverage are tightly coupled (same root cause, same verification
  surface) and mirror the exact RED/GREEN shape task 210 itself already used for its own fix, so
  splitting test-writing and fix-implementing into two dependent tasks would not change any
  implementation choice between them — one task is the minimal correct decomposition.
- **Depends on**: None

## Dependency Reasoning

Only one new task is proposed; there is no dependency graph to reason about. The task is
self-contained: it fixes a bug entirely within the shared iterate engine (`models/structure.py`
and/or `iterate/constraints.py`) and does not touch `iterate/models.py` (task 210's Phase 3
territory) or any theory-specific `_pin_theory_specific_values` override.

**Scope boundary with task 210 (not a spawned-task dependency, but recorded for clarity)**: New
Item 1 must not edit `code/src/model_checker/iterate/models.py` or
`code/src/model_checker/iterate/tests/integration/test_models.py`'s
`TestGenericPinningReachesRebuiltSolve` class — those are task 210's own Phase 3/4 artifacts.
Task 210's remaining phases (3 closure, 4, 6) depend on New Item 1's fix landing first, but that
dependency is expressed through the user's decision and the `/implement 210` resumption sequence,
not through the spawned-task dependency graph, since task 210 is the parent being unblocked, not
a sibling of the new task.

## Task Detail: New Item 1

**Description for the implementer** (sufficient to act without re-reading task 210's plan):

In `code/src/model_checker/models/structure.py`, `ModelDefaults.solve()` creates a solver,
assigns `self.stored_solver = self.solver` immediately, then calls
`self._setup_solver(model_constraints)` which populates constraints and reassigns `self.solver`
to a new, populated solver object (`structure.py:254-260`). Because `stored_solver` is captured
*before* that reassignment, it is left pointing at the solver's empty, pre-population state
forever — for every theory. Combined with `solve()`'s `finally`-block cleanup
(`_cleanup_solver_resources()`, `structure.py:298-300`), which sets `self.solver = None`
unconditionally, `iterate/constraints.py`'s `ConstraintGenerator._create_persistent_solver()`
(lines 56-98) ends up building the live loop's persistent search solver from an empty assertion
set for every theory without a bimodal-style workaround (logos, exclusion, imposition).

Two candidate fix strategies (choose and justify one during planning/research; do not weigh
this decision in this spawn analysis):
1. **Root-cause reorder fix** in `models/structure.py`'s `solve()`: assign
   `self.stored_solver = self.solver` *after* `_setup_solver` reassigns `self.solver`, so
   `stored_solver` correctly references the populated solver (this attribute is not cleared by
   `_cleanup_solver_resources()`, so it survives past `solve()`'s return). Verify no other
   caller relies on `stored_solver`'s current (broken) pre-population timing before making this
   change — search all `stored_solver` usages repo-wide.
2. **Generalize the bimodal workaround** into the shared `ConstraintGenerator` base class
   (`iterate/constraints.py`), re-asserting `frame_constraints`/`model_constraints`/
   `premise_constraints`/`conclusion_constraints` onto `self.solver` after
   `_create_persistent_solver()` runs, for every theory — mirroring
   `theory_lib/bimodal/iterate.py:105-196`'s `_ensure_frame_constraints_in_search_solver` exactly,
   moved one level up so no per-theory override is required.

Either strategy must leave bimodal's own existing `_ensure_frame_constraints_in_search_solver`
override in place, unmodified (removing it is out of scope for this task — the two mechanisms
being redundant for bimodal post-fix is an accepted side effect, not a defect to resolve here).

Add live, non-mocked regression coverage (in `code/src/model_checker/iterate/tests/`, new or
extended file — implementer's choice) asserting, for logos, exclusion, and imposition:
- The persistent search solver (`iterator.constraint_generator.solver`) has a non-zero assertion
  count immediately after iterator construction against a real, solved `BuildExample` (this
  fails today — confirmed `0` for all three).
- More strongly: a model produced by that persistent solver actually satisfies the real
  `frame_constraints`/`model_constraints`/`premise_constraints`/`conclusion_constraints` — not
  merely a non-empty assertion count, which could pass vacuously with unrelated assertions.

Confirm bimodal's own `tests/integration/test_iterate.py` is unchanged in outcome (its own
workaround already covers it; this fix must not alter its behavior). Run the full
`iterate/` suite plus the four-theory directory gate and record results.

**Explicitly out of scope for this task** (task 210's own territory, left untouched):
- `code/src/model_checker/iterate/models.py`'s generic pinning loop (task 210 Phase 3).
- `code/src/model_checker/iterate/tests/integration/test_models.py`'s
  `TestGenericPinningReachesRebuiltSolve` and its future Phase 4 pin-presence assertion.
- Removing or simplifying bimodal's `_ensure_frame_constraints_in_search_solver` now that it may
  be redundant.

**Anticipated file scope**: `code/src/model_checker/models/structure.py`,
`code/src/model_checker/iterate/constraints.py`, `code/src/model_checker/iterate/tests/`.

## After Completion

Once New Item 1 is complete, resume task 210 with `/implement 210` to close out Phase 3
(re-run `TestGenericPinningReachesRebuiltSolve` — all three theories should now pass), then
proceed through Phase 4 (pin-presence assertion) and Phase 6 (full four-theory gate and fallout
review).

The blocker will be resolved because: once the live iteration loop's persistent search solver is
genuinely populated with the real frame/model/premise/conclusion constraints, every candidate
model it produces is an actual model of those constraints — so pinning its `is_world`/`possible`/
`verify`/`falsify` values and re-solving (task 210's own Phase 3 fix) will be satisfiable rather
than UNSAT, for logos and imposition exactly as it already is for exclusion.
