# Implementation Summary: Theory-Specific Extension Points in the Shared Model Iterator

- **Task**: 189 - Fix the shared model iterator's `is_world` assumption so the bimodal theory can iterate
- **Status**: [COMPLETED]
- **Started**: 2026-09-25T23:38:00Z
- **Completed**: 2026-09-26T01:20:00Z
- **Effort**: ~10.5 hours (vs. 11.5 estimated)
- **Dependencies**: None
- **Artifacts**: plans/01_iterator-theory-extension-points.md, baselines/00-10 (10 files)
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The shared `model_checker/iterate` framework hard-coded the assumption that every theory exposes
`semantics.is_world()`, which crashed bimodal's `iterate: N > 1` outright and silently produced no
exclusion constraint even where the crash could be avoided. This plan introduced three explicit,
polymorphic extension points on `BaseModelIterator` (model-value pinning, exclusion-constraint
generation, isomorphism participation), each with a behavior-preserving base-class default, and
overrode all three in `BimodalModelIterator`. No `is_world` shim was added to `BimodalSemantics`.
A live, non-mocked `iterate: 3` run on a bimodal countermodel now yields three pairwise-distinct,
constraint-enforced certificates with zero isomorphic false-positive skips, while logos,
imposition and exclusion remain behaviorally unchanged (measured, not assumed).

## What Changed

- `iterate/models.py`: guarded the previously-unguarded `is_world`/`possible` loop in
  `build_new_model_structure`; added an optional `iterator=None` parameter to `ModelBuilder`,
  dispatching `_pin_theory_specific_values` unconditionally when injected.
- `iterate/core.py`: added three extension points on `BaseModelIterator` --
  `_pin_theory_specific_values` (no-op default), `_build_exclusion_constraints` /
  `_build_stronger_constraint` (wrapping/composing around `_create_difference_constraint`, whose
  default now delegates to `ConstraintGenerator`'s generic implementation instead of raising
  `NotImplementedError`), and `_check_model_isomorphism` (delegates to `IsomorphismChecker` by
  default). Routed `iterate_generator`'s three live constraint/isomorphism call sites through
  these hooks; left the dead, uncalled `_orchestrated_iterate` untouched (Non-Goal).
- `iterate/constraints.py`: docstring-only clarification of `ConstraintGenerator`'s narrowed role
  (solver plumbing plus generic hook default); zero logic change.
- `theory_lib/bimodal/iterate.py`: overrode all three hooks -- pins certificate variables (label
  bits, box guesses); `_check_model_isomorphism` unconditionally opts out of the shared
  graph-based check (which would otherwise false-positive on two empty `z3_world_states` graphs);
  module docstring rewritten to describe the fixed reality (HISTORY-framed) rather than the
  now-closed gap.
- `theory_lib/bimodal/docs/ITERATE.md` and `ARCHITECTURE.md`: removed the "iterate: N > 1
  currently crashes" limitation and its "use iterate: 1" guidance; rewrote the
  diversity-enforcement account to describe the certificate blocking clause the live loop now
  enforces.
- `iterate/README.md`: extended the Extension Guide with a table documenting all three hooks.
- Test coverage added across `iterate/tests/unit/test_core.py`,
  `test_models_edge_cases.py`, `test_core_abstract_methods.py` (updated for the new
  non-raising default),
  `iterate/tests/integration/test_graph_isomorphism_integration.py`, and
  `bimodal/tests/integration/test_iterate.py` (including the live, non-mocked
  `TestLiveIteration` class: 3-distinct-certificates, enforcement-not-coincidence, and
  clean-exhaustion tests).

## Decisions

- Composed rather than replaced the isomorphic-escape constraint (`_build_stronger_constraint`):
  logos's and imposition's own `_create_non_isomorphic_constraint`/`_create_stronger_constraint`
  overrides are `BoolVal(True)` no-op placeholders, so naively preferring them would have removed
  those two theories' only real escape constraint.
- Left `_orchestrated_iterate` (dead, uncalled) and `iterator.py`'s `IteratorCore.iterate()` (also
  dead, per the plan's own Non-Goals) untouched, even though they contain parallel-looking direct
  `ConstraintGenerator`/`IsomorphismChecker` calls -- confirmed unreferenced by any caller before
  leaving them.
- Phase 6's cross-theory regression gate criterion was met without the contingency branch: model
  counts (the actual criterion) were unchanged for all three `is_world` theories; a wall-clock
  timing artifact in exclusion's `checked_model_count` (timeout-bound, not logic-bound) was
  investigated and proven structurally to be measurement noise, not a constraint-content
  regression, since `constraints.py`'s logic diff between the pre- and post-Phase-3 commits is
  docstring-only.

## Plan Deviations

- None (implementation followed plan). One arithmetic error in Phase 3's own recorded evidence
  (238/14 vs. the correct 236/12) was found and corrected during Phase 4 -- a documentation
  correction, not a deviation from the plan's design or task list.

## Impacts

- `iterate: N > 1` now works end-to-end for bimodal via `BuildExample`/`BimodalModelIterator`,
  `iterate_example`, and `iterate_example_generator` -- previously usable only at `iterate: 1`.
- Logos, imposition and exclusion are unaffected in practice: their own `_create_difference_constraint`
  overrides are not newly invoked by this change (Phase 6 measured, rather than assumed, that the
  live loop's behavior for these three theories is unchanged); only bimodal gained real behavior.
- Any future theory lacking an `is_world`-style state-existence predicate now has a documented,
  tested extension-point contract (`iterate/README.md`'s Extension Guide) to follow instead of
  hitting the same crash bimodal did.

## Follow-ups

- Rotation/permutation-invariant isomorphism rejection for bimodal certificates remains
  unimplemented (documented Non-Goal); `bimodal/docs/ARCHITECTURE.md`'s "Extension Points"
  section names it as follow-on work using `WitnessRegistry.wrap`'s slot arithmetic.
- `graph.py`'s unconditional `/tmp/graph_debug.log` writes and the dead `iterate/base.py`/
  `iterator.py`/`models.py` `_initialize_*` code paths remain untouched (documented Non-Goals).

## References

- `specs/189_fix_shared_iterator_is_world_assumption/plans/01_iterator-theory-extension-points.md`
  (all 7 phases `[COMPLETED]`, with per-phase `#### Evidence` subsections)
- `specs/189_fix_shared_iterator_is_world_assumption/baselines/01` through `10` (pre-change
  baseline, three defect reproductions, per-theory live-run comparisons, post-fix live run, full
  regression-suite outputs)
- `specs/189_fix_shared_iterator_is_world_assumption/handoffs/phase-1-handoff-*.md`,
  `phase-4-handoff-*.md`
