# Implementation Summary: Fix stale `ModelConstraints.all_constraints` snapshot

- **Task**: 207 - Fix stale `all_constraints` snapshot; audit every production reader
- **Status**: [COMPLETED]
- **Started**: 2026-09-27T23:45:00Z
- **Completed**: 2026-09-28T01:14:00Z
- **Effort**: ~4.5 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_fix-stale-all-constraints.md, baselines/01_pre-fix-gate.md,
  baselines/02_post-fix-gate.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md,
  code/docs/core/TESTING_GUIDE.md

## Overview

`ModelConstraints.all_constraints` was an eager list concatenation computed once in `__init__`,
so it froze at construction time while bimodal's deliberately two-phase encoding (decision D6)
grew `frame_constraints` later, via `finalize_certificate()`. This permanently omitted the entire
(C1)-(C4) certificate encoding from `all_constraints` for every bimodal solve (measured: 2
constraints captured against a true 132-constraint post-solve set). This task converted the
attribute into a read-only computed property, migrated the one production write site and three
append sites that a property would otherwise silently turn into no-ops, delegated the test tree's
existing `full_constraints()` workaround to the now-correct production attribute, and verified
cross-theory safety under CI's own two-invocation gate shape plus the bimodal suite explicitly.

## What Changed

- `code/src/model_checker/models/constraints.py`: `all_constraints` is now a `@property` returning
  a fresh `frame_constraints + model_constraints + premise_constraints + conclusion_constraints`
  concatenation on every access, with a docstring stating (a) it is a live view, (b) it is
  read-only (assignment raises `AttributeError`; appending to the returned list is a no-op), and
  (c) `_setup_solver` never reads it, for any theory.
- `code/src/model_checker/iterate/models.py`: removed the one production assignment
  (`model_constraints.all_constraints = list(temp_solver.assertions())`), replaced with a comment
  explaining nothing downstream read that value and naming the pre-existing F4 consequence left
  unfixed (see Follow-ups).
- `code/src/model_checker/theory_lib/{logos,exclusion,bimodal}/semantic/core.py`: redirected all
  three `inject_z3_model_values` append sites from `all_constraints.append(...)` (now a silent
  no-op on a computed property) to `model_constraints.model_constraints.append(...)` — the
  ModelConstraints-owned pinned-literal group, deliberately distinct from bimodal's own
  `iterate.py` `frame_constraints`-pinning pattern.
- The four theories' `test_injection.py` files: redirected mock seeding/reads to
  `model_constraints`, seeding each mock's other three component lists for attribute-surface
  completeness; every assertion count and structural check is unchanged.
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py`: `full_constraints()` now
  delegates to `list(structure.model_constraints.all_constraints)`, proven element-for-element
  `is`-identical to the old manual re-concatenation before the swap; its docstring is rewritten as
  history. Fixed the now-stale pointer at `test_pinned_eval.py:264`.
- Added regression coverage: three `ModelConstraints` unit-contract tests (live-view,
  recompute-not-stored, assignment-raises) in `models/tests/unit/test_constraints.py`, and one
  bimodal post-solve certificate-coverage test
  (`TestAllConstraintsReflectsCertificateAfterSolve` in
  `theory_lib/bimodal/tests/integration/test_iterate.py`).
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`: corrected the stale
  "bypassing the shared engine's `all_constraints` path" note; added an explicit correction
  paragraph stating the property fix, that `_setup_solver` never read `all_constraints` for any
  theory (so this was never a soundness issue), and that the verbose/`--save` display now reports
  the full certificate encoding.
- `docs/architecture/MODELS.md` and `docs/architecture/SEMANTICS.md`: checked for claims asserting
  the stale construction-time-snapshot shape; none found (all three `all_constraints` mentions are
  illustrative pseudocode-example locals, not implementation claims), so left unchanged per the
  plan's "skip rather than edit for its own sake" instruction.

## Decisions

- Chose the computed-property approach over the two alternatives the plan asked to weigh
  (late-emitter-maintains-the-list; promoting the test helper to production) because it is the
  only option that cannot drift out of sync with the four component lists by construction, and it
  required zero changes to any single-phase theory's behavior.
- Redirected the three injection append sites to `model_constraints.model_constraints` rather than
  `frame_constraints`, keeping that pattern textually and semantically distinct from bimodal's own
  `iterate.py` frame_constraints-pinning (which is unrelated and must keep working).
- Kept the `iterate/models.py:152` replacement comment deliberately short after an initial,
  more thorough draft pushed `ModelBuilder.build_new_model_structure`'s source line count past
  `test_simplified_iterator.py::test_simplified_method_shorter`'s `< 170`-line threshold — fixed by
  shortening the comment, never by touching that test's assertion (plan explicitly forbids
  weakening any existing assertion).

## Plan Deviations

- None (implementation followed plan). The `iterate/models.py` comment-length adjustment during
  Phase 2 was a within-phase correction to satisfy an existing, unweakened assertion, not a
  deviation from the plan's scope or approach.

## Impacts

- `all_constraints` now always reflects the current constraint state for all four theories.
  Logos, exclusion, and imposition (single-phase; their component lists never mutate after
  `__init__`) are bit-identical in behavior — proven by the full theory_lib suite and CI's full
  gate showing zero change beyond this task's own added tests.
- Bimodal's verbose "SATISFIABLE CONSTRAINTS:" display and `--save` output now report the full
  certificate encoding (132 constraints for a representative example) instead of the near-empty
  pre-fix snapshot (2 constraints) — a user-visible correction, not a solve-path change.
- `iterate/models.py`'s reader-1 concern (research finding F3) is unaffected: bimodal's
  `_pin_theory_specific_values` bypass, which pins values directly into
  `semantics.frame_constraints`, continues to work exactly as before; the removed assignment at
  line 152 was never read by anything downstream.
- No change to what Z3 is asked to solve, for any theory, at any point: `_setup_solver` never read
  `all_constraints` before or after this fix.

## Follow-ups

- **F4 (recorded, not fixed by this task)**: the generic `is_world`/`possible`/`verify`/`falsify`
  pinning loop in `iterate/models.py` (lines preceding the removed assignment) accumulates its
  pins into a local `temp_solver` that is now visibly write-only for any theory without a
  `_pin_theory_specific_values` override — i.e. logos, exclusion, and imposition (bimodal has an
  override and is unaffected, per F3). Those three theories' rebuilt models during iteration are
  therefore effectively unpinned: the generic pins are computed but never make it into the solve
  that actually produces the next model. Evidence: `reports/01_fix-stale-all-constraints.md`'s F4
  (a live, non-mocked logos iteration probe showing rebuilt model 2's `is_world` signature as an
  independent, unpinned resolve; `iterate/core.py`'s loop has no consistency check that would
  catch a divergent rebuild). Recommend a follow-up task scoped to: (1) confirming the same live
  probe for exclusion and imposition, (2) deciding whether the fix is a
  `_pin_theory_specific_values` default that actually applies `temp_solver`'s assertions, or a
  different mechanism, and (3) adding regression coverage analogous to this task's
  `TestAllConstraintsReflectsCertificateAfterSolve`, but for iteration correctness rather than
  display completeness.

## Minor Observation (not actioned; outside this task's named doc-file scope)

`code/src/model_checker/theory_lib/bimodal/iterate.py:145-146`'s
`_ensure_frame_constraints_in_search_solver` docstring still says, present tense, that
`all_constraints` "permanently misses" the certificate encoding — no longer accurate now that the
property is live, though the defensive design it documents (reading the four component lists
directly, never `all_constraints`) remains correct and necessary for the separate `stored_solver`
bug that docstring is actually about. Phase 6's file list named only `A2_GAP.md` and the two
architecture docs for correction, so this was left as found rather than expanding scope
unilaterally; worth a one-line fix alongside any future touch of that file.

## References

- Plan: `specs/207_fix_stale_all_constraints_snapshot/plans/01_fix-stale-all-constraints.md`
- Research: `specs/207_fix_stale_all_constraints_snapshot/reports/01_fix-stale-all-constraints.md`
- Pre-fix baseline: `specs/207_fix_stale_all_constraints_snapshot/baselines/01_pre-fix-gate.md`
- Post-fix gate + diff: `specs/207_fix_stale_all_constraints_snapshot/baselines/02_post-fix-gate.md`
- Corrected doc: `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`
