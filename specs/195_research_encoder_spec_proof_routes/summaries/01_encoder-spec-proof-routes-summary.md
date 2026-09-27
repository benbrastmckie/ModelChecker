# Implementation Summary: Task #195

- **Task**: 195 - research_encoder_spec_proof_routes
- **Status**: [COMPLETED]
- **Started**: 2026-09-27T06:30:00Z
- **Completed**: 2026-09-27T08:25:00Z
- **Effort**: ~2 hours
- **Dependencies**: 192 (A2_GAP.md, complete), 193/194/201/202 (complete)
- **Artifacts**: plans/01_encoder-spec-proof-routes.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Landed the encoder-specification proof-routes research's durable conclusions in the two
documents that carry the A2 story (`A2_GAP.md`, `ADEQUACY.md`) and took the two cheap "free wins"
the research identified inside this task's declared file scope: the swept-grid A0 standing test
strengthening, and the documentation of the aggregate-vs-per-candidate limit, the recommended
route, and the `max_witnesses` precondition. All six plan phases completed with no deviations.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` — section 10's route table gained
  three new rows: **(g) Verified SMT-LIB emitter**, **(h) Translation validation**, and
  **(i) Consume a verified bounded enumerator**, each classified by section 2's link types or as
  removing the obligation; the "Honest ranking" paragraph extended to cover them. Section 8
  gained a third exact limit (the leg (i)/(iii) *comparison* is aggregate, not per-candidate,
  distinct from the exhaustive *enumeration*), naming the per-candidate strengthening as the open
  obligation and linking it to route (h) as translation validation in the small. Section 10
  gained a closing subsection, "The recommended route, and what is declined," recording the
  staged recommendation (routes (a)/(b)/(c)/(g)/(h) declined for now; route (i) as the scoped
  rigor route; the per-candidate strengthening as the immediate local work; Z3 UNSAT-proof
  reconstruction declined on principle) and naming three remaining unaddressed obligations by
  durable anchor. Section 11's see-also now points at `ADEQUACY.md` section 7.1 and cites the
  research report by topic.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — section 7.1's closing sentence
  replaced with a positive "satisfiable in principle" statement followed by the ordered
  (iii-a)-(iii-e) prerequisite list for demonstrating condition (iii), with exactly (iii-a) marked
  blocking. Section 7 gained a `max_witnesses` precondition note beside the (ADEQ) statement, and
  the A2/A3 component-table rows each gained a one-clause precondition. Section 7.3 states the
  precondition beside the A2 statement and notes the A2-triangle test runs uncapped.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` —
  `TestA0FrameClassStandingTest`'s two tests parametrized over an 11-point swept grid (22 cases
  total), with a new `timeout is False` assertion distinguishing genuine UNSAT from an
  inconclusive solver run, and an updated class docstring.

## Decisions

- Kept one test method per instance in Phase 5 (parametrized, not merged), so a failure's test ID
  names both the instance and the grid point.
- Forward-referenced `ADEQUACY.md` section 7.3 from section 7.1's (iii-d) bullet in Phase 3, ahead
  of Phase 4 actually adding that statement — this front-loaded Phase 4's own "one-line pointer"
  task, which needed no further edit once section 7.3 was written.
- Cited the research report in `A2_GAP.md` section 11 by topic only, with no task number and no
  `specs/` path, per the no-task-references-in-deliverables rule.

## Plan Deviations

- None (implementation followed plan).

## Verification

- Build: N/A (documentation and test changes only).
- Tests:
  - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -k A0FrameClass -v`: 22 passed.
  - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`: 528 passed in 140.60s (up from the 508-passed prior-run hypothesis by the net +20 new parametrized A0FrameClass cases; no decrease).
  - `PYTHONPATH=code/src pytest code/tests/ -q`: 645 passed, 5 skipped in 47.50s (matches the prior-run hypothesis exactly).
  - Manual sweep of both A0 instances over the 11-point grid: all 22 points genuinely UNSAT (`z3_model_status=False`, `certificate=None`, `timeout=False`), runtimes 0.007-0.048s each; no grid point dropped.
  - Deliberate temporary inversion of `prior_UZ`'s assertion failed exactly its 11 parametrized cases, leaving `z1`'s 11 cases green; reverted and re-confirmed 22 passed.
- Files verified: Yes (all four touched files re-read and diff-checked before each commit).
- Task-reference lint: clean across `A2_GAP.md`, `ADEQUACY.md`, and `test_structure.py`.
- Cross-reference resolution: verified `subformula_closure` (`semantic/formula.py`),
  `extract_certificate` (`semantic/core.py`), `_setup_solver`/`assert_tracked`
  (`models/structure.py`), `closureOf` (cited elsewhere in this codebase's docs/tests),
  `semantic/symmetry.py`, `iterate.py`, and `ADEQUACY.md` sections 7.1-7.4 and `A2_GAP.md`
  section 9's corollary all resolve.
- `max_witnesses` consistency: `ADEQUACY.md`, `SETTINGS.md`, `USER_GUIDE.md`,
  `API_REFERENCE.md`, and `witness_registry.py`'s docstring all make one consistent claim
  (under-complete when capped below the boxed-subformula count; never unsound).

## Impacts

- The A2 story in `A2_GAP.md` and `ADEQUACY.md` now records the full route inventory the research
  evaluated (nine routes total), the honest staged recommendation, and the concrete, dependency-
  ordered prerequisite list for demonstrating `ADEQUACY.md` section 7.1's condition (iii).
- `ADEQUACY.md` no longer omits `max_witnesses` as a precondition of A2/A3 completeness.
- The A0 standing test now covers the full swept grid measured by the research, with a
  non-inconclusiveness assertion, closing one of the two "free wins" the research identified.

## Follow-ups

- The per-candidate strengthening of the A2-triangle differential (named as the immediate local
  work in `A2_GAP.md` section 10's new closing subsection) is owned by a separate task, per this
  plan's declared non-goals.
- The `family -> assignment` round-trip inverse of `extract_certificate`, the set-level closure
  differential between `semantic/formula.py`'s `subformula_closure` and Lean's `closureOf`, and
  the external ask for the non-`fmp` half of the bounded enumerator (route (i)) remain named,
  unaddressed obligations in `A2_GAP.md`'s new closing subsection.
- The two recommended `.claude/context/` domain notes were explicitly excluded from this plan's
  scope (a disposable deploy artifact; belongs under a `/meta` task in the source store).

## References

- Plan: `specs/195_research_encoder_spec_proof_routes/plans/01_encoder-spec-proof-routes.md`
- Research report: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md`
- Edited: `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`,
  `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`,
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`
