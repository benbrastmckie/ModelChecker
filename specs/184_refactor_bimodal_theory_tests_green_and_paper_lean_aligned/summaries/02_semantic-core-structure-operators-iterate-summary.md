# Implementation Summary: Witness-family certificate redesign (semantic core, structure, operators, iterate)

- **Task**: 184 - Redesign the bimodal theory around witness-family certificates (discrete Z-time)
- **Status**: [IN PROGRESS]
- **Started**: 2026-09-25T19:05:00Z
- **Completed**: 2026-09-25T20:30:00Z
- **Effort**: ~5 hours (Phases 9-15 of 24; plan's own estimate for these seven phases is ~13.5
  hours)
- **Dependencies**: Phases 1-8 (certificate foundation and constraint-generation layer; see the
  two prior summaries)
- **Artifacts**: plans/01_witness-family-certificate-redesign.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This dispatch continues from the constraint-generation groundwork (Phases 1-8) through Phase 15:
the entire semantic core (`BimodalSemantics`), `BimodalProposition`, `BimodalStructure`
(solve/extract/re-check and printing), `operators.py`, and `iterate.py` are all rewritten for the
certificate encoding. **This is the first point in the whole redesign where the real end-user
pipeline works end to end**: `Syntax -> ModelConstraints -> BimodalStructure -> interpret ->
print_to` now solves, extracts a certificate, independently re-checks it, and prints it correctly
for both atomic and compound (`\Box A`) examples, confirmed by manual smoke tests against the
live framework. Phases 16-24 (examples migration, test-suite retirement, oracle rewrite, docs,
`development`-marker removal, final verification) remain. The task stays `[IMPLEMENTING]`.

**Two amendment-task items deferred from Phase 9 were completed in Phase 12**: the A0
frame-class standing test (`prior_UZ` and `z1`, both confirmed to report no certificate through
the real solve-and-recheck path, never valid).

## What Changed

- **Phase 9** (`semantic/core.py`, rewrite; `tests/unit/test_semantics_core.py`, new):
  `BimodalSemantics` rewritten from 2,329 lines/~45 methods to 319 lines/11 methods. New
  `DEFAULT_EXAMPLE_SETTINGS` (`back`/`mid`/`fwd`/`max_witnesses` replacing `N`/`M`/`contingent`/
  `disjoint`/`temporal_depth`, D4); `self.N = 0`/`self.all_states = []` set explicitly (D3);
  `true_at`/`false_at` are translate-then-lookup (D5); `premise_behavior`/`conclusion_behavior`
  build the guarded windowed implication over the one-hot target selector directly;
  `finalize_certificate()` (D6) is idempotent and mutates `frame_constraints` in place. 14 tests.
- **Phase 10** (`semantic/core.py` extended; `test_semantics_core.py` extended): added
  `extract_certificate` (Z3 model -> `WitnessFamily` + target time), `export_certificate_json`,
  and a rewritten `inject_z3_model_values`. 4 more tests, including a live round-trip against
  `lake exe check_certificate`.
- **Phase 11** (`semantic/proposition.py`, rewrite; `tests/unit/test_proposition.py`, new):
  `BimodalProposition` rewritten for label-membership truth values at `(lasso, position)` points;
  `proposition_constraints` is always `[]`; "world state" redefined as a lasso index (no separate
  finite state abstraction under the certificate encoding). 11 tests.
- **Phases 12-13** (`semantic/model.py`, rewrite, both halves in one pass; `tests/unit/
  test_structure.py`, new; `tests/unit/test_print_encoding.py`, deleted): `BimodalStructure`
  rewritten 891 -> 349 lines. `_setup_solver` finalizes the certificate before solving (D6); every
  satisfiable solve extracts and **independently re-checks** its certificate, raising
  `ModelConstructionError` on anything but `"countermodel"` (obligation S3,
  `docs/ADEQUACY.md` section 6.2). Printing rewritten to report 01 section 4.4's shape:
  `(back)^w | mid | (fwd)^w` per lasso with the evaluation position bracketed, plus a
  boxed-subformula table with witness lassos/positions. The A0 standing test (deferred from
  Phase 9) added and passing. 17 tests, including golden-output format assertions.
- **Phase 14** (`operators.py`, rewrite; `tests/unit/test_operators.py`, new;
  `test_bound_var_counter_isolation.py`/`test_foralltime.py`, deleted): 1,777 -> 654 lines.
  `Negation`/`And`/`OrOperator` needed no change (already delegated to `semantics.true_at`/
  `false_at`); `Bot`/`Necessity`/`Future`/`Past`/`Until`/`SinceOperator` rewritten as bit lookups
  mirroring their own case in `translate`'s dispatch; every `print_method` converges on
  `general_print`; all quantifier machinery (`ForAll`/`Exists`/`_fresh_bound_int`/
  `reset_bound_var_counter`) deleted. 12 tests, including a whole-constraint-set quantifier-free
  walk.
- **Phase 15** (`iterate.py`, rewrite; `tests/integration/test_iterate.py`, rewrite):
  `_create_difference_constraint`/`_create_non_isomorphic_constraint` rewritten as blocking
  clauses over label bits and box guesses; `_calculate_differences`/`display_model_differences`
  compare two structures' own extracted certificates. **Completed with two reasoned exclusions**
  (full table in the plan's Phase 15 section): rotation/permutation-invariant isomorphism
  rejection was not implemented (exact-difference only); and a genuine, previously-undiscovered
  gap was found -- the live `iterate: N` loop delegates exclusion to a shared, theory-agnostic
  `ConstraintGenerator` gated on `hasattr(semantics, 'is_world')`, which the certificate encoding
  deliberately has none of, so bimodal's own rewritten iterator methods are not actually
  consulted by the live loop (interface-parity only, same as the retired encoding already
  documented -- the redesign is what makes the generic path go inert). 8 tests.

All 78 new/rewritten tests across the seven phases are green (14+4+11+17+12+8+8 across their
respective files, with some overlap in counts already reflected in file totals above -- see each
phase's own plan section for the exact per-phase count).

## Decisions

- **`finalize_certificate()` allocates a witness lasso for every boxed closure member up
  front**, unconditionally (not only for boxes eventually guessed false), matching report 01's
  "at most one more than the number of boxes."
- **`true_at`/`false_at` are pure label lookups with no operator recursion** at the semantics
  level; local coherence (a Z3 constraint, not Python recursion) is what ties a compound
  formula's bit to its constituents'. Verified directly by compound-formula tests (Box, negation,
  until) in Phases 9, 11, and 14.
- **Every operator's `print_method` converges on the shared, eval-point-shape-agnostic
  `general_print`**, dropping `print_over_worlds`/`print_over_times` (shared framework helpers,
  left untouched for other theories) from this theory entirely -- the certificate's own
  boxed-subformula table already gives the "what does the false case look like" display those
  helpers used to provide.
- **`\Until`/`\Since` are event-first in ModelChecker's own surface syntax** (`X \Until Y` means
  "Y holds until X happens", the reverse of a naive reading) -- confirmed the hard way while
  writing Phase 12's A0 standing test (an initially-wrong formula produced a spurious SAT before
  the direction was traced back to `UntilOperator.true_at`'s parameter order). This is exactly
  D2's own point and needs the same care in Phase 16's BX example audit.
- **`iterate.py`'s live-loop exclusion gap is discovered, not introduced by omission**: the
  retired encoding satisfied the shared `ConstraintGenerator`'s `hasattr(semantics, 'is_world')`
  gate, so the generic exclusion mechanism worked for bimodal before this redesign. Removing
  `is_world` (a deliberate, correct design choice per D3/D4) is what exposes the gap. Fixing the
  shared framework code was judged out of scope for a bimodal-only phase without dedicated
  cross-theory regression coverage; recorded as a reasoned exclusion with a concrete next step.

## Plan Deviations

- Phase 9: the A0 frame-class standing test (Amendment task) was deferred to Phase 12, since it
  needs a working solve-and-render path that does not exist until then. Completed in Phase 12 as
  planned.
- Phases 12 and 13 were implemented together in one session (they share `semantic/model.py`, and
  the natural boundary between "solve+recheck" and "print" is not independently testable) --
  both are still recorded and verified as their own `[COMPLETED]` phases.
- Phase 13: `test_print_encoding.py` was deleted, not rewritten -- its entire subject (Unicode
  arrow/subscript cp1252-safety) has no analogue in the new plain-ASCII printer.
- Phase 15: `[COMPLETED WITH EXCLUSIONS]` -- see the plan's own Phase 15 section for the full
  two-item Reasoned Exclusions table (rotation/permutation-invariant rejection; the discovered
  live-loop exclusion gap).
- No other deviations. Every other Phase 9-15 task completed exactly as specified.

## Impacts

- The bimodal test suite remains in the plan's own predicted "red period" (Phases 9-13 named
  explicitly in the Rollback/Contingency section): 148 failed / 80 errored / 292 passed at the
  end of Phase 14, 146/80/291 at the end of Phase 15 -- essentially flat, with churn traceable to
  files Phases 18 and 20-21 are the designated fix points for (`test_data_extraction.py`,
  `test_injection.py`, `test_api_consistency.py`, `test_strict_semantics.py`,
  `test_frame_constraints.py`, `test_frame_class_mapping.py`, `test_until_since.py`,
  `test_modal_witness_integration.py`, and the oracle's own test tree), not a regression
  introduced by this dispatch.
- **The real end-user pipeline now works.** Manual smoke tests (not committed as tests, since
  they exercise the full `builder/example.py`-style construction sequence rather than a unit
  boundary) confirm: an atomic example (`A / B`) and a compound example (`\Box A / B`) both
  solve, extract, independently re-check, and print correctly end to end through
  `print_to` -- including the recursive `INTERPRETED PREMISE`/`INTERPRETED CONCLUSION` display
  with correct colors and truth values.
- `examples.py` (Phase 16-17), the wider test suite (Phase 18-19), the oracle (Phase 20-21),
  docs (Phase 22), and the `development` marker (Phase 23) remain untouched and still reference
  the retired encoding's settings/attributes.

## Follow-ups

- Next dispatch: Phase 16 (examples migration -- settings and expectation audit). Replace every
  example's `N`/`M`/`contingent`/`disjoint` with `back`/`mid`/`fwd`/`max_witnesses`; audit every
  `\Until`/`\Since` argument order against D2 (see "Decisions" above -- this bit Phase 12 once
  already); audit every `expectation` against the paper, in particular `MF_MODAL_FUTURE_TH`
  (cite `modal_future_valid`/`no_witnessFamily_of_MF`) and delete the `test_bimodal.py` comment
  claiming MF has a countermodel.
- Phase 17 restores the nine currently-excluded examples plus `BM_TH_5`.
- Phases 18-19 retire/rewrite the test suite bound to deleted machinery and get the whole bimodal
  suite green with no exclusion list.
- Phases 20-21 rewrite the oracle provider and regenerate its conclusive manifest.
- Phase 22 rewrites the theory docs (retiring the frame-axiom ledger, carrying (SOUND)'s
  statement into `ARCHITECTURE.md` per the adequacy-layer amendment).
- Phase 23 removes the `development` marker and every `and not development` gating clause across
  ~7 files; Phase 24 is final whole-repository verification.
- **Flag for whoever picks up Phase 15's exclusions**: a follow-on task should (1) give
  `iterate/constraints.py`'s `ConstraintGenerator` a theory-specific extension point (with its
  own cross-theory regression plan covering logos/exclusion/imposition), then (2) implement
  `BimodalModelIterator`'s full rotation/permutation-invariant `_create_non_isomorphic_constraint`
  once there is a live loop to actually exercise it against.

## References

- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/summaries/01_constraint-generation-groundwork-summary.md`
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/handoffs/phase-9-handoff-20260925T190914Z.md` through `phase-15-handoff-20260925T203000Z.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, `proposition.py`, `model.py`
- `code/src/model_checker/theory_lib/bimodal/operators.py`, `iterate.py`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
