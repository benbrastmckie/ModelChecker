# Implementation Summary: Task #192

- **Task**: 192 - A2 proof-vs-implementation gap companion report
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T18:40:00Z
- **Completed**: 2026-09-26T19:35:00Z
- **Effort**: ~1 hour
- **Dependencies**: None
- **Artifacts**: plans/01_a2-gap-companion-document.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Created `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`, the deep-treatment companion
document to `ADEQUACY.md` and `TRUST_PIPELINE.md` on the A2 (encoding-completeness)
proof-versus-implementation gap: the full category argument for why a proof about the
mathematics cannot discharge a claim about what the Z3 encoder emits, the complete
emitted-constraint surface with each emitter's clause shape written out, and a per-route analysis
of what closing the gap would require. Wired the new document into `ADEQUACY.md` section 7.3,
`docs/README.md` (Quick Navigation and Documentation Overview), and `TRUST_PIPELINE.md`'s "See
also". Documentation only — no source or test file was edited.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` — Created. Eleven sections: what the
  document is; the category argument; the machine-checked / shared-by-import / neither
  three-status table; the emitted-constraint surface (seven call sites, four tracked groups);
  the one-hot selector's conservativity argument; the one remaining independently-defined window
  (and its subsequent closure); the historical local-coherence defect and the standing test's
  blindness to it; what a bounded exhaustive test does and does not establish; the S3 trust-base
  consequence; a per-route table for closing the gap; and a "See also".
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — Section 7.3 gains a short
  cross-reference to `A2_GAP.md`, placed at the section's opening so it reads as pointing readers
  to the deep treatment rather than replacing any of the section's own content.
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` — `A2_GAP.md` added to the Quick
  Navigation "Essential Documentation" bullet list and to the Documentation Overview section
  (its own subsection).
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — "See also" gains an
  `A2_GAP.md` entry, at the top of the list, describing it as the deep treatment of the
  encoder-side gap Stage 2 summarizes.

## Decisions

- Followed the research report's section-to-document mapping (A-I to sections 2-10)
  near-verbatim, as instructed by the plan's Research Integration table, adjusting prose register
  to match `ADEQUACY.md`/`TRUST_PIPELINE.md`'s terse, table-heavy, citation-precise style and
  converting every citation from `file:line` to module-path-plus-symbol form.
- Placed the `ADEQUACY.md` section 7.3 cross-reference at the section's *opening* rather than its
  end, because a concurrently-dispatched sibling task (194) was independently inserting its own
  new paragraph at the end of that same section; anchoring at the opening kept the two edits in
  non-adjacent git hunks, so each could be verified and committed independently without either
  task's uncommitted work being swept into the other's commit.

## Plan Deviations

- **Phase 3 (task "Write section 6")**, and consequently sections 3(ii)/(iii) and section 10's
  route (e): *altered*. While this task was in progress, two concurrently-dispatched sibling
  tasks (193 "extend_a2_triangle_grid_to_nb_nf_2" and 194
  "close_a2_selector_and_window_drift_gaps") landed real, committed changes to the shared working
  tree that closed exactly the gaps this document's original draft (transcribed from the research
  report) described as open:
  - Task 194 made `WitnessRegistry.target_window()` delegate directly to `certificate._box_window`
    (closing "the one remaining independently-defined window"), pinned the two windows' agreement
    with a swept-range regression test, and added `TestSelectorConservativity`
    (`tests/unit/test_witness_constraints.py`), a property test pinning the one-hot selector's
    conservativity argument against `certificate._target_holds`, and recorded the argument itself
    in `ADEQUACY.md` section 7.3.
  - Task 193 widened the A2-triangle test's Tier 1 grid to additionally cover
    `back = 2, mid = 1, fwd = 2` (the `nb = 2` regime the historical defect required) for both
    box-free closures and one size-2 boxed closure, leaving only a pre-existing size-3 boxed
    closure as a named, infeasible residual (~10.7 billion candidates at `nb = nf = 2`).

  Sections 5, 6, 7, 8, and 10 (and the cross-referencing parts of section 3) were rewritten,
  after re-reading the sibling tasks' committed diffs and their own plan files, to describe the
  *current, accurate* state of the codebase rather than ship claims the same working tree already
  contradicted. This is a scope-preserving deviation: the document's structure, its eleven
  sections, and its core category argument (section 2) are unaffected; what changed is that two
  of its running examples of open gaps are now honestly reported as closed (with the argument
  that closing them was evidence, not proof, per section 2 and section 8, made explicit in each
  case). See the phase 3 and phase 6 checklist annotations in the plan file, and the phase-6
  progress file's `deviations` entry, for the itemized record.
- **Phase 6 ("Final scope check")**: *altered*, cosmetically. `A2_GAP.md` was committed at the
  end of phases 1-5 (before the concurrent-sibling revisions above required further edits to it
  in phase 6), so `git status --short` showed it as modified rather than untracked at the final
  scope check. The set of touched paths is unchanged from the plan's four.

## Verification

- Build: N/A (documentation only, no source changes)
- Tests: N/A (no test run required or expected; `git status --short` confirmed no file under
  `semantic/`, `models/`, `tests/`, `oracle/`, or `.claude/` was touched)
- Files verified: Yes — every Lean identifier, Python module/function/method, and test fixture
  named in `A2_GAP.md` was checked to resolve against the live source (`witness_constraints.py`,
  `certificate.py`, `core.py`, `witness_registry.py`, `proposition.py`,
  `model_checker/models/constraints.py`, `model_checker/models/structure.py`, `ADEQUACY.md`'s own
  Lean citation table, and `oracle/bimodal_logic/ground_truth.py`'s supported-tags set). No
  `file:line` citation and no task/project-number citation appears anywhere in the four touched
  files' added content (verified by grep, per the plan's blocking checks).

## Impacts

- Gives future readers and implementers of the bimodal theory's certificate search a single,
  citation-precise account of exactly what is and is not proved about the Z3 encoder, at the
  depth needed to reason about routes for closing the gap (extraction, direct verification,
  reflection) versus routes that merely strengthen evidence (widening the differential grid,
  making the selector argument executable).
- Because this document was authored concurrently with two sibling tasks actively closing parts
  of the gap it describes, it also now serves as an accurate, as-of-writing snapshot of exactly
  which of those gaps are closed and which remain — most usefully, the one true residual named in
  section 7/10: the pre-existing size-3 boxed closure's `nb = nf = 2` coverage, currently
  infeasible under the suite's time budget.

## Follow-ups

- None from this task directly. Section 10's per-route table already names, by description only
  (never by task or project number), the substantial unstarted routes (extraction, direct
  verification, reflection) and the smaller residual (widening the size-3 boxed closure's grid,
  if it ever becomes affordable).

## References

- `specs/192_a2_proof_vs_implementation_gap_report/plans/01_a2-gap-companion-document.md`
- `specs/192_a2_proof_vs_implementation_gap_report/reports/01_a2-proof-implementation-gap.md`
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/README.md`
