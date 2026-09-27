# Implementation Summary: Task #201

- **Task**: 201 - Correct A2_GAP.md's emitted-constraint surface and semantic/core.py's sole-writer claim
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T22:14:00Z
- **Completed**: 2026-09-26T23:05:00Z
- **Effort**: 1.0 hours
- **Dependencies**: None
- **Artifacts**: plans/01_a2-gap-surface-correction.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Corrected two false or incomplete documentation/comment claims in the bimodal theory's
certificate-encoding trust surface, and recorded a trade-off the plan's research had surfaced but
not yet documented. All three edits are prose/comment-only; no executable code path was touched.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` — Section 4 gained a new item **(8)**
  documenting `IterativeModelSearch._pin_theory_specific_values` (`iterate.py:190`) as an eighth
  emission call site: it appends unit-literal pins directly to `semantics.frame_constraints`
  (`iterate.py:266`, `:280`) during model iteration, after `finalize_certificate()` has already run
  once (`iterate.py:231`). The section's four "seven"-count occurrences (opening count, the
  "Assembly" paragraph, and the "Net correction" paragraph) were updated to distinguish the seven
  single-solve-reachable call sites from this iteration-only eighth. Section 6 gained a new
  paragraph ("**The cost this closure also introduced.**") stating that `WitnessRegistry.target_window()`'s
  delegation to `certificate._box_window` — while removing a drift hazard — also removes
  independence between the A2-triangle differential's leg (i) (`certificate.recheck`) and leg
  (iii) (the real Z3 encoding) for that specific window, since both legs now call the identical
  Python function; a defect confined to `_box_window`'s own formula is invisible to that
  differential by construction.
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` — The D6 comment block
  (lines 164-166 pre-edit) was narrowed from an unqualified "finalize_certificate() is the sole
  writer" claim to the true, scoped claim: sole writer *inside this class* within a single solve,
  preserving the by-reference-alias rationale (`models/constraints.py:80`) verbatim, with a new
  sentence naming `iterate.py`'s `_pin_theory_specific_values` as a second writer outside the
  class during model iteration, and a cross-reference to `A2_GAP.md` section 4 call site (8).

## Decisions

- Reworded the "Net correction" paragraph's qualified count away from the research report's
  literal suggested phrasing ("seven call sites reachable from a single solve") to "seven
  single-solve-reachable call sites" — the literal phrasing contains the exact substring the
  plan's own verification grep (for bare "seven call sites") requires to be absent from the file;
  the reworded text preserves identical meaning while passing that check.
- Left call sites (1)-(7) unrenumbered and confined the D6 edit strictly to the three-line comment
  block, per the plan's non-goals (no renumbering, no touching the sibling task's D4 monotonicity
  commentary elsewhere in `core.py`).

## Plan Deviations

- **Task 1.4** altered: reworded the Net correction paragraph's phrasing (see Decisions above)
  instead of using the report's literal suggested text verbatim, because that literal text would
  fail this same phase's own verification grep. Meaning is unchanged.

## Verification

- Build: N/A (documentation/comment-only change)
- Tests: Passed — `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`
  → 508 passed in 141.86s; `test_certificate_a2_triangle.py` (the test most directly touching the
  edited window-sharing and sole-writer claims) → 9 passed in 125.70s, run independently as well.
- `PYTHONPATH=code/src python3 -c "import model_checker.theory_lib.bimodal.semantic.core"` succeeds.
- Files verified: Yes — every file:line citation added (`iterate.py:190/231/266/280`,
  `witness_registry.py:183`, `certificate.py:219-221`, `witness_constraints.py:238`,
  `models/constraints.py:80`) re-checked against the current tree and matches what it claims.
- `grep -rn "seven emission call sites\|seven call sites\|all seven" code/src/model_checker/theory_lib/bimodal/docs/ docs/`
  returns nothing.
- `grep -n "sole writer" code/src/model_checker/theory_lib/bimodal/semantic/core.py` shows only the
  scoped phrasing.
- `git diff --stat` (against the plan's baseline commit) shows exactly two modified source files:
  `A2_GAP.md` and `core.py`.

## Impacts

- Downstream readers of `A2_GAP.md` and `core.py`'s D6 comment now see an accurate accounting of
  the certificate encoding's full emitted-constraint surface (including the iteration-only path)
  and an accurate, non-false claim about `frame_constraints`' writers.
- The A2-triangle differential test's blind spot (window-sharing independence loss) is now
  documented as a known, accepted trade rather than left implicit — relevant context for anyone
  extending or trusting that differential test in the future.

## Follow-ups

- None. The newly documented blind spot (section 6's independence cost) is explicitly out of scope
  for new tests per the plan's non-goals; this is a documentation-only task.

## References

- specs/201_correct_a2_gap_emitted_surface_and_sole_writer/reports/01_a2-gap-surface-correction.md
- specs/201_correct_a2_gap_emitted_surface_and_sole_writer/plans/01_a2-gap-surface-correction.md
- code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md
- code/src/model_checker/theory_lib/bimodal/semantic/core.py
