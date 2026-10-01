# Implementation Summary: Improve printed model display and colors

- **Task**: 222 - Improve printed model display and colors
- **Status**: [COMPLETED]
- **Started**: 2026-09-30T00:00:00Z
- **Completed**: 2026-09-30T00:00:00Z
- **Effort**: ~9 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_improve-printed-model-display.md, reports/01_bimodal-model-print-display.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Brought the bimodal theory's printed model output (and, for visual consistency, logos's and
exclusion's one-line evaluation block, inherited for free by imposition) up to the readability
of the older Logos-repo bimodal output: bounded line width, unambiguous lasso labels, a
multi-line evaluation-point block, duration-subscripted arrows, and wider color coverage within
the already-declared palette. All 8 plan phases closed; certificate search, lasso semantics, and
truth values were never touched -- only `print_*` methods, their private formatting helpers,
their tests, and the documentation describing the printed shapes.

## What Changed

- **Phase 1**: `print_evaluation`'s `Verification:` line (previously 234 chars unwrapped, the
  longest line in a default run) now wraps to an 80-column budget via `textwrap.wrap`, with a
  round-trip test confirming no word is lost or duplicated at a wrap boundary.
- **Phase 2**: `_lasso_roles` now emits exactly one of three bounded values (`main`, `witness`,
  `reserved, unused`) instead of an unbounded `witness for {formula list}` string -- the
  formula-keyed provenance is still fully recoverable from `Box guesses:`'s own
  `falsified at L{i}, t=±t` entries.
- **Phase 3**: `BimodalProposition.__repr__` now names extension-set members `{L0}`/`{L0, L1}`
  instead of bare integers (`{0}`), which were ambiguous with a time on a line that also reads
  `t=-2`; sorted by the underlying integer (not `pretty_set_print`'s string sort, which would
  misorder `L10` before `L2`).
- **Phase 4**: Transition arrows in a history chain now carry a Unicode-subscripted step
  duration (`⟹₁`) via `utils/glyphs.py::to_subscript`, with a `cp1252` regression test for the
  ASCII-digit fallback (`=>1`).
- **Phase 5**: `print_evaluation` replaced the one-line `Evaluation point: L0 at t=-2` with a
  labelled four-line block (`Lasso`, `History`, `Position`, `Label`), with `History` reusing a
  new `_history_line_for` helper so it is byte-identical to that lasso's own `Histories:` row.
- **Phase 6**: Logos's and exclusion's `print_evaluation` gained the same `Evaluation world:`
  heading-plus-value visual weight (imposition inherits logos's block, confirmed by an explicit
  inheritance test); the `Total Run Time` `sys.__stdout__` footer gates were re-confirmed clean
  (never touched).
- **Phase 7**: The `Evaluation point:` block's labels, not just values, are now colored blue,
  raising the colored-span count (10 -> 18 occurrences on a representative example) while
  staying within the declared SGR palette (`{34, 1;34, 90, 32, 31, 0}`); `render.py`'s
  `print_differences` was reviewed and found already palette-consistent (no change needed).
- **Phase 8**: Updated the module docstring, `ARCHITECTURE.md`'s Rendering Policy,
  `SETTINGS.md`'s `align_vertically` row and worked example, and `README.md`'s full "Sample
  Output" block (regenerated from a real run) to the new shapes; codified the 80-column
  convention as a new bullet in `CODE_STANDARDS.md`'s "Printed Output Conventions"; added a
  standing `sys.__stdout__`-audit test and an end-to-end width-gate integration test; wrapped
  the two remaining in-scope over-80 lines (`print_certificate`/`print_evaluation`'s
  no-certificate messages, and `BimodalProposition.print_proposition`'s truth-annotation line
  for a multi-lasso extension set).

## Decisions

- Role column bounded to three fixed values rather than folded into `Box guesses:` (OQ1):
  removes the unbounded width driver entirely without inventing a cross-reference mechanism.
- `Verification:` always wraps; no new verbosity setting (OQ2).
- Evaluation block is a heading plus four `label: value` lines reusing the shared history-chain
  helper, rather than a second independent rendering (OQ3).
- Logos/exclusion get a two-line heading-plus-value block (not a structural copy of bimodal's
  four-line block), matching their simpler single-world data (OQ4).
- The 80-column convention is codified in `CODE_STANDARDS.md` rather than left as an informal
  target.

## Plan Deviations

- Two unplanned, in-scope width fixes were added beyond the plan's named defects: wrapping the
  no-certificate messages in `print_certificate`/`print_evaluation` (136/103 chars unwrapped)
  and wrapping `print_proposition`'s truth-annotation line when a multi-lasso extension set
  (widened by Phase 3's `L{i}` fix) pushes it past 80 columns. Both are squarely bimodal's own
  `print_*` methods and were required to make the Phase 8 end-to-end width gate meaningful.
- Phase 8's literal "`awk 'length>80' | wc -l` returns `0`" verification target was not met
  exactly: 2 lines remain over 80 (both the same 170-char shape, from `models/structure.py`'s
  framework-shared `print_input_sentences`/`recursive_print` path, used identically by all four
  theories and not named in the dispatch's scope). This is recorded as a formal
  `[COMPLETED WITH EXCLUSIONS]` outcome on Phase 8 with a full Reasoned Exclusions record
  (reason + evidence) in the plan file, satisfying all five admission conditions in
  `status-markers.md`. Down from the recorded baseline of 35 over-80 lines to 2, both the single
  excluded item.
- A pre-existing, out-of-scope width residual was identified and explicitly left unfixed in the
  `-a` (non-default) view only: an example with two or more lassos sharing the
  `reserved, unused` role can still push the `-a` header 1-2 columns past 80, since each
  reserved lasso still gets its own header cell. Documented inline in
  `test_structure.py::TestRoleColumnIsBounded`'s own test docstring; the plan's Goal is scoped
  to the default view plus the `-a` header's *named* 119-char case (fixed), not every possible
  `-a` body permutation.

## Impacts

- `theory_lib/bimodal`'s default `dev_cli.py` output dropped from 35 over-80-column lines to 2
  (both the single documented, out-of-scope exclusion), with no line exceeding 170 chars from
  the historical 234-char maximum within bimodal's own print paths.
- Logos, exclusion, and imposition now print a visually consistent, two-line
  `Evaluation world:` block instead of a bare one-liner.
- Color coverage within bimodal's declared palette nearly doubled (10 -> 18 SGR occurrences on
  the representative TN_CM_1-shaped example) with zero new color meanings and zero codes outside
  the declared set.
- `output/color.py::use_colors`'s gating predicate and precedence order were never touched and
  remain unregressed; every new colored span is gated by the existing call.

## Follow-ups

- None required by this task. A future, separately-scoped task could re-architect
  `models/structure.py`'s recursive sentence-printing path to support line wrapping for very
  long formulas across all four theories, if that is ever prioritized -- no follow-up task was
  created here per the Reasoned Exclusions record's "no residual work" condition.

## References

- `specs/222_improve_printed_model_display_and_colors/plans/01_improve-printed-model-display.md`
- `specs/222_improve_printed_model_display_and_colors/reports/01_bimodal-model-print-display.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/render.py`
- `code/src/model_checker/theory_lib/logos/semantic/model.py`
- `code/src/model_checker/theory_lib/exclusion/semantic/model.py`
- `code/docs/core/CODE_STANDARDS.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md`
- `code/src/model_checker/theory_lib/bimodal/README.md`
