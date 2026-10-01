# Implementation Summary: Fix flaky aligned view width assertions

- **Task**: 223 - Fix flaky aligned view width assertions
- **Status**: [COMPLETED]
- **Started**: 2026-09-30T00:00:00Z
- **Completed**: 2026-09-30T00:00:00Z
- **Effort**: ~2.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_flaky-aligned-view-width-assertions.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Two bimodal display tests asserted a literal `<= 80` column bound on the `-a`
(`align_vertically`) history table, whose rendered width is a direct arithmetic function of the
role strings (`witness` = 7 chars vs `reserved, unused` = 16 chars) Z3's certificate draw happens
to assign — making the assertion unenforceable and nondeterministically flaky since commit
24d967bb. Both assertions now derive their expected bound from the roles the draw actually
returned, via one shared helper (`aligned_table_width`) that mirrors the production printer's
width formula exactly, and draw-independence is demonstrated (not assumed) via a second helper
(`force_lasso_roles`) that forces a wider draw in a dedicated test. No printer, semantics,
certificate-search, or truth-value code was touched. A measured-but-wrong `## [1.4.1]`
CHANGELOG paragraph discovered while diagnosing was corrected in the same round.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`: added
  `aligned_table_width(structure, roles, output)`, which mirrors `_print_history_table`'s width
  formula (`semantic/model.py:533-574`) line for line, and `force_lasso_roles(monkeypatch,
  roles)`, which patches `BimodalStructure._lasso_roles` to return an arbitrary role mix.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`:
  `test_aligned_view_header_and_rows_stay_within_80_columns` renamed to
  `test_aligned_view_header_and_rows_match_the_role_derived_width` and rewritten to assert
  equality against the derived width (header and the `---+---` rule line) and `<=` for data
  rows, instead of a literal `<= 80`. Added
  `test_aligned_view_header_matches_the_derived_width_under_a_forced_wider_draw`, forcing one and
  two `witness` -> `reserved, unused` substitutions (measured 81 and 90 columns) to prove
  draw-independence.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py`:
  `test_aligned_view_header_stays_within_80_columns_for_the_named_case` renamed to
  `test_aligned_view_header_matches_the_role_derived_width_for_the_named_case` and rewritten the
  same way. Added a forced-draw sibling test, and rescoped `TestEndToEndWidthGate`'s class
  docstring to state the 80-column rule applies to the default view only, naming the `-a` view's
  role-derived invariant and its one known over-80 line (the `Histories:` legend) explicitly.
- `code/CHANGELOG.md`: corrected the `## [1.4.1]` Changed bullet's default-view over-80 count
  (35 -> 2 was wrong; now 35 -> 0) and rewrote the Known limitation paragraph — one over-80 line,
  only in the `-a` view, from bimodal's own `print_certificate` `Histories:` legend (not two
  lines from `models/structure.py`'s shared recursive sentence printer) — and added a note that
  the `-a` table's width is role-derived rather than budget-bound, naming the owning tests.

## Decisions

- Chose Option A (derive the bound from the roles the draw returned) over Option B (pin a Z3
  seed, rejected — no precedent, `z3-solver>=4.8.0` has no upper bound so a pin gives no
  cross-version guarantee) and Option C (drop `-a` width coverage, which would lose
  width-regression coverage the research explicitly wanted kept).
- Discovered mid-implementation that the printer's `---+---` rule/separator line is a third,
  distinct line type whose own formula is always exactly `expected_width + 1` — an algebraic
  identity from sharing the same `time_width`/`slot_width`/`sum(widths)`/column-count terms with
  the header/row formula, not a second magic constant. The retired tests' `body_lines` filter
  silently included this line, which is why the historical CI failure on the unit test read
  `82 <= 80` (separator) while the integration test's narrower `header`-only check read
  `81 <= 80`. Both rewritten tests now assert the separator explicitly rather than relying on
  loose inclusion.
- Verified the TDD RED step via a reproducible (non-committed) scratch script using
  `force_lasso_roles`, rather than adding and then deleting a temporary test file, per the
  plan's own "scratch run captured in the phase notes" option.

## Plan Deviations

- None (implementation followed plan; the separator-line finding was anticipated by the plan's
  own Risk table — "assert the non-role scaffolding... stays within an absolute bound" — and
  resolved within Phase 2/3 scope rather than requiring a plan change).

## Impacts

- The two previously flaky tests (`test_aligned_view_header_and_rows_stay_within_80_columns` and
  `test_aligned_view_header_stays_within_80_columns_for_the_named_case`, renamed as above) no
  longer depend on which role vocabulary a given Z3 solve happens to draw, ending the
  nondeterministic Tests-workflow failures observed since 24d967bb (including on the v1.4.1
  release commit).
- `-a`-view width-regression coverage is preserved and strengthened: the derived bound is an
  equality check against the printer's own geometry, so a real regression in padding, separators,
  or scaffolding still fails loudly, and the forced-draw tests now exercise widths (81, 90
  columns) the live draw happens not to produce for this example.
- The published CHANGELOG's `## [1.4.1]` entry now states counts and attribution that match
  direct measurement.

## Follow-ups

- Tests-workflow green on Python 3.10/3.11/3.12 can only be confirmed by the user once this
  change reaches CI — only Python 3.13 was available in this environment, and agents must not
  push or open a PR (`.claude/rules/pr-prohibition.md`). The forced-draw evidence in Phase 5 is
  the local standing substitute.
- The 117-column `Histories:` legend in the `-a` view remains over 80 columns by design (a
  printer-text change, out of this task's test-only scope); the CHANGELOG now documents this
  accurately rather than claiming it fixed.
- The v1.4.1 git tag annotation still carries the original wrong wording and cannot be corrected
  without a destructive delete-and-re-push (user-only); the GitHub Release body can be edited by
  the user in place if desired.

## References

- `specs/223_fix_flaky_aligned_view_width_assertions/plans/01_flaky-aligned-view-width-assertions.md`
- `specs/223_fix_flaky_aligned_view_width_assertions/reports/01_flaky-aligned-view-width-assertions.md`
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py`
- `code/CHANGELOG.md`
