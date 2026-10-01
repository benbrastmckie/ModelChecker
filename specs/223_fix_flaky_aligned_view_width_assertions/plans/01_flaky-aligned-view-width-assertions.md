# Implementation Plan: Task #223

- **Task**: 223 - Fix flaky aligned view width assertions
- **Status**: [IMPLEMENTING]
- **Effort**: 3.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/223_fix_flaky_aligned_view_width_assertions/reports/01_flaky-aligned-view-width-assertions.md
- **Artifacts**: plans/01_flaky-aligned-view-width-assertions.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Two bimodal display tests assert a literal `<= 80` column bound on the `-a`
(`align_vertically`) history table, whose rendered width is a direct arithmetic function of the
role strings Z3's certificate draw happens to assign (`witness` = 7 chars vs
`reserved, unused` = 16, one per lasso column). The assertion is therefore unenforceable and
has held the Tests workflow red nondeterministically since 24d967bb. The fix replaces both
literal bounds with a bound **derived from the roles the draw actually returned**, using one
shared helper that mirrors the production width formula, and proves draw-independence by
monkeypatching `_lasso_roles` to force a wider draw. A measured-but-wrong `## [1.4.1]`
CHANGELOG paragraph found while diagnosing is corrected in the same round. No printer,
semantics, certificate-search, or truth-value code is touched.

### Research Integration

Key findings carried into this plan:
- **Exact width formula confirmed** at `semantic/model.py:533-574`. The aligned table line is
  `8 + time_width + slot_width + sum(widths) + 3*(len(widths) - 1)`, where each
  `widths[i] = max(len(f"L{i} {roles[i]}"), max cell length in column i)` — i.e. every column
  is padded to its own header cell, so each `reserved, unused` substituted for `witness` adds
  exactly 9 columns. Measured: 72 columns for the passing 4-role draw
  (`L0 main / L1 witness / L2 reserved, unused / L3 witness`), 81 with one substitution, 90
  with two. This matches the CI-observed `81 <= 80` and `82 <= 80` failures mechanically.
- **The project's codified 80-column rule explicitly covers the default (non-`-a`) view only**
  (`code/docs/core/CODE_STANDARDS.md:629-635`). The two flaky tests assert a bound the project
  never promised for `-a`, so the test claims — not the printers — are the defect. The unit
  test's own docstring already predicts the residual and then asserts against it anyway.
- **Option A (derive the bound from the returned roles) is the recommended fix**; Option B
  (pin a Z3 seed) is rejected — no seed-pinning precedent exists in the codebase and
  `pyproject.toml` pins `z3-solver>=4.8.0` with no upper bound, so a pinned seed gives no
  cross-version guarantee and proves only that one draw passes. Option C (drop width coverage
  for `-a` entirely) loses all `-a` width-regression coverage and duplicates an already-passing
  vocabulary test.
- **TDD red step must be forced, not awaited**: both tests pass locally across six
  `PYTHONHASHSEED` values, so the red condition is produced deterministically by
  monkeypatching `BimodalStructure._lasso_roles` to return an extra `reserved, unused` entry.
- **CHANGELOG `## [1.4.1]` is wrong on measurement** in two places (lines 20-23 claim "35 to 2"
  in the default view; lines 87-91 claim "two printed lines" both from
  `models/structure.py`'s shared recursive sentence printer). Measured today: 0 over-80 lines
  in the default view, 1 in the `-a` view — the 117-column `Histories:` legend emitted by
  bimodal's own `print_certificate` (`model.py:657-661`), not the shared printer.
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` is the established shared
  test-helper module for this suite (imported by both target files) and is the correct home for
  the derivation and forced-draw helpers.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap path was supplied in this dispatch; no roadmap consultation performed.

## Goals & Non-Goals

**Goals**:
- Both named assertions become independent of which role vocabulary the certificate draw
  assigns, so the Tests workflow stops failing nondeterministically.
- Draw-independence is demonstrated, not assumed: a forced draw carrying extra
  `reserved, unused` roles is exercised and the new assertion still holds.
- The failing condition is reproduced before the fix (TDD red, deterministic via monkeypatch).
- `-a`-view width regressions remain detectable: the derived bound still fails if the printer's
  own geometry (padding, separators, scaffolding) regresses, as distinct from the role draw.
- `code/CHANGELOG.md`'s `## [1.4.1]` entry states counts and attribution that match direct
  measurement.

**Non-Goals**:
- Any change to `semantic/model.py`, any other printer, the semantics, the certificate search,
  or any truth value. `model.py` is read-only reference material for the width formula.
- Bringing the 117-column `Histories:` legend within 80 columns. That is a printer-text change,
  excluded by this task's TESTS ONLY scope; the changelog is corrected to describe it accurately
  instead.
- Pinning any Z3 seed (`sat.random_seed` / `smt.random_seed`) or otherwise constraining the
  solver.
- Editing `code/docs/core/CODE_STANDARDS.md`. Its 80-column rule is already correctly scoped to
  the default view and needs no change.
- Rewriting the v1.4.1 git tag annotation (requires a destructive delete-and-re-push; user-only)
  or editing the GitHub Release body (user decision, see Risks).
- Pushing commits or opening a PR (see `.claude/rules/pr-prohibition.md`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A derived bound that re-implements the production formula only proves the printer is self-consistent, not that any user-facing budget holds | M | H | Accepted and documented in the test docstrings: per CODE_STANDARDS.md there is no codified `-a` budget to defend. Keep the formula-independent part of the check strict — assert the non-role scaffolding (time/slot/separator/padding overhead) stays within an absolute bound so a real geometry regression still fails. |
| The derived formula drifts from `_print_history_table` if that printer is later changed, silently weakening the test | M | M | Assert the derived value against the *actually rendered* header length with equality, not `<=`, so any printer-side geometry change breaks the test loudly instead of passing vacuously. |
| CI green cannot be verified from this dispatch (agents must not push; only Python 3.13 is available locally) | M | H | Draw-independence via the forced-draw monkeypatch is the local substitute for repeated CI runs, and is the acceptance criterion's own stated test. Report the residual CI observation to the user rather than claiming workflow green. |
| Monkeypatching a private method (`_lasso_roles`) couples the test to an internal name | L | M | Localize the monkeypatch in one documented `_build_support.py` helper so a rename has exactly one edit site; the method is already called directly by four existing tests in `test_structure.py`, so this is the suite's established idiom, not a new coupling. |
| Correcting CHANGELOG counts could itself go stale if the legend is later fixed | L | M | State the measurement and its origin (`print_certificate`'s `Histories:` legend, `-a` view only) rather than only a bare count, so a future legend fix produces an obvious, locatable edit. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 2, 3, and 4 touch three disjoint
files and may be dispatched together under territory contracts: Phase 2 owns
`tests/unit/test_structure.py`, Phase 3 owns `tests/integration/test_output_gate.py`, Phase 4
owns `code/CHANGELOG.md`. `tests/_build_support.py` is owned exclusively by Phase 1 and is
read-only for every later phase.

### Phase 1: Shared Helpers and Deterministic RED Reproduction [COMPLETED]

**Phase Notes**:
- Baseline re-measured for the named case (`\Box (A \vee B)` / `\Box A, \Box B`, back=2/mid=1/
  fwd=2): roles `{0: "main", 1: "witness", 2: "reserved, unused", 3: "witness"}`, rendered `-a`
  header is exactly 72 columns, 0 over-80 lines in the default view, 1 over-80 line in the `-a`
  view (the 117-column `Histories:` legend). All four figures match the research report exactly;
  no correction needed.
- Added `aligned_table_width(structure, roles, output)` and `force_lasso_roles(monkeypatch,
  roles)` to `_build_support.py`, mirroring `_print_history_table`'s width formula
  (`semantic/model.py:533-574`) line for line. Verified by direct computation that
  `aligned_table_width` returns exactly 72 for the unpatched live draw of the named case
  (matches the rendered header length to the column).
- TDD RED reproduced via a scratch script (not a committed test) using `force_lasso_roles` to
  substitute `witness` -> `reserved, unused` at one index (L1): the **existing** literal
  `<= 80` logic fails at a measured width of 82 (body-line max, matching the unit test's own
  assertion style), while `aligned_table_width` continues to equal the rendered header exactly
  (81 == 81). A second run substituting two indices (L1 and L3) measured 90 == 90, confirming
  the research-predicted figures (81 for one substitution, 90 for two) to the column. No
  temporary test file was added/removed; the RED output above is the required capture per this
  phase's own task list, produced via a non-committed scratch script per the
  "a test marked for removal... or a scratch run captured in the phase notes" option.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` is fully
  green: 773 passed. `git diff --stat` shows only `_build_support.py` modified.

**Goal**: Add the two test helpers both target files need, and prove the current literal-80
assertions fail against a forced wider draw — the TDD red step, produced deterministically
rather than by waiting for an unlucky solve.

**Tasks**:
- [ ] Re-measure the baseline before changing anything: render the named case
      (`\Box (A \vee B)` premise, `\Box A` / `\Box B` conclusions, back=2/mid=1/fwd=2) in both
      the default and `-a` views and record, in the phase notes, the returned roles dict, the
      rendered header length, and the count of over-80 lines in each view. Confirm or correct
      the research figures (roles `L0 main / L1 witness / L2 reserved, unused / L3 witness`,
      72-column header, 0 over-80 default / 1 over-80 `-a`).
- [ ] Add `aligned_table_width(structure, roles, output)` to
      `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`: compute the expected
      aligned-table line width from the same inputs `_print_history_table` uses — `time_width`,
      `slot_width`, per-column `widths` (header cell `f"L{i} {roles[i]}"` vs rendered cells),
      and the `" | "` separators. Docstring must name `semantic/model.py:533-574` as the
      mirrored source and state that equality (not `<=`) against the rendered header is the
      intended assertion, so a printer geometry change fails loudly.
- [ ] Add `force_lasso_roles(monkeypatch, roles)` to the same module: patch
      `BimodalStructure._lasso_roles` to return the supplied dict, so a test can exercise a
      draw with any role mix. Docstring must state why (the live solve cannot be steered, and
      `pyproject.toml`'s unbounded `z3-solver>=4.8.0` makes a seed pin worthless).
- [ ] Write a temporary RED check (a test marked for removal in this phase's own final step, or
      a scratch run captured in the phase notes) asserting the **existing** literal-80 logic
      against `force_lasso_roles` with two `reserved, unused` entries; capture the failure
      output showing the measured width exceeds 80 (expected ~90 per research).
- [ ] Capture the RED output verbatim in the phase notes, then remove the temporary check (the
      permanent draw-independence coverage lands in Phases 2 and 3).

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Research asserts the aligned line width is
`8 + time_width + slot_width + sum(widths) + 3*(len(widths) - 1)` and that the named case
measures 72 columns with 0 over-80 default-view lines and 1 over-80 `-a` line. Confirm each
figure by direct measurement in this phase's first step before building the helper on it; if
any figure differs, record the measured value and adjust the helper and Phase 4's changelog
wording to the measurement rather than to this plan's text.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` - add
  `aligned_table_width` and `force_lasso_roles`; no change to `_build` / `_settings`.

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` is green
  except for the deliberate temporary RED check, which fails with a width > 80 under the
  forced two-reserved draw.
- `aligned_table_width(...)` returns exactly the rendered header length for the live,
  unpatched draw of the named case.
- After the temporary check is removed, the bimodal suite is fully green again and
  `git diff --stat` shows `_build_support.py` as the only modified file.

---

### Phase 2: Derived Bound in the Unit Test [COMPLETED]

**Phase Notes**:
- Confirmed by reading the whole `TestRoleColumnIsBounded` class before editing: exactly one
  test (the renamed one) carried a literal `-a` width bound; the other four were untouched as
  planned.
- Discovered mid-phase (not anticipated by the plan text): the printer's `---+---` rule/separator
  line is a distinct line type whose own formula (`model.py:565-566`) is always exactly
  `expected_width + 1` -- an algebraic identity sharing `time_width`/`slot_width`/`sum(widths)`/
  column count with the header/row formula, not a second magic constant. The retired literal
  test's `body_lines` (everything except `Histories:`) silently included this separator line,
  which is why the historical CI failure on this file read `82 <= 80` (separator) rather than
  `81 <= 80` (header, which is what the sibling end-to-end-gate test checks). Both the rewritten
  test and its forced-draw sibling now assert `len(separator) == expected_width + 1` explicitly
  alongside the header equality and the row `<=` bound, so this test's scope is unchanged from
  before (still covers every printed table line) while being fully role-derived.
- Draw-independence verified by hand per the Verification criteria: patching the new test's
  equality/≤ assertions to a literal `<= 80` (scratch, reverted) makes
  `test_aligned_view_header_matches_the_derived_width_under_a_forced_wider_draw` fail with
  `assert 81 <= 80` -- confirming the forced-draw test is an actual draw-independence check, not
  a vacuous pass. File restored and diffed byte-identical to the pre-probe version afterward.
- No occurrence of a literal `80` remains in any `-a`/aligned-view assertion in this file (grep
  confirmed); the only `80` occurrences left are the untouched default-view tests and prose
  references to the retired bound.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -v`
  is fully green: 84 passed.

**Goal**: Replace `test_structure.py`'s literal `<= 80` aligned-view assertion with the derived
bound, and add permanent forced-draw coverage proving draw-independence.

**Tasks**:
- [ ] In `TestRoleColumnIsBounded::test_aligned_view_header_and_rows_stay_within_80_columns`
      (`tests/unit/test_structure.py`, assertion at line 655): obtain the roles dict the draw
      returned via `structure._lasso_roles(output=...)`, compute the expected width with
      `aligned_table_width`, and assert the rendered header length **equals** it and that every
      body row length is `<=` it (the shared `widths` list makes equal-or-shorter the printer's
      own invariant, since `line()` rstrips).
- [ ] Rename the test so it no longer claims an 80-column `-a` bound (e.g.
      `test_aligned_view_header_and_rows_match_the_role_derived_width`) and rewrite its
      docstring: drop the "residual left for the end-to-end width gate to catch" framing, state
      that CODE_STANDARDS.md's 80-column rule covers the default view only, and explain that the
      `-a` table's width is a function of the role draw so the enforceable invariant is
      role-derived.
- [ ] Add a sibling test using `force_lasso_roles` with an extra `reserved, unused` entry
      (and a second case with two) showing the derived assertion still holds at the wider
      widths — the acceptance criterion's explicit draw-independence demonstration.
- [ ] Leave `test_default_view_stays_within_80_columns`,
      `test_role_values_are_drawn_from_the_bounded_vocabulary`,
      `test_witness_role_provenance_is_recoverable_from_box_guesses`, and
      `test_aligned_header_role_values_are_bounded_too` untouched.

**Timing**: 45 minutes

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Research asserts exactly one of the five tests in
`TestRoleColumnIsBounded` needs its assertion changed (the one at line 655). Confirm by reading
the whole class before editing; if another test in the class also carries a literal `-a` width
bound, report it and include it rather than silently widening or silently skipping.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - rewrite the one
  aligned-view width assertion, its name and docstring; add the forced-draw sibling test.

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -v`
  is fully green.
- The new forced-draw test fails if the derived bound is replaced by a literal `80` (check
  once by hand, then restore) — proving it is the draw-independence check it claims to be.
- No occurrence of a literal `80` remains in the aligned-view assertions of this file.

---

### Phase 3: Derived Bound in the End-to-End Gate [COMPLETED]

**Phase Notes**:
- Rewrote `test_aligned_view_header_stays_within_80_columns_for_the_named_case` (renamed to
  `test_aligned_view_header_matches_the_role_derived_width_for_the_named_case`) to assert
  equality against `aligned_table_width`, and added
  `test_aligned_view_header_matches_the_derived_width_under_a_forced_wider_draw` using
  `force_lasso_roles` to demonstrate draw-independence in this gate directly (measured 90
  columns, well past the retired literal 80), rather than deferring that demonstration to the
  unit test alone.
- Rewrote `TestEndToEndWidthGate`'s class docstring: scoped the 80-column claim to the default
  view explicitly, named the `-a` view's role-derived invariant instead, and named the
  117-column `Histories:` legend as the one known, excluded-on-purpose `-a` over-80 line.
- `test_default_view_stays_within_80_columns_across_representative_examples` and its `_CASES`
  list left untouched, per the plan; it still asserts the literal 80 bound and still passes.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py -v`
  is fully green: 13 passed, 0 skipped, 0 failed.

**Goal**: Apply the same derived-bound treatment to
`test_output_gate.py::TestEndToEndWidthGate`'s aligned-view test, and correct the class
docstring's scope claim.

**Tasks**:
- [ ] In `test_aligned_view_header_stays_within_80_columns_for_the_named_case`
      (`tests/integration/test_output_gate.py`, assertion at line 245): replace
      `assert len(header) <= 80` with equality against `aligned_table_width` computed from the
      returned roles dict, and rename the test to drop the "within 80 columns" claim.
- [ ] Add a forced-draw case (via `force_lasso_roles`) so the end-to-end gate also demonstrates
      draw-independence rather than deferring it to the unit test.
- [ ] Update `TestEndToEndWidthGate`'s class docstring: it currently presents a single
      end-to-end 80-column assertion covering "the whole display-improvement effort". Scope it
      to the **default** view (matching CODE_STANDARDS.md and
      `test_default_view_stays_within_80_columns_across_representative_examples`), and state
      that the `-a` view is held to the role-derived width instead, with the `Histories:` legend
      named as the one known over-80 `-a` line, excluded by both tests on purpose.
- [ ] Leave `test_default_view_stays_within_80_columns_across_representative_examples` and its
      `_CASES` list untouched.

**Timing**: 30 minutes

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` - rewrite
  the one aligned-view assertion, its name and the class docstring; add the forced-draw case.

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py -v`
  is fully green.
- `test_default_view_stays_within_80_columns_across_representative_examples` still asserts the
  literal 80 bound and still passes (0 over-80 lines), unchanged.

---

### Phase 4: Correct the `## [1.4.1]` CHANGELOG Measurement Claims [COMPLETED]

**Phase Notes**:
- Re-grepped the whole `## [1.4.1]` section (lines 7-92) for every over-80/column-count claim
  before editing: exactly two locations matched, confirming the plan's Scope Hypothesis. No
  third claim found.
- Corrected the Changed bullet: "dropped from 35 to 2" -> "dropped from 35 to 0" (Phase 1's
  measured default-view figure).
- Rewrote the Known limitation paragraph into two bullets: the first corrects the count (one
  line, not two) and attribution (bimodal's own `print_certificate` `Histories:` legend in the
  `-a` view, not `models/structure.py`'s shared recursive sentence printer); the second records,
  per the plan's third task, that the `-a` table's width is role-derived rather than
  fixed-budget, naming both test classes so a future reader finds the contract.
- `git diff code/CHANGELOG.md` touches only lines inside the `## [1.4.1]` section (verified).

**Goal**: Bring the published `## [1.4.1]` entry's over-80-column counts and attribution in
line with direct measurement.

**Tasks**:
- [ ] Correct the "Changed" bullet's closing sentence (`code/CHANGELOG.md:20-23`): the
      default-view over-80 count is the value measured in Phase 1 (expected 0), not 2.
- [ ] Rewrite the "Known limitation" paragraph (`code/CHANGELOG.md:87-91`): one printed line
      still exceeds 80 columns, it appears in the `-a` / `--align_vertically` view only (the
      default view has none), and it is the fixed `Histories:` legend emitted by bimodal's own
      `print_certificate` — not two lines from `models/structure.py`'s framework-shared
      recursive sentence printer. State that bringing it within budget is a printer-text change
      deliberately left out.
- [ ] Add, in the same `## [1.4.1]` entry (under Known limitation or a Fixed note consistent
      with the file's existing conventions), that the `-a` view's table width is a function of
      the certificate draw's role vocabulary and is therefore held to a role-derived bound
      rather than an absolute column count — naming the two tests so a future reader finds the
      contract.
- [ ] Do not touch any other release section; do not touch the git tag annotation.

**Timing**: 30 minutes

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: Research asserts exactly two locations in `## [1.4.1]` are wrong on
measurement (lines 20-23 and 87-91). Re-grep the whole `## [1.4.1]` section for every over-80 /
column-count claim before editing; if a third claim exists, correct it too and say so, rather
than editing only the two this plan names.

**Files to modify**:
- `code/CHANGELOG.md` - the `## [1.4.1]` Changed bullet and Known limitation paragraph.

**Verification**:
- Every numeric over-80 claim in `## [1.4.1]` matches a figure measured in Phase 1.
- No attribution to `models/structure.py` remains for the `-a` legend line.
- `git diff code/CHANGELOG.md` touches only lines inside the `## [1.4.1]` section.

---

### Phase 5: Full Gate and Draw-Independence Evidence [NOT STARTED]

**Goal**: Confirm the whole suite is green, the fix is draw-independent rather than merely green
once, and nothing outside the declared test/doc scope changed.

**Tasks**:
- [ ] Run the full bimodal suite, then the whole test suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` and
      `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q`.
- [ ] Repeat the two previously-flaky tests across several `PYTHONHASHSEED` values and several
      consecutive runs, capturing the returned roles dict each time, to show the derived bound
      holds whichever way the draw falls (not just that it passed once).
- [ ] Record the draw-independence evidence explicitly: the forced-draw tests from Phases 2 and
      3 passing at the one-extra-`reserved, unused` and two-extra widths, with the computed
      bound printed alongside the rendered header length for each.
- [ ] Verify no printer behavior changed: `git diff --stat` must show only
      `tests/_build_support.py`, `tests/unit/test_structure.py`,
      `tests/integration/test_output_gate.py`, and `code/CHANGELOG.md` (plus `specs/**`). In
      particular `semantic/model.py` must be untouched.
- [ ] Confirm the default view still measures 0 over-80 lines and that no truth value changed
      (the default-view gate and the existing bimodal example expectations are the evidence).
- [ ] Note in the handoff that only Python 3.13 is available locally, so Tests-workflow green on
      3.10/3.11/3.12 is observed by the user after the change reaches CI; agents must not push
      (`.claude/rules/pr-prohibition.md`). The forced-draw evidence above is the local standing
      substitute for repeated CI runs.

**Timing**: 40 minutes

**Depends on**: 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification only).

**Verification**:
- Full test suite green; zero failures, zero new skips or xfails.
- The two formerly-flaky tests pass across every sampled `PYTHONHASHSEED` and every repeated
  run, with the roles dict recorded per run.
- `git diff --name-only` lists no file under `code/src/model_checker/theory_lib/bimodal/semantic/`
  or any other non-test, non-CHANGELOG source path.

---

## Testing & Validation

- [ ] The RED condition was reproduced before the fix: the original literal-80 logic fails
      under a forced draw carrying extra `reserved, unused` roles (Phase 1, output captured).
- [ ] Both rewritten assertions pass against the live draw and against forced draws with one
      and two extra `reserved, unused` roles (Phases 2, 3).
- [ ] `test_default_view_stays_within_80_columns` and
      `test_default_view_stays_within_80_columns_across_representative_examples` still assert
      the literal 80 bound for the default view and still pass unchanged.
- [ ] `test_role_values_are_drawn_from_the_bounded_vocabulary` and the other three untouched
      `TestRoleColumnIsBounded` tests still pass.
- [ ] Full repository suite green on the locally available interpreter, repeated runs.
- [ ] `semantic/model.py` and every other printer/semantics source file is byte-identical to
      its pre-task state.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` - `aligned_table_width`
  and `force_lasso_roles` helpers.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - role-derived
  aligned-view assertion plus forced-draw coverage.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` -
  role-derived aligned-view gate plus corrected class-docstring scope.
- `code/CHANGELOG.md` - measurement-accurate `## [1.4.1]` wording.
- `specs/223_fix_flaky_aligned_view_width_assertions/summaries/01_*-summary.md` - execution
  summary, including the measured figures and the draw-independence evidence table.

## Rollback/Contingency

Every change is confined to two test files, one test-support module, and a changelog paragraph —
no production code — so reverting is a `git revert` of this task's commits with no behavioral
consequence; the only effect of a revert is that the two assertions become flaky again.

If the derived-bound approach proves unworkable mid-implementation (for example if the rendered
header cannot be matched exactly because `_print_history_table`'s geometry depends on something
the test cannot observe), stop rather than widening scope into `model.py`, and report the
specific obstruction. The documented fallback is Option C from the research report: drop the
`-a` width assertion and rely on the already-passing role-vocabulary-boundedness test plus the
default-view gate — a strictly smaller change that still ends the flakiness, at the cost of
`-a` width-regression coverage. That trade-off is a scope reduction worth surfacing to the user
rather than deciding silently.
