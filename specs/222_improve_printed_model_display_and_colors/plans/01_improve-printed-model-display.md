# Implementation Plan: Task #222

- **Task**: 222 - Improve printed model display and colors
- **Status**: [COMPLETED]
- **Effort**: 9 hours
- **Dependencies**: None
- **Research Inputs**: specs/222_improve_printed_model_display_and_colors/reports/01_bimodal-model-print-display.md
- **Artifacts**: plans/01_improve-printed-model-display.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Bring the bimodal theory's printed model block (and, for visual consistency, the three
sibling theories' one-line evaluation block) up to the readability of the older Logos-repo
bimodal output: bounded line width, unambiguous lasso labels, a multi-line evaluation-point
block, duration-subscripted arrows, and wider color coverage within the already-declared
palette. This is a display/formatting change only — certificate search, lasso semantics, and
truth values are untouched; only `print_*` methods, their private formatting helpers, their
tests, and the documentation that describes the printed shapes change. Done means: a full
`examples.py` run emits no line over 80 columns (measured baseline today: max 234, 35 lines
over 80), the evaluation point reads as a labelled block, plain (non-TTY) output remains
fully informative with every escape stripped, and the existing color-gating predicate
(`output/color.py::use_colors`) is unchanged and unregressed.

### Research Integration

The report (`reports/01_bimodal-model-print-display.md`) confirmed all five dispatch defects
against live pty captures of both repos and resolved several plan-relevant unknowns that this
plan builds on directly:

- **The `sys.__stdout__` audit is already clean.** All three flagged sites
  (`logos/semantic/model.py:141`, `exclusion/semantic/model.py:338`,
  `imposition/semantic/model.py:120`) are the `Total Run Time` footer gate, structurally
  identical to bimodal's legitimate case — none is a color gate. **No code change is planned
  for this item**; Phase 8 adds a standing grep assertion so the finding cannot silently rot.
- **Open Question 5 is resolved (verified during planning, not assumed):**
  `ImpositionModelStructure` extends `LogosModelStructure` (`imposition/semantic/model.py:21`)
  and has no `print_evaluation` override — `grep -rn "def print_evaluation"` across
  `theory_lib/` returns exactly three hits (logos, exclusion, bimodal). Imposition inherits
  logos's block for free; the cross-theory phase therefore edits **two** files, not three.
- **`to_subscript` already exists** in `utils/glyphs.py` (lines 153-172), encoding-aware and
  width-neutral by construction. **No new glyph entry is needed** — the dispatch's assumption
  that one was required is superseded.
- **The `__repr__` fix is unpinned by existing tests**: every `truth_set`/`false_set`
  assertion in `test_proposition.py` is against the raw `Set[int]`, never the rendered string.
- **No written 80-column standard exists** in `CODE_STANDARDS.md` or `TESTING_GUIDE.md`. This
  plan takes the report's option (b): codify it (Phase 8) so the new width test enforces a
  documented convention rather than a magic number.
- The report's SGR measurement (10 occurrences / 7 values here vs. 13 / 5 in the benchmark)
  corrects the dispatch's "5 distinct SGR codes" figure but confirms its direction. Phase 7 is
  scoped to the concrete in-scope lever the report identified: coloring block *labels* as well
  as values, within the existing palette.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch; no ROADMAP.md consultation performed.

## Goals & Non-Goals

**Goals**:
- No line of a default (non-`-a`) `examples.py` run exceeds 80 columns, and the `-a` view's
  header does not either.
- Lasso extension sets print as `{L0}` / `{L0, L1}`, never bare integers ambiguous with times.
- The evaluation point prints as a labelled multi-line block naming the lasso, its arrow
  chain, the position (signed time plus slot), and the label at that position.
- Transition arrows carry a Unicode-subscripted step duration via the existing
  `utils/glyphs.py::to_subscript`, with an ASCII/cp1252 fallback regression test.
- Color coverage extends to block labels within the declared `_BLUE`/`_HILITE`/`_GRAY`/
  `_GREEN`/`_RED` palette; no new color meanings are invented.
- Logos and exclusion's one-line `The evaluation world is:` gains matching visual weight
  (imposition inherits it).
- Documentation naming the changed shapes is updated in the same pass.

**Non-Goals**:
- Any change to certificate search, lasso semantics, box-guess computation, or truth values.
- Any change to `output/color.py::use_colors` or its precedence order — it is already better
  than the benchmark and must not regress.
- Removing the `Total Run Time` `output is sys.__stdout__` gates (a documented legitimate use).
- Adding a new user-facing setting or CLI flag (`_verification_label` is always-wrapped, not
  verbosity-gated — see Phase 1 rationale).
- Changing `render.py`'s formula rendering or `build_names` (no finding touches them;
  `print_differences` only needs to stay palette-consistent).
- Making `-a` the default view.

## Decisions (resolving the report's open questions)

These are ordinary planning judgment calls made here so the implementer does not re-litigate
them. Each records its rationale.

1. **Role-column strategy (OQ1): bound the role vocabulary, do not fold into `Box guesses:`.**
   `_lasso_roles` emits one of exactly three short forms — `main`, `witness`,
   `reserved, unused` (max 16 chars) — dropping the unbounded `witness for □χ, □ψ` formula
   list. The formula-keyed provenance is **already printed** by `_print_box_guesses` as
   `falsified at L{i}, t=±t`, so no information is lost and no cross-reference mechanism has
   to be invented (the report flagged invention as a genuine design risk). This removes the
   unbounded width driver entirely and fixes the `-a` header's 119-char case with the same
   edit.
2. **`Verification:` label (OQ2): always wrap, no new setting.** Wrapping at the 80-column
   budget with indented continuation lines keeps `out.count("Verification:") == 1` (the
   existing `test_output_gate.py` assertion) trivially true and avoids `settings/types.py` +
   `SETTINGS.md` churn for a verbosity flag nobody asked for.
3. **Evaluation block shape (OQ3):** a heading plus four indented `label: value` lines —
   `Lasso`, `History`, `Position`, `Label` — reusing `_history_cells`/`_join_history` through
   a new `_history_line_for(index, output)` helper factored out of `_print_history_lines`, so
   the chain in the block is byte-identical to that lasso's `Histories:` row.
4. **Cross-theory treatment (OQ4): matching visual weight, not a structural copy.** Logos and
   exclusion have no lasso chain, so they get a two-line block (heading plus one indented
   value line) with both lines blue — the benchmark's "every line of the block is colored"
   convention, adapted to their data.
5. **80 columns (report's final finding): codify it.** Phase 8 adds it to
   `CODE_STANDARDS.md`'s "Printed Output Conventions" so the width test enforces a stated
   convention.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Dropping the formula list from the role column loses information a reader relied on | M | M | `Box guesses:` already prints the same provenance keyed by formula; Phase 2 adds an assertion that every `witness` row's formula is recoverable from that table |
| A width fix in one place is undone by another phase's new output | H | M | Phase 8 re-runs the end-to-end max-width gate over the full `examples.py` run after every other phase lands; Phases 1 and 2 each carry their own narrower width assertion |
| Golden-output assertions become brittle and block unrelated future work | M | H | Assert structural invariants (line count, label presence, ordering, width bound) rather than byte-for-byte whole-block goldens; reserve exact-string assertions for the short label lines |
| Changing logos's `print_evaluation` silently alters imposition and any other subclass | H | M | Phase 6 is tier `full`; it greps for every `LogosModelStructure` subclass before editing and runs the whole theory_lib suite |
| New subscript glyph path raises on a cp1252 stream | H | L | `to_subscript` is already encoding-aware; Phase 4 adds the `make_encoding_test_streams` regression test the TESTING_GUIDE section 9 discipline requires |
| Color changes leak escapes into pipes | H | L | Every new colored span is gated by the existing `use_colors(output)` call already present in each method; `TestColorGating` is extended, never weakened |
| Docs left stale after print-shape change | M | M | Phase 8 is a named phase with enumerated doc targets, not optional cleanup |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 4 |
| 3 | 6 | 5 |
| 4 | 7 | 5, 6 |
| 5 | 8 | 1, 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Wrap the `Verification:` label [COMPLETED]

**Goal**: The `Verification:` output — present in every example, `-a` or not, and today the
single longest line at 234 chars — wraps inside an 80-column budget without changing its
wording or its one-occurrence-per-example contract.

**Tasks**:
- [ ] Write the failing test first, in
      `theory_lib/bimodal/tests/integration/test_output_gate.py`: for each of the module's
      existing no-checker scenarios, capture `print_evaluation` output and assert
      `max(len(line) for line in out.splitlines()) <= 80`.
- [ ] Add a second failing assertion that `out.count("Verification:") == 1` still holds and
      that the full unwrapped sentence is recoverable by joining the wrapped lines (so no
      word is lost or duplicated at a wrap boundary).
- [ ] Confirm the existing `FORBIDDEN_OVERCLAIM` absence assertions still pass unchanged.
- [ ] Implement: import `textwrap` in `bimodal/semantic/model.py`; in `print_evaluation`,
      wrap `self._verification_label()` with `textwrap.wrap(..., width=80,
      initial_indent="Verification: ", subsequent_indent="  ")` (or equivalent) and print the
      resulting lines. Leave `_verification_label`'s returned string unwrapped — it stays a
      pure single-line label; wrapping is a presentation concern of the print method.
- [ ] Update `_verification_label`'s and `print_evaluation`'s docstrings to say the label is
      wrapped at print time.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: The `Verification:` line is currently the single longest line at 234
chars and appears exactly once per example. Confirm at implementation time with
`./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | awk '{print length}' | sort -rn | head -1`
(expect `234` before, `<= 80` for this line after) and
`... | grep -c '^Verification:'` against the example count.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — `print_evaluation` wraps the
  label; `textwrap` import; two docstrings
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` — new
  width and round-trip assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py -v` passes
- The `Verification:` line no longer appears in `awk 'length>80'` output of a full run

---

### Phase 2: Bound the role column [COMPLETED]

**Goal**: `_print_history_lines`'s `role_width` padding can no longer be driven by an
arbitrarily long formula list, so every history row and the `-a` header fit inside 80 columns.

**Tasks**:
- [ ] Write the failing tests first in `theory_lib/bimodal/tests/unit/test_structure.py`:
      build a structure whose witness role would today render
      `witness for \Box \neg A, \Box \neg (A \vee B)` (the report's measured 49-char case) and
      assert every line of `print_certificate` output is `<= 80` in both the default and
      `align_vertically=True` views.
- [ ] Add an assertion that the role column's rendered value is drawn from exactly
      `{"main", "witness", "reserved, unused"}`.
- [ ] Add an assertion that for every lasso whose role is `witness`, the `Box guesses:` table
      in the same output contains a `falsified at L{i}` entry naming that lasso — the
      provenance is not lost, only relocated.
- [ ] Implement: in `_lasso_roles`, replace the
      `f"witness for {boxes}"` branch with the bare `"witness"`; drop the now-unused `render`/
      `names` work in that method if nothing else needs it.
- [ ] Verify `_print_history_table`'s header (`f"L{index} {roles[index]}"`) is fixed by the
      same change with no separate edit.
- [ ] Update `_lasso_roles`'s docstring to state the three-value vocabulary and to point at
      `Box guesses:` for the formula-keyed provenance.
- [ ] Confirm the existing `TestAlignedHistoryTable` assertions
      (`re.match(r"\s+t\s+slot\s+\| L0 main\s+\| L1 ", header)`,
      `any(line.strip().startswith("L0  main") ...)`) still pass — `main` is unchanged.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: 35 lines of a full run exceed 80 columns today; after Phase 1 removes
the `Verification:` lines, the remainder is hypothesized to be the ~6 history rows the report
measured (max 98) plus the `-a` header (119). Confirm by re-running the `awk 'length>80' | wc -l`
baseline after Phase 1 and again after this phase; if any over-80 line remains that is neither
a history row nor the `-a` header, stop and report it rather than widening this phase.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — `_lasso_roles` witness
  branch and docstring
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — new width,
  role-vocabulary, and provenance-recoverability assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -v` passes
- No history row or `-a` header exceeds 80 columns in a full run

---

### Phase 3: Unambiguous proposition extension sets [COMPLETED]

**Goal**: `|A| = < {0}, {} >` becomes `|A| = < {L0}, {} >`, so extension members can never be
misread as times on a line that also carries `t=-2`.

**Tasks**:
- [ ] Write the failing test first in `theory_lib/bimodal/tests/unit/test_proposition.py`:
      assert `repr(proposition)` contains `{L0}` and does not contain a bare `{0}`.
- [ ] Extend the existing `test_print_proposition_does_not_raise` with an assertion that the
      printed line carries the `L`-prefixed form.
- [ ] Implement: in `BimodalProposition.__repr__` (`semantic/proposition.py`), map each index
      through `f"L{i}"` before `pretty_set_print` — e.g.
      `pretty_set_print({f"L{i}" for i in self.truth_set})`. Confirm `pretty_set_print`'s
      ordering behavior on strings still yields a stable, readable order; sort explicitly by
      the underlying integer if it does not.
- [ ] Leave `self.truth_set` / `self.false_set` themselves as `Set[int]` — only the rendering
      changes, so every existing raw-attribute assertion keeps passing untouched.
- [ ] Update `__repr__`'s (or the class's) docstring to name the `L{i}` convention and its
      consistency with the rest of the printed block.

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: No existing assertion pins the `< {0}, {} >` string shape (the report
verified this against `test_proposition.py:62-63,165-166,168-181`). Confirm at implementation
time with `grep -rn "truth_set\|false_set\|< {" code/src/model_checker/theory_lib/bimodal/tests/`
before editing; if a pinning assertion turns up outside the files named there, update it in
this phase rather than deferring.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` — `__repr__` and its
  docstring
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` — new repr and
  printed-line assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py -v` passes
- A full run shows `|A| = < {L0}, ... >` with no bare-integer extension set

---

### Phase 4: Duration-subscripted transition arrows [COMPLETED]

**Goal**: Each `⟹` in a history chain carries the step duration as a Unicode subscript
(`⟹₁`), matching the benchmark, using the existing encoding-aware `to_subscript`.

**Tasks**:
- [ ] Write the failing tests first in `theory_lib/bimodal/tests/unit/test_structure.py`:
      assert the default-view output contains `⟹₁` (not a bare `⟹`) on a UTF-8 stream.
- [ ] Write the cp1252 regression test in the sanctioned existing style
      (`make_encoding_test_streams` / `read_encoding_test_stream`, mirroring
      `test_table_cp1252_leg_does_not_raise`): printing to the cp1252 stream must not raise
      and must render the plain-ASCII digit form.
- [ ] Assert the width bound from Phase 2 still holds — `to_subscript` is width-neutral by
      construction, so rows must not grow beyond the one added character per arrow.
- [ ] Implement: import `to_subscript` into `bimodal/semantic/model.py`; in `_join_history`,
      compute the gap between adjacent representative positions from the same
      `target_window()` sequence `_history_cells` walks, and build the arrow as
      `f" {glyph('DOUBLE_ARROW', output)}{to_subscript(dur, output)} "`.
- [ ] Note in the docstring that under the current `target_window()` every gap is `1`, so the
      subscript always renders `₁` today; the mechanism exists for windows that skip positions.
- [ ] Re-check `_join_history`'s column-padding math: the arrow string is now longer, and
      `widths` is computed from cells, not arrows, so alignment should be unaffected — assert
      it explicitly with a multi-lasso alignment test.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: `to_subscript` already exists and needs no new glyph entry (report
Finding 4, `utils/glyphs.py:153-172`). Confirm by reading that function before editing; if it
does not in fact accept `(n, output)` and fall back to ASCII digits, stop and re-scope rather
than adding a new glyph table entry silently.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — `_join_history` arrow
  construction, `to_subscript` import, docstring
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — subscript,
  cp1252 fallback, and alignment assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -v` passes
- Piping a run through a cp1252-encoded stream raises no `UnicodeEncodeError`

---

### Phase 5: Multi-line evaluation-point block (bimodal) [COMPLETED]

**Goal**: Replace `Evaluation point: L0 at t=-2` with a labelled block naming the lasso, its
arrow chain, the position, and the label at that position — all data already on `self`.

**Tasks**:
- [ ] Write the failing golden-structure tests first in
      `theory_lib/bimodal/tests/unit/test_structure.py`: assert the block is a heading
      `Evaluation point:` followed by exactly four indented lines whose labels are, in order,
      `Lasso`, `History`, `Position`, `Label`.
- [ ] Assert the `History` line's chain is byte-identical to that lasso's row in the
      `Histories:` block (with the row prefix stripped) — this pins the shared-helper
      contract rather than a brittle whole-block golden.
- [ ] Assert the `Position` line carries both the signed time and the slot name
      (`_slot_name`), and that every block line is `<= 80` columns.
- [ ] Assert the plain (non-TTY) rendering of the block is fully informative with no escapes.
- [ ] Implement: factor the per-row chain construction out of `_print_history_lines` into a
      new `_history_line_for(index, output)` helper so both call sites share it verbatim.
- [ ] Implement: rewrite `print_evaluation`'s point rendering to emit the four-line block from
      `self.main_point['lasso']`, `self.certificate`, `self.target_time`, and `_slot_name`,
      keeping the wrapped `Verification:` output from Phase 1 immediately after it.
- [ ] Leave the no-certificate (D8) branch of `print_evaluation` unchanged.
- [ ] Confirm `test_output_gate.py`'s `out.count("Verification:") == 1` and the
      `FORBIDDEN_OVERCLAIM` checks still pass.

**Timing**: 2 hours

**Depends on**: 1, 2, 4

**Verification Tier**: interface

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — new `_history_line_for`,
  rewritten `print_evaluation` point block, `_print_history_lines` refactor, docstrings
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — block-structure,
  chain-identity, and plain-output assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes
- `./dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py` shows the block on
  every example, `TN_CM_1` included

---

### Phase 6: Cross-theory evaluation block (logos, exclusion) [COMPLETED]

**Goal**: Logos and exclusion's single-line `The evaluation world is: {world}` gains the same
visual weight as bimodal's new block — a heading plus an indented, fully colored value line —
so the four theories read consistently. Imposition inherits logos's implementation.

**Tasks**:
- [ ] Before editing, grep for every subclass of `LogosModelStructure` and every override of
      `print_evaluation` across `theory_lib/` to confirm the blast radius is exactly the two
      files named below plus inheriting subclasses.
- [ ] Write the failing tests first, in each theory's own existing structure/printing test
      module: assert `print_evaluation` emits a heading line plus one indented value line,
      that both lines are blue on a fake-TTY stream, that neither exceeds 80 columns, and
      that the plain rendering names the world with no escapes.
- [ ] Add an imposition-side test asserting the inherited block appears in its output, so the
      inheritance relationship is pinned rather than assumed.
- [ ] Implement in `logos/semantic/model.py::print_evaluation`: replace the single
      `f"\nThe evaluation world is: {BLUE}{...}{RESET}\n"` print with a two-line block
      (`Evaluation world:` heading, indented value), wrapping the label text in blue as well
      as the value.
- [ ] Implement the structurally identical change in `exclusion/semantic/model.py::print_evaluation`.
- [ ] Do not touch either file's `output is sys.__stdout__` `Total Run Time` footer.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: Exactly two `print_evaluation` implementations need editing — logos and
exclusion — because `ImpositionModelStructure` extends `LogosModelStructure` with no override
(verified during planning via `grep -rn "def print_evaluation" theory_lib/`, three hits total
including bimodal). Re-run that grep at implementation time; if a fourth override has appeared
or another subclass overrides it, extend this phase's file list before editing.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic/model.py` — `print_evaluation`
- `code/src/model_checker/theory_lib/exclusion/semantic/model.py` — `print_evaluation`
- The corresponding logos / exclusion / imposition test modules — new block-shape and
  color-gating assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -v` passes (full theory_lib
  suite, because a shared base class changed)
- Running each theory's `examples.py` shows the consistent block

---

### Phase 7: Extend color coverage within the declared palette [COMPLETED]

**Goal**: Raise bimodal's colored-span count toward the benchmark's by coloring the new
block's labels as well as its values, without inventing any new color meaning.

**Tasks**:
- [ ] Write the failing test first in `test_structure.py`'s `TestColorGating` style: on a
      fake-TTY stream, assert each of the evaluation block's lines opens its own blue span
      (the benchmark's per-line convention, not one span wrapping the block), and count the
      distinct SGR values emitted to confirm they are a subset of the declared palette
      `{34, 1;34, 90, 32, 31, 0}`.
- [ ] Assert the same output on a plain stream contains no `\033[` at all, and that removing
      every escape leaves text that still distinguishes every colored distinction (the
      "color never carries information alone" rule from `CODE_STANDARDS.md`).
- [ ] Implement: extend the blue spans in `print_evaluation`'s block to cover each line's
      label text, gated by the already-present `use_colors(output)` call.
- [ ] Review `semantic/render.py::print_differences` for palette consistency with the block;
      change only if it now clashes, and record "no change needed" explicitly if it does not.
- [ ] Do not add any palette constant beyond the five declared in `model.py` and do not touch
      `output/color.py`.

**Timing**: 1 hour

**Depends on**: 5, 6

**Verification Tier**: interface

**Scope Hypothesis**: The declared palette is the five constants at `model.py:353-358` plus
`_RESET`. Confirm by reading that block at implementation time; if the SGR-subset assertion
fails because framework code in `models/structure.py` contributes additional codes
(white/yellow from `set_colors`), scope the assertion to `model.py`-originated spans rather
than loosening it to admit arbitrary codes.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — blue spans in the
  evaluation block
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — palette-subset
  and escape-stripping assertions

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -v` passes
- A pty capture of `TN_CM_1` shows more colored spans than before and no code outside the
  declared palette

---

### Phase 8: Documentation sync and end-to-end width gate [COMPLETED WITH EXCLUSIONS]

**Goal**: Every document that describes the now-changed printed shapes is updated in the same
pass, the 80-column convention is codified, and a single end-to-end assertion locks the whole
result in.

**Tasks**:
- [x] Update `bimodal/semantic/model.py`'s module docstring "Printed output" section (around
      lines 69-85): the role vocabulary, the subscripted arrows, the multi-line evaluation
      block, the wrapped `Verification:` line.
- [x] Update `bimodal/docs/ARCHITECTURE.md`'s "Rendering Policy" section (around lines
      276-314): the `L{i}  {role}  …` row shape, the arrow subscript, the evaluation block,
      and the role-provenance pointer to `Box guesses:`.
- [x] Update `bimodal/docs/SETTINGS.md`'s `align_vertically` row and the prose beneath it
      (around line 167), which quotes the old arrow-chain shape verbatim.
- [x] Add a fourth bullet to `code/docs/core/CODE_STANDARDS.md`'s "Printed Output Conventions"
      codifying the 80-column budget for model output, naming the test that enforces it.
- [x] Add the standing `sys.__stdout__` audit assertion: a test (or a documented grep in
      TESTING_GUIDE terms) asserting that every `output is sys.__stdout__` occurrence under
      `theory_lib/*/semantic/model.py` sits in a `Total Run Time` footer, so the report's
      "already clean" finding cannot silently rot.
- [x] Add the end-to-end width gate: an integration test running a representative multi-example
      print and asserting no emitted line exceeds 80 columns, in both default and `-a` views.
- [x] Run the full suite and a full `dev_cli.py` run; confirm `awk 'length>80' | wc -l` is `0`
      against the recorded baseline of `35` -- **result: 2, not 0; see Reasoned Exclusions
      below** (both occurrences are the single excluded item, `models/structure.py`'s
      framework-shared `print_input_sentences`, not a new or different defect).
- [x] Ensure no documentation edit outside `specs/**` cites a task number (per
      `.claude/rules/no-task-references-in-deliverables.md`); cite filenames and section
      headings instead. Confirmed via a grep sweep of every file this phase touched: no hits.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| `models/structure.py`'s `print_input_sentences`/`_print_sentence_group`/`recursive_print` path (the `1. (long formula)` interpreted-premise/conclusion line, 170 chars on the two `\Until`/`\Since` distribution examples) | This is framework-shared code used identically by every theory (logos, exclusion, imposition, bimodal), not bimodal-specific or named in the dispatch's concrete-defects list or cross-theory scope section. The line is composed token-by-token across a recursive call chain through each theory's own operator `print_method` implementations (not a single string this file builds and could `textwrap.fill`), so wrapping it is a materially larger, independent re-architecture of the shared recursive printer -- output would need to be captured to a buffer, measured, and re-flowed across every operator class -- not a narrow display fix, and carries real regression risk for all four theories' formula rendering, disproportionate to this display-polish task's scope ("Only `print_*` methods, formatting helpers, and their tests are in scope" read together with the dispatch's explicit four-file theory list). | `awk 'length($0)>80' /tmp/phase8_final.txt` on a full `./dev_cli.py .../bimodal/examples.py` run after every other phase landed shows exactly 2 lines over 80, both this exact 170-char shape (`1. (((A \Until B) ...` and `1. (((A \Since B) ...`), down from the recorded baseline of 35 (every bimodal-specific defect: 15 unwrapped `Verification:` lines, 6 over-80 history rows, 2 over-80 role-column cases, 12 over-80 no-certificate messages -- all independently fixed and verified in Phases 1-5 and this phase). `grep -n "def print_input_sentences\|def _print_sentence_group\|def recursive_print" code/src/model_checker/models/structure.py` confirms the method lives in the shared framework base class, not `theory_lib/bimodal/`. |

This exclusion satisfies all five admission conditions (`status-markers.md`): it is a deliberate
scope decision, not a stalled attempt; it names exactly one item (not "the rest of the phase");
the reason and evidence above are both stated; and no residual work remains for a future
dispatch -- the shared framework printer is a known, permanent, intentional scope boundary of
this display-focused task, not a deferred follow-up.

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7

**Verification Tier**: full

**Scope Hypothesis**: Four documentation targets are named above (module docstring,
ARCHITECTURE.md, SETTINGS.md, CODE_STANDARDS.md). Confirm completeness at implementation time
by grepping the repo for the old literal shapes — `Evaluation point:`, `witness for`,
`L{i}  {role}`, and the quoted arrow chain `(-2:B) ⟹` — and updating every hit outside
`specs/**` and outside generated notebook output.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — module docstring
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` — Rendering Policy
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` — `align_vertically` row
- `code/docs/core/CODE_STANDARDS.md` — Printed Output Conventions, new width bullet
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` —
  end-to-end width gate and `sys.__stdout__` audit assertion

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/ -v` and
  `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -v` both pass
- `./dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py | awk 'length>80' | wc -l`
  returns `0` (baseline: `35`)
- No grep hit for an old printed shape outside `specs/**`

---

## Testing & Validation

- [ ] Tests are written before implementation in every phase (RED -> GREEN -> REFACTOR), per
      `code/docs/core/TESTING_GUIDE.md`'s mandatory TDD requirement.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -v` passes (required by
      Phase 6's shared-base-class change).
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` passes.
- [ ] Max line width over a full `examples.py` run is `<= 80` in both default and `-a` views.
- [ ] cp1252 and ASCII fallback streams raise no encoding error for the new subscript path.
- [ ] Plain (non-TTY) output contains zero `\033[` sequences and remains fully informative.
- [ ] Fake-TTY output contains only SGR codes from the declared palette.
- [ ] `out.count("Verification:") == 1` and the `FORBIDDEN_OVERCLAIM` absence check survive
      unchanged in every scenario of `test_output_gate.py`.
- [ ] No test asserting certificate contents, box guesses, or truth values changes.

## Artifacts & Outputs

- Modified: `code/src/model_checker/theory_lib/bimodal/semantic/model.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py`
- Modified: `code/src/model_checker/theory_lib/logos/semantic/model.py`
- Modified: `code/src/model_checker/theory_lib/exclusion/semantic/model.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py`
- Modified: logos / exclusion / imposition printing test modules (exact paths located in Phase 6)
- Modified: `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
- Modified: `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md`
- Modified: `code/docs/core/CODE_STANDARDS.md`
- Summary artifact: `specs/222_improve_printed_model_display_and_colors/summaries/01_*-summary.md`

## Rollback/Contingency

Every phase is a self-contained, independently revertible print-shape change with its own
tests, and each is committed on green per the Commit-Per-Green-Substep Mandate — so the normal
contingency is reverting the single offending phase's commit, not the whole task.

If a phase must be abandoned mid-edit with uncommitted work in the tree, take a durable,
non-reverting checkpoint first with `bash .claude/scripts/git-snapshot.sh 222 --no-revert`,
then discard. A genuine whole-tree rollback (discarding uncommitted work) is the scenario
`context/contracts/recovery.md`'s rollback rung governs — use the invocation shape documented
there, including its out-of-scope override flag, rather than improvising a `git reset --hard`.

Phase-specific fallbacks:
- **Phase 2**: if dropping the formula list from the role column proves to lose information a
  reader genuinely needs, fall back to truncating the role to a fixed budget with an ellipsis
  (`witness for □A, …`) rather than reverting to unbounded width.
- **Phase 4**: if the subscripted arrow disturbs column alignment in a way the width math
  cannot absorb, revert just the arrow change — it is the most cosmetic of the five defects
  and the least load-bearing for the 80-column goal.
- **Phase 6**: if changing logos's base-class `print_evaluation` breaks a subclass not found
  by the Phase 6 grep, revert Phase 6 alone; bimodal's block (Phase 5) stands independently
  and the cross-theory consistency goal can be re-scoped as a follow-up task.
