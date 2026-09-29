# Implementation Plan: Task #218

- **Task**: 218 - Refactor bimodal/ theory countermodel presentation
- **Status**: [IMPLEMENTING] (revised round: Phases 1-7 closed in the prior round at commit 5d259d66; Phases 8-9 are new)
- **Effort**: 16 hours (12 completed in Phases 1-7; 4 remaining in Phases 8-9)
- **Dependencies**: None
- **Research Inputs**: specs/218_refactor_bimodal_countermodel_presentation/reports/01_bimodal-countermodel-presentation.md
- **Artifacts**: plans/01_bimodal-countermodel-presentation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false
- **Revised**: 2026-09-28 (reviser-agent, forced `--plan` round with user focus; session sess_1790656279_e5bb8c_218)

## Overview

Rewrite what `dev_cli.py` prints for a bimodal example so it is readable and honest: user-notation
formulas instead of dataclass reprs, a witness line computed from the certificate itself (the
original `Witness: L{i} at position {p}` line read a *reserved* registry index and was verifiably
wrong on `MD_CM_1`), a per-lasso role column, a bounds line replacing the meaningless
`Atomic States: 0`, one `Verification:` line instead of two, a glyph set with ASCII fallbacks, an
optional time-aligned table behind the existing-but-dead `-a/--align_vertically` flag, and
iteration diffs that match `docs/ITERATE.md`. Exactly one systemic (non-bimodal) change is made:
a shared `use_colors(output)` predicate honoring `isatty()`/`NO_COLOR`/`TERM=dumb`/`FORCE_COLOR`
replaces the framework-wide `output is sys.__stdout__` identity test. Phases 1-7 delivered all of
that (full suite `3416 passed, 5 skipped`; summary in
`summaries/01_bimodal-countermodel-presentation-summary.md`).

**This revision** (Phases 8-9) changes the DEFAULT history display, per the user's focus for this
round: the compact `(back)^ω | mid | (fwd)^ω` one-liner is dropped as the default in favour of a
time-labelled arrow chain in the old Logos style -- one row per lasso, every state carrying its
signed time as `(t:atoms)`, adjacent states joined by the `⟹` glyph (ASCII `=>` via
`utils/glyphs.py`), the three segments separated by `|`, `…` marking the periodic repetition of
the back/fwd segments, `[ ]` marking the evaluation point, and the per-position columns aligned
across rows:

```
Histories:  (one row per lasso: (t:atoms) states joined by ⟹, … marks the periodic back/fwd segments, | separates back | mid | fwd, [ ] marks the evaluation point)
  L0  main                … [-2:B] ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …
  L1  witness for \Box A  … (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …
  L2  reserved, unused    … (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …
  L3  witness for \Box B  … (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:A) …
```

The block is renamed `Histories:` (with the one-line legend above) on every path -- default, `-a`,
and the no-certificate case. The role column, the `Box guesses:` table with certificate-derived
witnesses, the `Search bounds:` line, and the `-a` time-aligned table (as the alternate view) are
all kept unchanged. Golden tests, the README sample output, and the docs are updated in the same
round. Semantics (`witness_constraints.py`, `formula.py`) are not touched. Every phase is TDD and
every new non-ASCII glyph ships with a real-encoded-stream regression test per
`TESTING_GUIDE.md` section 9. Definition of done for this round: the bimodal, utils, and builder
e2e suites pass with the new golden shape; `grep -rn "Certificate:"` over `code/` finds no printed
heading; a live `dev_cli.py ... | cat -v` run shows the arrow chains with zero `^[[` escapes; the
cp1252 subprocess leg is clean.

### Research Integration

The research report (`reports/01_bimodal-countermodel-presentation.md`) supplies: the twelve
concrete defects F1-F12 with sources; the evidence that F1 is a real bug (registry index is
capacity, not provenance -- `box_faithfulness_constraints` lets any lasso falsify a box); the
salvage inventory from the old Logos presentation (Finding 3: time-aligned horizontal rows
`W_0: (-1:a) ⟹₁ (0:a.b) ⟹₁ (+1:b)` with column widths computed so equal times align across
worlds -- `print_world_histories`, `_create_formatted_states`, `_calculate_column_widths`,
`_create_time_positions`, `_create_world_line`; signed times via `format_time`; BLUE/GRAY
palette; the `align_vertically` toggle); the infrastructure to reuse (`utils/glyphs.py` --
whose `DOUBLE_ARROW` entry `⟹`/`=>` already exists -- `syntax.all_sentences` + `formula.translate`
reverse map, `set_colors`, `ANSIToMarkdown`'s red/green-only contract, `_capture_model_output`'s
`StringIO` path); external CLI conventions (clig.dev, no-color.org); the target output mock in
Finding 7; and decisions D1-D8. Phases 1-7 adopted D1-D8 as written.

**This revision integrates no new report.** It is driven by the user's focus statement for the
forced `--plan` round, which resolves one judgment call the prior round made the other way: the
prior plan kept the `Certificate:` heading and the `(back)^ω | mid | (fwd)^ω` one-liner because
they preserved a pinned substring with zero test churn; the user now asks for the old Logos arrow
chain (report Finding 3, first row of the salvage table, whose verdict "the periodic segments
become bracketed groups instead of `⟹` chains" is hereby reversed) as the default and for the
`Histories` heading the Finding 7 mock already used. Finding 3's `⟹ₙ` duration-subscript verdict
stands: the shift between adjacent printed positions is always 1, so the arrow carries no
subscript. `reports_integrated`: `01_bimodal-countermodel-presentation.md` (integrated in plan
version 1; carried forward unchanged in this revision).

### Prior Plan Reference

The prior version of this file (same round number `01`, committed at `5d259d66` with all seven
phases `[COMPLETED]`) is superseded in place. Phases 1-7 below are preserved verbatim from it,
including their probe results and deviations; only the metadata block, this Overview, the
Goals/Risks/Dependency tables, the Testing & Validation list, and the Artifacts/Rollback sections
are revised, and Phases 8-9 are appended.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals** (Phases 1-7, delivered):
- Fix F1: the printed witness for a false box is a `(lasso, t)` pair that (C3) actually accepts,
  computed from `certificate.lassos` x `_box_window`, never from `WitnessRegistry._witness_lassos`.
- Fix F2/F10: no dataclass repr on any user-facing path (certificate printer, box-guess table,
  iteration diffs); formulas render in the user's own notation with a structural fallback.
- Fix F3/F4/F5/F6/F7: one `Verification:` line (12-hex checkout), a `Search bounds:` line in
  place of `Atomic States`, a role column per lasso, an explicit `Evaluation point: L0 at t=-2`
  line, a legend for the label notation.
- Fix F9 (systemic): a single shared color predicate used by the framework and every theory
  printer; plain text on pipes, files, `NO_COLOR`, and `TERM=dumb`.
- Make `-a/--align_vertically` live again for bimodal (D6) as the switch for a time-aligned table
  view salvaged from the old vertical renderer.
- Fix F11: extraction helpers name lassos `L0..` consistently with the screen.
- Update `README.md` "Sample Output", `docs/SETTINGS.md`, `docs/ITERATE.md`, and restore the
  rendering-policy subsection `utils/glyphs.py` cites in `docs/ARCHITECTURE.md`.

**Goals** (Phases 8-9, this revision):
- The DEFAULT history block is a time-labelled arrow chain: one row per lasso, `(t:atoms)` states
  (signed `t` via `render.signed_time`; atoms via the existing `_format_label` -- `A`, `{A,B}`,
  `∅`), joined by ` ⟹ ` within a segment, ` | ` between the back/mid/fwd segments, `… ` / ` …`
  bracketing the periodic back and fwd segments, `[t:atoms]` for the evaluation point, and each
  position's column padded to its widest cell across all lassos so times align across rows.
- The block heading is `Histories:` with a one-line legend, on the default, `-a`, and
  no-certificate paths alike; the string `Certificate:` no longer appears in any printed output.
- `⟹` and `…` are routed through `utils/glyphs.py` (`DOUBLE_ARROW` exists; `ELLIPSIS` is new)
  with real-encoded-stream tests; the `OMEGA` entry, unreferenced once the one-liner is gone, is
  retired.
- The role column, the `Box guesses:` table, the `Search bounds:` line, `Evaluation point:`, the
  single `Verification:` line, and the `-a` table are unchanged apart from the heading.
- Golden tests, `test_output_gate.py`, the builder e2e pipeline test, `README.md`, and
  `docs/{SETTINGS,ARCHITECTURE,USER_GUIDE}.md` are updated in the same round.

**Non-Goals**:
- The certificate search, (C1)-(C4), the checker protocol, or the JSON wire format semantics.
- Any edit to `semantic/witness_constraints.py` or `semantic/formula.py` (user focus: do NOT
  touch semantics).
- Adopting Rich or any new runtime dependency (D1).
- F8 (double `====` separator) and F12 (bare-`print()` WARNING in `set_colors`) -- framework
  cosmetics with no bimodal angle (D8).
- Changing the wording of the three documented verification states (D8/F2 contract); only the
  checkout hash is shortened.
- Flipping the `align_vertically` default to `True` (left `False`; the table stays the opt-in
  alternate view).
- Duration subscripts on the arrows (`⟹₁`): adjacent printed positions always differ by 1.
- Changing the `-a` table's body (rows, slot column, bracket marker, bold target row).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Golden-output tests (`TestGoldenOutputCertificateFormat`, `TestAlignedHistoryTable`, `TestPrintingDoesNotClaimValidity`, `test_output_gate.py`, `builder/tests/e2e/test_full_pipeline.py`) break by design | H | H | Rewrite the tests first in the same phase (TDD); keep the D8/F2 substrings verbatim: `"No certificate found"`, `"not a validity claim"`, `"independently checked"`, `"WitnessFamily.Refutes"`, `"re-checked by this repository's own pure-Python decision procedures only"`, `"no independent checker available"`, `"independent check skipped"`. `"Certificate:"` is deliberately dropped from this list in this revision (user focus renames the block); every pin of it is enumerated in Phase 8's Scope Hypothesis |
| New glyphs (`ω`, `□`, `◇`, `¬`, `∧`, `∨`, `→`, `⊥`, `⊤`, and now `⟹`, `…`) crash on a cp1252 pipe | H | M | Every glyph goes through `glyph()`; each gets a real-encoded-stream test per `TESTING_GUIDE.md` 9.2 (never `io.StringIO`). `…` (U+2026) IS a cp1252 code point (0x85), so -- exactly like `¬` in Phase 1 -- its `...` fallback is pinned on an `ascii` stream, while `⟹` (U+27F9) is not in cp1252 and its `=>` fallback is pinned on cp1252 |
| Cross-row alignment breaks when one lasso has a wider cell (`(-2:{A,B})` vs `(-2:B)` vs `(-2:∅)`) or when an ASCII fallback changes a cell's width | M | M | Column width per position = max rendered cell width over all lassos, computed from the *rendered* strings (as `_print_history_table` already does), then each cell left-justified to that width before the joiner; pinned by a test asserting every ` ⟹ ` / ` \| ` joiner sits at the same column index in every row |
| Alignment premise: every lasso must share `back`/`mid`/`fwd` lengths | M | L | `BimodalSemantics.extract_certificate` (`semantic/core.py`, the `LabelledLasso(back=..., mid=..., fwd=...)` construction) slices every lasso from the registry's `nb`/`nm`/`nf`, so the premise holds by construction; the renderer asserts `lasso.nb == registry.nb` etc. and raises a clear `ValueError` (fail-fast) rather than misaligning silently |
| The builder e2e test (`test_full_pipeline.py`, subprocess `dev_cli.py`) is slow and easy to skip | M | M | Phase 8 runs it explicitly by path; Phase 9's final gate runs the full suite |
| Color predicate changes other theories' captured output | M | L | `capsys`/`StringIO` are non-TTY, so tests see no colors today and none after; explicit tests exist for `StringIO`, `NO_COLOR`, `FORCE_COLOR`, `TERM=dumb` (Phase 3) |
| `model_checker.output` import from `models/structure.py` creates an import cycle | M | M | Resolved in Phase 3 (no cycle) |
| Reverse-lookup renderer sees two sentences with the same `translate` result (`A \vee B` vs `(\neg A \rightarrow B)`) | L | M | First-seen wins, built in `syntax.all_sentences` insertion order (deterministic); documented in the renderer docstring and pinned by a test (Phase 1) |
| Witness scan picks the main lasso when a reader expects "another history" | L | M | Prefer the first non-main `(lasso, t)` falsifier; fall back to the main lasso honestly; both branches tested (Phase 2) |
| `extract_states` rename `lasso0` -> `L0` breaks JSON collector consumers | M | L | Confirmed zero collector consumers in Phase 2 |
| Overlap with in-flight bimodal doc tasks on `docs/ARCHITECTURE.md` | L | L | Phase 9 edits one paragraph ("Label notation") only; re-read the file immediately before editing |
| Decision (revised): rename the block to `Histories:` on every path, per user focus | -- | -- | Supersedes the prior round's "keep `Certificate:`" decision; the no-certificate path prints `Histories:` followed by the unchanged D8 message, so `"No certificate found"` and `"not a validity claim"` survive verbatim |
| Decision: empty `mid` collapses to a single ` \| ` (`… (-1:A) \| (0:∅) …`), never `\| \|` | -- | -- | Keeps rows readable for `mid=0` examples; documented in the `_join_history` docstring and `README.md`, pinned by the single-slot golden test |
| Decision: the evaluation-point cell swaps its parentheses for brackets (`[+2:A]`), width-neutral | -- | -- | Matches the user's example literally and keeps alignment arithmetic trivial |
| Decision: retire the `OMEGA` glyph entry once unreferenced | -- | -- | No dead glyphs (clean-break principle); the `^ω` *mathematical* notation for a lasso stays in prose (`USER_GUIDE.md`) because it names the structure, not the printed form |
| Decision: role column from certificate scan only (`main` / `witness for □χ` / `reserved, unused`) | -- | -- | Never prints registry reservation as provenance (D2); unchanged from Phase 4 |
| Decision: `align_vertically` default stays `False` | -- | -- | The arrow chain is the default; the table is opt-in via `-a` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 6 | 1, 2, 3 (Phase 4); 1 (Phase 6) |
| 3 | 5 | 4 |
| 4 | 7 | 4, 5, 6 |
| 5 | 8 | 4, 5, 7 |
| 6 | 9 | 8 |

Phases within the same wave can execute in parallel. Waves 1-4 are closed. Phase 8 rewrites the
default-path printer that Phases 4 and 5 produced and re-pins the tests Phase 7's gate ran; Phase 9
regenerates the docs Phase 7 wrote from Phase 8's output, so the two new phases are strictly
sequential.

Reminder for every phase: deliverable files under `code/` and `docs/` MUST NOT cite task numbers
(`.claude/rules/no-task-references-in-deliverables.md`); cite filenames and section headings.

### Phase 1: Formula Renderer and Glyph Entries [COMPLETED]

**Goal**: A `render(formula, output, names=None) -> str` function that prints any closure
`Formula` in the user's notation (reverse `translate` lookup) or a structural fallback mirroring
`Formula.lean`'s derived-operator patterns, with every non-ASCII symbol routed through `glyph()`.

**Tasks**:
- [x] Write `code/src/model_checker/theory_lib/bimodal/tests/unit/test_render.py` first: (a)
  `names` built from a `Syntax` over `\Box (A \vee B)` renders `Box(Imp(Imp(A,Bot),B))` as
  `\Box (A \vee B)` and the inner `Imp(Imp(A,Bot),B)` as `(A \vee B)`; (b) structural fallback
  cases with no `names`: `Imp(x,Bot)` -> `¬x`, `Imp(Imp(a,Bot),b)` -> `(a ∨ b)`,
  `Imp(Imp(a,Imp(b,Bot)),Bot)` -> `(a ∧ b)`, `Imp(Bot,Bot)` -> `⊤`, `Box(x)` -> `□x`,
  `Imp(Box(Imp(x,Bot)),Bot)` -> `◇x`, `Untl(g,e)` -> `(g U e)`, `Snce(g,e)` -> `(g S e)`,
  `Imp(Untl(⊤,Imp(a,Bot)),Bot)` -> `\Future a` and the `Snce` mirror -> `\Past a`, generic
  `Imp(a,b)` -> `(a → b)`, `Bot()` -> `⊥`; (c) duplicate-translation tie-break: first-seen wins
  in `all_sentences` insertion order; (d) `repr` of every dataclass is unchanged.
- [x] Extend `code/src/model_checker/utils/tests/unit/test_glyphs.py` with `cp1252` and utf-8
  cases (existing `_FakeStream` pattern) for each new entry: `OMEGA` (`ω`/`w`), `BOX`
  (`□`/`[]`), `LOZENGE` (`◇`/`<>`), `NEG` (`¬`/`~`), `AND` (`∧`/`&`), `OR` (`∨`/`|`), `IMP`
  (`→`/`->`; reuse `ARROW` if identical), `BOT` (`⊥`/`_|_`), `TOP` (`⊤`/`T`).
- [x] Add the entries to `_GLYPHS` in `code/src/model_checker/utils/glyphs.py`.
- [x] Create `code/src/model_checker/theory_lib/bimodal/semantic/render.py` with `render(...)`
  and `build_names(syntax) -> Dict[Formula, str]` (`{translate(s): s.name for s in
  syntax.all_sentences.values()}`, first-seen wins); export from `semantic/__init__.py` if that
  module re-exports siblings (confirm by reading it). *Deviation (altered)*: `semantic/__init__.py`
  re-exports only the three theory classes, never sibling helper modules (`certificate`,
  `formula` are imported by module path), so `render` follows the same convention and is not
  re-exported. `IMP` reuses the existing `ARROW` entry (identical `→`/`->`); `¬` is a cp1252
  code point, so its `~` fallback is pinned on an `ascii` stream instead.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_render.py code/src/model_checker/utils/tests -q`.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Nine new glyph entries and eleven fallback patterns are needed; confirm
against `Formula.lean`'s "Naming Convention" section
(`~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean`) and `formula.py`'s
`_translate_uncached` before finalizing the pattern list -- any operator `translate` produces
that the fallback does not cover must be added.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/render.py` - new: `render`, `build_names`
- `code/src/model_checker/theory_lib/bimodal/semantic/__init__.py` - re-export if siblings are re-exported
- `code/src/model_checker/utils/glyphs.py` - new `_GLYPHS` entries
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_render.py` - new
- `code/src/model_checker/utils/tests/unit/test_glyphs.py` - cp1252/utf-8 cases for new glyphs

**Verification**:
- All new tests pass; `repr(Box(Atom('A')))` is byte-identical to before (Z3 variable names in
  `witness_registry.py` depend on it).
- No file outside the list above changed (`git status --short`).

---

### Phase 2: Certificate-Derived Witness and Extraction Consistency [COMPLETED]

**Goal**: Replace the registry-index witness lookup with a scan of the certificate that returns a
`(lasso_index, t)` pair (C3) accepts, expose it to the JSON collectors, and name lassos `L0..`
in every extraction helper.

**Tasks**:
- [x] Write tests first in `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`
  (new class `TestBoxWitnessFromCertificate`): build `MD_CM_1`'s shape via
  `tests/_build_support._build(["\\Box (A \\vee B)"], ["\\Box A", "\\Box B"], back=2, mid=1,
  fwd=2, verify="off")`; for every false box `chi`, assert `structure.box_witness(chi)` returns
  `(i, t)` with `chi not in structure.certificate.lassos[i].label(t)` and `t in
  _box_window(lassos[i])`; assert a non-main lasso is preferred when one exists (construct or
  find a case, else assert the main-lasso fallback on a hand-built `LabelledLasso`); assert
  `box_witness` returns `None` for a true box.
- [x] Update `TestExtractionHelpers` and `tests/integration/test_data_extraction.py` to expect
  `L0`-style names from `extract_states`/`extract_evaluation_world`, and a new
  `extract_relations()["box_guesses"]` list of `{formula: <repr>, guess: bool, witness:
  {lasso: int, position: int} | None}` entries (repr is acceptable in JSON; screen rendering is
  Phase 4's job).
- [x] In `semantic/model.py`: add `box_witness(self, child) -> Optional[Tuple[int, int]]`
  (iterate `enumerate(certificate.lassos)` x `_box_window(lasso)`, skip index 0 on the first
  pass, fall back to index 0); add `box_guesses(self) -> List[Tuple[Formula, bool,
  Optional[Tuple[int,int]]]]` sorted by `repr` for determinism; delete
  `_first_missing_position`; extend `extract_relations`; rename `lasso{i}` -> `L{i}` in
  `extract_states`/`extract_evaluation_world`.
- [x] `grep -rn "lasso0\|lasso{" code/src/model_checker/output` to confirm no collector hardcodes
  the old name. *Probe result*: zero hits in `output/` and `builder/`; the only `lasso{i}`
  consumers were the two bimodal test files named above (both updated).
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q`.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: Only `test_structure.py` and `test_data_extraction.py` assert the
`lasso{i}` naming; confirm with `grep -rn "lasso0" code/src code/tests` before renaming.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - `box_witness`, `box_guesses`, extraction helpers; remove `_first_missing_position`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - new witness tests, extraction expectations
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py` - `L0` naming, `box_guesses` shape

**Verification**:
- Witness tests pass on `MD_CM_1` (`Box(A)` witness lies on a lasso/position whose label omits
  `A`; `Box(B)` witness is on `L0`, reported honestly).
- `print_certificate` still runs (it temporarily reads `box_witness` instead of the registry;
  its full rewrite is Phase 4) and the existing `Witness: L` assertion is adjusted, not deleted.

---

### Phase 3: Shared Color Predicate (Systemic) [COMPLETED]

**Goal**: One `use_colors(output) -> bool` predicate (`NO_COLOR` > `FORCE_COLOR` > `TERM=dumb` >
`isatty()`) replaces every `output is sys.__stdout__` color test in the framework and in the
logos/exclusion/imposition printers; bimodal adopts it in Phase 4.

**Tasks**:
- [x] Write `code/src/model_checker/output/tests/unit/test_color.py` first (create the `tests/`
  tree if `output/` has none -- check `ls code/src/model_checker/output`): `StringIO` -> False;
  a fake stream with `isatty() -> True` -> True; same with `monkeypatch.setenv("NO_COLOR",
  "1")` -> False; `TERM=dumb` -> False; `StringIO` with `FORCE_COLOR=1` -> True; a stream
  without `isatty` -> False; `NO_COLOR` set AND `FORCE_COLOR` set -> False (no-color.org
  precedence).
- [x] Add a framework test (`code/src/model_checker/models/tests/` or the existing structure test
  location -- locate with `ls code/src/model_checker/models/tests`) asserting
  `_print_sentence_group` into a `StringIO` emits no `\033[` and into an `isatty()` fake does.
- [x] Create `code/src/model_checker/output/color.py` with `use_colors(output) -> bool` and
  re-export from `output/__init__.py`; verify `python -c "import model_checker.models.structure"`
  still imports (fallback: `utils/colors.py`, see Risks).
- [x] Replace `output is sys.__stdout__` color gates: `models/structure.py::_print_sentence_group`;
  `theory_lib/logos/semantic/model.py` (`print_evaluation`, `print_states`);
  `theory_lib/exclusion/semantic/model.py` (`print_states`, `print_negation`,
  `print_witness_functions`, `print_evaluation`); `theory_lib/imposition/semantic/model.py`
  (`print_imposition`). Leave the `if output is sys.__stdout__: ... Total Run Time` gates in each
  `print_all` untouched -- they gate timing output, not color.
- [x] Add a test that `builder/module.py::_capture_model_output`'s `StringIO` capture still
  contains no escapes (so `ANSIToMarkdown` input is unchanged); do not add a special echo-path
  override -- the echo was never colored, and `FORCE_COLOR` now covers anyone who wants it.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests
  code/src/model_checker/theory_lib/exclusion/tests code/src/model_checker/theory_lib/imposition/tests
  code/src/model_checker/models code/src/model_checker/output -q` and the live check
  `cd code && ./dev_cli.py src/model_checker/theory_lib/logos/examples.py | cat -v | grep -c '\^\['`
  (expect `0`).

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: Eight color-gate sites across four files (per
`grep -rn "output is sys.__stdout__" code/src/model_checker --include=*.py`); re-run that grep
after editing and confirm the only survivors are the `Total Run Time` gates in `print_all`.
*Probe result (hypothesis incomplete)*: the eight `output is sys.__stdout__` sites were replaced
and the four `Total Run Time` gates are the only survivors, but the live pipe check still showed
escapes from three sites the grep pattern never matched, all gated in this phase as the same
systemic change (*deviation: extended*): `logos/semantic/model.py::print_model_differences`
(`output is sys.stdout`, a variant spelling), `imposition/iterate.py::display_model_differences`
(26 unconditional `\033[` literals, replaced by named constants gated once), and
`imposition/semantic/model.py::print_model_differences` (42 unconditional `self.COLORS`/
`self.RESET` uses -- the printer the runner actually calls). `builder/runner.py`'s `--maximize`
GREEN/RED output was gated on `sys.stdout` for the same reason. The `_capture_model_output`
test lives in `builder/tests/unit/test_module_output_capture.py`; the framework test in
`models/tests/unit/test_structure_print.py::TestSentenceGroupColorGate`. `IM_CM_0` (the only
imposition example with `iterate: 2`) is commented out of `example_range`, so the iterate diff
path was verified with a scratch example instead.

**Files to modify**:
- `code/src/model_checker/output/color.py` - new `use_colors`
- `code/src/model_checker/output/__init__.py` - re-export
- `code/src/model_checker/models/structure.py` - `_print_sentence_group`
- `code/src/model_checker/theory_lib/logos/semantic/model.py` - two sites
- `code/src/model_checker/theory_lib/exclusion/semantic/model.py` - five sites
- `code/src/model_checker/theory_lib/imposition/semantic/model.py` - one site
- `code/src/model_checker/output/tests/unit/test_color.py` - new
- framework/`builder` test file for the `StringIO` capture assertion (locate at implementation time)

**Verification**:
- Predicate tests pass; other theories' suites unchanged (green before and after).
- Live pipe check shows zero escapes for logos; `NO_COLOR=1 ./dev_cli.py ...` on a TTY shows none.

---

### Phase 4: Bimodal Printer Rewrite [COMPLETED]

**Goal**: `print_info` header, certificate block, box-guess table, evaluation point, verification
line, and interpreted-sentence wording match the report's Finding 7 mock (with the `Certificate:`
heading retained), using Phase 1's renderer, Phase 2's witness, and Phase 3's predicate.

**Tasks**:
- [x] Rewrite the pinned tests first: `test_structure.py` `TestGoldenOutputCertificateFormat`,
  `TestVerificationLabelRendering`, `TestPrintingDoesNotClaimValidity`, and
  `tests/integration/test_output_gate.py`. New golden expectations (utf-8 `capsys` stream):
  header contains `Search bounds: back=2, mid=1, fwd=2 (4 lassos: 1 main + 3 reserved
  witnesses)` and NOT `Atomic States`; a `Certificate:` line carrying the legend
  `each lasso is (back)^ω | mid | (fwd)^ω over atoms; [ ] marks the evaluation point`; rows
  `L0  main  ([B], B)^ω | B | (B, B)^ω` style with role column values `main` /
  `witness for □A` / `reserved, unused`; a `Box guesses:` table with `□A  false  falsified at
  L3, t=+2` and `□(A ∨ B)  true`; `Evaluation point: L0 at t=-2`; exactly one `Verification:`
  line (assert `out.count("Verification:") == 1`) with the checkout shortened to 12 hex chars;
  the three D8/F2 states' substrings verbatim; empty labels as `∅`; no `Atom(` / `Imp(` / `Box(`
  substrings anywhere in `out`.
- [x] Add a `cp1252` end-to-end test for `print_certificate` per `TESTING_GUIDE.md` 9.2
  (expect `^w`, `[]`, `{}`, `|` fallbacks and no `UnicodeEncodeError`).
- [x] Keep `test_print_evaluation_reports_no_certificate_case` (standalone call still prints) but
  make `print_all` skip `print_evaluation` when `certificate is None` so the no-certificate
  message prints once; add an assertion `out.count("No certificate found") == 1` on the
  `print_all` path.
- [x] `proposition.py::print_proposition`: `(True at L0, t=-2)` wording; update
  `tests/unit/test_proposition.py` if it pins the old text (grep `in lasso`).
- [x] Implement in `semantic/model.py`: `_print_model_details` override (bounds + lasso count);
  `_format_label` -> atoms joined by `, ` with `∅` glyph for empty, `[ ]` marker preserved;
  `_format_lasso` with `^ω` glyph; `_lasso_roles()` from `box_guesses()`; `print_certificate`
  (legend line, aligned role column, `Box guesses:` table via `render`); `print_evaluation`
  (`Evaluation point:` + single `Verification:`); `_verification_label` shortens the checkout to
  `[:12]`; colors (BLUE evaluation-point row, GRAY reserved rows, GREEN/RED guess values)
  gated by `use_colors(output)` and never carrying information alone.
- [x] Update the `semantic/model.py` module docstring's output-shape description.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q` and a
  live `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | cat -v |
  grep -c '\^\['` (expect `0`).

**Timing**: 2 hours

**Depends on**: 1, 2, 3

**Verification Tier**: full

**Scope Hypothesis**: Four test classes plus `test_output_gate.py` and possibly
`test_proposition.py` pin the current text; confirm with
`grep -rln "Witness: L\|in lasso\|Atomic States\|Box(Atom" code/src/model_checker/theory_lib/bimodal/tests`
before rewriting, and treat any additional hit as in scope for this phase.
*Probe result*: exactly those files pinned the text (`test_structure.py`, `test_output_gate.py`,
`test_proposition.py`); all rewritten. *Deviations*: (altered) the box-guess table and role
column render in the user's own notation (`\Box A`, `witness for \Box A`) because every boxed
closure member is a named sentence or derived subsentence (`\Diamond A` records
`\Box \neg A`), so the mock's `□A` fallback form surfaces only in iteration diffs -- the
golden tests pin the user-notation form; (altered) multi-atom labels keep braces (`{A,B}`) so
the `, ` slot separator stays unambiguous, single atoms print bare; (extended) `print_all` now
prints the certificate block on the no-certificate path too (D8 message once, then the closing
separator) instead of returning after the header; the no-certificate header's lasso count reads
`semantics._active_lassos` (package-internal). The cp1252 end-to-end leg pins `^w` and `{}`
(the glyphs a real example reaches); `[]` is covered by `test_render.py`'s cp1252 leg.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - printer rewrite, `_print_model_details` override
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` - `(True at L0, t=-2)`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - golden rewrite, cp1252 leg
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` - single-line verification expectations
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` - if it pins the old wording

**Verification**:
- Bimodal suite green; `test_output_gate.py`'s `FORBIDDEN_OVERCLAIM` assertions still hold.
- Live run of `MD_CM_1` shows `□A  false  falsified at L3, t=+2`-shaped lines whose `(lasso, t)`
  satisfies the (C3) predicate, and `Verification:` appears once per example.

---

### Phase 5: Time-Aligned Table View Behind `align_vertically` [COMPLETED]

**Goal**: `-a/--align_vertically` (already parsed by `__main__.py` and present in
`DEFAULT_GENERAL_SETTINGS`) becomes live for bimodal and selects a per-position table salvaged
from the old vertical renderer; default `False` keeps Phase 4's one-line rows.

**Tasks**:
- [x] Tests first (`test_structure.py`, new `TestAlignedHistoryTable`): with
  `align_vertically=True` the certificate block prints a header row `t   slot | L0 main | L1 |
  ...`, one row per representative position `-2 .. +2` with signed times and slot annotations
  (`back[0]`, `mid[0]`, `fwd[1]`), the target row marked with `[ ]` (and bold only when
  `use_colors`); with the default the one-line rows print; `SettingsManager` no longer warns
  `Flag 'align_vertically' doesn't correspond to any known setting` for bimodal (capture the
  warning path or assert the key survives in `structure.settings`).
- [x] `semantic/core.py`: `ADDITIONAL_GENERAL_SETTINGS = {"align_vertically": False}`; update
  the comment there and the stale one in `examples.py` `general_settings`.
- [x] `semantic/model.py`: `_print_history_table(output)`; `print_certificate` dispatches on
  `self.settings.get("align_vertically", False)`; column widths computed from rendered labels;
  `DOWN_ARROW`/`to_subscript` reuse where the old renderer used them.
- [x] `docs/SETTINGS.md` "General Settings": replace the "defines no bimodal-specific general
  setting" paragraph with the `align_vertically` description and a short table example.
- [x] Run the bimodal suite and `cd code && ./dev_cli.py -a src/model_checker/theory_lib/bimodal/examples.py | head -60`.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: Only `core.py`, `examples.py`, `model.py`, `SETTINGS.md`, and
`test_structure.py` change; confirm `grep -rn align_vertically code/src --include=*.py` shows no
other bimodal consumer to update.
*Probe result*: confirmed -- the only non-settings/CLI consumers are the three bimodal files
named. Live `dev_cli.py -a` run: the 25 `Flag 'align_vertically' doesn't correspond to any
known setting` warnings printed before this phase are gone (0), table renders for every
countermodel, 0 escapes on a pipe; default run prints no table. Bold on the target row is
the only color the table adds, gated by `use_colors`.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - `ADDITIONAL_GENERAL_SETTINGS`
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - `_print_history_table`, dispatch
- `code/src/model_checker/theory_lib/bimodal/examples.py` - stale comment
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` - General Settings section
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - table tests

**Verification**:
- `-a` produces the table, default produces one-line rows; no settings warning for bimodal;
  cp1252 leg of the table (uses only glyphs already covered) does not raise.

---

### Phase 6: Iteration Diffs in User Notation [COMPLETED]

**Goal**: `iterate.py`'s `_calculate_differences`/`display_model_differences` produce the
`L0, position -1: + □A` / `- A` shape `docs/ITERATE.md` documents, rendering formulas via
Phase 1's `render` instead of `repr`.

**Tasks**:
- [x] Tests first in `tests/integration/test_iterate.py` (extend
  `test_display_model_differences_does_not_raise` into a golden test): build two structures
  whose certificates differ in one label bit and one box guess (hand-built `LabelledLasso`
  certificates are acceptable), set `model_differences`, and assert the printed lines are
  `  L0, position -1: + □A`-shaped, `Box Guess Changes:` lines read `□A: False -> True`, and no
  `Atom(`/`Imp(` substring appears.
- [x] `_calculate_differences`: store `added`/`removed` formula sets per position (not sorted
  repr lists); keep `box_guesses` keyed by the `Formula` object.
- [x] `display_model_differences`: render with `render(formula, output, names)` where `names`
  comes from `model_structure.syntax` (fallback structural); `+`/`-` prefixes; colors (GREEN
  `+`, RED `-`) via `use_colors(output)`.
- [x] Reconcile `docs/ITERATE.md`'s sample block with the actual output (regenerate from the
  test's captured text) and update `docs/API_REFERENCE.md`'s one-line description if the
  signature changes.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q`
  and `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py` with an example
  setting `iterate` >= 2 (scratch file under the scratchpad directory).

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: `iterate.py`, `test_iterate.py`, `ITERATE.md`, and possibly
`API_REFERENCE.md` are the only files; confirm `grep -rn "model_differences" code/src/model_checker/theory_lib/bimodal`
lists no other reader of the diff dict's shape.
*Probe result (hypothesis incomplete)*: no other reader of the dict, but the live
`dev_cli.py` run with `iterate: 3` never reached `display_model_differences` at all --
`builder/runner.py` calls `structure.print_model_differences()`, which `BimodalStructure` did
not override, so the framework's generic "Structural Properties" block printed instead.
*Deviation (extended)*: the display logic lives in `semantic/render.py::print_differences`,
shared by `BimodalModelIterator.display_model_differences` and a new
`BimodalStructure.print_model_differences` override (`semantic/model.py`); `iterate_example`'s
per-structure monkeypatch wrapper was removed as redundant. `API_REFERENCE.md` documents the new
method (signatures otherwise unchanged).

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - `_calculate_differences`, `display_model_differences`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - golden diff test
- `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` - sample block regenerated
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` - only if the signature changes

**Verification**:
- Golden diff test passes; live iterate run prints user-notation diffs with no reprs.

---

### Phase 7: Docs, Naming Consistency, and Final Gate [COMPLETED]

**Goal**: User-facing docs match the new output, the rendering-policy subsection `utils/glyphs.py`
cites exists, and the whole test suite plus a live pipe check pass.

**Tasks**:
- [x] `theory_lib/bimodal/README.md` "Sample Output" (and the `(back)^w | mid | (fwd)^w` mention
  near the Basic Usage section): regenerate from a real `dev_cli.py` run of `BM_CM_1` (utf-8
  capture), including the `Search bounds` header line and `Box guesses` table.
- [x] `theory_lib/bimodal/docs/ARCHITECTURE.md`: add a "Rendering policy" subsection (glyph
  fallback via `utils/glyphs.py`, color gating via `output.color.use_colors`, label notation,
  witness-from-certificate rule); update `utils/glyphs.py`'s module docstring pointer to name the
  subsection heading exactly.
- [x] `code/docs/core/CODE_STANDARDS.md`: add a short "Printed Output Conventions" section (color
  predicate, palette meanings GREEN/RED top-level truth, WHITE/YELLOW nested, BLUE evaluation
  point, GRAY reserved; `ANSIToMarkdown` red/green-only contract; glyph rule with a pointer to
  `TESTING_GUIDE.md` section 9).
- [x] `theory_lib/bimodal/docs/USER_GUIDE.md`: grep for `Witness:` / `Atomic States` / `lasso 0`
  and update any sample text. *Probe result*: no hit in `USER_GUIDE.md` (its "Evaluation Points"
  section carries no printed-output sample), so no edit was needed; the only stale samples were
  `README.md`'s "Sample Output" and its settings sentence, both regenerated from a live run.
- [x] Final gate: `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q`;
  `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | cat -v | grep -c '\^\['`
  (expect `0`); `PYTHONIOENCODING=cp1252 python code/dev_cli.py <scratch example file>` per
  `TESTING_GUIDE.md` 9.3 (expect no `UnicodeEncodeError`); `ruff check code/src/model_checker/theory_lib/bimodal code/src/model_checker/output/color.py`.
- [x] Run `bash .claude/scripts/check-task-references.sh` (or the repo-wide lint it wraps) over
  the touched `code/` and `docs/` files to confirm no task-number citations. *Probe result*: the
  script's `PATH_SCOPE` accepts only `agent-system/extensions`, `.opencode`, `lua`, `.memory`
  (exit 2 on `code`), so the equivalent grep (`\btasks? [0-9]+\b|\(task [0-9]+\)`) was run over
  every touched `code/` file: zero hits.

**Timing**: 1.5 hours

**Depends on**: 4, 5, 6

**Verification Tier**: prose

**Scope Hypothesis**: Four doc files plus one docstring; confirm with
`grep -rln "Witness: L\|Atomic States\|lasso 0\|(back)^w" code/src/model_checker/theory_lib/bimodal/README.md code/src/model_checker/theory_lib/bimodal/docs docs`
and add any further hit to this phase.
*Probe result*: hits were `README.md` (sample + settings sentence) and one `(back)^w` line in
`USER_GUIDE.md` (updated to `^ω`); `docs/` hits are other theories' `Atomic States` samples,
out of scope. Final gate: full suite `3416 passed, 5 skipped` (511s); bimodal pipe check 0
escapes; `PYTHONIOENCODING=cp1252` legs (default, `-a`, iterate, full examples file) clean;
ruff findings in the bimodal tree are all in files unchanged since the task's base commit.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/README.md` - Sample Output regenerated
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - Rendering policy subsection
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` - sample text if stale
- `code/docs/core/CODE_STANDARDS.md` - Printed Output Conventions
- `code/src/model_checker/utils/glyphs.py` - docstring pointer only

**Verification**:
- Full suite green; live pipe check zero escapes; cp1252 subprocess leg clean; task-reference
  lint clean on deliverable files.


---

### Phase 8: Time-Labelled Arrow-Chain Histories as the Default [COMPLETED]

**Goal**: The default certificate block prints as `Histories:` with a one-line legend and one
aligned arrow-chain row per lasso -- `… [-2:B] ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …` -- with
`⟹`/`…` routed through `utils/glyphs.py`, the `Histories:` heading on every path (default, `-a`,
no-certificate), and every test that pinned the old `Certificate:` heading or the
`(back)^ω | mid | (fwd)^ω` one-liner rewritten first.

**Tasks**:
- [x] Glyph tests first: extend `code/src/model_checker/utils/tests/unit/test_glyphs.py` with an
  `ELLIPSIS` entry (`…`/`...`) using the existing `_FakeStream` pattern -- utf-8 -> `…`;
  cp1252 -> `…` (U+2026 is cp1252 0x85, so it must NOT fall back there; pin this explicitly so a
  future "fix" cannot silently ASCII-ify it); `ascii` -> `...` (the same `ascii`-stream recipe
  Phase 1 used for `¬`). Confirm `DOUBLE_ARROW`'s existing cp1252 (`=>`) and utf-8 (`⟹`) cases
  still cover the arrow (they do at `test_glyphs.py` lines 46-60 and 109-118 today). Remove the
  `("OMEGA", "ω", "w")` row from the parametrized table.
- [x] Add `"ELLIPSIS": ("…", "...")` to `_GLYPHS` in `code/src/model_checker/utils/glyphs.py`;
  delete the `OMEGA` entry and its `(back)^ω | mid | (fwd)^ω` comment; update the `glyph()`
  docstring's name list and the formula-renderer block comment (which currently says "plus the
  `^ω` period marker on every printed lasso").
- [x] Rewrite the pinned bimodal tests first, in
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`:
  - `TestPrintingDoesNotClaimValidity`: `"Certificate:" in out` -> `"Histories:" in out`; add
    `assert "Certificate:" not in out` on the `print_all` no-certificate path (the D8 message
    text `No certificate found within the configured bounds ... This is not a validity claim`
    stays verbatim and is still asserted).
  - Rename `TestGoldenOutputCertificateFormat` -> `TestGoldenOutputHistoriesFormat` and update
    its docstring. Single-slot test (`back=1, mid=0, fwd=1`): the `L0` row is one of
    `L0  main  … [-1:A] | (0:∅) …` / `L0  main  … (-1:∅) | [0:A] …` (empty `mid` collapses to
    one `|`). Legend test: exactly one line starts with `Histories:` and it contains
    `(t:atoms) states joined by ⟹, … marks the periodic back/fwd segments, | separates back | mid | fwd, [ ] marks the evaluation point`.
    Full `MD_CM_1` test: rows `L0..L3` each match
    `^\s+L\d\s+.+?\s{2,}… \S+ ⟹ \S+ \| \S+ \| \S+ ⟹ \S+ …$` (with cells of the form
    `\(-2:[^)]+\)` / `\[-2:[^\]]+\]`, i.e. `(t:atoms)` with the signed time); each row contains
    exactly two ` | ` separators (mid=1) and exactly two ` ⟹ ` joiners (back=2, fwd=2); exactly
    one row contains `[` and it is `L0`; `"^ω" not in out`; `out.count("Histories:") == 1`;
    `"Certificate:" not in out`; the role, `Box guesses:`, `Evaluation point:`,
    `Verification:`-count, `(True at L0, t=...)`, no-repr, and no-escape assertions are kept
    as they are.
  - New alignment test: build an example whose lassos have cells of different widths at the same
    position (e.g. `_build(["A", "B"], ["\\Box (A \\wedge B)"], back=1, mid=1, fwd=1)`, whose
    main lasso carries `{A,B}` where a witness lasso carries a single atom or `∅`; if the solver
    does not produce differing widths, assign a hand-built `WitnessFamily` of `LabelledLasso`s
    to `structure.certificate` as `test_iterate.py` already does) and assert that the list of
    column indices of every ` ⟹ ` and ` | ` joiner is identical across all `L{i}` rows.
  - `test_empty_labels_render_as_the_empty_set_glyph`: unchanged (`∅` appears inside `(t:∅)`).
  - `test_cp1252_stream_gets_ascii_fallbacks_without_raising`: expect `=>` and `{}` in the
    cp1252 rendering and neither `⟹` nor `∅`; the `…` glyph is expected to SURVIVE on cp1252
    (assert `"…" in rendered`); add an `ascii`-stream leg (via
    `make_encoding_test_streams`/an `ascii`-encoded `io.TextIOWrapper` per `TESTING_GUIDE.md`
    9.2) asserting `...` and `=>` and no `UnicodeEncodeError`; the utf-8 control asserts `⟹`
    and `…`.
  - `TestAlignedHistoryTable`: `lines[0].startswith("Histories:")`; replace `"^ω" not in out`
    with `"⟹" not in out` (no arrow-chain rows in table mode); `test_default_keeps_one_line_rows`
    additionally asserts `"⟹" in out` and `"…" in out`.
- [x] Update the two integration/e2e pins first, too:
  `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` line 64
  (`"Certificate:"` -> `"Histories:"`) and
  `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` line 97 (`assertIn(
  "Histories:", ...)`), rewriting that test's docstring paragraph and inline comment that name
  the `"Certificate:"` label (cite `theory_lib/bimodal/semantic/model.py`'s `print_certificate`
  and this heading; keep the "audited retention on bimodal" rationale intact).
- [x] Implement in `code/src/model_checker/theory_lib/bimodal/semantic/model.py`:
  - `_format_state(t, label, output, marked) -> str`: `({signed_time(t)}:{_format_label(label)})`,
    or `[...]` when `marked`.
  - `_history_cells(index, lasso, output) -> List[str]`: one cell per position of
    `self.semantics.witness_registry.target_window()`; `marked` iff `index ==
    self.main_point["lasso"]` and `t == self.target_time`. Fail fast with `ValueError` if
    `(lasso.nb, lasso.nm, lasso.nf) != (registry.nb, registry.nm, registry.nf)`.
  - `_join_history(cells, widths, output) -> str`: pad each cell to `widths[i]`
    (left-justified); join within the back segment and within the fwd segment by
    ` {DOUBLE_ARROW} `, between segments by ` | ` (an empty `mid` yields exactly one ` | `
    between back and fwd); prefix `{ELLIPSIS} ` and suffix ` {ELLIPSIS}`; `rstrip()` nothing
    inside (padding is internal), but strip trailing padding on the last fwd cell before the
    suffix so rows do not end in stray spaces.
  - `_print_history_lines(output)`: compute `widths[i] = max(len(cells[i]) for every lasso)`
    over the rendered cells (ASCII fallbacks included), then print `  {L{i}:<name_width}
    {role:<role_width}  {joined}` with the existing BLUE main-row / GRAY reserved-row color
    gating via `use_colors` unchanged. Delete `_format_lasso`.
  - `print_certificate`: heading `Histories:` on all three branches. Default legend (one line,
    glyphs via `glyph()`):
    `Histories:  (one row per lasso: (t:atoms) states joined by ⟹, … marks the periodic back/fwd segments, | separates back | mid | fwd, [ ] marks the evaluation point)`;
    `-a` legend: `Histories:  (rows are representative positions; back repeats leftward, fwd rightward; [ ] marks the evaluation point)`;
    no-certificate branch: `Histories:` then the unchanged D8 message. Keep the method name
    `print_certificate` (the framework calls it by that name; it prints the certificate's
    histories).
  - Update the module docstring's "Printed output" paragraph (lines describing `(back)^ω | mid |
    (fwd)^ω` and the `Certificate:` block) to the new shape.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests
  code/src/model_checker/utils/tests code/src/model_checker/builder/tests/e2e/test_full_pipeline.py -q`
  and the live check `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py |
  cat -v | grep -c '\^\['` (expect `0`), then eyeball `MD_CM_1` and `BM_CM_1` in the same run for
  the aligned arrow chains.

**Timing**: 2.5 hours

**Depends on**: 4, 5, 7

**Verification Tier**: full

**Scope Hypothesis**: Exactly six test sites pin the old heading or one-liner --
`test_structure.py` lines 189, 392, 439, 512 (plus the `^ω` assertions at 420, 494, 530 and the
one-liner shapes at 384-385), `test_output_gate.py` line 64, and
`builder/tests/e2e/test_full_pipeline.py` line 97 -- and `OMEGA` is referenced only at
`semantic/model.py` lines 412 and 589, `utils/glyphs.py` lines 59 and 131, and
`test_glyphs.py` line 163. Confirm with
`grep -rn "Certificate:\|\^ω\|(back)\^\|OMEGA" code/src code/tests --include=*.py` before
editing and treat any additional hit as in scope for this phase; if `OMEGA` turns out to have a
consumer outside that list, keep the entry and record the exclusion.

**Files to modify**:
- `code/src/model_checker/utils/glyphs.py` - `ELLIPSIS` entry; `OMEGA` removed; docstring/comment updates
- `code/src/model_checker/utils/tests/unit/test_glyphs.py` - `ELLIPSIS` cases; `OMEGA` row removed
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - `_format_state`, `_history_cells`, `_join_history`, `_print_history_lines`, `print_certificate` headings/legends, module docstring; `_format_lasso` removed
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - golden rewrite, alignment test, encoding legs, `-a` heading pin
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` - heading pin
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - heading pin and docstring

**Verification**:
- Bimodal, utils, and builder e2e suites green; `grep -rn "Certificate:" code/src code/tests
  --include=*.py` returns only class names (`TestCheckCertificate`, `class Certificate:` in the
  test model, `...WithCertificate`), never a printed heading.
- Live `MD_CM_1` rows show `… [-2:B] ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …`-shaped chains whose
  ` ⟹ ` / ` | ` joiners sit at identical columns in all four rows; the `Box guesses:` witness
  `(lasso, t)` still satisfies the (C3) predicate; `Verification:` appears once per example.
- `semantic/witness_constraints.py` and `semantic/formula.py` are untouched (`git status --short`).

---

### Phase 9: Docs, README Sample, and Final Gate [NOT STARTED]

**Goal**: Every user-facing description of the printed history block matches the arrow-chain
default and the `Histories:` heading, the code comments that describe the one-liner are updated,
and the whole test suite plus the live pipe and cp1252 checks pass.

**Tasks**:
- [ ] `code/src/model_checker/theory_lib/bimodal/README.md`: regenerate the "Sample Output"
  countermodel block (`BM_CM_1`) and the no-certificate block (`BM_TH_1`) from a real utf-8
  `dev_cli.py` capture; rewrite the explanatory paragraph under the sample (currently "Each
  certificate row is `(back)^ω | mid | (fwd)^ω` over the label's atoms ...") to describe
  `(t:atoms)` states, the `⟹` chain, `…` for the periodic segments, `|` between back/mid/fwd,
  the empty-`mid` collapse, and `[ ]` on the main lasso; update the settings sentence near
  "Basic Usage" ("by default every history prints as a single `(back)^ω | mid | (fwd)^ω` line").
- [ ] `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` "General Settings": the
  `align_vertically` table row's description ("instead of one `(back)^ω | mid | (fwd)^ω` line per
  lasso") and both sample blocks (`Certificate:` -> `Histories:`; the default sample regenerated
  as arrow-chain rows from the same capture).
- [ ] `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` "Rendering Policy" ->
  "Label notation" paragraph: describe the arrow-chain row (`L{i}  {role}  … (t:atoms) ⟹ … | … |
  … ⟹ … …`), the per-position column alignment across rows, and the unchanged `-a` transposition;
  re-read the file immediately before editing.
- [ ] `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` "Lassos and Positions": keep
  the `(back)^ω | mid | (fwd)^ω` sentence as the *structural* description of a lasso, and add one
  sentence saying how it is printed (`Histories:` rows of `(t:atoms)` states joined by `⟹`).
- [ ] Code comments: `code/src/model_checker/theory_lib/bimodal/examples.py` `general_settings`
  comment ("False: one `(back)^ω | mid | (fwd)^ω` line per lasso") and
  `code/src/model_checker/theory_lib/bimodal/semantic/core.py`'s `ADDITIONAL_GENERAL_SETTINGS`
  comment; `code/src/model_checker/theory_lib/bimodal/semantic/render.py` module docstring if it
  mentions the period marker (grep `ω`).
- [ ] `code/docs/core/CODE_STANDARDS.md` "Printed Output Conventions" and
  `code/docs/core/TESTING_GUIDE.md` section 8.14 (the e2e bimodal-retention note): update any
  mention of the `Certificate:` label or the one-liner; grep first (see Scope Hypothesis).
- [ ] Final gate: `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q`;
  `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | cat -v | grep -c '\^\['`
  (expect `0`) and the same with `-a`; `PYTHONIOENCODING=cp1252 python code/dev_cli.py <scratch
  example file>` per `TESTING_GUIDE.md` 9.3 for the default and `-a` views (expect no
  `UnicodeEncodeError`, `=>` in place of `⟹`); `ruff check
  code/src/model_checker/theory_lib/bimodal/semantic/model.py code/src/model_checker/utils/glyphs.py`.
- [ ] Task-reference lint over every touched `code/` file (the repo script's `PATH_SCOPE` rejects
  `code/`, so run the equivalent grep `\btasks? [0-9]+\b|\(task [0-9]+\)` as Phase 7 did): zero
  hits.

**Timing**: 1.5 hours

**Depends on**: 8

**Verification Tier**: prose

**Scope Hypothesis**: The one-liner or the `Certificate:` heading is described in exactly these
prose locations: `README.md` (lines ~199-201, ~574-576, ~597-600, ~624), `docs/SETTINGS.md`
(~167, ~172-174, ~182), `docs/ARCHITECTURE.md` (~281-286), `docs/USER_GUIDE.md` (~60),
`examples.py` (~118), `semantic/core.py` (~150), and possibly `code/docs/core/CODE_STANDARDS.md`
and `code/docs/core/TESTING_GUIDE.md` 8.14. Confirm with
`grep -rn "(back)\^\|\^ω\|Certificate:" code/src/model_checker/theory_lib/bimodal/README.md code/src/model_checker/theory_lib/bimodal/docs code/src/model_checker/theory_lib/bimodal/*.py code/src/model_checker/theory_lib/bimodal/semantic/*.py code/docs docs`
before editing; other theories' docs are out of scope; `docs/ADEQUACY.md`'s "Lemma 2
(Histories)" is a theorem name, not a display reference, and is not edited.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/README.md` - Sample Output regenerated; settings sentence; explanatory paragraph
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` - General Settings row and both samples
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - "Label notation" paragraph
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` - one added sentence
- `code/src/model_checker/theory_lib/bimodal/examples.py` - comment only
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - comment only
- `code/src/model_checker/theory_lib/bimodal/semantic/render.py` - docstring only, if it mentions the period marker
- `code/docs/core/CODE_STANDARDS.md`, `code/docs/core/TESTING_GUIDE.md` - only if the grep hits

**Verification**:
- Full suite green; live pipe checks (default and `-a`) zero escapes; cp1252 subprocess legs
  clean; `ruff` clean on the two touched modules; task-reference grep clean; the README sample
  is byte-identical to the captured `BM_CM_1` block apart from the solver time and checkout hash.

## Testing & Validation

Closed in the prior round (Phases 1-7):
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q` green after
  Phases 1, 2, 4, 5, 6, 7.
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/utils/tests code/src/model_checker/output -q`
  green after Phases 1 and 3.
- [x] Logos/exclusion/imposition suites green after Phase 3 (no captured-output change).
- [x] Every new glyph has a `cp1252` test using a real encoded stream (`TESTING_GUIDE.md` 9.2).
- [x] D8/F2 substrings preserved verbatim (grep the strings listed in Risks against the Phase 4
  test file).
- [x] `out.count("Verification:") == 1` per example; `out.count("No certificate found") == 1` on
  the `print_all` no-certificate path.
- [x] Printed witness `(lasso, t)` satisfies `child not in lassos[lasso].label(t)` on `MD_CM_1`.
- [x] `./dev_cli.py ... | cat -v | grep -c '\^\['` is `0`; `NO_COLOR=1` on a TTY prints plain
  text; `FORCE_COLOR=1` into a pipe prints color.
- [x] `-a` switches to the table view; default unchanged one-line rows.
- [x] Full suite `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q` green at the
  end of Phase 7.

This round (Phases 8-9):
- [ ] `ELLIPSIS` glyph: utf-8 `…`, cp1252 `…` (survives), `ascii` `...`; `DOUBLE_ARROW` cp1252
  `=>` still covered; no `OMEGA` reference remains in `code/`.
- [ ] Golden `MD_CM_1`: four `L{i}` rows of the shape `… (t:atoms) ⟹ (t:atoms) | (t:atoms) |
  (t:atoms) ⟹ (t:atoms) …`, exactly one bracketed cell (on `L0`), joiners at identical column
  indices across rows, `out.count("Histories:") == 1`, `"Certificate:" not in out`,
  `"^ω" not in out`.
- [ ] Single-slot example (`mid=0`): `… [-1:A] | (0:∅) …` or `… (-1:∅) | [0:A] …` (one `|`).
- [ ] Cross-row alignment test with differing cell widths passes.
- [ ] cp1252 end-to-end leg: `=>`, `{}`, `…` present; `⟹`, `∅` absent; `ascii` leg: `...`; no
  `UnicodeEncodeError` on either.
- [ ] `-a` view: heading `Histories:`, table body unchanged, `"⟹" not in out`.
- [ ] `test_output_gate.py` and `builder/tests/e2e/test_full_pipeline.py` pass with the
  `Histories:` pin; the seven D8/F2 substrings other than the heading remain verbatim.
- [ ] `semantic/witness_constraints.py` and `semantic/formula.py` untouched (`git diff --stat`
  against `5d259d66` lists neither).
- [ ] Docs regenerated from a live capture; `grep -rn "(back)\^\|Certificate:"` over the bimodal
  README/docs/comments returns only the `USER_GUIDE.md` structural sentence and
  `ADEQUACY.md`'s lemma name.
- [ ] Full suite `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q` green at the
  end of Phase 9; live pipe checks (default, `-a`) zero escapes; cp1252 subprocess legs clean.

## Artifacts & Outputs

- `specs/218_refactor_bimodal_countermodel_presentation/plans/01_bimodal-countermodel-presentation.md` (this file, revised in place)
- `specs/218_refactor_bimodal_countermodel_presentation/summaries/01_bimodal-countermodel-presentation-summary.md`
  (prior round's summary; the implementer of Phases 8-9 writes this round's summary at the
  round number the orchestrator assigns)
- Prior round, new modules: `code/src/model_checker/theory_lib/bimodal/semantic/render.py`,
  `code/src/model_checker/output/color.py`; new tests: `bimodal/tests/unit/test_render.py`,
  `output/tests/unit/test_color.py`, `builder/tests/unit/test_module_output_capture.py`
- This round, modified: `bimodal/semantic/model.py` (arrow-chain rows, `Histories:` headings),
  `utils/glyphs.py` (`ELLIPSIS` added, `OMEGA` removed), `utils/tests/unit/test_glyphs.py`,
  `bimodal/tests/unit/test_structure.py`, `bimodal/tests/integration/test_output_gate.py`,
  `builder/tests/e2e/test_full_pipeline.py`, bimodal `README.md`,
  `docs/{SETTINGS,ARCHITECTURE,USER_GUIDE}.md`, `examples.py` and `semantic/core.py` comments,
  and `code/docs/core/{CODE_STANDARDS,TESTING_GUIDE}.md` only if the Phase 9 grep hits

## Rollback/Contingency

- Each phase commits per green sub-step (`Commit Mode` default `per-substep`), so reverting a
  phase is `git revert` of its commits in reverse order. Phases 8 and 9 are additive to the
  Phase 1-7 baseline at `5d259d66`: reverting both restores the one-liner default exactly.
- If Phase 8's cross-row alignment proves unreadable at real widths (very wide `{A,B,C}` cells
  padding narrow rows), keep the arrow chain and the `Histories:` heading but drop the padding
  (cells unpadded, joiners unaligned), record the exclusion in a `#### Reasoned Exclusions`
  table under Phase 8 with the captured output as evidence, and leave the `-a` table as the
  aligned view.
- If `OMEGA` turns out to have a consumer the Phase 8 grep did not list, keep the entry and its
  test row and record the exclusion; nothing else in the phase depends on its removal.
- If Phase 3's predicate causes an import cycle that the `utils/colors.py` fallback does not
  resolve (not observed), revert Phase 3 alone and have Phase 4 gate bimodal colors on a
  bimodal-local `isatty()`/`NO_COLOR` check; the rest of the plan is unaffected.
- A genuine whole-tree rollback of uncommitted work follows
  `context/contracts/recovery.md`'s rollback rung (`bash .claude/scripts/git-snapshot.sh 218`,
  with `--allow-out-of-scope` only if tracked edits outside `file_scope` must be included), never
  a bare precautionary snapshot at phase start.
