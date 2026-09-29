# Implementation Plan: Task #218

- **Task**: 218 - Refactor bimodal/ theory countermodel presentation
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours
- **Dependencies**: None
- **Research Inputs**: specs/218_refactor_bimodal_countermodel_presentation/reports/01_bimodal-countermodel-presentation.md
- **Artifacts**: plans/01_bimodal-countermodel-presentation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Rewrite what `dev_cli.py` prints for a bimodal example so it is readable and honest: user-notation
formulas instead of dataclass reprs, a witness line computed from the certificate itself (the
current `Witness: L{i} at position {p}` line reads a *reserved* registry index and is verifiably
wrong on `MD_CM_1`), a per-lasso role column, a bounds line replacing the meaningless
`Atomic States: 0`, one `Verification:` line instead of two, an `^ω`/`∅` glyph set with ASCII
fallbacks, an optional time-aligned table behind the existing-but-dead `-a/--align_vertically`
flag, and iteration diffs that match `docs/ITERATE.md`. Exactly one systemic (non-bimodal) change
is made: a shared `use_colors(output)` predicate honoring `isatty()`/`NO_COLOR`/`TERM=dumb`/
`FORCE_COLOR` replaces the framework-wide `output is sys.__stdout__` identity test, so pipes and
redirected files stop receiving ANSI escapes. Every phase is TDD (tests before code) and every
new non-ASCII glyph ships with a `cp1252` regression test per `TESTING_GUIDE.md` section 9.
Definition of done: the full bimodal suite and utils suite pass, the D8/F2 wording substrings the
output gate pins are preserved verbatim, and a live `dev_cli.py ... | cat -v` run shows no
`^[[` escapes.

### Research Integration

The research report (`reports/01_bimodal-countermodel-presentation.md`) supplies: the twelve
concrete defects F1-F12 with sources; the evidence that F1 is a real bug (registry index is
capacity, not provenance -- `box_faithfulness_constraints` lets any lasso falsify a box); the
salvage inventory from the old Logos presentation (time-aligned rows, signed times, BLUE/GRAY
palette, `align_vertically` toggle, `+`/`-` diff markers); the infrastructure to reuse
(`utils/glyphs.py`, `syntax.all_sentences` + `formula.translate` reverse map, `set_colors`,
`ANSIToMarkdown`'s red/green-only contract, `_capture_model_output`'s `StringIO` path); external
CLI conventions (clig.dev, no-color.org); the target output mock in Finding 7; and decisions
D1-D8. This plan adopts D1-D8 as written. Two planning judgment calls the report left open are
resolved here (see Risks & Mitigations "Decisions" rows): the `Certificate:` heading is kept (with
the legend appended on the same line) so the pinned substring survives, and the role column is
derived only from the certificate scan -- a lasso the scan does not name is `reserved, unused`,
never "reserved for □χ", so nothing on screen implies registry provenance.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
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

**Non-Goals**:
- The certificate search, (C1)-(C4), the checker protocol, or the JSON wire format semantics.
- Adopting Rich or any new runtime dependency (D1).
- F8 (double `====` separator) and F12 (bare-`print()` WARNING in `set_colors`) -- framework
  cosmetics with no bimodal angle (D8).
- Changing the wording of the three documented verification states (D8/F2 contract); only the
  checkout hash is shortened.
- Flipping the `align_vertically` default to `True` (left `False`; may be revisited later).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Golden-output tests (`TestGoldenOutputCertificateFormat`, `test_output_gate.py`) break by design | H | H | Rewrite the tests first in the same phase (TDD); keep the D8/F2 substrings verbatim: `"Certificate:"`, `"No certificate found"`, `"not a validity claim"`, `"independently checked"`, `"WitnessFamily.Refutes"`, `"re-checked by this repository's own pure-Python decision procedures only"`, `"no independent checker available"`, `"independent check skipped"`; run the bimodal suite after every phase |
| New glyphs (`ω`, `□`, `◇`, `¬`, `∧`, `∨`, `→`, `⊥`, `⊤`) crash on a cp1252 pipe | H | M | Every glyph goes through `glyph()`; each gets a `cp1252` test using `TESTING_GUIDE.md` 9.2's real encoded-stream recipe (never `io.StringIO`) |
| Color predicate changes other theories' captured output | M | L | `capsys`/`StringIO` are non-TTY, so tests see no colors today and none after; add explicit tests for `StringIO` (no color), `NO_COLOR` (no color), `FORCE_COLOR` (color), `TERM=dumb` (no color) |
| `model_checker.output` import from `models/structure.py` creates an import cycle | M | M | Phase 3's first step is `python -c "import model_checker.models.structure"` after adding the import; if it cycles, place the predicate in `utils/colors.py` instead and re-export from `output/__init__.py` lazily |
| Reverse-lookup renderer sees two sentences with the same `translate` result (`A \vee B` vs `(\neg A \rightarrow B)`) | L | M | First-seen wins, built in `syntax.all_sentences` insertion order (deterministic); documented in the renderer docstring and pinned by a test |
| Witness scan picks the main lasso when a reader expects "another history" | L | M | Prefer the first non-main `(lasso, t)` falsifier; fall back to the main lasso honestly; test both branches |
| `extract_states` rename `lasso0` -> `L0` breaks JSON collector consumers | M | L | Update `tests/integration/test_data_extraction.py` first; grep `output/collectors` for `lasso` before renaming |
| Overlap with in-flight bimodal doc tasks on `docs/ARCHITECTURE.md` | L | L | Phase 7 adds one new subsection only; re-read the file immediately before editing |
| Decision: keep `Certificate:` heading rather than the mock's `Histories` | -- | -- | Preserves the pinned substring with zero test churn; legend appended on the same line |
| Decision: role column from certificate scan only (`main` / `witness for □χ` / `reserved, unused`) | -- | -- | Never prints registry reservation as provenance (D2); simpler and honest |
| Decision: `align_vertically` default stays `False` | -- | -- | Keeps the one-line golden shape the default path pins; the table is opt-in via `-a` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 6 | 1, 2, 3 (Phase 4); 1 (Phase 6) |
| 3 | 5 | 4 |
| 4 | 7 | 4, 5, 6 |

Phases within the same wave can execute in parallel. Wave 1's three phases own disjoint files
(Phase 1: `semantic/render.py` + `utils/glyphs.py`; Phase 2: `semantic/model.py` extraction
helpers only; Phase 3: framework + logos/exclusion/imposition printers). Phase 4 is the only
phase that rewrites `semantic/model.py`'s print methods; Phase 6 owns `iterate.py`.

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

### Phase 4: Bimodal Printer Rewrite [NOT STARTED]

**Goal**: `print_info` header, certificate block, box-guess table, evaluation point, verification
line, and interpreted-sentence wording match the report's Finding 7 mock (with the `Certificate:`
heading retained), using Phase 1's renderer, Phase 2's witness, and Phase 3's predicate.

**Tasks**:
- [ ] Rewrite the pinned tests first: `test_structure.py` `TestGoldenOutputCertificateFormat`,
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
- [ ] Add a `cp1252` end-to-end test for `print_certificate` per `TESTING_GUIDE.md` 9.2
  (expect `^w`, `[]`, `{}`, `|` fallbacks and no `UnicodeEncodeError`).
- [ ] Keep `test_print_evaluation_reports_no_certificate_case` (standalone call still prints) but
  make `print_all` skip `print_evaluation` when `certificate is None` so the no-certificate
  message prints once; add an assertion `out.count("No certificate found") == 1` on the
  `print_all` path.
- [ ] `proposition.py::print_proposition`: `(True at L0, t=-2)` wording; update
  `tests/unit/test_proposition.py` if it pins the old text (grep `in lasso`).
- [ ] Implement in `semantic/model.py`: `_print_model_details` override (bounds + lasso count);
  `_format_label` -> atoms joined by `, ` with `∅` glyph for empty, `[ ]` marker preserved;
  `_format_lasso` with `^ω` glyph; `_lasso_roles()` from `box_guesses()`; `print_certificate`
  (legend line, aligned role column, `Box guesses:` table via `render`); `print_evaluation`
  (`Evaluation point:` + single `Verification:`); `_verification_label` shortens the checkout to
  `[:12]`; colors (BLUE evaluation-point row, GRAY reserved rows, GREEN/RED guess values)
  gated by `use_colors(output)` and never carrying information alone.
- [ ] Update the `semantic/model.py` module docstring's output-shape description.
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q` and a
  live `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | cat -v |
  grep -c '\^\['` (expect `0`).

**Timing**: 2 hours

**Depends on**: 1, 2, 3

**Verification Tier**: full

**Scope Hypothesis**: Four test classes plus `test_output_gate.py` and possibly
`test_proposition.py` pin the current text; confirm with
`grep -rln "Witness: L\|in lasso\|Atomic States\|Box(Atom" code/src/model_checker/theory_lib/bimodal/tests`
before rewriting, and treat any additional hit as in scope for this phase.

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

### Phase 5: Time-Aligned Table View Behind `align_vertically` [NOT STARTED]

**Goal**: `-a/--align_vertically` (already parsed by `__main__.py` and present in
`DEFAULT_GENERAL_SETTINGS`) becomes live for bimodal and selects a per-position table salvaged
from the old vertical renderer; default `False` keeps Phase 4's one-line rows.

**Tasks**:
- [ ] Tests first (`test_structure.py`, new `TestAlignedHistoryTable`): with
  `align_vertically=True` the certificate block prints a header row `t   slot | L0 main | L1 |
  ...`, one row per representative position `-2 .. +2` with signed times and slot annotations
  (`back[0]`, `mid[0]`, `fwd[1]`), the target row marked with `[ ]` (and bold only when
  `use_colors`); with the default the one-line rows print; `SettingsManager` no longer warns
  `Flag 'align_vertically' doesn't correspond to any known setting` for bimodal (capture the
  warning path or assert the key survives in `structure.settings`).
- [ ] `semantic/core.py`: `ADDITIONAL_GENERAL_SETTINGS = {"align_vertically": False}`; update
  the comment there and the stale one in `examples.py` `general_settings`.
- [ ] `semantic/model.py`: `_print_history_table(output)`; `print_certificate` dispatches on
  `self.settings.get("align_vertically", False)`; column widths computed from rendered labels;
  `DOWN_ARROW`/`to_subscript` reuse where the old renderer used them.
- [ ] `docs/SETTINGS.md` "General Settings": replace the "defines no bimodal-specific general
  setting" paragraph with the `align_vertically` description and a short table example.
- [ ] Run the bimodal suite and `cd code && ./dev_cli.py -a src/model_checker/theory_lib/bimodal/examples.py | head -60`.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: Only `core.py`, `examples.py`, `model.py`, `SETTINGS.md`, and
`test_structure.py` change; confirm `grep -rn align_vertically code/src --include=*.py` shows no
other bimodal consumer to update.

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

### Phase 7: Docs, Naming Consistency, and Final Gate [NOT STARTED]

**Goal**: User-facing docs match the new output, the rendering-policy subsection `utils/glyphs.py`
cites exists, and the whole test suite plus a live pipe check pass.

**Tasks**:
- [ ] `theory_lib/bimodal/README.md` "Sample Output" (and the `(back)^w | mid | (fwd)^w` mention
  near the Basic Usage section): regenerate from a real `dev_cli.py` run of `BM_CM_1` (utf-8
  capture), including the `Search bounds` header line and `Box guesses` table.
- [ ] `theory_lib/bimodal/docs/ARCHITECTURE.md`: add a "Rendering policy" subsection (glyph
  fallback via `utils/glyphs.py`, color gating via `output.color.use_colors`, label notation,
  witness-from-certificate rule); update `utils/glyphs.py`'s module docstring pointer to name the
  subsection heading exactly.
- [ ] `code/docs/core/CODE_STANDARDS.md`: add a short "Printed Output Conventions" section (color
  predicate, palette meanings GREEN/RED top-level truth, WHITE/YELLOW nested, BLUE evaluation
  point, GRAY reserved; `ANSIToMarkdown` red/green-only contract; glyph rule with a pointer to
  `TESTING_GUIDE.md` section 9).
- [ ] `theory_lib/bimodal/docs/USER_GUIDE.md`: grep for `Witness:` / `Atomic States` / `lasso 0`
  and update any sample text.
- [ ] Final gate: `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q`;
  `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | cat -v | grep -c '\^\['`
  (expect `0`); `PYTHONIOENCODING=cp1252 python code/dev_cli.py <scratch example file>` per
  `TESTING_GUIDE.md` 9.3 (expect no `UnicodeEncodeError`); `ruff check code/src/model_checker/theory_lib/bimodal code/src/model_checker/output/color.py`.
- [ ] Run `bash .claude/scripts/check-task-references.sh` (or the repo-wide lint it wraps) over
  the touched `code/` and `docs/` files to confirm no task-number citations.

**Timing**: 1.5 hours

**Depends on**: 4, 5, 6

**Verification Tier**: prose

**Scope Hypothesis**: Four doc files plus one docstring; confirm with
`grep -rln "Witness: L\|Atomic States\|lasso 0\|(back)^w" code/src/model_checker/theory_lib/bimodal/README.md code/src/model_checker/theory_lib/bimodal/docs docs`
and add any further hit to this phase.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/README.md` - Sample Output regenerated
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - Rendering policy subsection
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` - sample text if stale
- `code/docs/core/CODE_STANDARDS.md` - Printed Output Conventions
- `code/src/model_checker/utils/glyphs.py` - docstring pointer only

**Verification**:
- Full suite green; live pipe check zero escapes; cp1252 subprocess leg clean; task-reference
  lint clean on deliverable files.

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q` green after
  Phases 1, 2, 4, 5, 6, 7.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/utils/tests code/src/model_checker/output -q`
  green after Phases 1 and 3.
- [ ] Logos/exclusion/imposition suites green after Phase 3 (no captured-output change).
- [ ] Every new glyph has a `cp1252` test using a real encoded stream (`TESTING_GUIDE.md` 9.2).
- [ ] D8/F2 substrings preserved verbatim (grep the eight strings listed in Risks against the
  Phase 4 test file).
- [ ] `out.count("Verification:") == 1` per example; `out.count("No certificate found") == 1` on
  the `print_all` no-certificate path.
- [ ] Printed witness `(lasso, t)` satisfies `child not in lassos[lasso].label(t)` on `MD_CM_1`.
- [ ] `./dev_cli.py ... | cat -v | grep -c '\^\['` is `0`; `NO_COLOR=1` on a TTY prints plain
  text; `FORCE_COLOR=1` into a pipe prints color.
- [ ] `-a` switches to the table view; default unchanged one-line rows.
- [ ] Full suite `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q` green at the
  end of Phase 7.

## Artifacts & Outputs

- `specs/218_refactor_bimodal_countermodel_presentation/plans/01_bimodal-countermodel-presentation.md` (this file)
- `specs/218_refactor_bimodal_countermodel_presentation/summaries/01_bimodal-countermodel-presentation-summary.md`
- New modules: `code/src/model_checker/theory_lib/bimodal/semantic/render.py`,
  `code/src/model_checker/output/color.py`
- New tests: `bimodal/tests/unit/test_render.py`, `output/tests/unit/test_color.py`
- Modified: `bimodal/semantic/{model,proposition,core}.py`, `bimodal/iterate.py`,
  `bimodal/examples.py`, `utils/glyphs.py`, `models/structure.py`, `output/__init__.py`,
  logos/exclusion/imposition `semantic/model.py`, bimodal `README.md`, `docs/{SETTINGS,ITERATE,ARCHITECTURE,USER_GUIDE}.md`,
  `code/docs/core/CODE_STANDARDS.md`, and the bimodal/utils/output test files named per phase

## Rollback/Contingency

- Each phase commits per green sub-step (`Commit Mode` default `per-substep`), so reverting a
  phase is `git revert` of its commits in reverse order; Wave 1 phases are independent and can be
  reverted individually.
- If Phase 3's predicate causes an import cycle that the `utils/colors.py` fallback does not
  resolve, revert Phase 3 alone and have Phase 4 gate bimodal colors on a bimodal-local
  `isatty()`/`NO_COLOR` check; the rest of the plan is unaffected.
- If Phase 5's table proves unreadable at real column widths, keep the setting live but ship
  the one-line view for both values and record the exclusion in a `#### Reasoned Exclusions`
  table under Phase 5 with the captured output as evidence.
- A genuine whole-tree rollback of uncommitted work follows
  `context/contracts/recovery.md`'s rollback rung (`bash .claude/scripts/git-snapshot.sh 218`,
  with `--allow-out-of-scope` only if tracked edits outside `file_scope` must be included), never
  a bare precautionary snapshot at phase start.
