# Research Report: Refactor bimodal/ countermodel presentation in dev_cli.py output

- **Task**: 218 - Refactor bimodal/ theory countermodel presentation
- **Started**: 2026-09-29T00:19:39Z
- **Completed**: 2026-09-29T00:58:00Z
- **Effort**: ~40 minutes
- **Dependencies**: None (tasks 216/217/199/198/200 touch bimodal docs/adequacy only; no overlap with printing)
- **Sources/Inputs**:
  - Current printer: `code/src/model_checker/theory_lib/bimodal/semantic/model.py` (`_format_label`, `_format_lasso`, `_first_missing_position`, `_verification_label`, `print_certificate`, `print_evaluation`, `print_all`)
  - Current proposition printer: `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` (`print_proposition`)
  - Certificate semantics: `semantic/certificate.py` (`LabelledLasso`, `WitnessFamily`, `_box_faithful`, `_box_window`), `semantic/witness_constraints.py` (`box_faithfulness_constraints`), `semantic/witness_registry.py` (`allocate_witness_lasso`, `wrap`, `target_window`), `semantic/core.py` (`finalize_certificate`, `extract_certificate`), `semantic/formula.py` (`translate`, dataclass reprs)
  - Iteration printer: `theory_lib/bimodal/iterate.py` (`_calculate_differences`, `display_model_differences`)
  - Framework: `models/structure.py` (`print_info`, `_print_model_details`, `print_input_sentences`, `recursive_print`), `models/proposition.py` (`set_colors`), `utils/glyphs.py` (`glyph`, `to_subscript`, `stream_can_encode`), `builder/example.py` (`print_model`), `builder/module.py` (`_capture_model_output`), `builder/runner.py` (iteration display), `output/formatters/markdown.py` (`ANSIToMarkdown`), `output/progress/animated.py` (only `NO_COLOR` reader in the codebase), `settings/settings.py`, `__main__.py` (`-a/--align_vertically`)
  - Old presentation (inspiration only): `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py` lines 2177-2830 and 2908-3045; `.../bimodal/examples.py` `general_settings`
  - Docs: `theory_lib/bimodal/README.md` "Sample Output", `docs/SETTINGS.md` ("The three output states", "General Settings"), `docs/ITERATE.md`, `code/docs/core/TESTING_GUIDE.md` section 9 (output-encoding policy)
  - Tests pinning current output: `bimodal/tests/unit/test_structure.py` (`TestPrintingDoesNotClaimValidity`, `TestVerificationLabelRendering`, `TestGoldenOutputCertificateFormat`), `bimodal/tests/integration/test_output_gate.py`
  - Lean side: `~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean` (derived-operator definitions and the "Naming Convention" section)
  - Live run: `python code/dev_cli.py <scratch file>` over `EX_CM_1, MD_CM_1, TN_CM_1, BM_CM_1, BM_CM_2, MD_TH_1`, captured with `cat -v`
  - Empirical check script (via `bimodal/tests/_build_support._build`) comparing registry witness indices against actual (C3) falsifiers
  - Web: clig.dev "Output" section, no-color.org, Rich `Console` docs (terminal/`NO_COLOR`/`FORCE_COLOR`/`TERM=dumb` handling)
- **Artifacts**: `specs/218_refactor_bimodal_countermodel_presentation/reports/01_bimodal-countermodel-presentation.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The current bimodal printer (`semantic/model.py`, written during the certificate-encoding rewrite) is functionally honest but presentationally rough: it leaks Python dataclass reprs (`Box(Atom(base='A', fresh_index=None))`), prints a 200-character verification sentence twice per example, prints a meaningless `Atomic States: 0` line inherited from `ModelDefaults`, and shows every reserved lasso with no indication of which ones actually do work.
- One line is factually wrong, not merely ugly: `Witness: L{i} at position {p}` reads the lasso index from `WitnessRegistry._witness_lassos`, but `box_faithfulness_constraints` lets *any* lasso falsify a box. Verified on `MD_CM_1`: `Box(A)` is reserved lasso 1 but only `(L3, t=2)` falsifies it; `Box(B)` is reserved lasso 3 but every falsifier lies on `L0`. The live run prints `Witness: L2 at position None` for exactly this reason.
- Salvageable from the old Logos presentation: the time-aligned columns (`W_i` rows / `Time` rows with `↓`), the `⟹ₙ` duration arrows, signed time labels (`+1`, `-2`), BLUE evaluation-point / GRAY history coloring, the `align_vertically` toggle, and the `+`/`-` difference markers. The `_to_subscript` helper was already hoisted to `utils/glyphs.py`, which also gives the encoding-safe fallback discipline any new glyph must use.
- Color is decided framework-wide by `output is sys.__stdout__`, never by `isatty()`/`NO_COLOR`/`TERM=dumb`; ANSI escapes are emitted into pipes and redirected files (confirmed with `dev_cli.py ... | cat -v`). Only the progress bar honors `NO_COLOR`. This is the one systemic change the task should make, via a single shared predicate, not by adopting Rich (see Decisions).
- `-a/--align_vertically` and `DEFAULT_GENERAL_SETTINGS["align_vertically"]` are dead code: no theory reads the setting since bimodal's rewrite. Recommendation: bimodal re-adopts it (via `ADDITIONAL_GENERAL_SETTINGS`) to select the time-aligned table view vs the compact one-line view, making the existing CLI flag live again with zero framework change.
- Recommended shape: a formula renderer that reverses `translate` (user notation, falling back to structural rendering), a per-lasso role label (`main` / `witness for □A` / `reserved, unused`), a witness line computed from the certificate itself, a bounds line replacing `Atomic States`, one verification line, and an optional time-aligned table; all glyphs through `glyph()` with cp1252 regression tests per `TESTING_GUIDE.md` section 9.

## Context & Scope

- **What is being evaluated**: everything printed for one bimodal example by `dev_cli.py examples.py` -- the `print_info` header (framework), the `Certificate:` / `Boxed subformulas:` / `Evaluation Point:` blocks (bimodal), the `INTERPRETED PREMISE(S)/CONCLUSION(S)` tree (framework `recursive_print` + bimodal `print_proposition`), and the iteration `=== DIFFERENCES FROM PREVIOUS MODEL ===` block (bimodal `iterate.py`).
- **Constraints**:
  - D8 (never report validity) and F2 (verification wording discipline) are documented contracts (`semantic/model.py` module docstring, `docs/SETTINGS.md` "The three output states"); tests assert specific substrings (`"Certificate:"`, `"No certificate found"`, `"not a validity claim"`, `"independently checked"`, `"WitnessFamily.Refutes"`, `"re-checked by this repository's own pure-Python decision procedures only"`, `"no independent checker available"`, `"independent check skipped"`, and the golden `L0 (main): ([{A}])^w | - | ({})^w` shape). Any redesign must either preserve these or update the tests in the same phase (TDD: tests first).
  - `TESTING_GUIDE.md` section 9: any new non-ASCII glyph on a print path must go through `utils/glyphs.glyph`/`to_subscript` and ship with a `cp1252` regression test in the same change.
  - Saved output (`--save`) is captured into `io.StringIO` by `builder/module.py::_capture_model_output`, then passed through `ANSIToMarkdown.convert`, which only understands `\033[31m` (red, to `**bold**`) and `\033[32m` (green, to `_italic_`) and strips everything else. Any color scheme must stay within plain SGR codes this converter can strip.
  - `pyproject.toml` runtime dependencies are only `z3-solver` and `networkx`; adding a terminal library is a dependency-policy decision, not a local one.
  - The task says "other systematic model-checker changes only as needed"; the findings below separate bimodal-local defects from the two systemic ones (color gating, dead `align_vertically` flag).
- **Out of scope**: the certificate search, (C1)-(C4), the checker protocol, JSON wire format. Only how results are displayed.

## Findings

### 1. Current output, as actually rendered (live run)

For `MD_CM_1` (`\Box (A \vee B)` therefore `\Box A`, `\Box B`) the CLI prints, in order: the framework header (`EXAMPLE ...`, `Atomic States: 0`, `Semantic Theory: Bimodal`, premises/conclusions, `Solver Run Time`), then:

```
Certificate:
  Verification: independently checked -- Lean constructed a WitnessFamily.Refutes term for this certificate by applying a compile-time kernel-checked implication to four run-time decisions (acceptance: entailment, checkout e25e0bddbf99cfeb233e5c3df10c557d281a4d16)
  L0 (main): ([{B}], {B})^w | {B} | ({B}, {B})^w
  L1 (witness 1): ({B}, {B})^w | {B} | ({B}, {B})^w
  L2 (witness 2): ({B}, {B})^w | {B} | ({B}, {B})^w
  L3 (witness 3): ({B}, {B})^w | {B} | ({B}, {A})^w

Boxed subformulas:
  Box(Atom(base='A', fresh_index=None)) = False
    Witness: L3 at position -2 (({B}, {B})^w | {B} | ({B}, {A})^w)
  Box(Atom(base='B', fresh_index=None)) = False
    Witness: L2 at position None (({B}, {B})^w | {B} | ({B}, {B})^w)
  Box(Imp(left=Imp(left=Atom(base='A', fresh_index=None), right=Bot()), right=Atom(base='B', fresh_index=None))) = True

Evaluation Point:
  Main lasso: L0
  Target position: -2
  Verification: independently checked -- Lean constructed ... (same 200-char line again)

INTERPRETED PREMISE:
1.  |\Box (A \vee B)| = < {0, 1, 2, 3}, {} >  (True in lasso 0 at position -2)
      |(A \vee B)| = < {0, 1, 2, 3}, {} >  (True in lasso 0 at position -2)
...
Total Run Time: 0.0715 seconds

========================================
========================================
```

Concrete defects, each with its source:

| # | Defect | Source | Severity |
|---|--------|--------|----------|
| F1 | `Witness: L2 at position None` -- and more generally the witness lasso named is the registry's *reserved* index, not the lasso that falsifies the box | `model.py::print_certificate` reads `witness_registry._witness_lassos.get(child)`; `witness_constraints.py::box_faithfulness_constraints` asserts `somewhere_absent` over *all* lassos; `core.py::finalize_certificate` allocates one lasso per `Box` regardless of guess | Wrong output (misleading) |
| F2 | Formula reprs (`Box(Atom(base='A', fresh_index=None))`, `Imp(left=Imp(...), right=Bot())`) instead of the user's `\Box A`, `(A \vee B)` | `formula.py` dataclass default `__repr__`; printer uses `{child!r}`; `iterate.py::_calculate_differences` uses `repr(child)` and `sorted(map(repr, label))` too | Unreadable |
| F3 | Verification sentence printed twice, ~200 chars each, with a 40-char commit hash | `print_certificate` and `print_evaluation` both call `_verification_label()` | Noise |
| F4 | `Atomic States: 0` -- bimodal has no `N`; `core.py:160` sets `self.N = 0` only to satisfy the base class | `models/structure.py::_print_model_details` is not overridden | Misleading |
| F5 | Reserved-but-unused lassos (`L1`, `L2` above, identical and doing no work) are labelled `witness 1`, `witness 2` with no role information | one lasso per `Box` in closure, guessed-true boxes included | Confusing |
| F6 | No explanation of what `position -2` means (the printed window is `[-back, mid+fwd)` = `[-2, 3)`; `-2` is `back[0]`); the `[..]` marker in `L0` is the only cue; no bounds line | printer prints `target_time` raw; bounds only appear in the no-certificate message | Opaque |
| F7 | Label braces `{}`/`{A,B}` are set notation for atoms only, though labels actually hold every closure formula; the legend is nowhere on screen | `_format_label` filters to `Atom` (by design, report 01 section 4.4) but does not say so | Minor |
| F8 | Double `====` separator between examples (closing separator from `print_all` + opening one from `_print_section_header`) | framework-wide, logos/imposition do the same | Cosmetic, systemic |
| F9 | ANSI escapes are emitted when stdout is a pipe/file (`^[[32m` visible in `cat -v`) | `use_colors = output is sys.__stdout__` in `models/structure.py::_print_sentence_group`, and the same identity test in every theory's `print_evaluation`/`print_states`; no `isatty()`/`NO_COLOR`/`TERM` check anywhere except `output/progress/animated.py` | Systemic |
| F10 | Iteration diff prints full repr lists per position (`Position -1: ['Atom(...)', ...] -> [...]`) while `docs/ITERATE.md` documents `L0, position -1: + Box(A)` | `iterate.py::display_model_differences` vs docs -- code/docs drift | Unreadable + drift |
| F11 | JSON/markdown collectors name worlds `lasso0` (`extract_states`, `extract_evaluation_world`) while the screen says `L0` | `model.py::extract_states` | Inconsistent |
| F12 | `PropositionDefaults.set_colors` prints a `WARNING` with a bare `print()` (not to `output`) when a truth value is `None` | `models/proposition.py:112` | Minor, systemic |

### 2. Why F1 is a real bug (evidence)

`_box_faithful` (C3) in `certificate.py` defines a false guess as: some lasso, some position in `_box_window`, omits `chi`. The Z3 side (`box_faithfulness_constraints`) encodes exactly that disjunction over *every* lasso index it is given. `finalize_certificate` allocates a lasso index per boxed subformula purely as *capacity* (so the search can always find room for a falsifier); nothing ties `_witness_lassos[chi]` to where the solver actually placed the falsification. Empirical check on the default bounds (`back=2, mid=1, fwd=2`, `verify='off'`), via `bimodal/tests/_build_support._build`:

```
MD_CM_1: Box(A) guess=False registry_index=1 actual_falsifiers=[(3, 2)]
         Box(B) guess=False registry_index=3 actual_falsifiers=[(0,-2),(0,-1),(0,0),(0,1),(0,2)]
BM_CM_1: Box(A) guess=False registry_index=1 actual_falsifiers=[(1,-2),(1,-1),(1,0),(1,1),(1,2)]
```

The printer happened to be right for `BM_CM_1` (the README's sample) and wrong for `MD_CM_1`. `_first_missing_position` then returns `None` whenever the reserved lasso is not a falsifier. The fix is to compute the witness from the certificate: the first `(lasso, t)` over `enumerate(certificate.lassos)` x `_box_window(lasso)` with `child not in lasso.label(t)` -- the same scan `recheck` performs, so the printed witness is by construction one (C3) accepts. Prefer a witness on a non-main lasso when one exists (readers expect "another history"), else report the main lasso honestly.

### 3. What the old Logos presentation did (salvage inventory)

Old `BimodalStructure` (retired `(world_id, time)` encoding) printed `World Histories:` then `Evaluation Point:` then interpreted sentences. Elements worth carrying over, adapted to lassos:

| Old element | Old code | Salvage verdict for lassos |
|-------------|----------|----------------------------|
| Time-aligned horizontal rows: `W_0: (-1:a) ⟹₁ (0:a.b) ⟹₁ (+1:b)` with column widths computed so equal times align across worlds | `print_world_histories`, `_create_formatted_states`, `_calculate_column_widths`, `_create_time_positions`, `_create_world_line` | Yes -- one row per lasso, one column per representative position in `[-back, mid+fwd)`; the periodic segments become bracketed groups instead of `⟹` chains |
| Vertical table: `Time | W_0 | W_1` header, `=` rule, one row per time, `↓` arrow rows, bold-yellow highlight of time 0 | `print_world_histories_vertical` | Yes -- time rows top-to-bottom is the clearest way to show *which slot is which* across 3-4 lassos; highlight the target position instead of time 0; add a segment annotation column (`back[0]`, `mid`, `fwd[1]`) |
| Signed times `+1` / `-2` / `0` | `format_time` | Yes -- distinguishes the fwd side visually |
| `⟹ₙ` duration-subscript arrows | `_to_subscript` (now `utils.glyphs.to_subscript`) | Partially -- the shift is always by 1 between adjacent slots, so subscripts add nothing; but `^ω` on the periodic segments should be a glyph with `^w` fallback (the current literal `^w` reads as "to the w") |
| BLUE evaluation point, GRAY histories, `\033[1;33m` highlight | `print_evaluation`, both history printers | Yes for the palette (matches logos' BLUE evaluation world); but gate on the shared color predicate (Finding 5), not `output is sys.__stdout__` |
| `align_vertically` setting toggling horizontal vs vertical | `general_settings` in old `examples.py`, `print_all` | Yes -- see Finding 6 |
| `=== DIFFERENCES FROM PREVIOUS MODEL ===` with `+ World W_2 added`, `- Time 1: b`, `Time 0: a -> a.b` | `print_model_differences` | Yes -- per-position `+ □A` / `- A` lines using the renderer, matching `docs/ITERATE.md`'s already-documented shape |
| Sentence-level `(True in W_0 at time 0)` | old `print_proposition` | Already mirrored as `(True in lasso 0 at position -2)`; rename to `(True at L0, t=-2)` for consistency with the history rows |

Nothing from the old semantics (`world_histories`, `world_arrays`, `time_shifts`, `bitvec_to_worldstate`) is applicable; the theory is a different object now.

### 4. Existing infrastructure to reuse (do not reinvent)

- `utils/glyphs.py`: `glyph(name, output)` with `_GLYPHS` table (`DOUBLE_ARROW`, `ARROW`, `DOWN_ARROW`, `BLOCK_*`, `NULL_STATE`, `EMPTY_SET`) and `to_subscript(n, output)`; `stream_can_encode` is memoized. New glyphs needed: `OMEGA` (`ω`/`w`), `BOX` (`□`/`[]`), `NEG` (`¬`/`~` -- note `¬` *is* in cp1252 but keep the fallback uniform), `AND`/`OR`/`IMP`/`BOT`/`TOP` (`∧ ∨ → ⊥ ⊤` / `&`, `|`, `->`, `_|_`, `T`), and possibly `LOZENGE` (`◇`) if the renderer collapses `¬□¬` to `◇`. Each needs a `cp1252` test per `TESTING_GUIDE.md` 9.
- `syntactic.Syntax.all_sentences` (`{infix_string: Sentence}` including every subsentence) plus `formula.translate` (memoized in `_TRANSLATE_CACHE`) gives a reverse map `Formula -> user spelling` for free: `{translate(s): s.name for s in structure.syntax.all_sentences.values()}`. Closure members that are only intermediate translation products (`Imp(B, Bot)` from `\wedge`, `Imp(Bot, Bot)` = top, the `Untl(top, ...)` inside `\Future`) need the structural fallback renderer. `Formula.lean`'s "Naming Convention" and derived definitions (`neg`, `and`, `or`, `top`, `diamond`, `allFuture`, `allPast`, `someFuture`, `somePast`, `next`, `prev`) are the authoritative pattern list for that fallback.
- `models/proposition.py::set_colors` -- returns `(RESET, FULL, PART)` and already encodes the GREEN/RED top-level, WHITE/YELLOW nested convention used by every theory; keep `print_proposition` on it.
- `output/formatters/markdown.py::ANSIToMarkdown` -- constrains the palette: red and green are the only codes with a markdown meaning; blue/gray/bold are stripped. Fine for a screen palette, but do not encode information *only* in a color the converter strips.
- `builder/module.py::_capture_model_output` -- when `--save` is on, output is rendered once into a `StringIO` (so `output is sys.__stdout__` is false, i.e. no colors) and echoed to the console. Any `isatty`-based predicate must therefore accept an explicit override (the runner knows it is echoing to a terminal) or the saved run loses colors on screen exactly as it does today.
- Tests: `bimodal/tests/_build_support._build(premises, conclusions, **settings)` builds a `BimodalStructure` in one call; `capsys` + `output=sys.stdout` is the established convention for print tests (`test_structure.py:162-168`).

### 5. External guidance (CLI display conventions)

- clig.dev "Output": humans first -- detect TTY; disable color when stdout is not a TTY, when `NO_COLOR` is set, when `TERM=dumb`, or on `--no-color`; keep line-oriented output greppable; don't print developer-only detail by default (verbose mode instead); use symbols judiciously. Source: [Command Line Interface Guidelines](https://clig.dev/), [no-color.org](https://no-color.org/).
- Rich's `Console` is the reference implementation of that policy in Python (`NO_COLOR` > `FORCE_COLOR` > `TERM=dumb` > `isatty`, with `force_terminal`/`TTY_COMPATIBLE` overrides for CI) and would give tables/alignment for free. Source: [Rich Console docs](https://rich.readthedocs.io/en/latest/console.html), [Rich on GitHub](https://github.com/textualize/rich). It is *not* recommended here (see Decisions): it is a new runtime dependency for a ~150-line feature, its markup would not survive `ANSIToMarkdown`, and `StringIO` capture already works with plain SGR codes.
- Lasso notation in the temporal-logic literature is `u·v^ω` (prefix, then loop) -- the `^ω` superscript is the standard reading of "repeat forever"; a bi-infinite lasso `(back)^ω | mid | (fwd)^ω` is a direct extension readers of LTL countermodels will recognize. Sources: [Kleene Theorems for Lasso Languages and ω-Languages](https://arxiv.org/pdf/2402.13085), [Ultimately periodic words of rational ω-languages](https://link.springer.com/chapter/10.1007/3-540-58027-1_27).

### 6. The dead `align_vertically` flag

`grep -rn align_vertically code/src --include=*.py` (excluding tests) hits only `__main__.py:149,234` (the `-a` flag), `settings/settings.py:420` (`DEFAULT_GENERAL_SETTINGS`), `settings/types.py:59,130`, and a comment in `bimodal/examples.py:118`. No semantics class declares it in `ADDITIONAL_GENERAL_SETTINGS`, so `SettingsManager` warns `Flag 'align_vertically' doesn't correspond to any known setting` and drops it. Under the project's No Backwards Compatibility principle this is either removed or made live. Making it live for bimodal (the only temporal theory) costs one dict entry in `BimodalSemantics.ADDITIONAL_GENERAL_SETTINGS` and reuses the existing `-a` flag, help text (`Display temporal models vertically (top-to-bottom time flow)`), and settings plumbing unchanged -- no framework edit required.

### 7. Proposed target output (mock, for the plan to adopt)

```
========================================

EXAMPLE MD_CM_1: there is a countermodel.

Semantic Theory: Bimodal
Search bounds: back=2, mid=1, fwd=2 (4 lassos: 1 main + 3 reserved witnesses)

Premise:
1. \Box (A \vee B)

Conclusions:
2. \Box A
3. \Box B

Solver Run Time: 0.0014 seconds

Histories  (each lasso is (back)^ω | mid | (fwd)^ω over atoms; [ ] marks the evaluation point)
  L0  main               ([B], B)^ω | B | (B, B)^ω
  L1  reserved, unused   (B, B)^ω | B | (B, B)^ω
  L2  reserved, unused   (B, B)^ω | B | (B, B)^ω
  L3  witness for □A     (B, B)^ω | B | (B, A)^ω

Box guesses
  □A          false   falsified at L3, t=+2
  □B          false   falsified at L0, t=-2
  □(A ∨ B)    true

Evaluation point: L0 at t=-2
Verification: independently checked (Lean WitnessFamily.Refutes, acceptance: entailment, checkout e25e0bddbf99)

INTERPRETED PREMISE:
1.  |\Box (A \vee B)| = < {0, 1, 2, 3}, {} >  (True at L0, t=-2)
...
```

With `align_vertically=True` (the `-a` flag), the `Histories` block becomes the salvaged table:

```
Histories  (t ranges over all integers; back repeats leftward, fwd rightward)
   t   slot     | L0 main | L1      | L2      | L3 witness □A
  ---------------+---------+---------+---------+--------------
  -2   back[0]  | [B]     | B       | B       | B
  -1   back[1]  | B       | B       | B       | B
   0   mid[0]   | B       | B       | B       | B
  +1   fwd[0]   | B       | B       | B       | B
  +2   fwd[1]   | B       | B       | B       | A
```

Empty labels render via `glyph("EMPTY_SET")` (`∅` / `{}`); `ω`, `□`, `∨` via new glyph entries with ASCII fallbacks (`w`, `[]`, `|`). All ANSI color (GREEN/RED truth values, BLUE evaluation point, GRAY reserved rows, bold target row) goes through one shared predicate (Finding 5) so pipes and `NO_COLOR` get plain text.

## Decisions

- **D1 -- Plain ANSI + `utils/glyphs`, not Rich.** Reasons: dependency policy (`z3-solver`, `networkx` only), `ANSIToMarkdown` compatibility, `StringIO` capture path, and the small size of the feature. Revisit only if a later task wants tables across all theories.
- **D2 -- Compute the witness from the certificate, never from `WitnessRegistry._witness_lassos`.** The registry index is capacity, not provenance (Finding 2). The registry's map may still be used to label a lasso as "reserved for □χ" in the role column, but "falsified at" must come from the label scan.
- **D3 -- Render formulas in the user's notation via reverse `translate` lookup, with a structural fallback that mirrors `Formula.lean`'s derived-operator patterns.** Never print dataclass reprs on any user-facing path (printer *and* iteration diffs). Keep `repr` untouched (Z3 variable names in `witness_registry.py` depend on `{formula!r}`).
- **D4 -- Keep D8/F2 wording verbatim, print it once.** One `Verification:` line, in the evaluation block; the three documented states keep their asserted substrings; shorten the checkout to 12 hex chars.
- **D5 -- Bimodal overrides `_print_model_details` to print `Search bounds` instead of `Atomic States`**, rather than changing the framework header for every theory.
- **D6 -- Re-adopt `align_vertically` in bimodal** (`ADDITIONAL_GENERAL_SETTINGS = {"align_vertically": False}`) to select table vs one-line histories. Default `False` keeps the golden one-line shape the existing tests pin; the plan may flip the default after the tests are rewritten if the table proves clearer.
- **D7 -- One systemic change is warranted: a shared `use_colors(output)` predicate** (`isatty()`, `NO_COLOR`, `TERM=dumb`, `FORCE_COLOR`, plus an explicit override for the `--save` echo path) living in `model_checker.output` or `model_checker.utils`, replacing `output is sys.__stdout__` in `models/structure.py` and each theory's printers. Scope it as its own phase so it can be dropped or deferred without blocking the bimodal work; the bimodal printer calls the predicate from day one.
- **D8 -- Do not touch F8 (double separator) or F12 (bare-print WARNING) in this task** beyond noting them; both are framework-wide cosmetics with no bimodal-specific angle.

## Recommendations

Ordered for a plan; each phase is one agent run and TDD (tests before code):

1. **Formula renderer** (`semantic/formula.py` or new `semantic/render.py`): `render(formula, output, names=None) -> str`; reverse-lookup dict built from `syntax.all_sentences`; structural fallback for `Imp(x,Bot)`->`¬x`, `Imp(Imp(a,Bot),b)`->`(a ∨ b)`, `Imp(Imp(a,Imp(b,Bot)),Bot)`->`(a ∧ b)`, `Imp(Bot,Bot)`->`⊤`, `Imp(Untl(⊤,Imp(a,Bot)),Bot)`->`\Future a` (and `\Past` mirror), `Box`->`□`, generic `Imp`->`(a → b)`, `Untl`/`Snce`->`(g U e)`/`(g S e)`; glyph entries + cp1252 tests. Owner: python-implementation-agent.
2. **Witness computation** (`model.py`): replace `_first_missing_position` + registry lookup with a certificate scan over all lassos x `_box_window`; unit test on an `MD_CM_1`-shaped example asserting the printed witness satisfies `child not in lassos[i].label(t)`. Also expose it via `extract_relations`/a new `extract_box_guesses` for the JSON collector.
3. **Header and layout** (`model.py`): `_print_model_details` override (bounds line, lasso count); role column per lasso (`main` / `witness for □χ` / `reserved, unused`, derived from phase 2's scan); single `Verification:` line; `Evaluation point: L0 at t=-2`; `^ω` glyph; `∅` for empty labels; `(True at L0, t=-2)` in `print_proposition`. Update `TestGoldenOutputCertificateFormat` first.
4. **Time-aligned table view** (`model.py`, salvaged from old `print_world_histories_vertical`): rows per representative position with signed `t` and slot annotation, columns per lasso, target row highlighted; gated by `align_vertically`; `ADDITIONAL_GENERAL_SETTINGS` entry; remove the stale comment in `examples.py:118`; document in `docs/SETTINGS.md` "General Settings".
5. **Iteration diffs** (`iterate.py`): render per-position `+`/`-` formula lines using the renderer, matching `docs/ITERATE.md`; `Box guess` lines in user notation; test with two structures.
6. **Shared color predicate** (systemic, optional-but-recommended): `use_colors(output)` honoring `NO_COLOR`/`TERM=dumb`/`isatty`/`FORCE_COLOR`; replace `output is sys.__stdout__` in `models/structure.py::_print_sentence_group` and the theory printers (`logos`, `imposition`, `exclusion`, `bimodal`); keep `--save` echo colored via explicit override; tests with a non-tty `StringIO` and `monkeypatch.setenv("NO_COLOR", "1")`.
7. **Naming consistency + docs**: `extract_states` worlds as `L0..` (or document why `lasso0`); update `README.md` "Sample Output", `docs/SETTINGS.md`, `docs/ITERATE.md`, `docs/ARCHITECTURE.md` (the "rendering policy subsection" `utils/glyphs.py` cites no longer exists there -- restore it); regenerate the sample from a real run.

## Risks & Mitigations

- **Golden-output tests break by design** (`TestGoldenOutputCertificateFormat`, `test_output_gate.py` substrings). Mitigation: rewrite tests in the same phase, keep the D8/F2 substrings verbatim, run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -v` after every phase.
- **New glyphs crash on cp1252 pipes** (the exact bug `utils/glyphs.py` exists for). Mitigation: every glyph via `glyph()`; cp1252 tests per `TESTING_GUIDE.md` 9.1 (a real encoded stream, not `StringIO`).
- **Color predicate changes other theories' output** in tests that capture `sys.stdout` via `capsys` (a non-tty): today they see no colors (`output is sys.__stdout__` is false under capsys too), so behaviour is unchanged for them; the `--save` echo path is the only place that could regress -- cover it with an explicit test.
- **`ANSIToMarkdown` strips new colors silently**: acceptable as long as no information is carried by color alone (role column and `[ ]` marker are textual).
- **Reverse-lookup renderer hits a sentence whose `translate` result appears twice** (e.g. `A \vee B` and `(\neg A \rightarrow B)` translate identically): first-seen wins; deterministic if built from `syntax.all_sentences` insertion order (premises then conclusions, outer before inner). Document in the renderer docstring.
- **Overlap with in-flight bimodal tasks** (216, 217, 199): they edit `docs/ADEQUACY.md`, `TRUST_PIPELINE.md`, `state.json`, and a new round-trip ledger -- none touch `semantic/model.py`, `iterate.py`, `README.md` "Sample Output", or `SETTINGS.md`. Coordinate only if phase 7 edits `ARCHITECTURE.md` sections those tasks also touch.

## Context Extension Recommendations

- **Topic**: terminal color/glyph policy for printed model output
  **Gap**: `TESTING_GUIDE.md` section 9 covers encoding fallbacks, but no context or docs file states the color-gating rule (today implicitly `output is sys.__stdout__`), the palette meanings (GREEN/RED top-level truth, WHITE/YELLOW nested, BLUE evaluation point), or `ANSIToMarkdown`'s two-color contract.
  **Recommendation**: add a short "Printed Output Conventions" section to `code/docs/core/CODE_STANDARDS.md` (or a `code/docs/development/OUTPUT_CONVENTIONS.md`) once phase 6 lands, and cite it from `utils/glyphs.py`'s docstring in place of the missing `bimodal/docs/ARCHITECTURE.md` rendering subsection.

## Appendix

- Live-run capture: `/tmp/claude-1000/-home-benjamin-Projects-ModelChecker/bebb3857-abd1-4338-a7e5-b0febf214e12/scratchpad/bimodal_sample.out` (scratch; regenerate with a file setting `example_range` to a subset of `unit_tests` and running `python code/dev_cli.py <file>`).
- Witness-mismatch check: run from `code/` with `PYTHONPATH=src:src/model_checker/theory_lib/bimodal/tests`, build via `_build_support._build(premises, conclusions, back=2, mid=1, fwd=2, verify="off")`, then compare `structure.semantics.witness_registry._witness_lassos` against `[(i, t) for i, l in enumerate(structure.certificate.lassos) for t in _box_window(l) if child not in l.label(t)]`.
- Existing print tests to rewrite: `bimodal/tests/unit/test_structure.py:161-260`, `bimodal/tests/integration/test_output_gate.py:56-140`.
- Old-code line references (Logos repo `bimodal/semantic.py`): `print_proposition` 2177-2226, `print_evaluation` 2391-2432, `_to_subscript` 2437-2442, `format_time` 2444-2455, horizontal renderer 2474-2617, vertical renderer 2639-2757, `print_all` 2759-2786, `print_model_differences` 2908-3045.
- Web sources: [clig.dev](https://clig.dev/), [no-color.org](https://no-color.org/), [Rich Console](https://rich.readthedocs.io/en/latest/console.html), [Rich GitHub](https://github.com/textualize/rich), [Kleene Theorems for Lasso Languages](https://arxiv.org/pdf/2402.13085), [Ultimately periodic words of rational ω-languages](https://link.springer.com/chapter/10.1007/3-540-58027-1_27).
