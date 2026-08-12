# Research Report: Nonexistent CLI Flags in User-Facing Docs

**Task**: 162 — Audit and fix nonexistent CLI flags documented across user-facing docs.
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD

## Verified Ground Truth

`code/src/model_checker/__main__.py`'s `ParseFileFlags._create_parser()` registers exactly:

| Long flag | Short | Notes |
|---|---|---|
| `--load_theory` | `-l` | `choices=theories` from `registry.get_registered()` |
| `--contingent` | `-c` | store_true |
| `--non_null` | `-n` | store_true |
| `--non_empty` | `-e` | store_true |
| `--disjoint` | `-d` | store_true |
| `--maximize` | `-m` | store_true |
| `--save` | `-s` | `nargs='*'`, `choices=['markdown', 'json']` only — **no `notebook`, no `all`** |
| `--sequential` | `-q` | store_true |
| `--align_vertically` | `-a` | store_true |
| `--z3` | (none) | mutually exclusive with `--cvc5` |
| `--cvc5` | (none) | mutually exclusive with `--z3` |
| `--print_constraints` | `-p` | store_true |
| `--print_z3` | `-z` | store_true |
| `--print_impossible` | `-i` | store_true |
| `--version` | `-v` | action=version |
| `--upgrade` | `-u` | store_true |

No `-N`, no `-M`/`--M`, no `--max-time`, no `--verbose`, no `--output-dir`, no `--format`, no `--subtheory`/`-st`, no `--coherence-check`, no `--witness-optimization`, no `--imposition-depth`, no `--state-modification`, no `--save-output`, no `--no-terminal`, no `--iso-debug` exist anywhere in `_create_parser()` or its history.

## Finding 1 — `--subtheory` / `-st` (17 occurrences: WORKFLOW.md, TOOLS.md, PROJECT.md, GETTING_STARTED.md)

**Root cause is deeper than a missing flag.** All four docs frame subtheory selection as a
*project-scaffolding* feature: `model-checker -l logos --subtheory modal` supposedly creates a
project containing only the modal subtheory + its dependencies. This is doubly wrong:

1. `--subtheory`/`-st` do not exist on the CLI parser at all.
2. Even the underlying `BuildProject` class does not implement subtheory filtering.
   `code/src/model_checker/builder/project.py:102` — `__init__(self, theory=None,
   subtheories=None)` — its own docstring for `subtheories` reads **"unused, kept for API
   compatibility"** (line ~110). `__main__.py`'s `-l` branch (`if module_flags.load_theory:
   builder = BuildProject(semantic_theory_name); builder.ask_generate()`) never passes
   `subtheories` at all. Project generation via `-l logos` always copies the complete logos
   template (all subtheories) regardless of any filter.

The real, working mechanism for subtheory selection lives one level down, in the **Python API**
used when instantiating a theory to run/build examples (not when scaffolding a project):
`code/src/model_checker/theory_lib/logos/__init__.py:29` —
`get_theory(config=None, *, subtheories=None)`. Passing `subtheories=['modal']` calls
`LogosOperatorRegistry.load_subtheories(['modal'])`, which (per
`code/src/model_checker/theory_lib/logos/operators.py:41-75`, `load_subtheory`) resolves
`self.dependencies.get(name, [])` and recursively loads dependencies first — this is where
"automatic dependency loading" genuinely happens. It only affects which operators are loaded
into the returned theory dict for that Python session; it has no effect on project scaffolding
or file generation.

**Implication for rewrite**: this is not a token swap (`--subtheory X` → some other flag). The
prose needs restructuring: (a) `-l logos` always scaffolds the full logos project; (b) subtheory
filtering is something you do in code — typically inside the generated project's own
`examples.py`/`semantic.py`, or in an ad hoc script — via
`from model_checker.theory_lib import logos; theory = logos.get_theory(subtheories=['modal'])`;
(c) dependency auto-loading happens inside `get_theory`/`load_subtheory`, not the CLI.

Occurrence sites confirmed via grep:
- `docs/usage/WORKFLOW.md`: lines 30-32, 43, 410
- `docs/usage/TOOLS.md`: lines 201-203
- `docs/usage/PROJECT.md`: lines 20-22, 117-119
- `docs/installation/GETTING_STARTED.md`: lines 217-219

## Finding 2 — `--verbose` (PIPELINE.md, ITERATE.md, SETTINGS.md [architecture], OUTPUT.md, TOOLS.md)

No `verbose` CLI flag, and no `verbose` key in any theory's `DEFAULT_GENERAL_SETTINGS`/
`DEFAULT_EXAMPLE_SETTINGS`/`ADDITIONAL_GENERAL_SETTINGS` (checked bimodal, logos, exclusion,
imposition). The only real "verbose" mechanism in the codebase is the environment variable
`MODELCHECKER_VERBOSE` (`code/src/model_checker/settings/settings.py:31`:
`VERBOSE_SETTINGS = os.environ.get('MODELCHECKER_VERBOSE', '').lower() == 'true'`).

Occurrence sites:
- `docs/architecture/PIPELINE.md`: line 56 (`--save --verbose --format json`), line 356 (diagram
  box listing `--verbose` as a CLI flag), line 420 (`--verbose --save`)
- `docs/architecture/ITERATE.md`: line 1094 (`# Debug messages (with --verbose)`)
- `docs/architecture/SETTINGS.md`: line 22 (diagram box: `• --verbose  Overrides all other
  settings`)
- `docs/usage/OUTPUT.md`: line 353 (`--verbose \` in a multi-line save command)
- `docs/usage/TOOLS.md`: line 434 (`--save json --verbose`)

Recommended fix: replace CLI `--verbose` mentions with the `MODELCHECKER_VERBOSE=true` env var
where the doc is demonstrating debug output, or simply delete the flag from example command
lines where it isn't load-bearing to the example. `ITERATE.md`'s `DEBUG_CONFIG` dict also sets
`'verbose': True` as if it were a settings-dict key (line ~918) — that is equally fictional and
should be corrected or removed in the same pass since it's adjacent to the `--iso-debug` finding
below.

## Finding 3 — `--output-dir` and `--format` (OUTPUT.md, PIPELINE.md)

Neither exists on the parser, and **there is currently no CLI-level way to control the output
directory or format-selection independent of `--save`'s own `choices`.**
`code/src/model_checker/output/manager.py:88` — `create_output_directory(self, custom_name:
str = None)` supports a custom name parameter, but `code/src/model_checker/builder/module.py:166`
calls it as `self.output_manager.create_output_directory()` — no argument, ever. The output
directory is always the auto-generated `output_<timestamp>/`. `--format` doesn't exist at all;
`--save`'s own `nargs='*'` positional-style arguments (`markdown`/`json`) already serve as format
selection (`--save json`, not `--save --format json`).

**Related live code bug (not docs, but the same fabrication baked into source):**
`code/src/model_checker/output/errors.py:38` — `OutputDirectoryError`'s default suggestion text
for a permission error reads `"Check write permissions or use --output-dir flag"`. This is a
real, user-visible runtime error message that recommends a flag that has never existed. Worth
flagging to the planner as an in-scope or closely-adjacent fix even though it's source, not docs,
because a user hitting this error and trying `--output-dir` gets "unrecognized arguments" —
exactly the failure mode this task exists to eliminate.

Occurrence sites:
- `docs/usage/OUTPUT.md`: lines 354, 376, 390, 417 (`--output-dir`); line 448 also has an
  unrelated but equally fictional `--no-terminal` (see Finding 5 below)
- `docs/architecture/PIPELINE.md`: line 56 (`--format json`)

Recommended fix: rewrite these examples to state the output directory is auto-named
`output_<timestamp>/` (or, if `--save` is given a bare/explicit form, describe actual behavior),
and drop `--format` in favor of `--save json`/`--save markdown`.

## Finding 4 — `code/src/model_checker/settings/README.md` "Theory-Specific Flags" section

**Verdict: never real, not planned-and-dropped.** Evidence:
- `git log --all -p -S <token>` for `coherence_check`, `witness_optimization`,
  `imposition_depth`, `state_modification`, and `'-M'` against `__main__.py` returns **zero**
  hits in the entire repo history — these strings have never appeared in the parser at any
  commit.
- None of `coherence_check`, `witness_optimization`, `imposition_depth`, `state_modification`
  appear anywhere in `DEFAULT_EXAMPLE_SETTINGS`/`ADDITIONAL_GENERAL_SETTINGS` for the exclusion
  theory (`code/src/model_checker/theory_lib/exclusion/semantic/core.py:93` — real keys are
  `N, possible, contingent, non_empty, non_null, disjoint, fusion_closure, iterate, max_time,
  expectation`) or the imposition theory (`code/src/model_checker/theory_lib/imposition/
  semantic/core.py:92` — real keys are `N, contingent, non_empty, non_null, disjoint, max_time,
  iterate, expectation`, plus `ADDITIONAL_GENERAL_SETTINGS = {"derive_imposition": False}`).
  These names are wholesale invention, not a renamed/removed real feature.
- `M` **is** real, but only as a per-example settings-dict key for bimodal
  (`DEFAULT_EXAMPLE_SETTINGS['M']`, `bimodal/semantic/core.py:51`) — it has never been a CLI
  flag (`-M`/`--M`). The doc conflates "settings dict key" with "CLI flag."
- `save_output` **is** real as a settings-dict key (`SemanticDefaults.DEFAULT_GENERAL_SETTINGS`,
  many files) but, again, was never exposed as a `--save-output` CLI flag.

Recommended fix: delete or substantially rewrite the "Theory-Specific Flags" subsection
(lines 222-234) to stop presenting these as CLI flags. If the settings themselves
(`derive_imposition` for imposition, `M`/`align_vertically` for bimodal) are worth documenting,
present them correctly as example-file/general-settings dict keys, not CLI flags, consistent with
the file's own "Theory-Specific Configuration" section higher up (which already does this
correctly for `align_vertically` and `derive_imposition`).

### Scope note: settings/README.md has MORE nonexistent-flag issues than the 12 named in the task

The task's out-of-scope list ("hyphenated long-flag spellings ... already fixed separately")
names only `docs/usage/{SETTINGS,SEMANTICS,TOOLS,README,PROJECT}.md` and
`logos/docs/USER_GUIDE.md`. **`code/src/model_checker/settings/README.md` is not on that list**,
and it independently contains the same class of hyphenation bugs, plus two more fully-fictional
flags, all inside the same "Available Command-Line Flags"/"Usage Examples" sections that
surround the named "Theory-Specific Flags" block:

| Line(s) | Text | Problem |
|---|---|---|
| 31 | `# --print-z3, --contingent, etc.` | hyphenated; real flag is `--print_z3` |
| 195 | `./dev_cli.py -N 4 --contingent --print-z3 examples/modal.py` | `-N` does not exist (N is settings-dict only); `--print-z3` hyphenated |
| 215-216 | `` `--non-empty` ``, `` `--non-null` `` | hyphenated; real flags are `--non_empty`, `--non_null` |
| 225 | `` `-M <int>` or `--M <int>` `` | fully fictional (Finding 4 above) |
| 226 | `` `--align-vertically` `` | hyphenated; real flag is `--align_vertically` |
| 238-240 | `` `--print-impossible` ``, `` `--print-constraints` or `-p` ``, `` `--print-z3` or `-z` `` | first and third are hyphenated (real: `--print_impossible`, `--print_z3`); `-p` line is correct |
| 258 | `model-checker --contingent --non-null examples/test.py` | hyphenated |
| 261 | `model-checker -p -z --contingent --non-empty examples/complex.py` | hyphenated |
| 264 | `model-checker --M 4 --align-vertically examples/bimodal_test.py` | `--M` fictional; `--align-vertically` hyphenated |
| 268 | `model-checker --print-z3 --print-constraints --print-impossible --max-time=10000 examples/debug.py` | all three hyphenated; `--max-time` additionally fictional as a CLI flag (max_time is settings-dict only, no CLI equivalent at any spelling) |

Two illustrative Python-source blocks in the "Implementing New Settings" section (lines 480-497)
use `--your-setting`/`-ys` and `--complexity-level`/`-cl` as **hypothetical** examples of how a
developer would register a *new* argparse entry — these are clearly framed as instructional code
(`# In cli.py - add argument parser entries`) rather than claims about existing flags, so they
are not bugs, but they are worth keeping in mind when designing the regression guard (see below)
so it doesn't false-positive on them.

Recommend the planner treat `settings/README.md` as needing a full pass, not just the
12-occurrence "Theory-Specific Flags" subsection, since the surrounding sections share the file
and the same class of defect.

## Additional findings beyond the four named items (for planner triage)

Found while grepping every `--[a-z-]+` token in the affected files; not explicitly named in the
task description but same defect class and in directly adjacent text:

1. **`--save notebook` / `--save all`** are not valid `--save` values — the parser's `choices`
   are only `['markdown', 'json']`. `docs/usage/OUTPUT.md` documents `notebook` extensively
   (lines 12, 123-127, 154, 254-255, 285, 387-393, 441) and `all` at least once implicitly (line
   173 shows bare `--save` described as "Save in all formats", which actually matches current
   bare-`--save` behavior — that line is arguably fine — but `docs/usage/TOOLS.md:440` has
   literal `--save all --output-dir comparisons/`, and OUTPUT.md's own internal contradiction at
   lines 151-155 shows `--save` (bare) described twice, once as "Interactive mode - prompts for
   format" (inaccurate — bare `--save` does not prompt, it saves both formats per
   `test_flag_matrix.py::test_save_bare_produces_markdown_and_json`) and once as "Save in all
   formats" (accurate). `notebook` as a format has residual internal plumbing
   (`code/src/model_checker/output/constants.py:6` `FORMAT_NOTEBOOK = 'notebook'`, referenced in
   `output/errors.py`, `output/helpers.py`, `builder/module.py`, `builder/project.py`,
   `builder/runner.py`) but it is **not** wired into the CLI `--save` `choices`, so it cannot
   currently be requested from the command line at all.
2. **`--no-terminal`** (`docs/usage/OUTPUT.md:448`, "Disable terminal output when saving - Use
   `--no-terminal`") does not exist on the parser.
3. **`--iso-debug`** (`docs/architecture/ITERATE.md:926`, `./dev_cli.py --iso-debug
   examples/iterate_test.py`) does not exist on the parser.

These are the same bug class (nonexistent CLI flag documented as real) in the same files already
being touched for Findings 2 and 3, so fixing them in the same pass is low-marginal-cost; leaving
them would mean the new regression test (below) fails immediately unless they're also fixed or
explicitly excluded, since a flag-token extractor cannot distinguish "explicitly out of task
scope" from "genuinely broken."

## Regression Guard Design

No existing test extracts flags from markdown. `code/tests/cli/test_flag_matrix.py` already has
the complementary check in the other direction
(`test_every_registered_flag_is_covered_or_excluded`, lines 46-62) — it walks
`ParseFileFlags().parser._actions` and asserts every registered flag is either dispatch-tested or
explicitly excluded. The new guard should walk the same `parser._actions` list to build the
canonical `{'--load_theory', '-l', '--contingent', '-c', ...}` allowed-token set (never a
hand-transcribed copy — `test_help_lists_every_registered_long_flag`, lines 84-97, shows the
established idiom of deriving expected content from `parser._actions` rather than a literal
list), plus always-allow `-h`/`--help` (argparse auto-adds these; they are not in `_actions`
under a custom dest but should be allowlisted explicitly since `-h`/`--help` are legitimately
documented everywhere).

Suggested shape (new file, e.g. `code/tests/cli/test_docs_flag_matrix.py`, or a new test class
appended to `test_flag_matrix.py`):

1. **File scope**: glob the doc set actually touched by this task plus siblings in the same
   directories — `docs/usage/*.md`, `docs/architecture/*.md`, `docs/installation/*.md`,
   `code/src/model_checker/settings/README.md`, `code/src/model_checker/theory_lib/*/docs/*.md`,
   `code/README.md`, `README.md`. Recommend the planner decide explicitly whether `code/docs/**`
   (internal dev-standards docs, much larger surface, more prose-only false-positive risk) is
   in scope for the guard or deliberately excluded — this report doesn't find any current
   violations there but hasn't exhaustively read that tree's CLI-example blocks.
2. **Extraction scope**: only scan fenced code blocks whose language tag is
   `bash`/`sh`/`shell`/`console` (or, defensively, blocks whose content contains `model-checker`
   or `dev_cli.py`), **not** ` ```python ` blocks — this is what naturally excludes
   `settings/README.md`'s hypothetical `parser.add_argument('--your-setting', ...)` illustration
   from being treated as a documented-as-real flag, without needing a special-case allowlist for
   that one Python snippet.
3. **Token regex**: within qualifying blocks, match `(?<!\w)--[a-zA-Z][a-zA-Z0-9_-]*` for long
   flags and `(?<!\w)-[a-zA-Z](?![a-zA-Z0-9_-])` for single-letter short flags — but also needs to
   catch multi-letter short-form typos like `-st` (not a valid argparse short flag pattern at
   all, since this project's short flags are always exactly one character); a token matching
   `-[a-zA-Z]{2,}` that isn't a recognized long flag should be flagged as invalid on sight (it's
   never valid regardless of the allowed-flags set, since this parser has no multi-letter short
   options).
4. **Assertion**: every extracted long-flag token must be in the parser's registered
   `option_strings` (plus `--help`); every extracted single-letter short-flag token must likewise
   be registered (plus `-h`); every multi-letter single-hyphen token is unconditionally a
   failure. Report file:line:token in the failure message the same way
   `test_every_registered_flag_is_covered_or_excluded` reports set differences, so a future
   doc-drift failure is immediately actionable.
5. Consider a narrow allowlist mechanism (e.g. an inline HTML comment marker
   `<!-- doc-flag-lint: ignore-next -->` or a per-file/per-line exclusion tuple in the test) for
   any genuinely-intentional non-flag-like `--word` tokens that might appear in code fences for
   unrelated tools (none observed in this audit, but e.g. a `git diff --stat` example would false
   positive if the extractor isn't scoped tightly enough to `model-checker`/`dev_cli.py`
   invocation lines).

## Files with confirmed current uncommitted changes (context, not touched by this research)

Per the task's note, `README.md`, `code/README.md`, `code/src/model_checker/__main__.py`,
`code/src/model_checker/theory_lib/logos/docs/USER_GUIDE.md`,
`code/tests/cli/test_flag_matrix.py`, and `docs/usage/{PROJECT,README,SEMANTICS,SETTINGS,
TOOLS}.md` already carry uncommitted fixes for the swapped `--non_null`/`--non_empty` help
strings and hyphenated-flag-spelling cleanup. This audit did not re-verify or duplicate that
work; the counts and line numbers above are from the current working-tree state (post those
uncommitted edits), confirmed by re-grepping after reading the diffs were present.
