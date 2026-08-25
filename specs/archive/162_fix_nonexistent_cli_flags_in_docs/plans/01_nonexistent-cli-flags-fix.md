# Implementation Plan: Fix Nonexistent CLI Flags in Docs

- **Task**: 162 - Audit and fix nonexistent CLI flags documented across user-facing docs
- **Status**: [COMPLETED]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: specs/162_fix_nonexistent_cli_flags_in_docs/reports/01_nonexistent-cli-flags-audit.md
- **Artifacts**: plans/01_nonexistent-cli-flags-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

User-facing documentation advertises CLI flags that the argparse parser
(`model_checker.__main__.ParseFileFlags._create_parser()`) has never registered, so copy-pasted
example commands fail with `unrecognized arguments`. This plan builds an executable regression
guard first (a doc-flag lint that derives its allowed-token set from `parser._actions`, never a
hand-transcribed list), demonstrates RED against the current documentation tree, then fixes the
documentation in file-owned parallel phases, fixes one live source-side fabrication in
`output/errors.py`, and finally flips the guard to a hard-failing test. Definition of done: the
doc-flag lint passes with no `xfail`, the existing CLI suites still pass, and no invocation line
in the scanned documentation set names a flag that the parser (or the `dev_cli.py` wrapper)
does not accept.

### Research Integration

The research report's verified parser inventory, `--subtheory` root-cause analysis (subtheory
filtering is a Python-API concern, `logos.get_theory(subtheories=[...])`, never a CLI or
scaffolding concern — `BuildProject.__init__`'s `subtheories` parameter is documented in-source
as "unused, kept for API compatibility"), the `settings/README.md` "never real, not
planned-and-dropped" verdict, and the proposed extractor design are all adopted directly. Two
report conclusions are amended by plan-time verification against the working tree:

1. **`--iso-debug` IS real.** It is a `code/dev_cli.py` wrapper flag consumed before argparse
   (`if "--iso-debug" in sys.argv: ... sys.argv.remove("--iso-debug")`), alongside the `-load` /
   `--load` aliases the same block rewrites to `-l`. `docs/architecture/ITERATE.md:926` and
   `code/README.md:259` are therefore correct and MUST NOT be "fixed"; the guard must model a
   two-tier vocabulary (argparse flags + dev_cli wrapper flags).
2. **The violation set is larger than the report's four findings.** A plan-time prototype of the
   proposed extractor over 204 markdown files surfaced additional fabricated flags the report did
   not name: `--benchmark` and `--test-all-settings` (`docs/usage/PROJECT.md`), `--profile`
   (`docs/installation/DEVELOPER_SETUP.md`), `--generate-license` / `--base-theory` / `--author`
   / `--theory-name` (`code/docs/contracts/THEORY_LICENSING.md`), and `-t`
   (`code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`). These are handled in Phase 7.

The report's open question — whether `code/docs/**` is in guard scope — is decided here: **yes,
in scope.** The prototype found exactly one genuine violation there (`THEORY_LICENSING.md`) and
its only false positive (`grep -E` downstream of a pipe) is eliminated by the pipeline-truncation
rule in Phase 1 rather than by narrowing scope.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context, so no roadmap phases are included.
`specs/ROADMAP.md` exists and its "Durable Decisions" section establishes the relevant precedent
this plan follows: correctness invariants in this repository are enforced by executable tests
(`test_layering.py`, `test_theory_conformance.py`), not by prose promises. The doc-flag lint is
the same pattern applied to documentation.

## Goals & Non-Goals

**Goals**:
- Add an executable regression guard that extracts flag tokens from markdown invocation lines and
  asserts each is registered on `ParseFileFlags().parser` (or is a known `dev_cli.py` wrapper flag).
- Remove or rewrite every documented CLI flag that the parser does not accept, across
  `docs/**`, `code/docs/**`, `code/src/model_checker/**/*.md`, `code/README.md`, and `README.md`.
- Restructure `--subtheory` prose to teach the real mechanism (`logos.get_theory(subtheories=[...])`)
  rather than swapping one token for another.
- Fix the live, user-visible `--output-dir` recommendation in
  `code/src/model_checker/output/errors.py`.

**Non-Goals**:
- Implementing any of the fabricated flags (`--subtheory`, `--verbose`, `--output-dir`,
  `--format`, `--no-terminal`, `--benchmark`, `--profile`, `--generate-license`, `-t`, `-N`,
  `--max-time`, `-M`). No new argparse entry is added by this task.
- Wiring the residual `notebook` output plumbing (`output/constants.py FORMAT_NOTEBOOK`) into
  `--save`'s `choices`. Docs stop advertising it; the plumbing is left untouched.
- Re-doing the uncommitted hyphenated-spelling and `--non_null`/`--non_empty` help-string fixes
  already present in the working tree for `README.md`, `code/README.md`, `__main__.py`,
  `logos/docs/USER_GUIDE.md`, `test_flag_matrix.py`, and `docs/usage/{PROJECT,README,SEMANTICS,SETTINGS,TOOLS}.md`.
- Linting prose mentions outside shell invocation lines. The guard covers invocation lines only;
  diagram boxes and narrative mentions are fixed by hand in Phases 3-7 (see Risks).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Extractor false-positives on other tools' flags sharing a line (`pip install --user`, `ls -la`, `grep -E`, `cProfile -o`) | H | H | Match only lines whose first token is a `model-checker` / `dev_cli.py` / `python -m model_checker` invocation, and truncate at the first `\|`, `&&`, `\|\|`, `;`, or redirection operator. Phase 1 ships explicit negative unit tests for each of these four observed cases. |
| `--iso-debug` / `-load` / `--load` wrongly "fixed" out of correct docs | M | M | Phase 1 defines `_DEV_CLI_WRAPPER_FLAGS` with a companion test asserting each literal is still present in `code/dev_cli.py`, so removing the wrapper flag breaks the test rather than silently widening the allowlist. |
| Committing a red test violates git-workflow's no-partial-commit rule | M | H | Phase 2 lands the doc-scan test under `@pytest.mark.xfail(strict=True)`. Every commit is green; `strict=True` makes the eventual xpass a hard failure, mechanically forcing the Phase 8 flip. |
| Report line numbers drift (working tree has uncommitted edits to several targets) | M | H | Every phase re-greps its owned files rather than trusting report line numbers, and confirms its own token count against the lint output before closing. |
| Doc phases 3-7 collide on shared files | M | M | Phases own whole files, not flag families. `docs/usage/TOOLS.md` and `docs/usage/PROJECT.md` each belong to exactly one phase including their off-theme tokens. |
| Guard blind spot: prose/diagram mentions are not invocation lines and pass silently | M | H | Accepted and documented. Phases 4 and 5 fix the known prose sites (`ITERATE.md:1094` comment, `ITERATE.md` `DEBUG_CONFIG['verbose']`, `SETTINGS.md:22` diagram box, `OUTPUT.md:448` `--no-terminal` bullet) by hand and record the blind spot in the test module docstring. |
| Discarding the working tree's existing uncommitted fixes | H | L | No `git checkout`/`reset` on target files at any point; edits are additive to the current working-tree state. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 5, 6, 7 | 2 |
| 4 | 8 | 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel. Wave 3 phases own disjoint file sets and may
be dispatched concurrently.

---

### Phase 1: Doc-flag extractor and allowed-token derivation [COMPLETED]

**Goal**: Build the machinery of the regression guard — allowed-token derivation and the token
extractor — with its own unit tests passing, before any documentation is scanned.

**Tasks**:
- [x] Create `code/tests/cli/test_docs_flag_matrix.py` with a module docstring recording (a) that
      the allowed set is derived from `parser._actions`, never hand-transcribed, and (b) the
      declared blind spot: only shell invocation lines inside fenced code blocks are scanned;
      prose and diagram mentions are not.
- [x] Implement `_registered_option_strings()` returning every `opt` from
      `ParseFileFlags().parser._actions` `option_strings`, plus `-h`/`--help` (argparse builtins),
      following the idiom of `test_help_lists_every_registered_long_flag`.
- [x] Implement `_DEV_CLI_WRAPPER_FLAGS = {'--iso-debug', '--load', '-load'}` with an inline
      comment citing `code/dev_cli.py`'s pre-argparse `sys.argv` rewriting block.
- [x] Add `test_dev_cli_wrapper_flags_still_exist()` asserting each literal appears in
      `code/dev_cli.py`'s source, so allowlist drift fails loudly.
- [x] Implement `_iter_invocations(text)`: walk fenced blocks, admit only ` ```bash `/` ```sh `/
      ` ```shell `/` ```console `/untagged blocks, join trailing-backslash continuations, strip a
      leading `$ ` prompt and `PYTHONPATH=...` prefix, match only lines beginning with
      `model-checker`, `./dev_cli.py`, `dev_cli.py`, or `python -m model_checker`, and truncate at
      the first `|`, `&&`, `||`, `;`, or redirection operator. Yield `(line_number, command)`.
- [x] Implement `_extract_flag_tokens(command)` yielding long (`--foo`) and short (`-f`) tokens,
      classifying any `-[a-zA-Z]{2,}` single-hyphen token as unconditionally invalid (this parser
      has no multi-letter short options — this is what catches `-st`).
- [x] Add extractor unit tests over inline fixture strings covering: a valid invocation passes;
      ` ```python ` blocks are skipped (the `parser.add_argument('--your-setting', ...)`
      illustration in `settings/README.md`); `pip install --user model-checker` is not an
      invocation; `ls -la` / `apt ... -y` are not invocations; `./dev_cli.py ... | grep -E "..."`
      truncates before `-E`; `python -m cProfile -o profile.stats dev_cli.py ...` is not an
      invocation; a backslash-continued multi-line invocation is joined; `-st` is reported.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: one new file, `code/tests/cli/test_docs_flag_matrix.py`, and no edits to
existing files. Confirm by `git status --short` showing exactly one added path under
`code/tests/cli/` before committing.

**Files to modify**:
- `code/tests/cli/test_docs_flag_matrix.py` - new file: allowed-token derivation, extractor, and
  extractor unit tests

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/cli/test_docs_flag_matrix.py -v` passes (extractor unit
  tests only; no doc scan exists yet).

---

### Phase 2: Doc-scan test (RED demonstration) and violation inventory [COMPLETED]

**Goal**: Point the extractor at the real documentation tree, demonstrate RED with a complete,
actionable violation inventory, and land it in a committable (green) state via a strict xfail.

**Tasks**:
- [x] Add `_DOC_GLOBS` to the test module: `docs/**/*.md`, `code/docs/**/*.md`,
      `code/src/model_checker/**/*.md`, `code/README.md`, `README.md`. Explicitly exclude
      `specs/**` and `.claude/**` (task artifacts deliberately quote broken flags) with a comment
      stating why.
- [x] Add `test_documented_flags_are_registered()` asserting every extracted token is registered
      or a dev_cli wrapper flag, failing with a sorted `file:line: token` report modeled on
      `test_every_registered_flag_is_covered_or_excluded`'s set-difference message style.
- [x] Add a sanity assertion that the scan visited a non-trivial number of files, so a broken glob
      cannot produce a vacuous pass.
- [x] Run the test, capture the full failure output, and write the inventory to
      `specs/162_fix_nonexistent_cli_flags_in_docs/reports/02_violation-inventory.md`, grouped by
      the owning phase (3-7).
- [x] Mark `test_documented_flags_are_registered` with
      `@pytest.mark.xfail(strict=True, reason="RED until docs are fixed; xfail removed in Phase 8")`
      so the commit is green and the eventual xpass hard-fails.

**Timing**: 45 minutes

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: the prototype scan predicts **10 violating files and roughly 47 violating
tokens** across the declared globs. Confirm by recording the actual failure output in
`02_violation-inventory.md`; if the real count differs materially, reconcile the phase-to-file
ownership below before proceeding to Wave 3 and note the discrepancy in the inventory.

**Files to modify**:
- `code/tests/cli/test_docs_flag_matrix.py` - add doc globs and the scanning test (xfail)
- `specs/162_fix_nonexistent_cli_flags_in_docs/reports/02_violation-inventory.md` - new file

**Verification**:
- The scanning test reports XFAIL (not PASS, not ERROR) and the captured output enumerates
  concrete `file:line: token` triples.
- `PYTHONPATH=code/src pytest code/tests/cli/ -q` is green overall.

---

### Phase 3: Rewrite subtheory prose in WORKFLOW.md, PROJECT.md, GETTING_STARTED.md [COMPLETED]

**Goal**: Replace the `--subtheory`/`-st` project-scaffolding fiction with the real Python-API
mechanism, and clear the remaining fabricated flags in these three owned files.

**Tasks**:
- [x] `docs/usage/WORKFLOW.md`: rewrite the `--subtheory`/`-st` passages to state that
      `model-checker -l logos` scaffolds the complete logos project (all subtheories), and that
      subtheory selection happens in code via
      `from model_checker.theory_lib import logos; theory = logos.get_theory(subtheories=['modal'])`.
- [x] Relocate the "automatic dependency loading" claim to where it is true:
      `LogosOperatorRegistry.load_subtheory` resolves and recursively loads declared dependencies
      when `get_theory(subtheories=[...])` is called — it affects which operators are loaded in
      that Python session, not which files are generated.
- [x] `docs/usage/PROJECT.md`: apply the same rewrite to its two `--subtheory` passages.
- [x] `docs/usage/PROJECT.md`: remove or replace the fabricated `model-checker examples.py
      --test-all-settings` and `model-checker examples.py --benchmark` examples (neither flag nor
      any equivalent exists).
- [x] `docs/installation/GETTING_STARTED.md`: apply the same `--subtheory` rewrite.
- [x] Re-grep all three files for `subtheory`, `-st`, `--benchmark`, `--test-all-settings` and
      confirm no remaining claim presents them as CLI flags.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: 16 violating tokens across these three files (WORKFLOW.md 5, PROJECT.md 8,
GETTING_STARTED.md 3). Confirm by re-running the doc lint restricted to these three paths and
observing zero remaining tokens for them.

**Files to modify**:
- `docs/usage/WORKFLOW.md` - subtheory prose restructure
- `docs/usage/PROJECT.md` - subtheory prose restructure; drop `--test-all-settings`, `--benchmark`
- `docs/installation/GETTING_STARTED.md` - subtheory prose restructure

**Verification**:
- The doc lint (run ad hoc against these three paths) reports zero tokens for them.
- Any replacement Python snippet is import-checkable:
  `PYTHONPATH=code/src python -c "from model_checker.theory_lib import logos; logos.get_theory(subtheories=['modal'])"`.

---

### Phase 4: Fix output and tools usage docs [COMPLETED]

**Goal**: Correct every fabricated flag and every fabricated `--save` value in the two owned
usage docs, including the prose-only claims the guard cannot see.

**Tasks**:
- [x] `docs/usage/OUTPUT.md`: remove `--output-dir` from every example; state instead that the
      output directory is always the auto-generated `output_<timestamp>/`
      (`OutputManager.create_output_directory()` is called with no argument from
      `builder/module.py`, so no CLI-level override exists).
- [x] `docs/usage/OUTPUT.md`: remove `--verbose` from example command lines.
- [x] `docs/usage/OUTPUT.md`: remove `notebook` as a documented `--save` value throughout —
      `--save`'s `choices` are `['markdown', 'json']` only; note in a sentence that notebook
      export is not currently reachable from the CLI.
- [x] `docs/usage/OUTPUT.md`: resolve the bare-`--save` self-contradiction — delete the
      "Interactive mode - prompts for format" description (bare `--save` writes both formats, per
      `test_save_bare_produces_markdown_and_json`) and keep the accurate "Save in all formats".
- [x] `docs/usage/OUTPUT.md`: delete the `--no-terminal` bullet (prose-only; the guard will not
      catch it).
- [x] `docs/usage/TOOLS.md`: apply the Phase 3 subtheory rewrite to its `--subtheory`/`-st`
      passage (this file is owned here, not by Phase 3).
- [x] `docs/usage/TOOLS.md`: remove `--verbose`; replace `--save all --output-dir comparisons/`
      with a valid invocation.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: 10 guard-visible tokens (OUTPUT.md 5, TOOLS.md 5) plus at least two
prose-only sites in OUTPUT.md (`--no-terminal`, the notebook format discussion) that the guard
cannot detect. Confirm the guard-visible half by re-running the lint on these two paths; confirm
the prose half by grepping both files for `no-terminal`, `notebook`, `verbose`, `output-dir`.

**Files to modify**:
- `docs/usage/OUTPUT.md` - drop `--output-dir`, `--verbose`, `--no-terminal`, notebook-as-format;
  fix bare-`--save` contradiction
- `docs/usage/TOOLS.md` - subtheory rewrite; drop `--verbose`, `--save all`, `--output-dir`

**Verification**:
- Doc lint reports zero tokens for both paths.
- `grep -n -- '--output-dir\|--verbose\|--no-terminal\|--save all' docs/usage/OUTPUT.md docs/usage/TOOLS.md`
  returns nothing.

---

### Phase 5: Fix architecture docs [COMPLETED]

**Goal**: Remove the `--verbose` and `--format` fictions from the three owned architecture docs
while preserving the genuinely real `--iso-debug`.

**Tasks**:
- [x] `docs/architecture/PIPELINE.md`: remove `--verbose` and `--format json` from example
      command lines; where format selection is being illustrated, use `--save json` /
      `--save markdown`.
- [x] `docs/architecture/PIPELINE.md`: remove `--verbose` from the CLI-flags diagram box.
- [x] `docs/architecture/SETTINGS.md`: remove the `• --verbose Overrides all other settings`
      diagram entry; if a debug-output mechanism is worth naming there, name the real one, the
      `MODELCHECKER_VERBOSE=true` environment variable (`settings/settings.py`'s
      `VERBOSE_SETTINGS`).
- [x] `docs/architecture/ITERATE.md`: fix the `# Debug messages (with --verbose)` comment to
      reference `MODELCHECKER_VERBOSE=true`.
- [x] `docs/architecture/ITERATE.md`: remove or correct the `DEBUG_CONFIG` dict's `'verbose': True`
      entry, which presents a nonexistent settings key.
- [x] `docs/architecture/ITERATE.md`: leave the `./dev_cli.py --iso-debug` example unchanged and
      add a short note that it is a `dev_cli.py` wrapper flag, not a `model-checker` flag.

**Timing**: 45 minutes

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: 3 guard-visible tokens (all in PIPELINE.md) plus 3 prose/diagram-only sites
(SETTINGS.md diagram, ITERATE.md comment, ITERATE.md `DEBUG_CONFIG`). Confirm by re-running the
lint on all three paths and grepping them for `verbose` and `--format`.

**Files to modify**:
- `docs/architecture/PIPELINE.md` - drop `--verbose`, `--format`
- `docs/architecture/SETTINGS.md` - drop `--verbose` diagram entry
- `docs/architecture/ITERATE.md` - fix verbose comment and `DEBUG_CONFIG`; annotate `--iso-debug`

**Verification**:
- Doc lint reports zero tokens for all three paths.
- `grep -rn -- '--verbose\|--format' docs/architecture/` returns nothing.
- `grep -n -- '--iso-debug' docs/architecture/ITERATE.md` still returns the preserved example.

---

### Phase 6: Rewrite settings/README.md flag documentation [COMPLETED]

**Goal**: Bring `code/src/model_checker/settings/README.md` fully in line with the real parser —
this file needs a whole-file pass, not just the named "Theory-Specific Flags" subsection.

**Tasks**:
- [x] Delete or rewrite the "Theory-Specific Flags" subsection: `--coherence-check`,
      `--witness-optimization`, `--imposition-depth`, `--state-modification`, `--save-output`, and
      `-M`/`--M` were never real (verified by `git log --all -S` returning zero hits repo-wide).
- [x] Where the underlying setting genuinely exists, document it correctly as a settings-dict key
      rather than a CLI flag — `M` (bimodal `DEFAULT_EXAMPLE_SETTINGS`), `save_output`
      (`SemanticDefaults.DEFAULT_GENERAL_SETTINGS`), `derive_imposition` (imposition
      `ADDITIONAL_GENERAL_SETTINGS`) — matching the file's own already-correct "Theory-Specific
      Configuration" section.
- [x] Fix every hyphenated long-flag spelling in this file: `--print-z3`, `--print-constraints`,
      `--print-impossible`, `--non-empty`, `--non-null`, `--align-vertically` become their
      underscore forms.
- [x] Remove `-N` from the `./dev_cli.py -N 4 ...` example — `N` is a settings-dict key with no
      CLI equivalent at any spelling.
- [x] Remove `--max-time=10000` from the debug example — `max_time` is likewise settings-dict only.
- [x] Leave the "Implementing New Settings" Python illustrations (`--your-setting`,
      `--complexity-level`) untouched; they are inside ` ```python ` blocks and are correctly
      framed as instructional, and Phase 1's block-language filter already excludes them.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: 12 guard-visible tokens in this one file (`--M`, `--align-vertically`,
`--coherence-check`, `--max-time`, `--non-empty`, `--non-null`, `--print-constraints`,
`--print-impossible`, `--print-z3`, `--witness-optimization`, `-N`), plus additional
non-invocation-line mentions in the flag reference tables. Confirm by re-running the lint on this
path and separately grepping the file for each fabricated token.

**Files to modify**:
- `code/src/model_checker/settings/README.md` - whole-file flag-documentation pass

**Verification**:
- Doc lint reports zero tokens for this path.
- `grep -n -- '--print-z3\|--non-empty\|--non-null\|--align-vertically\|--print-constraints\|--print-impossible\|--max-time\|--M\|-N \|coherence-check\|witness-optimization\|imposition-depth\|state-modification\|save-output' code/src/model_checker/settings/README.md`
  returns only intentional settings-dict-key mentions, if any.

---

### Phase 7: Residual docs sweep and the output/errors.py source fix [COMPLETED]

**Goal**: Clear the remaining fabricated flags found outside the report's four findings, and fix
the one live runtime message that recommends a flag that never existed.

**Tasks**:
- [x] `code/docs/contracts/THEORY_LICENSING.md`: remove or rewrite the "Automated License
      Generation" invocation — `--generate-license`, `--base-theory`, `--author`, and
      `--theory-name` do not exist. If no such automation exists, delete the claim rather than
      restating it in another form.
- [x] `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`: replace `model-checker -t
      my_test_name` with the real invocation (`PYTHONPATH=code/src pytest ... -k my_test_name`).
- [x] `docs/installation/DEVELOPER_SETUP.md`: remove `./dev_cli.py --profile examples/slow.py`;
      the file already shows the working alternative (`python -m cProfile -o profile.stats
      dev_cli.py examples/slow.py`).
- [x] `code/src/model_checker/output/errors.py`: change `OutputDirectoryError`'s permission-branch
      default suggestion from "Check write permissions or use --output-dir flag" to text that
      names no nonexistent flag.
- [x] Add a unit test asserting no `OutputDirectoryError` default suggestion string names an
      unregistered `--flag` token, reusing the Phase 1 allowed-token derivation.
- [x] `code/README.md`: confirm the `--iso-debug` mention is framed as a `dev_cli.py` flag; adjust
      wording only if it implies a `model-checker` flag. Do not delete it.

**Timing**: 45 minutes

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: 6 guard-visible tokens across three markdown files (THEORY_LICENSING.md 4,
CONTRIBUTING.md 1, DEVELOPER_SETUP.md 1), plus one source-string fix in `output/errors.py` that
the doc lint does not cover. Confirm the markdown half via the lint; confirm the source half via
the new unit test.

**Files to modify**:
- `code/docs/contracts/THEORY_LICENSING.md` - drop the fabricated license-generation invocation
- `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md` - replace `model-checker -t`
- `docs/installation/DEVELOPER_SETUP.md` - drop `--profile`
- `code/src/model_checker/output/errors.py` - fix the `--output-dir` suggestion string
- `code/tests/cli/test_docs_flag_matrix.py` (or an output-suite test file) - suggestion-string test
- `code/README.md` - wording check only

**Verification**:
- Doc lint reports zero tokens for the three markdown paths.
- The new suggestion-string test passes.
- `PYTHONPATH=code/src pytest code/tests/ -q -k "output or errors"` shows no regressions.

---

### Phase 8: Flip the guard to green and run the full gate [COMPLETED]

**Goal**: Remove the strict xfail so the guard fails hard on future drift, and confirm the whole
change set is green.

**Tasks**:
- [x] Remove the `@pytest.mark.xfail(strict=True, ...)` decorator from
      `test_documented_flags_are_registered`.
- [x] Run the doc lint across the full declared glob set and confirm zero violations.
- [x] Update `02_violation-inventory.md` with the final before/after counts.
- [x] Add a short note to `code/tests/cli/` (module docstring or `code/docs/core/TESTING_GUIDE.md`,
      whichever matches existing convention) describing the guard, its allowlist derivation, and
      its declared prose blind spot.
- [x] Run the full test suite.

**Timing**: 45 minutes

**Depends on**: 3, 4, 5, 6, 7

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: zero remaining violations across all 204 scanned markdown files. Confirm by
the doc lint passing without xfail; a non-zero count means a Wave 3 phase left residue and must be
reopened rather than allowlisted.

**Files to modify**:
- `code/tests/cli/test_docs_flag_matrix.py` - remove xfail
- `specs/162_fix_nonexistent_cli_flags_in_docs/reports/02_violation-inventory.md` - final counts
- Testing documentation - short guard description

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/cli/ -v` fully green, no XPASS, no XFAIL.
- `PYTHONPATH=code/src pytest code/tests/ -q` green.

---

## Testing & Validation

- [x] `PYTHONPATH=code/src pytest code/tests/cli/test_docs_flag_matrix.py -v` passes with no
      xfail/xpass.
- [x] `PYTHONPATH=code/src pytest code/tests/cli/test_flag_matrix.py -v` still passes (no
      regression to the existing complementary guard).
- [x] `PYTHONPATH=code/src pytest code/tests/ -q` passes. (474 passed, 4 skipped pre-existing/unrelated, 0 failures)
- [x] The extractor's negative unit tests demonstrably reject `pip install --user model-checker`,
      `ls -la`, `./dev_cli.py ... | grep -E "..."`, and `python -m cProfile -o ... dev_cli.py ...`.
- [x] `--iso-debug`, `--load`, `-load` remain documented and remain accepted by the guard.
- [x] Spot-run one rewritten command from each of Phases 3-7 and confirm it does not produce
      `unrecognized arguments`.

## Artifacts & Outputs

- `code/tests/cli/test_docs_flag_matrix.py` - the regression guard
- `specs/162_fix_nonexistent_cli_flags_in_docs/reports/02_violation-inventory.md` - RED inventory
  and final before/after counts
- `specs/162_fix_nonexistent_cli_flags_in_docs/summaries/01_nonexistent-cli-flags-summary.md` -
  implementation summary
- Corrected documentation: `docs/usage/{WORKFLOW,PROJECT,OUTPUT,TOOLS}.md`,
  `docs/installation/{GETTING_STARTED,DEVELOPER_SETUP}.md`,
  `docs/architecture/{PIPELINE,SETTINGS,ITERATE}.md`,
  `code/src/model_checker/settings/README.md`,
  `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`,
  `code/docs/contracts/THEORY_LICENSING.md`
- `code/src/model_checker/output/errors.py` - corrected suggestion string

## Rollback/Contingency

Every phase is an independent, committed green state, so rollback is per-phase `git revert` of
that phase's commit. The guard itself (Phases 1-2) is additive and reverts cleanly on its own
without touching documentation. If the extractor proves too false-positive-prone to reach green
in Phase 8, the fallback is to narrow `_DOC_GLOBS` to the directories this task actually fixed
(`docs/**`, `code/src/model_checker/settings/README.md`) and record the deferred scope as a
follow-up task — never to widen the allowlist with fabricated flag tokens, which would defeat the
guard's purpose. Do not use `git reset --hard` or `git checkout --` on any target file: several
carry unrelated uncommitted fixes from prior work.
