# Implementation Summary: Fix Nonexistent CLI Flags in Docs

- **Task**: 162 - Audit and fix nonexistent CLI flags documented across user-facing docs
- **Plan**: `specs/162_fix_nonexistent_cli_flags_in_docs/plans/01_nonexistent-cli-flags-fix.md`
- **Status**: Implementation complete, all 8 phases COMPLETED
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD

## What was done

Built an executable regression guard first, then used it to drive the fix. Phase 1 built the
guard's machinery -- allowed-token derivation from `ParseFileFlags().parser._actions` (never
hand-transcribed), a `_DEV_CLI_WRAPPER_FLAGS` allowlist (`--iso-debug`, `--load`, `-load`) for
flags `code/dev_cli.py` consumes before argparse ever runs, a fenced-code-block invocation
extractor, and a flag-token extractor -- with 10 passing unit tests over inline fixtures. Phase 2
pointed the extractor at the real 204-file documentation tree, landed the scanning test under
`@pytest.mark.xfail(strict=True)` to demonstrate RED in a committable green state, and wrote a
full violation inventory (11 files, 46 tokens) grouped by owning phase.

Phases 3-7 then fixed the inventory in file-owned parallel phases:
- **Phase 3**: rewrote the `--subtheory`/`-st` project-scaffolding fiction in `WORKFLOW.md`,
  `PROJECT.md`, and `GETTING_STARTED.md` to teach the real mechanism
  (`logos.get_theory(subtheories=[...])`), and removed the fabricated `--test-all-settings`/
  `--benchmark` examples.
- **Phase 4**: whole-file passes on `OUTPUT.md` and `TOOLS.md` -- removed `--output-dir`,
  `--verbose`, `--no-terminal`, and every `notebook`-as-`--save`-value mention (not CLI-reachable;
  `--save`'s `choices` are `markdown`/`json` only), and fixed the bare-`--save` self-contradiction.
- **Phase 5**: removed `--verbose`/`--format` fictions from `PIPELINE.md` and `SETTINGS.md` while
  preserving the genuinely real `--iso-debug` example in `ITERATE.md`, and fixed its
  `DEBUG_CONFIG['verbose']` and `# Debug messages (with --verbose)` prose sites to reference the
  real `MODELCHECKER_VERBOSE` environment variable.
- **Phase 6**: whole-file pass on `code/src/model_checker/settings/README.md` -- deleted six
  never-real "Theory-Specific Flags" (`--coherence-check`, `--witness-optimization`,
  `--imposition-depth`, `--state-modification`, `-M`/`--M`; confirmed absent from `git log --all
  -S` history), re-documented the settings that genuinely exist as settings-dict keys instead of
  CLI flags (`M`, `save_output`, `derive_imposition`), kept `--align_vertically`/`-a` as the real
  CLI flag it is, and fixed every hyphenated long-flag spelling to its underscore form.
- **Phase 7**: deleted the fabricated "Automated License Generation" section from
  `THEORY_LICENSING.md`, replaced `model-checker -t my_test_name` with the real pytest invocation
  in `CONTRIBUTING.md`, removed the `--profile` example from `DEVELOPER_SETUP.md`, and fixed the
  live `OutputDirectoryError` permission-branch suggestion in `output/errors.py` that recommended
  the nonexistent `--output-dir` flag. Added a unit test reusing the Phase 1 allowed-token
  derivation to guard the suggestion string against future drift.

Phase 7's own fixes happened to clear the last 6 inventoried violations, so the strict-`xfail`
guard immediately produced `XPASS(strict)` -- a hard failure under pytest's strict-xfail
semantics. Per the plan's own Risk table ("`strict=True` makes the eventual xpass a hard failure,
mechanically forcing the Phase 8 flip"), the xfail decorator's removal was pulled forward into
the Phase 7 commit rather than leaving `code/tests/cli/` red; this is documented as a deviation
in the Phase 7 handoff. Phase 8 then confirmed zero violations across all 204 files, updated the
inventory with final before/after counts per phase, added a status note to the guard's module
docstring, and ran the full repository test suite.

## Verification results

- `PYTHONPATH=code/src pytest code/tests/cli/ -v` -- 74 passed, 0 xfailed, 0 xpassed.
- `_scan_doc_violations()` over the full `_DOC_GLOBS` set: 204 files scanned, 0 violations (down
  from 46 across 11 files at Phase 2's RED baseline).
- Spot-run commands from each of Phases 3-7 (`logos.get_theory(subtheories=['modal'])`,
  `--contingent --print_z3`, `--align_vertically`, the `pytest -k` invocation from
  `CONTRIBUTING.md`) all executed without `unrecognized arguments`.
- `PYTHONPATH=code/src pytest code/tests/ -q` -- full-suite run; see the Phase 8 handoff for the
  final pass count.

## Files modified

- `code/tests/cli/test_docs_flag_matrix.py` (new) - the regression guard: allowed-token
  derivation, dev_cli wrapper allowlist, invocation extractor, flag-token extractor, doc scan,
  and the `output/errors.py` suggestion-string guard.
- `specs/162_fix_nonexistent_cli_flags_in_docs/reports/02_violation-inventory.md` (new) - RED
  inventory and final before/after counts.
- `docs/usage/WORKFLOW.md`, `docs/usage/PROJECT.md`, `docs/installation/GETTING_STARTED.md`
- `docs/usage/OUTPUT.md`, `docs/usage/TOOLS.md`
- `docs/architecture/PIPELINE.md`, `docs/architecture/SETTINGS.md`, `docs/architecture/ITERATE.md`
- `code/src/model_checker/settings/README.md`
- `code/docs/contracts/THEORY_LICENSING.md`
- `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`
- `docs/installation/DEVELOPER_SETUP.md`
- `code/src/model_checker/output/errors.py`

## Plan Deviations

- **xfail removal pulled forward from Phase 8 into Phase 7's commit.** Phase 7's fixes cleared
  the last 6 violations, which turned the strict-xfail-marked scanning test into a hard
  `XPASS(strict)` failure. Removing the `@pytest.mark.xfail(...)` decorator -- nominally Phase
  8's first task -- was mechanically required to keep the Phase 7 commit green, per the plan's own
  Risk table language anticipating exactly this outcome. Documented in the Phase 7 handoff; Phase
  8's remaining tasks (final inventory counts, testing-guide note, full-suite run) were completed
  as their own phase.
- **Extended notebook-mention removal beyond the plan's named site in `OUTPUT.md`/`TOOLS.md`.**
  The plan's Phase 4 task list named only the "Jupyter Notebook Format" section; the fix was
  extended to every other `notebook`-as-`--save`-value mention in `OUTPUT.md` (Format Selection
  Guide, directory-structure diagram, Practical Examples, Troubleshooting) and the one `--save
  notebook` line in `TOOLS.md`, since `--save`'s `choices` are `markdown`/`json` only and a
  partial removal would still misinform readers. Same-file, same-task-family extension.
- No other deviations. All phases followed the plan's task lists.

## No push, tag, or PR

Confirmed: no `git push`, `git tag`, or `gh pr create` was run at any point in this dispatch, per
`.claude/rules/pr-prohibition.md`.
