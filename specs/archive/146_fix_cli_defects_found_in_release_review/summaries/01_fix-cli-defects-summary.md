# Implementation Summary: Fix CLI Defects Found in Release Review

- **Task**: 146 - fix_cli_defects_found_in_release_review
- **Status**: [COMPLETED]
- **Started**: 2026-08-11T19:12:00Z
- **Completed**: 2026-08-11T20:10:00Z
- **Effort**: 5.5 hours (estimated)
- **Dependencies**: None
- **Artifacts**: plans/01_fix-cli-defects.md, reports/01_cli-defect-fixes.md, baselines/01_pre-change-suite-baseline.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Fixed all six user-visible CLI polish defects from the 2026-08-11 release review (issues 8, 9,
11, 12, 13, 15) across `code/src/model_checker/__main__.py`, `output/config.py`,
`builder/module.py`'s existing error path, and `builder/project.py`. Each fix landed as its own
verified-green phase with at least one targeted, independently runnable assertion in the new
`code/tests/unit/test_main_cli.py` module (the first direct unit-test coverage of
`ParseFileFlags`) or `builder/tests/unit/test_project.py`. No behavior changed beyond the six
named items; the argparse parser was not refactored wholesale.

## What Changed

- **Issue 8 (`-p` no-op)**: Added the missing `'p': 'print_constraints'` entry to
  `ParseFileFlags._short_to_long`, plus a coverage test that walks `parser._actions` and asserts
  every registered single-character short option has a `_short_to_long` entry (or sits on a named
  allowlist for options that are argparse built-ins / not settings keys: `-h`, `-v`).
- **Issue 9 (stale `--load_theory` help)**: `--load_theory`'s `choices=` and `help=` are now
  derived from `registry.get_registered()` inside `_create_parser()` (lazy import to avoid a
  circular import), replacing the hardcoded `help='Load semantic theory: bimodal.'`. An invalid
  theory name now fails fast at argparse time.
- **Issue 11 (`--save jupyter` discarded)**: Removed `'jupyter'` from `--save`'s `choices=` (no
  Jupyter writer exists anywhere under `output/`) and corrected the "No args = all formats" help
  text to name the two formats actually produced (markdown, json).
- **Issue 12 (`--sequential` traceback)**: Wrapped `BuildModule(module_flags)` in `main()` with a
  `try/except NotImplementedError`, converting the pre-existing, already user-appropriate
  `NotImplementedError` from `builder/module.py::_initialize_output_management` into a clean
  one-line `Error: ...` message and `sys.exit(1)`. The flag stays registered.
- **Issue 13 (dead `-j`/`--jupyter` pre-check)**: Deleted the orphaned Jupyter dependency
  pre-check block at the top of `main()` -- no `-j`/`--jupyter` argparse action was ever
  registered, so the block could never fire.
- **Issue 15 (`__pycache__` warning leak)**: `BuildProject._copy_files` now filters `available`
  immediately after `os.listdir()`, excluding `COPY_IGNORE_PATTERNS` entries and `*.pyc` files, so
  every downstream consumer of `available` is covered, not just the warning site.

## Decisions

- **Issue 8 clustered flags (`-cn`)**: documented, not fixed (see Follow-ups).
- **Issue 11**: removed `jupyter` rather than implementing a writer -- no export pipeline exists,
  and the value never produced output (it silently created an empty directory).
- **Issue 12**: kept `--sequential`/`-q` registered and caught the error at the call site, rather
  than hiding the flag (hiding it would touch more surface: parser, `_short_to_long`, settings
  default).
- **Issue 13**: deleted the dead block rather than registering `-j`/`--jupyter` for real, since
  wiring up real Jupyter support is net-new feature work outside this task's scope.

## Plan Deviations

- None (implementation followed plan).

## Scope-Creep Flags (explicitly not scope creep)

Two changes touch argparse's accepted-input surface and could be mistaken for scope creep beyond
the task's CONSTRAINTS line ("no behavior change beyond these six items"). Both are the direct
and necessary consequence of the named defect, not additional scope:

- **`--load_theory` gains `choices=`** (issue 9): the review item is specifically that
  `--load_theory`'s help/validation is stale and lacks `choices=`; adding registry-derived
  `choices=` *is* the fix, not an addition to it.
- **`--save` loses `jupyter`** (issue 11): the review item is specifically that `--save jupyter`
  is silently discarded; rejecting it at argparse time *is* the fix for "accepted then discarded."

- **Phase 6 exit-code divergence**: `sys.exit(1)` on the caught `NotImplementedError` deliberately
  diverges from the neighboring cvc5 and upgrade error paths in `main()`, which `print` then
  `return` (exit 0 implicitly). This divergence is intentional: the task's verification requires a
  non-zero exit for a clean CLI error, and matching the weaker neighboring convention would fail
  that requirement.

## Impacts

- `model-checker --help` now lists all four registered theories (`bimodal`, `logos`, `exclusion`,
  `imposition`) instead of only `bimodal`, and a typo'd theory name now fails immediately with
  argparse's `invalid choice` message instead of surfacing later as a `FileNotFoundError`.
- `--save jupyter` now exits non-zero with `invalid choice` instead of silently accepting and
  discarding the value.
- `--sequential`/`-q` now exits cleanly with a one-line error instead of a Python traceback.
- `-p`/`--print_constraints` now behave identically (previously `-p` was a silent no-op).
- Project generation no longer emits a `Warning: Skipped non-manifest item: __pycache__` line on
  every run; a genuinely unexpected stray item still warns.
- `-j`/`--jupyter` remain unrecognized options (unchanged from the user's perspective; the dead
  pre-check that could never fire is simply gone).

## Follow-ups

- **Clustered short-flag override gap (`-cn`)**: `SettingsManager._extract_user_provided_flags`
  only recognizes `len(arg) == 2` short tokens (e.g. `-p`), so argparse's clustered short-flag
  form (e.g. `-cn` for `-c` and `-n` together) is parsed correctly by argparse itself but is *not*
  detected as user-provided by the override-detection path -- a clustered flag silently fails to
  register its override. This is now documented with an explanatory comment on
  `_extract_user_provided_flags` in `code/src/model_checker/settings/settings.py`, per this task's
  explicit "decide explicitly whether to fix or document this" instruction. Left for the follow-on
  broad CLI end-to-end suite work (release review issue 6) to fix or scope further.

## Regression Verification

- Phase 1 baseline (pre-change, this task): `code/tests/` 283 passed; `code/src/model_checker/`
  1910 passed; total 2193 passed -- matches the release review's quoted figure exactly.
- Post-change `PYTHONPATH=code/src pytest code/tests/ -q`: **397 passed, 4 skipped, 0 failed**
  (Phase 8, measured). The count above the 283 baseline is explained by this task's own 10 new
  tests in `test_main_cli.py` plus unrelated, concurrently-landed additions from another
  in-flight task (`code/tests/packaging/`) sharing this working tree; the 4 skips are
  pre-existing and unrelated to this task's changes (missing on-disk `notebooks/` directories for
  two theories).
- Post-change `PYTHONPATH=code/src pytest code/src/model_checker/ -q`: **1912 passed, 0 failed**
  (Phase 8, measured). The +2 over the 1910-passing baseline is this task's two new
  `builder/tests/unit/test_project.py` assertions from Phase 7 (pycache-silent, stray-still-warns).
  Zero regressions confirmed against the baseline -- no test that passed before now fails.
- `model-checker --help`: confirmed all four registered theories (`bimodal`, `logos`,
  `exclusion`, `imposition`) listed under `--load_theory`, no "jupyter" under `--save`, and
  accurate "No args = markdown and json" wording.

## References

- `specs/146_fix_cli_defects_found_in_release_review/plans/01_fix-cli-defects.md`
- `specs/146_fix_cli_defects_found_in_release_review/reports/01_cli-defect-fixes.md`
- `specs/146_fix_cli_defects_found_in_release_review/baselines/01_pre-change-suite-baseline.md`
- `code/tests/unit/test_main_cli.py`
- `code/src/model_checker/builder/tests/unit/test_project.py`
