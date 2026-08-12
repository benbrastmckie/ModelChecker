# Implementation Plan: Task #146

- **Task**: 146 - fix_cli_defects_found_in_release_review
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/146_fix_cli_defects_found_in_release_review/reports/01_cli-defect-fixes.md
- **Artifacts**: plans/01_fix-cli-defects.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Fix six independent, user-visible CLI polish defects surfaced by the 2026-08-11 release review
(issues 8, 9, 11, 12, 13, 15) across `__main__.py`, `output/config.py`, `builder/module.py`, and
`builder/project.py`. The CLI is working end to end (4/4 theories generated and executed from an
installed wheel) with the full suite at 2193/2193 green, so every change here is a scoped
correction on a working system, never a repair of breakage. Each defect gets its own phase with
at least one targeted assertion, and the parser is not refactored wholesale. Definition of done:
all six defects fixed, each with a passing minimal assertion, and the full suite still green.

### Research Integration

The research report (`reports/01_cli-defect-fixes.md`) confirmed every root cause by direct read
and resolved several open product decisions. This plan adopts its recommendations verbatim and
records them as fixed decisions so the implementer does not re-litigate them:

| Item | Decision adopted |
|------|------------------|
| Issue 8 enforcement | Add the missing `'p'` entry **plus a coverage test** that walks `parser._actions`. Do NOT derive `_short_to_long` from the parser -- that touches the parsing code path and edges into "wholesale parser refactor". |
| Issue 8 clustered flags (`-cn`) | **Document only.** Add an explanatory comment on `_extract_user_provided_flags`; do not change cluster handling. This is the task's explicit "decide explicitly whether to fix or document this" instruction, answered. |
| Issue 9 | Build `help=` and `choices=` from `registry.get_registered()` inside `_create_parser()`. Registration timing was verified live: importing `model_checker.__main__` already yields `['bimodal','logos','exclusion','imposition']`, so the registry is populated before any parser is built. |
| Issue 11 | **Remove** `'jupyter'` from `choices=`; do not implement a Jupyter writer (no export pipeline exists anywhere under `output/`). Separately correct the "No args = all formats" wording. |
| Issue 12 | **Keep the flag registered**; catch `NotImplementedError` at the `BuildModule(...)` call site and print a clean one-line error with a non-zero exit. Hiding the flag touches more surface (parser, `_short_to_long`, settings default). |
| Issue 13 | **Delete** the block. No `-j`/`--jupyter` action exists and no other code path branches on it; registering it would be net-new feature work. |
| Issue 15 | Filter `available` immediately after `os.listdir` using the existing `COPY_IGNORE_PATTERNS` constant plus a `.pyc` check, so every downstream consumer of `available` is covered, not just the warning site. |
| Test location | `code/tests/unit/test_main_cli.py`. The research left this open; `code/tests/unit/test_registry.py` already exists at that exact level, which settles the precedent. Issue 15's assertions go in the package-local `builder/tests/unit/test_project.py` instead, alongside existing `BuildProject` coverage. |

Two findings from the report materially shape the phase ordering: no file anywhere imports
`ParseFileFlags` today (so the first phase must create the test module before any defect phase
can assert anything), and five of the six defects touch `__main__.py` (so those phases are
chained rather than parallelized, despite touching disjoint line ranges).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. Its Durable Decisions entry records the
registration-based registry (`model_checker/registry.py`) as the sole source of "which theories
exist", replacing three previously drifting sources. Phase 4 advances that decision directly:
`--load_theory`'s hardcoded `help='Load semantic theory: bimodal.'` is the last hardcoded theory
name on the CLI surface. No other phase advances a roadmap item. This plan does not modify
ROADMAP.md.

## Goals & Non-Goals

**Goals**:
- Fix all six named defects (review issues 8, 9, 11, 12, 13, 15).
- Give each fix at least one targeted, independently runnable assertion.
- Establish the first direct unit-test coverage of `ParseFileFlags`.
- Keep the full suite green (2193/2193 baseline).

**Non-Goals**:
- Implementing a Jupyter output-format writer.
- Refactoring the argparse parser or `_short_to_long` derivation.
- Fixing clustered short-flag (`-cn`) override detection -- documented, not fixed.
- The broad CLI end-to-end suite (review issue 6) -- a separate, dependent task.
- Any behavior change beyond what each of the six items itself calls for.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Adding `choices=` to `--load_theory` breaks the existing `test_invalid_theory_name` integration test | M | L | That test asserts `returncode != 0` and `'theory' or 'invalid'` in stderr; argparse's `invalid choice: 'x' (choose from ...)` satisfies both. Phase 4 re-runs it explicitly rather than assuming. |
| Importing `registry` at `__main__.py` module scope creates a circular import | M | L | Import inside `_create_parser()` (lazy), not at module top. Registration timing already verified: registry is populated by the time `__main__` finishes importing. |
| Removing `'jupyter'` from `--save` choices breaks a user's saved script | L | L | The value never produced output -- it created an empty directory and wrote nothing. Rejecting it loudly is strictly better than silently discarding it. Flag the change in the implementation summary. |
| Phase 6's `sys.exit(1)` diverges from neighboring `main()` error paths, which `print` then `return` (exit 0) | L | M | Deliberate: verification requires a non-zero exit. Use `sys.exit(1)` and note the divergence in the summary rather than silently matching the weaker neighboring convention. |
| Five phases edit the same file (`__main__.py`) | M | M | Phases 2-6 are chained sequentially, never run in parallel. Only Phase 7 (`builder/project.py`) runs concurrently with the `__main__.py` chain. |
| Suppressing `__pycache__` accidentally suppresses genuine non-manifest warnings | M | L | Phase 7 asserts both directions: pycache silent AND a stray unknown file still warns. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 7 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 8 | 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel. Phases 2-6 are chained because all five
edit `code/src/model_checker/__main__.py`; their line ranges are disjoint but concurrent edits to
one file are not safe. Phase 7 is the only genuinely parallel branch (it touches
`builder/project.py` exclusively).

---

### Phase 1: Establish CLI unit-test module and regression baseline [COMPLETED]

**Goal**: Create the test module every subsequent phase asserts into, and record the pre-change
suite baseline so regressions are attributable.

**Tasks**:
- [x] Record the pre-change baseline: run `PYTHONPATH=code/src pytest code/tests/ -q` and
      `PYTHONPATH=code/src pytest code/src/model_checker/ -q`, saving both pass/fail counts into
      `specs/146_fix_cli_defects_found_in_release_review/baselines/` (create the directory only
      when writing to it).
- [x] Create `code/tests/unit/test_main_cli.py` importing `ParseFileFlags` from
      `model_checker.__main__`.
- [x] Add one smoke test: `ParseFileFlags()` constructs and its `.parser` is an
      `argparse.ArgumentParser`.
- [x] Confirm the new file is collected: `PYTHONPATH=code/src pytest code/tests/unit/test_main_cli.py -v`.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: The baseline is hypothesized to be 2193 total passing (283 in
`code/tests/`, 1910 in the in-package suite), per the release review. Confirm by running both
commands and recording actual counts -- do not assume. If the actual baseline differs, record the
actual number and use that as the comparison point for Phase 8.

**Files to modify**:
- `code/tests/unit/test_main_cli.py` - new file; imports `ParseFileFlags`, one construction smoke test
- `specs/146_fix_cli_defects_found_in_release_review/baselines/` - new; recorded baseline counts

**Verification**:
- `pytest code/tests/unit/test_main_cli.py` passes with at least one test collected.
- Baseline counts recorded to a file, not only to the transcript.

---

### Phase 2: Delete the dead `-j`/`--jupyter` pre-check (issue 13) [COMPLETED]

**Goal**: Remove the orphaned Jupyter dependency pre-check at the top of `main()`, which can
never fulfill its purpose because argparse rejects `-j`/`--jupyter` immediately afterward.

**Tasks**:
- [x] Delete the `jupyter_flags` / `needs_jupyter` block at the top of `main()` in
      `code/src/model_checker/__main__.py` (currently the first statement in `main()`, ahead of
      the `len(sys.argv) < 2` check).
- [x] Confirm no other reference survives:
      `grep -n "jupyter_flags\|needs_jupyter" code/src/model_checker/__main__.py` returns nothing.
- [x] Add a test to `code/tests/unit/test_main_cli.py` asserting `-j` and `--jupyter` are not
      registered options (e.g. absent from `parser._option_string_actions`), documenting that the
      deletion changes nothing observable.

**Timing**: 0.25 hours

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/__main__.py` - delete the dead pre-check block from `main()`
- `code/tests/unit/test_main_cli.py` - assert `-j`/`--jupyter` are unregistered

**Verification**:
- The grep returns no matches.
- New test passes.
- `model-checker -j examples.py` still fails with argparse's `unrecognized arguments` error, now
  without the preceding dependency message.

---

### Phase 3: Fix `-p` short-flag mapping and add coverage test (issue 8) [COMPLETED]

**Goal**: Make `-p` behave identically to `--print_constraints`, and make the missing-mapping bug
class immediately test-caught.

**Tasks**:
- [x] Add `'p': 'print_constraints'` to `ParseFileFlags._short_to_long` in
      `code/src/model_checker/__main__.py`.
- [x] Add a coverage test to `code/tests/unit/test_main_cli.py`: walk `parser._actions`, collect
      every single-character short option string, and assert each has a matching entry in
      `_short_to_long`.
- [x] Add an equivalence test: `-p file.py` and `--print_constraints file.py` produce the same
      resulting `print_constraints` setting after `SettingsManager` override application.
- [x] Document the clustered-short-flag gap: add a comment on
      `SettingsManager._extract_user_provided_flags` in
      `code/src/model_checker/settings/settings.py` noting that only `len(arg) == 2` short tokens
      are recognized, so clustered forms like `-cn` are parsed correctly by argparse but are not
      detected as user-provided by the override path. State that this is known and deliberately
      out of scope, not an oversight.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: interface

**Scope Hypothesis**: `_short_to_long` currently holds 13 entries (c, d, e, l, m, n, q, s, i, v,
u, z, a) against a registered short-option surface hypothesized to be 14 including `p`. Confirm
at implementation time by running the new coverage test *before* adding the `'p'` entry -- it
must fail listing exactly `p` as the sole gap. If it reports additional gaps, resolve each
explicitly rather than adding entries blindly; some registered short options (`-v` as
`action='version'`, `-u`, `-l`) are not settings keys and may legitimately need exclusion from
the assertion, which the test should encode as a named allowlist rather than a silent omission.

**Files to modify**:
- `code/src/model_checker/__main__.py` - add `'p': 'print_constraints'` to `_short_to_long`
- `code/src/model_checker/settings/settings.py` - comment documenting the clustered-flag gap (no behavior change)
- `code/tests/unit/test_main_cli.py` - short-option coverage test, `-p` equivalence test

**Verification**:
- Coverage test fails before the fix (naming `p`), passes after.
- Equivalence test passes.
- `PYTHONPATH=code/src pytest code/src/model_checker/settings/tests/ -q` still green (comment-only
  change, but the module is re-imported).

---

### Phase 4: Derive `--load_theory` help and choices from the registry (issue 9) [COMPLETED]

**Goal**: Stop advertising only `bimodal`, and make an invalid theory name fail fast at argparse
time instead of surfacing later as a `FileNotFoundError`.

**Tasks**:
- [x] Inside `_create_parser()` in `code/src/model_checker/__main__.py`, lazily
      `from model_checker import registry` and read `theories = registry.get_registered()`.
      Do NOT add the import at module scope.
- [x] Pass `choices=theories` and `help=f"Load semantic theory: {', '.join(theories)}."` to the
      `--load_theory`/`-l` argument.
- [x] Add a test: `parse_args(['--load_theory', 'logos', 'f.py'])` succeeds; and every name in
      `registry.get_registered()` is accepted.
- [x] Add a test: `parse_args(['--load_theory', 'nonsense', 'f.py'])` raises `SystemExit`.
- [x] Re-run the pre-existing integration test
      `code/tests/integration/test_error_handling.py::TestCLIErrorHandling::test_invalid_theory_name`
      unmodified and confirm it still passes via the new argparse path.
- [x] Confirm `model-checker --help` lists all registered theory names.

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: The registry is hypothesized to report exactly four theories
(`bimodal`, `logos`, `exclusion`, `imposition`) and to be fully populated by the time
`_create_parser()` runs. Both were confirmed live during planning by importing
`model_checker.__main__` and reading `registry.get_registered()`. Re-confirm at implementation
time rather than hardcoding four anywhere: the test must assert against
`registry.get_registered()` itself, never against a literal list, or it reintroduces the very
drift this phase removes.

**Files to modify**:
- `code/src/model_checker/__main__.py` - registry-derived `choices=` and `help=` on `--load_theory`
- `code/tests/unit/test_main_cli.py` - valid-name and invalid-name argparse tests

**Verification**:
- New tests pass.
- `test_invalid_theory_name` passes unmodified.
- `model-checker --help` output contains every name in `registry.get_registered()`.
- No literal theory name remains in `__main__.py`'s `--load_theory` registration (the epilog's
  `-l bimodal` usage example is illustrative prose and may stay).

---

### Phase 5: Remove the unsupported `jupyter` save format and correct help wording (issue 11) [COMPLETED]

**Goal**: Stop accepting a `--save` value that produces no output and no error, and make the help
text match actual behavior.

**Tasks**:
- [x] Remove `'jupyter'` from the `--save` `choices=` list in
      `code/src/model_checker/__main__.py`.
- [x] Update the `--save` help string: drop "jupyter" and replace "No args = all formats" with
      wording matching actual behavior (bare `--save` yields markdown + json only).
- [x] Add a test asserting `parse_args(['--save', 'jupyter', 'f.py'])` raises `SystemExit`.
- [x] Add a test asserting bare `--save` still yields `formats == ['markdown', 'json']` from
      `create_output_config`, unchanged.
- [x] Leave `code/src/model_checker/output/config.py` behavior unchanged; optionally add a brief
      comment there noting that the supported format set is markdown + json and is mirrored in the
      parser's `choices=`.

**Timing**: 0.5 hours

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: `create_output_config` is hypothesized to map only `'markdown'`/`'md'` and
`'json'`, with no `jupyter` branch anywhere under `code/src/model_checker/output/`. Confirm by
grepping the output package for `jupyter` before editing; if a writer does exist, stop and
escalate, because the adopted decision (remove rather than implement) rests on its absence.

**Files to modify**:
- `code/src/model_checker/__main__.py` - drop `'jupyter'` from `choices=`; correct help wording
- `code/src/model_checker/output/config.py` - optional clarifying comment only, no behavior change
- `code/tests/unit/test_main_cli.py` - rejection test and bare-`--save` regression test

**Verification**:
- `model-checker --save jupyter examples.py` exits non-zero with argparse's `invalid choice` error.
- Bare `--save` behavior unchanged.
- `PYTHONPATH=code/src pytest code/src/model_checker/output/tests/ -q` green.

---

### Phase 6: Convert the `--sequential` traceback into a clean CLI error (issue 12) [COMPLETED]

**Goal**: A user typing `--sequential`/`-q` gets a one-line error and a non-zero exit, not a
Python traceback. The flag stays registered.

**Tasks**:
- [x] Wrap the `module = BuildModule(module_flags)` construction in `main()`
      (`code/src/model_checker/__main__.py`) in
      `try: ... except NotImplementedError as e: print(f"Error: {e}"); sys.exit(1)`.
- [x] Verify the existing `NotImplementedError` message raised by
      `builder/module.py::_initialize_output_management` is already user-appropriate (it is: it
      explains the removal and points at `--save` batch mode). Do not reword it.
- [x] Add a test asserting `-q examples.py` exits non-zero and its stderr/stdout contains no
      `"Traceback"` substring, using the existing `run_cli_command` helper in
      `code/tests/utils/helpers.py`.
- [x] Do NOT remove or hide the flag, and do NOT touch `_short_to_long['q']` or the
      `sequential` settings default.

**Timing**: 0.75 hours

**Depends on**: 5

**Verification Tier**: interface

**Files to modify**:
- `code/src/model_checker/__main__.py` - `try/except NotImplementedError` around `BuildModule(...)`
- `code/tests/unit/test_main_cli.py` (or `code/tests/integration/test_error_handling.py` if the
  subprocess helper fits better there) - clean-error assertion

**Verification**:
- `model-checker --sequential examples.py` exits non-zero with a single `Error: ...` line.
- No `Traceback` in the output.
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -q` green.

**Note on exit code**: `sys.exit(1)` is deliberate and diverges from the neighboring cvc5 and
upgrade error paths in `main()`, which `print` then `return` (exit 0). Verification requires a
non-zero exit, so match the requirement, not the weaker neighboring convention, and call out the
divergence in the implementation summary.

---

### Phase 7: Suppress `__pycache__` / `*.pyc` in the manifest-filter loop (issue 15) [COMPLETED]

**Goal**: Stop printing `Warning: Skipped non-manifest item: __pycache__` on every project
generation, without weakening the warning for genuinely unexpected items.

**Tasks**:
- [x] In `code/src/model_checker/builder/project.py`, filter `available` immediately after the
      `os.listdir(self.source_dir)` call: exclude any entry in the existing
      `COPY_IGNORE_PATTERNS` constant and any entry ending in `.pyc`.
- [x] Do NOT modify `REQUIRED_COPY_ITEMS` or `OPTIONAL_COPY_ITEMS` -- those are contract lists
      referenced by `docs/THEORY_ARCHITECTURE.md`.
- [x] Add a test to `code/src/model_checker/builder/tests/unit/test_project.py`: build a synthetic
      source tree under `tmp_path` containing `__pycache__/` and assert no
      `"Skipped non-manifest item: __pycache__"` entry appears in `log_messages` or stdout.
- [x] Add the negative-direction test: a stray unknown item (e.g. `stray_file.tmp`) in the same
      synthetic tree still produces the WARNING.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: interface

**Scope Hypothesis**: `COPY_IGNORE_PATTERNS` is hypothesized to be
`['__pycache__', '.ipynb_checkpoints']`, already defined in `project.py` for
`shutil.copytree`'s `ignore=` argument, and the manifest-filter loop is hypothesized to be the
only site in that file that warns on pycache (two other sites already special-case it
deliberately). Confirm both by reading the file before editing; if a third warning site exists,
cover it in this phase rather than deferring.

**Files to modify**:
- `code/src/model_checker/builder/project.py` - filter `available` after `os.listdir`
- `code/src/model_checker/builder/tests/unit/test_project.py` - pycache-silent and stray-warns tests

**Verification**:
- Both new tests pass (silent for pycache, still warns for a stray file).
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -q` green.
- A real generation against a theory directory with a populated `__pycache__` prints no pycache
  warning.

---

### Phase 8: Full-suite regression and implementation summary [COMPLETED]

**Goal**: Confirm no regression against the Phase 1 baseline and record the changes, including
the two argparse-surface changes that a reader might mistake for scope creep.

**Tasks**:
- [x] Run `PYTHONPATH=code/src pytest code/tests/ -q` and compare against the Phase 1 baseline.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/ -q` and compare against the Phase 1
      baseline.
- [x] Run `model-checker --help` and confirm: all registered theories listed, no "jupyter" under
      `--save`, accurate "No args" wording.
- [x] Write `specs/146_fix_cli_defects_found_in_release_review/summaries/01_fix-cli-defects-summary.md`.
- [x] In the summary, explicitly flag the two argparse-acceptance changes (`--load_theory`
      `choices=`, `--save` losing `jupyter`) as called for by issues 9 and 11 themselves, not as
      scope creep beyond the CONSTRAINTS line. Also flag the Phase 6 `sys.exit(1)` divergence.
- [x] In the summary, record the clustered-short-flag (`-cn`) gap as knowingly documented rather
      than fixed, so it is discoverable by the follow-on CLI end-to-end suite work.

**Timing**: 0.75 hours

**Depends on**: 2, 3, 4, 5, 6, 7

**Verification Tier**: full

**Scope Hypothesis**: The post-change suite is hypothesized to match the Phase 1 baseline count
plus the newly added tests, with zero failures. Confirm against the recorded baseline file, not
against the 2193 figure quoted in the review -- Phase 1's actual measurement is the authority.

**Files to modify**:
- `specs/146_fix_cli_defects_found_in_release_review/summaries/01_fix-cli-defects-summary.md` - new

**Verification**:
- Both suites green, totals equal to baseline plus new tests.
- Summary written and contains the three flagged items above.

---

## Testing & Validation

- [x] `-p` and `--print_constraints` produce identical settings.
- [x] Every registered single-character short option has a `_short_to_long` entry (or a named
      allowlist exclusion).
- [x] `--help` lists every name in `registry.get_registered()` for `--load_theory`.
- [x] An unregistered theory name raises `SystemExit` at argparse time.
- [x] `code/tests/integration/test_error_handling.py::TestCLIErrorHandling::test_invalid_theory_name`
      passes unmodified.
- [x] `--save jupyter` is rejected; bare `--save` still yields `['markdown', 'json']`.
- [x] `--save` help text no longer says "all formats" or mentions jupyter.
- [x] `--sequential` exits non-zero with a one-line error and no traceback.
- [x] `-j`/`--jupyter` are unregistered; no `jupyter_flags`/`needs_jupyter` references remain.
- [x] Project generation emits no `__pycache__` warning; a stray unknown item still warns.
- [x] `PYTHONPATH=code/src pytest code/tests/ -q` green, at or above baseline (397 passed, 4
      skipped, vs. 283-passed baseline).
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/ -q` green, at or above baseline (1912
      passed vs. 1910-passed baseline).

## Artifacts & Outputs

- `code/tests/unit/test_main_cli.py` (new) - first direct unit coverage of `ParseFileFlags`
- `code/src/model_checker/__main__.py` (modified) - issues 8, 9, 11, 12, 13
- `code/src/model_checker/settings/settings.py` (modified) - clustered-flag documentation comment
- `code/src/model_checker/output/config.py` (optionally modified) - clarifying comment only
- `code/src/model_checker/builder/project.py` (modified) - issue 15
- `code/src/model_checker/builder/tests/unit/test_project.py` (modified) - issue 15 assertions
- `specs/146_fix_cli_defects_found_in_release_review/baselines/` - pre-change suite counts
- `specs/146_fix_cli_defects_found_in_release_review/summaries/01_fix-cli-defects-summary.md`

## Rollback/Contingency

Every phase is a small, independent edit committed separately, so any single defect fix can be
reverted with `git revert` of its phase commit without disturbing the other five. The two
higher-risk phases have specific fallbacks:

- **Phase 4** (`choices=` on `--load_theory`): if a lazy `registry` import inside
  `_create_parser()` still triggers a circular import, fall back to computing the theory list
  from `model_checker.theory_lib.AVAILABLE_THEORIES` (itself
  `_core_registry.get_registered()`), which is already imported transitively. If neither import
  path is viable, land the `help=` fix alone and mark the `choices=` half `[PARTIAL]` with the
  import obstacle recorded -- do not reintroduce a hardcoded list.
- **Phase 5** (removing `jupyter` from `choices=`): if removal proves user-visibly disruptive,
  the alternative is raising a clear "format not supported" error inside `create_output_config`
  instead of dropping the value silently. Either resolves the defect; the removal is preferred as
  the smaller change.

No database, migration, or persisted state is involved, so rollback is purely a source revert.
