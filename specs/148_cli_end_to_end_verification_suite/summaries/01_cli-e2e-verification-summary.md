# Implementation Summary: CLI End-to-End Verification Suite

- **Task**: 148 - cli_end_to_end_verification_suite
- **Status**: COMPLETED
- **Started**: 2026-08-11
- **Completed**: 2026-08-11
- **Artifacts**: `reports/01_cli-e2e-verification-research.md`, `plans/01_cli-e2e-verification-plan.md`, `summaries/01_cli-e2e-verification-summary.md`
- **Standards**: `code/docs/core/TESTING_GUIDE.md` (mandatory TDD), `code/docs/core/CODE_STANDARDS.md` (no backwards-compatibility shims, fail-fast)
- **Plan**: `specs/148_cli_end_to_end_verification_suite/plans/01_cli-e2e-verification-plan.md`
- **Research**: `specs/148_cli_end_to_end_verification_suite/reports/01_cli-e2e-verification-research.md`

## Overview

Built real behavioral end-to-end coverage for the CLI: a fast `code/tests/cli/` package
(`ParseFileFlags` unit tests, the short/long flag-equivalence sweep, and the ~15-flag matrix run
via `python -m model_checker`), console-script and generate-then-execute tests layered onto the
existing wheel-build-and-venv-install fixture in `code/tests/packaging/`, and reconciliation of
four existing files that were named like end-to-end coverage but were not (one deleted, two
rewritten, one retired entirely). One genuine production defect was found and fixed along the way
(`--cvc5` crashed on every invocation).

## What Changed

New test coverage:

| File | Change |
|---|---|
| `code/tests/cli/__init__.py`, `conftest.py` | New fast CLI test package and its local fixtures |
| `code/tests/cli/test_parse_file_flags.py` | New — `ParseFileFlags` unit tests and the short/long equivalence sweep |
| `code/tests/cli/test_flag_matrix.py` | New — ~15-flag behavioral matrix via `python -m model_checker` |
| `code/tests/packaging/test_cli_console_script.py` | New — real `model-checker` console-script behavior |
| `code/tests/packaging/test_generate_then_execute.py` | New — registry-driven generate-then-execute per theory |
| `code/tests/packaging/conftest.py` | New — shared packaging fixtures; `installed_venv` relocated here from `test_entry_point.py`, plus the Nix C++ runtime repair (see Decisions) |
| `code/tests/conftest.py`, `code/tests/utils/helpers.py` | Existing unused CLI harness adopted rather than rebuilt |

Existing files reconciled (the four the research identified as named-like-coverage but not):

| File | Disposition |
|---|---|
| `builder/tests/integration/test_cli_interactive_integration.py` | Retired (445 lines deleted) — drove an `interactive` flag the CLI cannot produce |
| `builder/tests/test_package_loading.py` | Mock-asserting `TestSubprocessExecution` deleted, tombstone comment left |
| `builder/tests/e2e/test_full_pipeline.py` | `test_iteration_workflow` rewritten (it passed `-i` believing it was an iteration flag) |
| `code/tests/e2e/test_batch_output_real.py` | Rewritten to assert real batch output, not just `returncode == 0` |
| `code/tests/integration/test_error_handling.py` | `test_conflicting_flags` `pass` stub replaced with a real mutex assertion |

Production code:

| File | Change |
|---|---|
| `code/src/model_checker/builder/runner.py` | Defect fix — `--cvc5` crashed on every invocation via an unconditional z3-only parameter reset (`8f33ef9a`) |

## Decisions

- **`test_cli_interactive_integration.py` retired rather than rewritten.** `builder/module.py:140-152`
  raises `NotImplementedError` whenever `config.sequential` is truthy, so `-q`/`--sequential` is a
  fail-fast path, not a working feature. Rewriting the file around `general_settings["sequential"]`
  (the research's open question) would have tested an error path, and the `interactive_manager.mode`
  internals it asserted against no longer exist. The fail-fast contract is instead covered by
  `test_sequential_fails_fast_without_traceback` in the flag matrix.
- **`--upgrade` asserted by construction, never executed**, since it shells out to
  `pip install --upgrade model-checker`. This leaves the one sanctioned `patch('subprocess.run')`
  site in the repo; it asserts the real constructed argv, not merely that a mock was called.
- **The stale baseline was corrected, not matched.** See the Phase 8 deviation table below.
- **Nix C++ runtime repair over an accepted skip.** The six `installed_venv`-backed tests
  originally skipped on this host: a pip-installed `z3-solver` wheel inside an isolated venv
  cannot resolve `libstdc++.so.6` on a non-FHS layout. `installed_venv` now prepends the Nix
  stdenv C++ runtime to `LD_LIBRARY_PATH` (the recipe the release-rehearsal work established for
  verifying a published wheel on this platform). Guarded on `nix` being present and the
  evaluation succeeding, so it is inert on a standard FHS runner. `handle_known_venv_libz3_link_failure`
  is retained as a backstop for hosts the repair does not cover.

## Phases Completed

All 8 phases complete. Phases 1-7 were implemented and committed in a prior dispatch
(commits `774bd130`, `a6c2c0b6`, `846b0d31`, `21e36ce7`, `12f8318a`, `b20e21e6`, `fac227a4`, plus
defect fix `8f33ef9a`). This dispatch executed Phase 8 (full-suite regression and runtime budget)
from scratch, since the prior dispatch's regression run result was never recorded.

### Phase 8: Full-suite regression and runtime budget

**Baseline correction (deviation)**: the plan and orchestrator delegation both cite a baseline of
283 top-level + 1910 in-package = 2193 green tests "before this task." Direct verification —
checking out the actual immediate-predecessor commit (`55ea4e8f`, "task 146: complete
implementation," the true parent of task 148's research commit `ca3d4ef8`) into an isolated git
worktree and running both suites there — showed this cited figure does not match that commit:

| Suite | Cited baseline | Verified baseline (`55ea4e8f`) |
|---|---|---|
| Top-level (`code/tests/`) | 283 | 401 (397 passed + 4 skipped) |
| In-package (`code/src/model_checker/`) | 1910 | 1912 |
| Total | 2193 | 2313 |

The verified `55ea4e8f` numbers were used as the reconciliation baseline instead of the plan's
stale figure, per the instruction to "account for the delta honestly rather than forcing a
match."

**Current results** (both suites green, zero failures):

| Suite | Result | Command |
|---|---|---|
| Top-level | 462 passed, 10 skipped (472 collected) in 69.29s | `PYTHONPATH=code/src pytest code/tests/ -v --durations=0` |
| In-package | 1902 passed, 86 subtests passed in 389.99s | `PYTHONPATH=code/src pytest code/src/model_checker/ -v --durations=0` |

**Delta reconciliation, top-level (401 -> 472, +71)**, verified via per-file `--collect-only`
counts at baseline vs. HEAD:

| File | Baseline | Current | Delta |
|---|---|---|---|
| `code/tests/cli/test_flag_matrix.py` (new) | 0 | 36 | +36 |
| `code/tests/cli/test_parse_file_flags.py` (new) | 0 | 24 | +24 |
| `code/tests/packaging/test_generate_then_execute.py` (new) | 0 | 6 | +6 |
| `code/tests/packaging/test_cli_console_script.py` (new) | 0 | 4 | +4 |
| `code/tests/e2e/test_batch_output_real.py` (rewritten) | 1 | 2 | +1 |
| `code/tests/integration/test_error_handling.py` (stub filled) | 27 | 27 | 0 |
| `code/tests/packaging/test_entry_point.py` (fixture moved out) | 3 | 3 | 0 |
| **Total** | | | **+71** ✓ matches 401→472 |

**Skipped-count delta — superseded by the post-Phase-8 repair.** As first measured, the count
rose +6 (4→10): the 6 new `installed_venv`-dependent tests (2 in `test_cli_console_script.py`,
4 in `test_generate_then_execute.py`) skipped on this host because a pip-installed `z3-solver`'s
bundled `libz3.so`/`libstdc++.so.6` cannot dynamically link inside an isolated venv on a non-FHS
layout. That meant the two headline deliverables — real console-script *behavioral* coverage and
the four-theory generate-then-execute sweep — were never actually executing here, only asserted.

This was subsequently repaired at its source (see Decisions): `installed_venv` now supplies the
Nix C++ runtime via `LD_LIBRARY_PATH`. **All six tests now execute and pass.** The final skipped
count is 4 — the same 4 present at baseline, all pre-existing `test_inclusions.py` cases where a
theory genuinely has no on-disk `notebooks/` directory. Task 148 therefore introduces zero new
skips.

**Delta reconciliation, in-package (1912 -> 1902, -10)**, verified via per-file test-count diff
against the same `55ea4e8f` baseline, entirely attributable to Phase 7's dispositions of the four
misleading files:

| File | Baseline count | Current count | Delta |
|---|---|---|---|
| `code/src/model_checker/builder/tests/integration/test_cli_interactive_integration.py` (retired) | 9 | 0 (file deleted) | -9 |
| `code/src/model_checker/builder/tests/test_package_loading.py` (mock test deleted) | 7 | 6 | -1 |
| `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` (rewritten, same count) | 3 | 3 | 0 |
| **Total** | | | **-10** ✓ matches 1912→1902 |

**Runtime budget**: top-level +37.1s (32.19s → 69.29s), in-package +21.96s (368.03s → 389.99s).
Judged acceptable: the top-level increase is dominated by the new `installed_venv`-backed
console-script/generate-then-execute tests (session-scoped fixture already amortized across all
of them — the individual per-test subprocess costs, per `--durations=0`, top out around 13.55s
setup for the first console-script test and ~1.4s for the flag-matrix's slowest cases) plus the
flag-matrix's per-flag CLI subprocess invocations, none of which are disproportionate to the
behavioral coverage gained. No markers were adjusted; no assertion was weakened to control
runtime.

**Assertion-weakening re-read**: re-read every assertion added in Phases 3-7.
- Zero `xfail` markers anywhere in the Phase 3-7 files (`grep -rn xfail` across
  `code/tests/cli/`, `code/tests/packaging/test_cli_console_script.py`,
  `code/tests/packaging/test_generate_then_execute.py`,
  `code/tests/e2e/test_batch_output_real.py`, and the Phase-7-touched builder test files returned
  nothing) — no defect required an `xfail` fallback; the one genuine production defect found
  (`--cvc5` crash) was fixed directly instead (commit `8f33ef9a`).
- Every `assert result.returncode == 0` in `code/tests/cli/test_flag_matrix.py` (19 occurrences)
  is paired with an additional behavioral assertion in the same test (output content check, file
  existence check, or `Traceback`-absence check) — none stand alone.
- `grep -rn "patch.*subprocess.run" code/` finds exactly one remaining site,
  `test_upgrade_constructs_expected_pip_command_without_executing` in
  `code/tests/cli/test_flag_matrix.py`. This is the plan's explicitly sanctioned exception
  (`--upgrade` "is asserted by constructed-command inspection and never executed"): the test
  asserts the real constructed argv list and `check=True`, not merely that the mock was called —
  it is not an instance of the prohibited assert-on-own-mock pattern the rest of Phase 7 removed.
- No silently-skipped parametrization case was found. The 6 environment skips noted at the time
  of this re-read have since been eliminated by the `LD_LIBRARY_PATH` repair; the only remaining
  skips are the 4 pre-existing `test_inclusions.py` no-notebooks cases.

**Requirement-letter-to-test mapping** (five requirement letters (a)-(e), per the research
report's gap inventory and recommendations):

| Letter | Requirement | Covering test(s) |
|---|---|---|
| (a) | Console-script behavioral coverage (real `model-checker` script, no `PYTHONPATH`) | `code/tests/packaging/test_cli_console_script.py::test_version_matches_python_dash_m_invocation`, `::test_help_matches_python_dash_m_invocation`, `::test_real_example_run_through_console_script`, `::test_console_script_runs_without_pythonpath`; augments existing `code/tests/packaging/test_entry_point.py::test_console_script_installed_and_executable`, `::test_console_script_runs`, `::test_entry_point_module_importable` |
| (b) | `ParseFileFlags` short/long equivalence (the `-p`-class regression guard) | `code/tests/cli/test_parse_file_flags.py::test_short_long_equivalence_sweep` (parametrized over every `_short_to_long` entry, with `::test_sweep_partition_covers_every_short_to_long_entry` as its own completeness assertion), plus `::test_clustered_short_flags_do_not_override_documented_gap`; mutex fix at `code/tests/integration/test_error_handling.py::TestCLIErrorHandling::test_conflicting_flags` |
| (c) | Flag matrix — every registered flag exercised behaviorally | `code/tests/cli/test_flag_matrix.py::test_every_registered_flag_is_covered_or_excluded` (completeness), `::test_boolean_flag_accepted`, `::test_output_affecting_boolean_flag_changes_output`, `::test_save_*` (3 tests), `::test_maximize_dispatches_to_run_comparison`, `::test_z3_flag_selects_backend_and_runs`, `::test_cvc5_flag`, `::test_upgrade_constructs_expected_pip_command_without_executing`, `::test_sequential_fails_fast_without_traceback` |
| (d) | Generate-then-execute for every registered theory | `code/tests/packaging/test_generate_then_execute.py::test_generate_then_execute` (parametrized over `registry.get_registered()`), `::test_parametrization_count_matches_live_registry` (completeness), `::test_registry_is_non_empty` |
| (e) | No test asserts against its own mock; misleading files reconciled | Phase 7 disposition: `code/src/model_checker/builder/tests/test_package_loading.py` (mock-asserting test deleted), `code/tests/e2e/test_batch_output_real.py` (rewritten to real batch-output assertions), `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py::test_project_creation_and_theory_library_execution` (renamed/rewritten from `test_iteration_workflow`), `code/src/model_checker/builder/tests/integration/test_cli_interactive_integration.py` (retired entirely — fail-fast contract has no internals left to assert against); verified via `grep -rn "patch.*subprocess.run" code/` showing only the sanctioned (c)/`--upgrade` exception |

## Plan Deviations

- **Baseline figure corrected** (documented above): the plan-stated 283+1910=2193 baseline does
  not match the actual pre-task-148 commit; verified baseline of 401+1912=2313 was used instead
  for delta reconciliation. This is a documentation correction, not a scope change — every delta
  from the verified baseline reconciles exactly against file-level changes.
- No other deviations. All Phase 8 checklist items completed as specified; no assertion was
  weakened; no new defect was found (the one defect discovered during this task's earlier phases,
  `--cvc5` crashing unconditionally, was already fixed and committed at `8f33ef9a` prior to this
  dispatch).

## Testing & Validation (from plan's Testing & Validation section)

- [x] `PYTHONPATH=code/src pytest code/tests/ -v` green. At Phase 8: 462 passed, 10 skipped.
      After the `LD_LIBRARY_PATH` repair: **468 passed, 4 skipped, 0 failed in 151.15s**.
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/ -v` green (1902 passed, 0 failed).
      Unaffected by the repair, which touches only `code/tests/packaging/conftest.py`.
- [x] Full-suite count reconciles against the verified baseline with every delta explained (see
      tables above).
- [x] `ParseFileFlags` is imported by `code/tests/cli/test_parse_file_flags.py`.
- [x] The short/long equivalence sweep covers every `_short_to_long` entry, with its own
      completeness assertion (`test_sweep_partition_covers_every_short_to_long_entry`).
- [x] The real `model-checker` console script is invoked for behavior, with no `PYTHONPATH` set
      (`test_console_script_runs_without_pythonpath`).
- [x] Generate-then-execute passes for every theory in `registry.get_registered()`.
- [x] `--save` is proven to produce files on disk (`test_save_bare_produces_markdown_and_json`,
      `test_save_with_explicit_format`).
- [x] `--upgrade` is asserted by constructed-command inspection and never executed.
- [x] No test in the repo patches `subprocess.run` and then asserts against its own mock.
- [x] `test_conflicting_flags` has a real mutex assertion, not a `pass` body.

## Files Modified (Phase 8)

- `specs/148_cli_end_to_end_verification_suite/plans/01_cli-e2e-verification-plan.md` (Phase 8
  marked `[COMPLETED]`, checklist items checked, deviation noted)
- `specs/148_cli_end_to_end_verification_suite/summaries/01_cli-e2e-verification-summary.md`
  (this file)

No production or test code was modified in Phase 8 — it is verification-only, as declared in the
plan's "Files to modify: None" for this phase.

## Impacts

- **The CLI is now covered where it was blind.** The `model-checker` console script — the
  package's single most user-visible artifact — is exercised as a real subprocess, and the
  primary user journey ("generate a project, then run it") is verified automatically for every
  registered theory instead of by hand at release time.
- **A shipped defect was caught by the new tests, not by a user**: `--cvc5` crashed on every
  invocation. This is the class of break the coverage gap existed to hide.
- **Runtime cost is real and concentrated.** The top-level suite went 32.19s (baseline) → 69.29s
  (Phase 8, with 6 tests skipping) → **151.15s** once those 6 actually run. Roughly 90s of the
  final figure is the `bimodal` generate-then-execute case alone, which runs that theory's entire
  default example set. This is a genuine trade-off, not free coverage — it matters for the CI
  workflow being added separately, where the packaging tests' placement (PR gate vs. release-only
  job) is an open decision.
- **`code/tests/packaging/` is now a shared-fixture directory**, not a collection of independent
  modules. `installed_venv` is session-scoped in `conftest.py`, so the wheel build and venv
  install happen once and amortize across every consumer; new console-script tests belong here
  rather than in `code/tests/cli/`, which has no venv harness by design.

## Follow-ups

- **The `-l` flag has no non-interactive coverage and cannot easily get any.** It dispatches to
  `BuildProject.ask_generate()` and blocks on `input()`, so it is excluded from the flag matrix
  by construction rather than by oversight. If `-l` is meant to be scriptable, that is a
  product-behavior question, not a test gap.
- **Verify the repair on a standard FHS runner.** `_nix_cxx_runtime_lib_dir()` is designed to be
  inert without `nix` on PATH, but that inert path has only been reasoned about here, not
  observed — CI is the first place it will actually be exercised.
- **Decide where the packaging tests run.** Given the ~90s bimodal case, blocking every PR on the
  full generate-then-execute sweep may not be the right cadence; a release-only or nightly job is
  a reasonable alternative.

## References

- Research report: `specs/148_cli_end_to_end_verification_suite/reports/01_cli-e2e-verification-research.md`
- Implementation plan: `specs/148_cli_end_to_end_verification_suite/plans/01_cli-e2e-verification-plan.md`
- Originating release review: `specs/reviews/review-20260811.md` (issues 4, 5, 6)
- Commits: `774bd130` (phase 1), `a6c2c0b6` (phase 2), `846b0d31` (phase 3), `21e36ce7` (phase 4),
  `8f33ef9a` (`--cvc5` defect fix), `12f8318a` (phase 5), `b20e21e6` (phase 6), `fac227a4`
  (phase 7), `c610c10c` (phase 8)
- Project standards: `code/docs/core/TESTING_GUIDE.md`, `code/docs/core/CODE_STANDARDS.md`
