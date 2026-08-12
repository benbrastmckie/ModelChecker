# Implementation Summary: Task #147

- **Task**: 147 - Correct stale release and environment docs
- **Status**: [COMPLETED]
- **Started**: 2026-08-11T00:00:00Z
- **Completed**: 2026-08-11T01:00:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_release-env-docs-corrections.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Corrected drift between four documentation files and the shipped release pipeline / Nix
environment, surfaced by the 2026-08-11 release review (issues 2, 14, 16). `.github/workflows/README.md`
was reduced to a claim-free pointer stub; `.github/RELEASE_SETUP.md` got its test-matrix wording
and two archive paths fixed; `code/docs/development/ENVIRONMENT_SETUP.md` was brought in line with
the `>=3.10` Python floor, the lowercase `code/` directory, and the `flake.nix`/`nix develop`
workflow; and `docs/installation/BASIC_INSTALLATION.md` gained a new NixOS post-publish
verification recipe. `.github/workflows/release.yml` and `flake.nix` were confirmed unmodified
throughout.

## What Changed

- `.github/workflows/README.md` — full-content replacement with a 3-line pointer stub to
  `../RELEASE_SETUP.md`. No claims about the Python matrix, secrets, directory casing,
  `run_update.py`, or `twine` remain.
- `.github/RELEASE_SETUP.md` — three isolated string fixes: the test-matrix wording (`Python 3.8
  and 3.12` -> `Python 3.10, 3.11, and 3.12`), and both `specs/125_release_engineering_and_pypi_rehearsal/`
  path citations repointed to `specs/archive/125_release_engineering_and_pypi_rehearsal/`.
- `code/docs/development/ENVIRONMENT_SETUP.md` — Python floor corrected (3.8 -> 3.10, citing
  `requires-python`); four `ModelChecker/Code` casing occurrences fixed; all six `shell.nix`/
  `nix-shell` references migrated to `flake.nix`/`nix develop`, with the NixOS Setup subsections
  (Repository Setup, Development Shell, Automatic Environment Activation) restructured so the
  `cd` targets match where `flake.nix` and `.envrc` actually live (repo root, not `code/`).
- `docs/installation/BASIC_INSTALLATION.md` — new `### Verifying a Published Release on NixOS`
  subsection appended to the end of `## NixOS Installation`, containing the verbatim
  `testvenv` + `PIP_USER=0` + `LD_LIBRARY_PATH` recipe and explanatory prose, framed explicitly
  as a verification procedure rather than a recommended install path. Pure addition — the
  existing `nix develop` guidance is untouched.

## Decisions

- **`.github/workflows/README.md`**: reduced to a pointer stub rather than rewritten or deleted,
  per the plan's Decision 1 — a stub carries no claims so it cannot drift again, and it preserves
  the file's function as a GitHub web-UI entry point.
- **`ENVIRONMENT_SETUP.md` scope expansion**: per the plan's Decision 2, fixed all four
  `ModelChecker/Code` casing occurrences and all six `shell.nix`/`nix-shell` references, not just
  the two named in the task description — same file, same root cause, no new files touched.

## Plan Deviations

- **Phase 3, `ModelChecker/Code` casing fix (lines 100, 131)**: altered rather than a literal
  `cd ModelChecker/Code` -> `cd ModelChecker/code` substitution. `flake.nix` and `.envrc` live at
  the repository root, not under `code/`, so the NixOS "Repository Setup" and "Automatic
  Environment Activation" subsections were changed to `cd ModelChecker` (repo root) instead, and
  a new `cd code` step was added to the "Development Shell" subsection so the later Verification
  subsection's `./run_tests.py`/`./dev_cli.py` invocations (which live under `code/`) remain
  correct. This keeps the doc's working-directory flow internally consistent rather than
  producing a check (`ls flake.nix .envrc`) that would fail from inside `code/`.
- **Phase 3, Development Shell bullet list**: dropped the "makes development scripts executable"
  bullet when rewriting the `shell.nix` prose as `flake.nix` prose — `flake.nix`'s `shellHook` sets
  `PYTHONPATH` and its `devPython` package set provides dependencies (both verified true), but
  there is no chmod/executable-bit step anywhere in `flake.nix`, so that claim was dropped rather
  than restated, per the plan's own "verify each bullet, drop what the flake doesn't do"
  instruction.
- **Phase 4, `PIP_USER=0`/`stdenv.cc.cc.lib` prose wording**: the phase's own verification grep
  expects each literal string to match exactly once in the file. Natural prose explanation would
  otherwise repeat the code-block token, producing two matches each. Reworded the explanatory
  headings/prose to reference the concepts (`set PIP_USER to 0`, "the nixpkgs C++ standard
  library output above") without repeating the exact substrings; the code recipe itself is
  verbatim as specified.
- **Phase 5, out-of-scope `run_update.py` inventory**: the plan's Non-Goals section hypothesized
  seven files outside scope still citing `run_update.py`/`test_update.py`. Re-running the grep at
  implementation time found only **six**: `docs/installation/DEVELOPER_SETUP.md`,
  `code/README.md`, `code/docs/development/README.md`, `code/docs/development/TEST_RELEASES.md`,
  `code/docs/development/PACKAGE_TESTING.md`, and `code/docs/implementation/DEVELOPMENT_WORKFLOW.md`.
  `code/docs/development/PYPI_RELEASE_GUIDE.md` — the seventh file named in the plan — does not
  actually reference `run_update.py` or `test_update.py` anywhere in its current content. None of
  these six (or the previously-hypothesized seventh) files were edited; this is a corrected count
  for the follow-up recommendation below, not new work performed.

## Verification

- Build: N/A (documentation-only task)
- Tests: N/A (documentation-only task)
- Files verified: Yes — all four target files read in full before and after editing; every
  phase's grep-based verification criteria re-run and passing (see per-phase progress files).
- `.github/workflows/release.yml` and `flake.nix`: confirmed unmodified (`git diff --stat` empty
  for both) throughout every phase.
- `bash .claude/scripts/check-task-references.sh`: 109 pre-existing findings, all under
  `.opencode/`; none in any of the four edited files (no new findings introduced).

## Impacts

- A contributor following `.github/RELEASE_SETUP.md` (now the sole release doc) no longer hits a
  broken archive path or a wrong test-matrix description; `.github/workflows/README.md` no longer
  points anyone at a nonexistent `PYPI_API_TOKEN`/`run_update.py` flow.
- A NixOS contributor following `code/docs/development/ENVIRONMENT_SETUP.md` no longer runs into a
  nonexistent `shell.nix` or `nix-shell`, and the doc's working-directory instructions now
  actually resolve at each step.
- A NixOS user wanting to verify a freshly published release now has a documented, working
  recipe, clearly separated from the ordinary-use `nix develop` install path.

## Follow-ups

- **File a follow-up task** for the out-of-scope `run_update.py`/`test_update.py` drift, now
  confirmed to span **six** files (not the seven originally hypothesized — see Plan Deviations):
  `code/README.md`, `code/docs/development/README.md`, `code/docs/development/PACKAGE_TESTING.md`,
  `code/docs/development/TEST_RELEASES.md`, `code/docs/implementation/DEVELOPMENT_WORKFLOW.md`,
  and `docs/installation/DEVELOPER_SETUP.md`. Neither `run_update.py` nor `test_update.py` exists
  anywhere in the repository. The follow-up should either restore a real script matching the
  documented behavior or strip these six files' claims down to the actual CI release process
  already documented accurately in `.github/RELEASE_SETUP.md`.
- This task's `git status --short` also shows unrelated untracked artifacts
  (`.syncprotect`, `.orchestrator-multi-state*.json`, `specs/146_*` and `specs/149_*` working
  files) from a concurrent multi-task orchestration session running alongside this one. None of
  these paths were touched by this task and none are included in this task's commits.

## References

- Plan: `specs/147_correct_stale_release_and_environment_docs/plans/01_release-env-docs-corrections.md`
- Research: `specs/147_correct_stale_release_and_environment_docs/reports/01_release-env-docs-drift.md`
- Review that surfaced the drift: `specs/reviews/review-20260811.md` (issues 2, 14, 16)
