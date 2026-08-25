# Implementation Summary: Wheel and Sdist Packaging Contract Tests

- **Task**: 149 - wheel_and_sdist_packaging_contract_tests
- **Status**: [COMPLETED]
- **Started**: 2026-08-11T19:14:28-07:00
- **Completed**: 2026-08-12T02:40:32Z
- **Effort**: 6 hours (plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_packaging-contract-tests.md, reports/01_packaging-contract-tests.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`code/pyproject.toml`'s `[tool.setuptools.package-data]` allowlist and `code/MANIFEST.in`'s sdist
rules previously asserted their sync-with-each-other invariant only in comments, with nothing
executable enforcing it and no CI job running on every push/PR. This task added an executable
`code/tests/packaging/` suite (108 tests under the new `packaging` pytest marker) that builds a
fresh wheel and sdist into a pytest temp directory and asserts exclusions, registry-driven
inclusions, wheel/sdist parity, and console-script installability, then wired two CI entry points
so the suite actually runs.

## What Changed

- `code/tests/packaging/` — new subpackage: `conftest.py` (build fixtures), `test_exclusions.py`,
  `test_inclusions.py` (registry-driven, `AVAILABLE_THEORIES`-parametrized), `test_parity.py`,
  `test_entry_point.py`, `test_build_smoke.py`. All five test modules carry
  `pytestmark = [pytest.mark.packaging, pytest.mark.slow]`.
- `code/pyproject.toml` — registered the `packaging` marker in `[tool.pytest.ini_options]`
  `markers`.
- `.github/workflows/packaging.yml` (new) — push/PR-triggered job that checks out, sets up Python
  3.11, installs `pytest` + `build`, and runs `cd code && python -m pytest tests/packaging/ -v -m
  packaging`. Narrowly scoped by design; does not run the general suite.
- `.github/workflows/release.yml` — one additive step ("Run packaging contract tests") added to
  the existing `build` job, after `twine check --strict` and before the `Upload distribution
  artifact` step. No changes to triggers, the test-and-release matrix, or any publish step.
- `.github/workflows/README.md` — added a `## Workflows` section (appended onto the pointer-stub
  content another concurrent task had already rewritten this file to) describing all three
  workflows in the directory: `release.yml`, `packaging.yml`, `differential-tests.yml`.
- `code/tests/packaging/conftest.py` — post-hoc fix (found by the plan's own deliberate-drift
  smoke check, run after all 6 phases were first marked complete): `built_artifacts` now clears
  `code/build/` and `src/model_checker.egg-info/` immediately before and after every session
  build. See "Decisions" below for why this was necessary.

## Decisions

- CI-gap remediation scope held to the minimum needed to satisfy the task's own "ensure whatever
  CI job runs them actually does run them" instruction: one new narrowly-scoped workflow plus one
  additive step in the existing release workflow, not a general full-suite CI job (explicit
  non-goal, stated in the plan and preserved here).
- `.github/workflows/` is outside task 149's declared `file_scope`
  (`code/pyproject.toml`, `code/MANIFEST.in`, `code/tests/packaging/`); the plan's Phase 6
  explicitly sanctions this expansion as the minimum necessary to satisfy the task description,
  and this implementation kept the expansion to exactly the three workflow files the plan named.
- The release.yml packaging-test step reinstalls `pytest` inline (`pip install pytest`) rather
  than depending on any prior job's environment, since the `build` job is a fresh
  `ubuntu-latest` runner with no pytest installed yet at that point.
- The Testing & Validation checklist's deliberate-drift smoke check (temporarily remove
  `docs/*.md` from `pyproject.toml`'s package-data, rebuild, confirm red, revert) initially
  false-passed: `python -m build --no-isolation` runs setuptools' legacy commands in place
  against `code/`, and `build_py`/`egg_info` are incremental by default, so a pre-existing stale
  `code/build/` (from an old manual build) let the "fresh" build silently ship already-copied
  `docs/*.md` files even after the config change. `--outdir` only redirects the final artifact
  location, never the intermediate caches. Fixed by clearing `code/build/` and
  `src/model_checker.egg-info/` (never `code/dist/`) before and after every session build;
  re-running the smoke check then correctly turned 40 assertions red, and green again on revert.

## Plan Deviations

- None from the plan's phase structure or scope (all 6 phases closed as originally planned). One
  post-hoc correction was made after all phases first reached green: `built_artifacts` in
  `code/tests/packaging/conftest.py` was fixed to clear setuptools' incremental build caches
  before/after each build, per the stale-build-cache defect recorded above and in the plan's
  Phase 1 section and Testing & Validation checklist. This is a bugfix within Phase 1's existing
  scope, not a scope change.

## Impacts

- Every push and pull request now runs a dedicated, fast-selectable packaging-contract check via
  `packaging.yml` (`-m packaging`, 108 tests, ~7s locally).
- Every tag-triggered release build is now contents-verified (via a fresh rebuild of the same
  commit) in addition to the pre-existing `twine check --strict` metadata check, before the
  built artifact is uploaded — a packaging-contract regression now blocks a release rather than
  only being caught after the fact.
- `.github/workflows/README.md` now documents all three workflows in the directory in one place,
  rather than only pointing to `RELEASE_SETUP.md`.

## Follow-ups

- None identified. The suite's `packaging`/`slow` marker pairing already keeps it deselectable
  from a fast local iteration loop (`-m "not slow"` or `-m "not packaging"`), and CI coverage
  is now in place on both the push/PR and release paths.

## References

- `specs/149_wheel_and_sdist_packaging_contract_tests/plans/01_packaging-contract-tests.md`
- `specs/149_wheel_and_sdist_packaging_contract_tests/reports/01_packaging-contract-tests.md`
- `code/tests/packaging/`
- `.github/workflows/packaging.yml`
- `.github/workflows/release.yml`
- `.github/workflows/README.md`
