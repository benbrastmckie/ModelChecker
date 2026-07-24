# Implementation Summary: Task #125

**Completed**: 2026-07-24
**Duration**: ~2 hours

## Overview

Fixed and modernized the GitHub release pipeline (`.github/workflows/release.yml`), migrated
publishing from a long-lived `PYPI_API_TOKEN` secret to PyPI Trusted Publishing (OIDC),
reconciled `.github/RELEASE_SETUP.md` with the single real workflow, rehearsed the build locally
in a NixOS-safe isolated venv, and produced a user-gated publish checklist. No PyPI/TestPyPI
upload, `git push`, tag push, or PR/`/merge` action was performed — those remain strictly
user-only per `.claude/rules/pr-prohibition.md`.

## What Changed

- `.github/workflows/release.yml` — fixed `cd Code` -> `cd code` casing bug (3 occurrences);
  fixed the CHANGELOG link to `code/CHANGELOG.md` on `blob/master`; restructured the single
  `publish` job into a `build` job (once, on Ubuntu: `python -m build`,
  `twine check --strict dist/*`, `upload-artifact`) plus two OIDC publish jobs
  (`publish-testpypi`, `permissions: id-token: write`, `environment: testpypi`,
  `continue-on-error: true`; `publish-pypi`, `permissions: id-token: write`,
  `environment: pypi`) both using `pypa/gh-action-pypi-publish@release/v1`; removed the entire
  `PYPI_API_TOKEN` env/secret block and its "missing token" error handling; moved the
  `Create GitHub Release` step into a new `github-release` job (`needs: publish-pypi`,
  `permissions: contents: write`); scoped top-level `permissions` down to `contents: read` with
  each job granting only what it needs.
- `.github/RELEASE_SETUP.md` — fully rewritten: replaced the "Required Secrets" section with a
  "Trusted Publishing (OIDC) Setup" section (PyPI/TestPyPI trusted publisher registration, `pypi`
  and `testpypi` GitHub Environments); replaced the "Workflow Overview" (previously describing
  two nonexistent workflows, `test-package.yml`/`pypi-release.yml`) with an accurate description
  of the single `release.yml` five-job pipeline; updated "Common Issues" and "Testing the Setup"
  to the OIDC model; kept the release-process narrative but pointed it at the new
  `PUBLISH-CHECKLIST.md`.
- `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/` — created; contains
  `build.log` (gitignored, see Notes), `wheel-contents.txt`, `twine-check.txt`,
  `pip-download-1.2.12.log` (gitignored), `sha256sums.txt`, `new-wheel-files.txt`,
  `ref-1.2.12-wheel-files.txt`, `top-level-dir-diff.txt`, `wheel-files-diff.txt`, and
  `parity-diff.md` — the full local rehearsal evidence (build, wheel-content check, strict twine
  check, and a classified parity diff against the last published `model-checker==1.2.12`).
- `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` — created; a
  step-by-step user-gated publish checklist ending in user-only push/tag/publish actions.

## Decisions

- Used `continue-on-error: true` on the `publish-testpypi` job rather than an `if:` condition, so
  a not-yet-configured TestPyPI trusted publisher never blocks the production `publish-pypi` job,
  while still surfacing a visible failure indicator in the Actions UI if it does fail.
- Scoped top-level workflow `permissions` down to `contents: read` and pushed `id-token: write`
  / `contents: write` to the individual jobs that need them, rather than keeping a broad
  top-level grant — least-privilege, and it makes the OIDC requirement self-documenting per job.
- Split the single `dist`-name workflow artifact between the `build` job (`upload-artifact`) and
  both publish jobs (`download-artifact`) so the exact bytes that passed `twine check --strict`
  are what gets published — never rebuilt per-job.
- For the local rehearsal, built an isolated venv **inside** `nix develop` (never touching
  `flake.nix`) and had to add `PIP_USER=0`/`--no-user` to every `pip install`, because
  `~/.config/pip/pip.conf` on this NixOS host sets `install.user=true` globally, which a venv
  rejects. Also had to run the entire venv-creation + build + check + parity-diff sequence as a
  single script inside one `nix develop` invocation, because `nix develop` assigns a fresh,
  non-persisting `TMPDIR` (a new `nix-shell.XXXXXX` subdirectory) on every separate invocation —
  a venv created in one invocation does not exist in the next.
- In the parity diff against `model-checker==1.2.12`, several deltas the plan's Risks table
  anticipated (restored `builder`/`iterate`/`jupyter`/`output`, restored
  `exclusion`/`imposition`, removed first-order subtheory) turned out to already be true of
  1.2.12 itself — 1.2.12 is not the right baseline to observe those specific changes. This is
  documented explicitly in `parity-diff.md` so a reviewer does not misread "no delta" as "the
  restoration didn't happen." The actual deltas found (a new `model_checker/solver/` module, a
  removed dead `model_checker/cli.py`) were both confirmed intended via `git log`.

## Plan Deviations

- None (implementation followed plan).

## Verification

- Build: N/A (no code build system for this task; the release.yml YAML was validated with
  `python -c "import yaml; yaml.safe_load(...)"` — passed).
- Tests: N/A (no Python test suite changed).
- Files verified: Yes — all Testing & Validation checklist items from the plan were re-run and
  passed:
  - `grep -n 'cd Code' .github/workflows/release.yml` → no matches.
  - `grep -n 'PYPI_API_TOKEN' .github/workflows/release.yml .github/RELEASE_SETUP.md` → no
    matches.
  - `release.yml` parses as YAML; `publish-testpypi`/`publish-pypi` carry
    `permissions: id-token: write` and `environment: testpypi`/`pypi`; both use
    `pypa/gh-action-pypi-publish@release/v1`.
  - `twine check --strict dist/*` → PASSED for `model_checker-1.3.0-py3-none-any.whl` and
    `model_checker-1.3.0.tar.gz`.
  - `check-wheel-contents dist/*.whl` → `OK`; wheel named `model_checker-1.3.0-py3-none-any.whl`;
    no `oracle` path in wheel or sdist.
  - Parity diff vs `model-checker==1.2.12` captured with SHA256 hashes and a classified delta
    table in `parity-diff.md`.
  - `RELEASE_SETUP.md` references only `release.yml`; documents OIDC/Environment setup.
  - `PUBLISH-CHECKLIST.md` present, confirms version 1.3.0, ends in user-only actions, marks
    push/tag/publish as **USER-ONLY**.

## Notes

- `build.log` and `pip-download-1.2.12.log` in the rehearsal directory are excluded from git
  tracking by the repository's global `*.log` `.gitignore` rule (out of this task's file scope to
  change). Both files exist on disk in the working tree as required by the plan; all other
  rehearsal evidence files (`wheel-contents.txt`, `twine-check.txt`, `sha256sums.txt`,
  `new-wheel-files.txt`, `ref-1.2.12-wheel-files.txt`, `top-level-dir-diff.txt`,
  `wheel-files-diff.txt`, `parity-diff.md`) are committed.
- The rehearsal's `dist/` build output under `code/dist/` is gitignored (`**/dist` in
  `.gitignore`) and was left in place after the rehearsal, not deleted or committed — consistent
  with the plan's Rollback/Contingency section (nothing under `code/` is mutated by this task; the
  build output there is a disposable local artifact, not tracked source).
- No PyPI/TestPyPI upload, `git push`, tag push, or PR/`/merge` action was performed by this
  agent at any point, per the task's hard constraints and `.claude/rules/pr-prohibition.md`. The
  task ends with `PUBLISH-CHECKLIST.md` awaiting the user.
