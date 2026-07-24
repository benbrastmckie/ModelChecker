# Implementation Plan: Task #125

- **Task**: 125 - release_engineering_and_pypi_rehearsal
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: Tasks 123 (Nix-verified build), 124 (docs/CHANGELOG refresh) — both complete
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md; parent plan phase 13 (specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md)
- **Artifacts**: plans/01_release-engineering-pypi-rehearsal.md (this file)
- **Standards**: plan-format.md, artifact-formats.md, plan-format-enforcement.md, pr-prohibition.md, git-workflow.md
- **Type**: general
- **Lean Intent**: false

## Overview

This plan implements plan phase 13 ("Release Engineering and Rehearsal") of the parent
`restore-model-checker-release` plan, now spawned as its own task. The predecessors are complete:
`code/pyproject.toml` already declares `name = "model-checker"` / `version = "1.3.0"`, the Nix flake
provides a green `packages.default` + `checks.default` gate, and `code/CHANGELOG.md` carries an
honest `## [1.3.0]` entry. The work here fixes and modernizes the GitHub release pipeline, rehearses
the build locally in a NixOS-safe way, verifies wheel identity/contents against the last published
release (1.2.12), and produces a user-gated publish checklist. No agent publishes to PyPI or pushes
to git — those remain strictly user-only actions per `pr-prohibition.md`.

### Research Integration

The parent team research (via the spawn-analysis report) established the concrete defects addressed
here: `.github/workflows/release.yml` uses `cd Code` (wrong casing; the directory is `code`) in both
the test-and-release and publish jobs; the publish job authenticates with a long-lived
`PYPI_API_TOKEN` secret rather than OIDC Trusted Publishing; and `.github/RELEASE_SETUP.md` documents
two workflows (`test-package.yml`, `pypi-release.yml`) that do not exist — the single real workflow
is `release.yml`. Direct inspection during planning confirmed all three, plus a fourth constraint:
the flake devShell (`nix develop`) ships only `nixZ3, setuptools, pip, networkx, pytest,
pytest-xdist` — it has **no** `build`, `twine`, or `check-wheel-contents`, and `flake.nix` is outside
this task's file scope. The local rehearsal must therefore install those tools into an isolated venv
created inside `nix develop`, never mutate the flake.

### Prior Plan Reference

No prior plan for task 125. The parent plan's phase 13 (lines 360-380) is the authoritative source
of scope and is reproduced faithfully here; its effort estimate (2.5 h) is adopted unchanged.

### Roadmap Alignment

`specs/ROADMAP.md` is an empty template with no items, and no `--roadmap` flag was passed. This plan
neither reads nor writes roadmap phases. Task 125 advances the parent task 117's release-readiness
objective (the final deliverable of the model-checker identity restoration).

## Goals & Non-Goals

**Goals**:
- Fix `.github/workflows/release.yml` directory casing (`cd Code` -> `cd code`) in both jobs.
- Migrate publishing to PyPI Trusted Publishing (OIDC) via `pypa/gh-action-pypi-publish@release/v1`
  in a separate, environment-gated (`pypi`) job with `permissions: id-token: write`; remove the
  long-lived `PYPI_API_TOKEN`.
- Add `twine check --strict dist/*` and a TestPyPI rehearsal step to the workflow.
- Reconcile `.github/RELEASE_SETUP.md` with the single actual workflow and the OIDC model.
- Perform a NixOS-safe local rehearsal: `python -m build`, `check-wheel-contents`,
  `twine check --strict`, and a wheel-content/hash parity diff vs `model-checker==1.2.12`; confirm
  the artifact is `model_checker-1.3.0` (not `bimodal_logic`) and excludes the oracle directory.
- Produce a step-by-step, user-gated publish checklist ending in user-only actions.

**Non-Goals**:
- Executing any PyPI upload (production or TestPyPI requiring credentials) — user-gated.
- Any `git push`, tag push, PR/MR creation, or `/merge` invocation — user-only per
  `pr-prohibition.md`.
- Modifying `flake.nix`, `code/pyproject.toml`, `code/MANIFEST.in`, or `code/CHANGELOG.md` — those
  are the finished output of tasks 123/124 and are outside this task's file scope. This task reads
  them as ground truth only.
- Changing the version number (1.3.0 is confirmed, not re-decided).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Rehearsal tools (`build`, `twine`, `check-wheel-contents`) absent from the flake devShell; installing them system-wide fails on NixOS | M | H | Create an isolated venv **inside** `nix develop` (`python -m venv`), `pip install` the tools there; never touch `flake.nix` (out of scope) |
| OIDC Trusted Publishing misconfigured (wrong environment name, missing `id-token: write`, artifact not passed between jobs) breaks a real release | H | M | Follow `pypa/gh-action-pypi-publish` canonical pattern: build once, `upload-artifact`/`download-artifact`, dedicated `pypi` environment job with `id-token: write`; validate YAML parses and job graph is correct; document the required PyPI trusted-publisher + GitHub Environment setup in RELEASE_SETUP.md |
| Parity diff vs 1.2.12 flags many differences and is misread as a regression | M | M | Pre-classify expected deltas (restored `builder`/`iterate`/`jupyter`/`output`, restored `exclusion`/`imposition`, removed first-order subtheory, relocated/excluded oracle) so reviewer distinguishes intended changes from accidents; document the diff, do not gate the release on byte-identity |
| Accidental real upload during rehearsal | H | L | Rehearsal never calls `twine upload`; only `twine check --strict`. TestPyPI/PyPI uploads are user-gated in the checklist. No credentials are used by the agent |
| Workflow still references stale token / wrong paths after edit | M | M | Grep the final `release.yml` and `RELEASE_SETUP.md` for `PYPI_API_TOKEN`, `cd Code`, `test-package.yml`, `pypi-release.yml`; assert zero matches |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. Phase 4 (local rehearsal) is independent of
the workflow/doc edits and may run concurrently with Phase 1; its results feed the Phase 5 checklist.

### Phase 1: Fix release.yml Directory Casing [COMPLETED]

**Goal**: Correct the `cd Code` -> `cd code` casing bug in every job so the workflow's build/test
steps operate in the real package directory.

**Tasks**:
- [x] In `.github/workflows/release.yml`, change `cd Code` to `cd code` in the test-and-release job
      (install-and-test step) and in the publish job (build step and publish step) — three
      occurrences. *(completed)*
- [x] Fix the `Create GitHub Release` step's CHANGELOG link to the real path
      (`code/CHANGELOG.md`, `blob/master/...`) rather than `blob/main/CHANGELOG.md`. *(completed)*
- [x] Grep the file to confirm no remaining `cd Code` (capital C) occurrences. *(completed)*

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `.github/workflows/release.yml` — directory casing in both jobs; CHANGELOG link path.

**Verification**:
- `grep -n 'cd Code' .github/workflows/release.yml` returns nothing.
- The YAML still parses (e.g. `python -c "import yaml,sys; yaml.safe_load(open('.github/workflows/release.yml'))"`).

---

### Phase 2: Migrate Publishing to OIDC Trusted Publishing [COMPLETED]

**Goal**: Replace the long-lived-token publish job with a build-once / publish-via-OIDC job graph
using `pypa/gh-action-pypi-publish@release/v1`, add `twine check --strict`, and add a TestPyPI
rehearsal step.

**Tasks**:
- [x] Restructure the workflow into a build stage and separate publish stages:
      - Keep/refit `test-and-release` as the cross-platform test matrix (unchanged intent).
      - Add a `build` job (runs once on ubuntu) that: `cd code`, `python -m build`,
        `twine check --strict dist/*`, then `actions/upload-artifact` the `dist/` contents.
      *(completed)*
- [x] Add a `publish-testpypi` job: `needs: [test-and-release, build]`, `environment: testpypi`,
      `permissions: id-token: write`, `actions/download-artifact` the dist, then
      `pypa/gh-action-pypi-publish@release/v1` with
      `repository-url: https://test.pypi.org/legacy/`. Make it non-fatal/skippable if the TestPyPI
      trusted publisher is not yet configured (document the dependency; do not hard-block prod on it
      unless desired). *(completed: used `continue-on-error: true` on the job)*
- [x] Add a `publish-pypi` job: `needs: [build, publish-testpypi]` (or `[test-and-release, build]`),
      `environment: pypi`, `permissions: id-token: write`, download the same artifact, then
      `pypa/gh-action-pypi-publish@release/v1` (default PyPI). No `TWINE_USERNAME`/`TWINE_PASSWORD`,
      no `PYPI_API_TOKEN`. *(completed)*
- [x] Remove the entire `PYPI_API_TOKEN` env/secret block and its "missing token" error handling.
      *(completed)*
- [x] Preserve the `Create GitHub Release` step (needs `contents: write`), attached to the publish
      job or a final release job. *(completed: new `github-release` job, needs: publish-pypi)*
- [x] Confirm top-level/job-level `permissions` grant `id-token: write` only where needed and retain
      `contents: write` for the release step. *(completed: top-level scoped to `contents: read`,
      job-level grants add only what each job needs)*

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `.github/workflows/release.yml` — job graph, OIDC publish jobs, artifact passing, twine check.

**Verification**:
- `grep -n 'PYPI_API_TOKEN' .github/workflows/release.yml` returns nothing.
- `grep -n 'id-token: write' .github/workflows/release.yml` present in each publish job.
- `grep -n 'gh-action-pypi-publish' .github/workflows/release.yml` present; `twine check --strict`
  present.
- YAML parses; job `needs:` graph is acyclic and correct (test/build -> testpypi -> pypi -> release).

---

### Phase 3: Reconcile RELEASE_SETUP.md with Reality [COMPLETED]

**Goal**: Rewrite `.github/RELEASE_SETUP.md` to describe the single actual `release.yml` workflow and
the OIDC Trusted Publishing model, removing the obsolete token-based instructions and nonexistent
workflow filenames.

**Tasks**:
- [x] Replace the "Required Secrets / PYPI_API_TOKEN" section with a "Trusted Publishing (OIDC)
      Setup" section: register a PyPI trusted publisher (repo `benbrastmckie/ModelChecker`, workflow
      `release.yml`, environment `pypi`) and, optionally, a TestPyPI trusted publisher (environment
      `testpypi`); create the matching GitHub Environments (`pypi`, `testpypi`) with any desired
      protection rules. No long-lived secrets required. *(completed)*
- [x] Replace the "Workflow Overview" section's references to `test-package.yml` /
      `pypi-release.yml` with an accurate description of the single `release.yml` (test matrix ->
      build+twine-check -> TestPyPI -> PyPI -> GitHub Release). *(completed)*
- [x] Update "Common Issues" and "Testing the Setup" to match OIDC (no `gh secret` for PyPI token;
      instead verify the trusted-publisher + environment configuration). *(completed)*
- [x] Keep the release-process (tag `vX.Y.Z`) narrative but align it with the user-gated checklist
      from Phase 5. *(completed: cross-references PUBLISH-CHECKLIST.md and pr-prohibition.md)*

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `.github/RELEASE_SETUP.md` — full reconciliation to single workflow + OIDC.

**Verification**:
- `grep -nE 'PYPI_API_TOKEN|test-package\.yml|pypi-release\.yml' .github/RELEASE_SETUP.md` returns
  nothing.
- Document names only the real `release.yml`; OIDC/Environment setup steps are present.

---

### Phase 4: NixOS-Safe Local Build Rehearsal and Parity Diff [COMPLETED]

**Goal**: Rehearse the exact build the workflow will run, verify artifact identity/contents, and
diff against the last published release, recording all evidence under the task directory.

**Tasks**:
- [x] Enter `nix develop`; create an isolated venv (`python -m venv "$TMPDIR/rehearsal-venv"`,
      activate) so `flake.nix` is never modified; `pip install build twine check-wheel-contents`
      into the venv. *(completed: required `PIP_USER=0`/`--no-user` because
      `~/.config/pip/pip.conf` sets `install.user=true` globally on this NixOS host; also required
      running the entire venv+build+check+diff sequence in a single `nix develop` invocation
      since each invocation gets a fresh, non-persisting `TMPDIR`)*
- [x] `cd code && python -m build`; capture `dist/` listing. Confirm the artifacts are
      `model_checker-1.3.0-*.whl` and `model_checker-1.3.0.tar.gz` — **not** `bimodal_logic`.
      *(completed: confirmed)*
- [x] `check-wheel-contents dist/*.whl` — expect clean; explicitly confirm the relocated top-level
      `oracle/` tree is absent from the wheel. *(completed: `OK`, no oracle path found in wheel
      or sdist)*
- [x] `twine check --strict dist/*` — expect PASS. *(completed: PASSED for wheel and sdist)*
- [x] `pip download --no-deps model-checker==1.2.12 -d "$TMPDIR/ref"`; unzip both wheels and diff the
      `RECORD`/file listings; compute `sha256` of each artifact. Classify differences against the
      expected deltas (restored `builder`/`iterate`/`jupyter`/`output`, restored
      `exclusion`/`imposition`, removed first-order subtheory, relocated/excluded oracle).
      *(completed: see parity-diff.md — those four items are already true of 1.2.12 itself, so
      they show no delta against this baseline; actual deltas found were a new `solver/` module
      and removed dead `cli.py`, both intended)*
- [x] Write the evidence to `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/`:
      `build.log`, `wheel-contents.txt`, `twine-check.txt`, `parity-diff.md` (with hashes and the
      classified delta table). *(completed, plus sha256sums.txt, new/ref wheel file listings,
      top-level-dir-diff.txt, wheel-files-diff.txt, pip-download-1.2.12.log)*

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/*` — rehearsal evidence artifacts
  (task-directory outputs; no repository source is changed by this phase).

**Verification**:
- Built artifact name is `model_checker-1.3.0`; oracle directory excluded from the wheel.
- `check-wheel-contents` clean; `twine check --strict dist/*` passes.
- Parity diff vs 1.2.12 captured with hashes and an intended-vs-accidental classification.

---

### Phase 5: User-Gated Publish Checklist [COMPLETED]

**Goal**: Confirm the final version and hand the user a step-by-step publish checklist that ends in
the user-only actions, with publish and push explicitly marked user-gated.

**Tasks**:
- [x] Confirm the final version is `1.3.0` (matches `code/pyproject.toml` and the `## [1.3.0]`
      CHANGELOG entry); note the confirmation in the checklist. *(completed)*
- [x] Write `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` covering:
      pre-flight (green tests / `nix build` / `nix flake check` / rehearsal reviewed), one-time OIDC
      setup pointer to RELEASE_SETUP.md, and the ordered release steps. *(completed)*
- [x] Mark every remote/irreversible step as **USER-ONLY**: the user pushes the branch, the user
      creates and pushes the `v1.3.0` tag (or invokes `/merge`), the user triggers/monitors the
      release workflow, the user performs any TestPyPI upload requiring credentials, and PyPI
      publish happens via OIDC on the user-pushed tag. State plainly that the agent performs none of
      these. *(completed)*
- [x] Cross-reference the Phase 4 rehearsal evidence and RELEASE_SETUP.md from the checklist.
      *(completed)*

**Timing**: 0.25 hours

**Depends on**: 3, 4

**Files to modify**:
- `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` — user-gated checklist.

**Verification**:
- Checklist exists, confirms version 1.3.0, ends in user-only actions, and marks publish + push as
  user-gated.
- No step instructs the agent to push, tag-push, upload to PyPI/TestPyPI, or run `/merge`.

---

## Testing & Validation

- [ ] `grep -n 'cd Code' .github/workflows/release.yml` → no matches.
- [ ] `grep -n 'PYPI_API_TOKEN' .github/workflows/release.yml .github/RELEASE_SETUP.md` → no matches.
- [ ] `release.yml` parses as YAML; publish jobs carry `permissions: id-token: write`,
      `environment: pypi`/`testpypi`, and use `pypa/gh-action-pypi-publish@release/v1`.
- [ ] `twine check --strict dist/*` passes on the locally built artifacts.
- [ ] `check-wheel-contents dist/*.whl` clean; wheel named `model_checker-1.3.0`, oracle excluded.
- [ ] Parity diff vs `model-checker==1.2.12` captured with hashes and reviewed.
- [ ] `RELEASE_SETUP.md` references only `release.yml` and documents OIDC/Environment setup.
- [ ] `PUBLISH-CHECKLIST.md` present, ends in user-only actions, publish/push marked user-gated.

## Artifacts & Outputs

- `.github/workflows/release.yml` — casing fixed, OIDC Trusted Publishing, `twine check --strict`,
  TestPyPI rehearsal step.
- `.github/RELEASE_SETUP.md` — reconciled to the single workflow and OIDC model.
- `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/` — build log, wheel-contents listing,
  twine-check output, parity-diff report with hashes.
- `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` — user-gated publish
  checklist.
- `specs/125_release_engineering_and_pypi_rehearsal/summaries/01_release-engineering-pypi-rehearsal-summary.md`
  (on completion).

## Rollback/Contingency

- All source edits are confined to two version-controlled files under `.github/`; either can be
  reverted independently via `git revert`/`git checkout` of the specific commit without affecting
  package code.
- The local rehearsal writes only to `$TMPDIR` (venv, dist copies, reference downloads) and to the
  task directory; nothing under `code/` or `flake.nix` is mutated, so there is nothing to roll back
  in the package itself.
- No PyPI/TestPyPI upload and no `git push`/tag-push occurs during implementation; the irreversible
  publish is gated entirely on explicit user action after the rehearsal is reviewed, so there is
  nothing to roll back on any package index.
- If OIDC Trusted Publishing cannot be configured by release time, the checklist documents the
  fallback of re-adding a scoped API token as a stopgap — but this is a documented contingency, not
  the plan; the default deliverable is token-free OIDC.
