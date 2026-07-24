# Publish Checklist: model-checker 1.3.0

This checklist walks through publishing `model-checker` 1.3.0. It ends in **user-only** actions
per `.claude/rules/pr-prohibition.md`: no agent pushes commits, pushes tags, creates PRs, invokes
`/merge`, or uploads to PyPI/TestPyPI. Steps below are explicitly marked **USER-ONLY** where that
applies; every other step is informational/verification and can be done by either the user or an
agent, but nothing in this checklist authorizes an agent to perform the USER-ONLY steps.

## 0. Version Confirmation

- **Confirmed**: the release version is **1.3.0**.
  - `code/pyproject.toml`: `name = "model-checker"`, `version = "1.3.0"`.
  - `code/CHANGELOG.md`: carries a `## [1.3.0] - 2026-07-24` entry (not `[Unreleased]`).
  - These two sources agree; no version bump is needed before tagging.

## 1. Pre-Flight Checks (verify before tagging)

- [ ] Tests are green. Re-run the project's test suite (or at minimum the Nix-gated subset) and
      confirm no regressions:
      ```bash
      nix flake check
      ```
- [ ] `nix build` succeeds and produces `packages.default`:
      ```bash
      nix build
      ```
- [ ] Review the Phase 4 local rehearsal evidence in
      `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/`:
      - `parity-diff.md` — artifact identity (`model_checker-1.3.0`, no `oracle/`), clean
        `check-wheel-contents`, `twine check --strict` PASSED on both wheel and sdist, and the
        classified diff against the last published release (1.2.12).
      - `twine-check.txt`, `wheel-contents.txt`, `sha256sums.txt` — raw evidence backing the
        summary above.
  - If anything in the rehearsal evidence looks wrong (unexpected files, wrong package name,
    failed checks), stop and investigate before tagging — do not proceed to step 2.
- [ ] Confirm `.github/workflows/release.yml` and `.github/RELEASE_SETUP.md` reflect the current
      state (Phases 1-3 of this task): no `cd Code` casing bug, no `PYPI_API_TOKEN` references,
      OIDC Trusted Publishing job graph (`build` -> `publish-testpypi` -> `publish-pypi` ->
      `github-release`).

## 2. One-Time OIDC Setup (skip if already configured)

Trusted Publishing (OIDC) must be configured on PyPI (and optionally TestPyPI) **before** the
first tag-triggered publish succeeds. Full instructions:
`.github/RELEASE_SETUP.md` (`Trusted Publishing (OIDC) Setup` section). In outline:

- [ ] **USER-ONLY**: register a PyPI trusted publisher for
      `benbrastmckie/ModelChecker`, workflow `release.yml`, environment `pypi`.
- [ ] **USER-ONLY** (optional, for the TestPyPI rehearsal job): register a TestPyPI trusted
      publisher, environment `testpypi`.
- [ ] **USER-ONLY**: create the `pypi` and `testpypi` GitHub Environments under
      **Settings → Environments** on the repository, with any desired protection rules (e.g.
      required reviewers on `pypi`).

If this step was already completed for a prior release, skip to step 3.

## 3. Ordered Release Steps

1. [ ] **USER-ONLY**: push the branch containing this task's changes to the remote (or land it via
       `/merge`, which itself is a user-invoked command — an agent never invokes `/merge`):
       ```bash
       git push origin <branch>
       ```
2. [ ] **USER-ONLY**: once the release-prep changes are on the default branch, create and push the
       version tag:
       ```bash
       git tag v1.3.0
       git push origin v1.3.0
       ```
3. [ ] **USER-ONLY**: the tag push triggers `.github/workflows/release.yml` automatically. Monitor
       it at https://github.com/benbrastmckie/ModelChecker/actions:
       - `test-and-release` (cross-platform test matrix) must pass first.
       - `build` builds the wheel/sdist once and runs `twine check --strict`.
       - `publish-testpypi` publishes to TestPyPI via OIDC (`continue-on-error: true` — a failure
         here does not block the next job; investigate anyway if it fails unexpectedly).
       - `publish-pypi` publishes to production PyPI via OIDC. **This is the point of no return**
         for this version number on the index (though `skip-existing: true` makes a re-run safe).
       - `github-release` creates the GitHub Release for the tag.
4. [ ] **USER-ONLY**: if TestPyPI or PyPI require any manual credential-based upload step outside
       the automated OIDC workflow (e.g. a manual `twine upload` fallback), that upload is
       performed by the user only — no agent runs `twine upload` under any circumstance.
5. [ ] Verify the published package:
       ```bash
       pip index versions model-checker   # or: pip install model-checker==1.3.0 --dry-run
       ```
       Confirm PyPI shows `1.3.0` and the GitHub Release page for `v1.3.0` exists with the
       expected notes linking `code/CHANGELOG.md`.

## Summary: What the Agent Never Does

Per `.claude/rules/pr-prohibition.md`, no agent involved in this task performs any of the
following — all of it is exclusively the user's action:

- `git push` (branch or tag, any form)
- `git tag` followed by a push of that tag
- Creating a pull/merge request, or invoking `/merge`
- Uploading to TestPyPI or PyPI via `twine upload` or any other credentialed method
- Configuring PyPI/TestPyPI trusted publishers or GitHub Environments

This task's agent work ends at the pre-flight/rehearsal evidence and this checklist. Everything
from "push the branch" onward in Section 3 is performed by the user.

## References

- `.github/RELEASE_SETUP.md` — full OIDC Trusted Publishing setup and workflow overview.
- `.github/workflows/release.yml` — the release pipeline itself (Phases 1-2 of this task).
- `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/parity-diff.md` — local rehearsal
  evidence and parity diff against `model-checker==1.2.12`.
- `.claude/rules/pr-prohibition.md` — the standing prohibition on agent push/PR/publish actions.
