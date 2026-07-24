# GitHub Release Pipeline Setup Guide

## Prerequisites

Releases publish to PyPI via **Trusted Publishing (OIDC)** — GitHub Actions authenticates to
PyPI directly using a short-lived OpenID Connect token issued for the workflow run. There is no
long-lived API token to create, store, or rotate.

## Trusted Publishing (OIDC) Setup

### 1. PyPI Trusted Publisher (Required)

1. Go to https://pypi.org and log in to the account that owns the `model-checker` project (or,
   for the first-ever publish of a brand-new project, use the "pending publisher" flow on
   https://pypi.org/manage/account/publishing/).
2. Navigate to the `model-checker` project's **Settings → Publishing** page (or
   **Account Settings → Publishing** for a pending publisher).
3. Add a new trusted publisher with:
   - **Owner**: `benbrastmckie`
   - **Repository name**: `ModelChecker`
   - **Workflow name**: `release.yml`
   - **Environment name**: `pypi`
4. Save. No token is generated or copied — PyPI now trusts OIDC tokens minted by the
   `release.yml` workflow when it runs under the `pypi` GitHub Environment.

### 2. TestPyPI Trusted Publisher (Optional, for the TestPyPI rehearsal step)

1. Go to https://test.pypi.org and create/log in to an account.
2. Register (or create) the `model-checker` project there, then add a trusted publisher the same
   way as above, but with **Environment name**: `testpypi`.
3. If this is skipped, the workflow's `publish-testpypi` job still runs but fails gracefully
   (`continue-on-error: true`) without blocking the production `publish-pypi` job — see
   "Workflow Overview" below.

### 3. GitHub Environments

Create two [GitHub Environments](https://github.com/benbrastmckie/ModelChecker/settings/environments)
matching the names configured on PyPI/TestPyPI above:

- `pypi` — used by the `publish-pypi` job. Optionally add required reviewers or a deployment
  branch/tag rule restricting it to `v*.*.*` tags for an extra manual gate before production
  publish.
- `testpypi` — used by the `publish-testpypi` job. Typically left unprotected since it only
  reaches TestPyPI.

No repository secrets are required for either environment — Trusted Publishing uses the
workflow's OIDC identity, not a stored credential.

## Workflow Overview

There is a single workflow, `.github/workflows/release.yml`, triggered on push of a version tag
(`v[0-9]+.[0-9]+.[0-9]+`, e.g. `v1.3.0`). It runs five jobs in this order:

1. **`test-and-release`** — cross-platform test matrix (Ubuntu/macOS/Windows, Python 3.8 and
   3.12): builds the package, installs the wheel, verifies the import and CLI work, and confirms
   the installed version matches the pushed tag.
2. **`build`** (needs `test-and-release`) — builds the wheel and sdist once on Ubuntu
   (`python -m build` in `code/`), runs `twine check --strict dist/*`, and uploads the `dist/`
   contents as a workflow artifact named `dist`.
3. **`publish-testpypi`** (needs `test-and-release`, `build`; environment `testpypi`) —
   downloads the `dist` artifact and publishes it to TestPyPI via
   `pypa/gh-action-pypi-publish@release/v1` using OIDC. Runs with `continue-on-error: true` so an
   unconfigured or already-published TestPyPI rehearsal never blocks the production publish.
4. **`publish-pypi`** (needs `build`, `publish-testpypi`; environment `pypi`) — downloads the
   same `dist` artifact and publishes it to production PyPI via the same action, again using
   OIDC (`permissions: id-token: write`, no repository-url override).
5. **`github-release`** (needs `publish-pypi`) — creates the GitHub Release for the tag via
   `gh release create`, linking to `code/CHANGELOG.md`.

Top-level workflow permissions default to `contents: read`; each job grants only the additional
permission it needs (`id-token: write` for the two publish jobs, `contents: write` for
`github-release`).

## Release Process

Releasing is a **user-only** sequence — see
`specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` for the full step-by-step
checklist. In outline:

1. Confirm `code/pyproject.toml`'s `version` and the latest `code/CHANGELOG.md` entry agree on the
   release version.
2. Commit any final release-prep changes.
3. Tag the release commit `vX.Y.Z` and push both the branch and the tag
   (`git push origin <branch>` then `git push origin vX.Y.Z`), or use `/merge` to land the branch
   first and tag afterward.
4. Pushing the tag triggers `release.yml`: tests run, the distribution is built and checked, then
   published to TestPyPI and PyPI via Trusted Publishing, then the GitHub Release is created.

No script automates step 3 for this repository; it is performed manually (or via `/merge`) by the
user, per `.claude/rules/pr-prohibition.md` — agents never push branches or tags.

## Monitoring Releases

### Check Workflow Status

- Go to https://github.com/benbrastmckie/ModelChecker/actions
- Look for the "Release" workflow run triggered by the pushed tag
- Check each job (`test-and-release`, `build`, `publish-testpypi`, `publish-pypi`,
  `github-release`) for success/failure

### Common Issues

#### `publish-pypi` fails with an OIDC / trusted-publisher error

**Symptom**: The publish step reports it cannot exchange the OIDC token, or PyPI rejects the
upload as untrusted.

**Fix**: Confirm the PyPI trusted publisher's **Owner**, **Repository name**, **Workflow name**
(`release.yml`), and **Environment name** (`pypi`) exactly match this repository and workflow,
and that the `pypi` GitHub Environment exists. See "Trusted Publishing (OIDC) Setup" above.

#### `publish-testpypi` fails or is skipped

**Symptom**: The `publish-testpypi` job shows a failure or red X, but `publish-pypi` still runs.

**Fix**: This is expected if the TestPyPI trusted publisher/environment is not configured — the
job runs with `continue-on-error: true` specifically so it cannot block a production release.
Configure the TestPyPI trusted publisher (optional, see above) if the rehearsal step should pass.

#### Version Already Exists

**Symptom**: PyPI or TestPyPI upload reports the version already exists.

**Fix**: Both publish steps use `skip-existing: true`, so a re-run of an already-published
version succeeds as a no-op rather than failing. To publish new content, increment the version.

#### Test Failures

**Symptom**: Tests fail on a specific platform/Python combination in `test-and-release`.

**Fix**: Check the job's logs for the specific failure; downstream `build`/`publish-*` jobs never
run if `test-and-release` fails (`needs:` dependency), so nothing is published.

## Testing the Setup

### Verify Trusted Publisher Configuration

There is no secret to list (Trusted Publishing has none) — verify configuration directly on
PyPI/TestPyPI project **Settings → Publishing** pages, and on GitHub under
**Settings → Environments** for `pypi` and `testpypi`.

### Local Rehearsal (No Publish)

The build/check portion of the pipeline can be rehearsed locally without any credentials or
network publish calls — see
`specs/125_release_engineering_and_pypi_rehearsal/rehearsal/` for a worked example
(`python -m build`, `check-wheel-contents`, `twine check --strict`, and a parity diff against the
previously published `model-checker==1.2.12`).

### Test Release Workflow (Dry Run on GitHub)

To exercise the full workflow without an intended production publish, push a throwaway
prerelease-style tag that will not collide with a real version, then delete it afterward:

```bash
git tag v999.999.999
git push origin v999.999.999

# Watch the workflow
gh run watch

# Clean up test tag
git tag -d v999.999.999
git push origin :v999.999.999
```

Only push a test tag with the user's explicit approval — tag pushes are a user-only action per
`.claude/rules/pr-prohibition.md`.

## Support

If you encounter issues:

1. Check workflow logs in GitHub Actions.
2. Verify the PyPI/TestPyPI trusted publisher configuration and the `pypi`/`testpypi` GitHub
   Environments (see "Trusted Publishing (OIDC) Setup" above).
3. Ensure version numbers are incremented for new content.
4. Check PyPI status page: https://status.python.org/
