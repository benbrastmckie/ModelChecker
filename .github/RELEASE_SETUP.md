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

### 2. TestPyPI Trusted Publisher (Effectively required — see the hard-gate note below)

1. Go to https://test.pypi.org and create/log in to an account.
2. Register (or create) the `model-checker` project there, then add a trusted publisher the same
   way as above, but with **Environment name**: `testpypi`.
3. **This is no longer a soft rehearsal step.** `publish-testpypi` is a hard gate: a failure
   there blocks the production `publish-pypi` job (via `verify-testpypi`, which installs and
   smoke-tests the artifact TestPyPI just received — see "Workflow Overview" below). If the
   TestPyPI trusted publisher is not configured, every normal tag-push release will fail here.
   The only sanctioned bypass is the `skip_testpypi` `workflow_dispatch` input, which must be
   set deliberately for that one run (see "Release Process" below) — it is not a substitute for
   configuring the trusted publisher.

### 3. GitHub Environments

Create two [GitHub Environments](https://github.com/benbrastmckie/ModelChecker/settings/environments)
matching the names configured on PyPI/TestPyPI above:

- `pypi` — used by the `publish-pypi` job. Optionally add required reviewers or a deployment
  branch/tag rule restricting it to `v*.*.*` tags for an extra manual gate before production
  publish.
- `testpypi` — used by the `publish-testpypi` job. Typically left unprotected since it only
  reaches TestPyPI.

**User decision point — required-reviewer protection on `pypi`**: as of this writing, both the
`pypi` and `testpypi` GitHub Environments have empty `protection_rules` (no required reviewers).
Adding a required-reviewer rule to `pypi` is web-UI-only configuration no agent can perform; it
is a genuine option worth considering now that `verify-testpypi` (see "Workflow Overview" below)
already proves the artifact installs and imports correctly before `publish-pypi` runs — a human
click may or may not still add value on top of that automated proof. This is left as an open
choice for whoever administers the repository, not decided here.

No repository secrets are required for either environment — Trusted Publishing uses the
workflow's OIDC identity, not a stored credential.

## Workflow Overview

There is a single workflow, `.github/workflows/release.yml`, triggered on push of a version tag
(`v[0-9]+.[0-9]+.[0-9]+`, e.g. `v1.3.0`) or manual `workflow_dispatch` (see "Release Process"
below for the `skip_testpypi` escape hatch that dispatch trigger exists for). It runs seven jobs
in this order:

1. **`preflight`** — seconds-cheap, no matrix. Fails fast, before the 9-job matrix and the build
   run, on: the tag version not matching `code/pyproject.toml`'s `version`; `code/CHANGELOG.md`
   missing a non-empty entry for the release version; the tag not being annotated and reachable
   from `origin/master`; or the tagged commit's `release.yml` differing from `origin/master`'s
   copy (the mechanical backstop for the push-before-tag ordering hazard — see "Release Process").
2. **`test-and-release`** (needs `preflight`) — cross-platform test matrix (Ubuntu/macOS/Windows,
   Python 3.10, 3.11, and 3.12): builds the package, installs the wheel, verifies the import and
   CLI work, and confirms the installed version matches the pushed tag.
3. **`build`** (needs `test-and-release`) — builds the wheel and sdist once on Ubuntu
   (`python -m build` in `code/`), runs `twine check --strict dist/*`, and uploads the `dist/`
   contents as a workflow artifact named `dist`.
4. **`publish-testpypi`** (needs `test-and-release`, `build`; environment `testpypi`) —
   downloads the `dist` artifact and publishes it to TestPyPI via
   `pypa/gh-action-pypi-publish@release/v1` using OIDC. **Hard gate**: a failure here blocks
   `publish-pypi` below (via `verify-testpypi`). The only bypass is the `skip_testpypi`
   `workflow_dispatch` input.
5. **`verify-testpypi`** (needs `test-and-release`, `build`, `publish-testpypi`) — installs the
   just-published artifact from TestPyPI (both `--index-url` and `--extra-index-url`, pinned to
   the exact tag version, with a bounded retry for index propagation lag), then smoke-tests it:
   import, `model_checker.__version__` equals the tag version, and `model-checker --help`. Proves
   the uploaded artifact is installable and importable, not merely that bytes moved. When
   `skip_testpypi` bypassed `publish-testpypi`, this job's steps no-op (nothing was uploaded to
   verify) so it reports success without attempting a check that could not possibly pass.
6. **`publish-pypi`** (needs `build`, `verify-testpypi`; environment `pypi`) — downloads the
   same `dist` artifact and publishes it to production PyPI via the same action, again using
   OIDC (`permissions: id-token: write`, no repository-url override).
7. **`github-release`** (needs `publish-pypi`) — creates the GitHub Release for the tag via
   `gh release create`, linking to `code/CHANGELOG.md`.

Top-level workflow permissions default to `contents: read`; each job grants only the additional
permission it needs (`id-token: write` for the two publish jobs, `contents: write` for
`github-release`).

## Release Process

Releasing is a **user-only** sequence — see
`specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` for the full step-by-step
checklist. In outline:

1. Confirm `code/pyproject.toml`'s `version` and the latest `code/CHANGELOG.md` entry agree on the
   release version. **`preflight` now enforces both of these as hard gates** (see "Workflow
   Overview" above) — write the `## [X.Y.Z]` `code/CHANGELOG.md` entry for the release *before*
   tagging, not after; `preflight` fails within seconds if it is missing or empty, naming the
   file and version in its failure message.
2. Commit any final release-prep changes, and **push (or land via `/merge`) the branch BEFORE
   creating and pushing the tag.** This ordering is required, not just conventional: GitHub
   Actions executes `.github/workflows/release.yml` **as it exists at the tagged commit**, not
   as it exists on `origin/master` at the time the workflow runs. A workflow-file change that is
   committed but not yet pushed (or a tag created against a commit not yet on the default branch)
   silently runs the *old* workflow file, or fails the `preflight` job's workflow-match
   assertion below if the tagged commit's `release.yml` disagrees with `origin/master`'s copy.
   This is the same class of failure the 1.3.0 release hit concretely: a workflow-file fix
   (`pip install build twine` → `... wheel`) that had been committed but not yet pushed only
   happened to resolve correctly by accident of push ordering, not by design. `preflight`'s
   final assertion (`.github/workflows/release.yml` at the tagged commit must match
   `origin/master`'s copy) is the mechanical backstop for this hazard, so a genuine ordering
   mistake now fails fast instead of running a stale or unreviewed workflow file silently.
3. Tag the release commit `vX.Y.Z` and push both the branch and the tag
   (`git push origin <branch>` then `git push origin vX.Y.Z`), or use `/merge` to land the branch
   first and tag afterward.
4. Pushing the tag triggers `release.yml`: `preflight` runs first (seconds-cheap tag/version/
   CHANGELOG/workflow-match checks), then tests run across the matrix, the distribution is built
   and checked, published to TestPyPI, verified installable and importable by `verify-testpypi`,
   published to PyPI, and finally the GitHub Release is created. See "Workflow Overview" above
   for the full seven-job topology.
5. **After PyPI publish**, confirm the new version is visible via the JSON API rather than
   `pip index versions model-checker` (deprecated/unstable output, not scripted anywhere in this
   pipeline): `curl -s https://pypi.org/pypi/model-checker/json | jq -r '.info.version'`, with a
   short bounded retry if PyPI's own index propagation lags. This is a manual post-publish
   sanity check, not a workflow step — `verify-testpypi` (step 4 above) is what actually gates
   the pipeline; this JSON-API check is for the human confirming production after the fact.

**`skip_testpypi` escape hatch**: if TestPyPI itself is known to be unavailable (e.g. an outage)
and a release must proceed without the rehearsal gate, dispatch `release.yml` manually
(`gh workflow run release.yml --ref vX.Y.Z -f skip_testpypi=true`, or via the Actions UI, run
against the tag being released) with `skip_testpypi` set to `true`. This is a deliberate,
visible, human-only action — it is never true under a normal `git push --tags` release, and
using it means `publish-pypi` runs without the "installable and importable" proof
`verify-testpypi` otherwise provides. Only use it when TestPyPI is genuinely the blocker, and
prefer writing the CHANGELOG entry or fixing the real defect over reaching for this escape when
`preflight` or `verify-testpypi` fail for other reasons.

No script automates step 3 for this repository; it is performed manually (or via `/merge`) by the
user, per `.claude/rules/pr-prohibition.md` — agents never push branches or tags.

## Monitoring Releases

### Check Workflow Status

- Go to https://github.com/benbrastmckie/ModelChecker/actions
- Look for the "Release" workflow run triggered by the pushed tag
- Check each job (`preflight`, `test-and-release`, `build`, `publish-testpypi`,
  `verify-testpypi`, `publish-pypi`, `github-release`) for success/failure

### Common Issues

#### `preflight` fails

**Symptom**: The workflow fails within seconds, before the test matrix ever starts.

**Fix**: Read the failing step's message — it names the exact file and version involved. The
four checks are: tag version vs. `code/pyproject.toml`'s `version`; a non-empty
`## [X.Y.Z]` entry in `code/CHANGELOG.md` for the release version; the tag being annotated and
reachable from `origin/master`; and the tagged commit's `.github/workflows/release.yml` matching
`origin/master`'s copy. The CHANGELOG check in particular is expected to fire on the next
release after this gate was added, until a `## [Unreleased]`/next-version entry is written — see
"Release Process" above.

#### `publish-pypi` fails with an OIDC / trusted-publisher error

**Symptom**: The publish step reports it cannot exchange the OIDC token, or PyPI rejects the
upload as untrusted.

**Fix**: Confirm the PyPI trusted publisher's **Owner**, **Repository name**, **Workflow name**
(`release.yml`), and **Environment name** (`pypi`) exactly match this repository and workflow,
and that the `pypi` GitHub Environment exists. See "Trusted Publishing (OIDC) Setup" above.

#### `publish-testpypi` fails

**Symptom**: The `publish-testpypi` job shows a failure or red X, and `publish-pypi` does not run.

**Fix**: This is now a hard gate (see "Workflow Overview" above) — a genuine `publish-testpypi`
failure is expected to block the release. Most commonly this means the TestPyPI trusted
publisher/environment is not configured; see "TestPyPI Trusted Publisher" above. If TestPyPI
itself is the problem (e.g. an outage) rather than configuration, see the `skip_testpypi`
escape hatch under "Release Process" above.

#### `verify-testpypi` fails

**Symptom**: `publish-testpypi` succeeded, but `verify-testpypi` fails and `publish-pypi` does
not run.

**Fix**: This means the artifact reached TestPyPI but could not be installed and imported back —
a real problem with the artifact itself (or, less likely, that TestPyPI's index had not yet
propagated the upload within the job's bounded retry window). Read the job's log: the install
step's retries are logged individually, and the smoke-test step names exactly which assertion
(version mismatch, import failure, `--help` failure) failed.

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

The build/check portion of the pipeline can be rehearsed locally, without any credentials or
network publish calls, using the checked-in runner:

```bash
bash code/scripts/release-verify.sh [--ref VERSION] [--out DIR]
```

The runner re-enters `nix develop` itself in a single guarded invocation (so `flake.nix` is never
touched), provisions a pinned toolchain (`code/scripts/release-tools-requirements.txt`) into a
venv, and needs network access twice: once to install that toolchain, once to `pip download` the
reference release it diffs against (`--ref`, default `1.2.12`, the last version published to
PyPI). Evidence is written to `--out DIR` (default `/tmp/release-verify-<UTC-timestamp>/`).

**Why the tools are pinned and not in `flake.nix`**: `check-wheel-contents` is not resolvable
from nixpkgs at all, and pinning with exact `==` versions keeps the evidence comparable across
releases instead of drifting with whatever happens to be latest on a given day. See the header of
`code/scripts/release-tools-requirements.txt` for the full rationale and re-pinning procedure.

**Evidence files** (11 total, written to `--out DIR`):

| File | Contents |
|------|----------|
| `build.log` | `python -m build` stdout/stderr plus a `code/dist/` directory listing |
| `twine-check.txt` | `twine check --strict code/dist/*` output |
| `wheel-contents.txt` | bare `check-wheel-contents` output (hard gate — see below) |
| `pip-download-<REF>.log` | `pip download --no-deps model-checker==<REF>` output |
| `new-wheel-files.txt` | sorted full file listing of the freshly built wheel |
| `ref-<REF>-wheel-files.txt` | sorted full file listing of the reference wheel |
| `wheel-files-diff.txt` | unified diff of the two file listings |
| `top-level-dir-diff.txt` | unified diff of the two maxdepth-2 directory listings |
| `sha256sums.txt` | SHA256 of the new wheel, new sdist, and reference wheel (3 lines) |
| `parity-diff.md` | generated evidentiary report; classification is a human step, never a gate |
| `summary.txt` | per-step status ledger: name, gate/informational classification, exit code |

**Reading guide — hard gates vs. informational steps**: provisioning, `python -m build`,
`twine check --strict`, and bare `check-wheel-contents` are **hard gates** — any one failing is a
real problem. The parity diff is **informational** — a nonempty diff there does not, by itself,
mean anything is wrong; a human reads it for context. The parity diff in particular is
evidentiary only: it is never read as a pass/fail gate, and byte-identity against the prior
release is not expected or required.

**Exit-code contract**:

| Exit | Meaning |
|------|---------|
| `0` | all hard gates green (informational steps may still be nonzero) |
| `1` | a hard gate failed |
| `2` | a required step (provisioning or the reference download) could not run at all — the evidence set is **incomplete** and must not be read as a pass |

**Reading a nonzero bare `check-wheel-contents` exit**: this is **not expected** on the current
tree. The four identical `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` files that
previously triggered `W002: Wheel contains duplicate files` have been removed — each theory's
version now derives solely from its `__init__.py`'s `__version__`. A nonzero exit here means the
hard gate failed and should be investigated like any other gate failure; there is no longer a
known, expected finding to filter out.

**Historical context only**: `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/`
holds the evidence from the one-off manual rehearsal that this runner automates. Its
`check-wheel-contents` result and sha256sums no longer reproduce against the current tree (the
tree has since lost the `VERSION`-file duplication that once triggered `W002`, and been rebuilt
many times over since) — treat it as a historical worked example, never as current, reviewable
evidence.

### Test Release Workflow (Dry Run on GitHub)

To exercise the full workflow without an intended production publish, push a throwaway
prerelease-style tag that will not collide with a real version, then delete it afterward:

**Note**: `preflight` (see "Workflow Overview" above) will fail this dry run at the
tag-vs-`code/pyproject.toml` version check, since `v999.999.999` will not match the real
project version — this is expected and stops the run before any publish step, which is
actually the safer outcome for a dry run. To exercise past `preflight`, temporarily point
`code/pyproject.toml`'s `version` at the same throwaway value on a disposable branch, or accept
that this dry run now only exercises `preflight` itself rather than the full downstream chain.

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
