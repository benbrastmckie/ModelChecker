# GitHub Release Pipeline Setup Guide

## Prerequisites

Before releases can work automatically, you need to configure PyPI API tokens as GitHub Secrets.

## Required Secrets

### 1. PYPI_API_TOKEN (Required)

This token allows GitHub Actions to upload releases to PyPI.

**Setup Steps:**

1. Go to https://pypi.org and log in
2. Navigate to Account Settings → API tokens
3. Click "Add API token"
4. Configure the token:
   - **Token name**: `ModelChecker GitHub Actions`
   - **Scope**: Select "Project: model-checker" (not entire account)
   - **Permissions**: Upload packages
5. Copy the token (starts with `pypi-`)
6. Go to https://github.com/benbrastmckie/ModelChecker/settings/secrets/actions
7. Click "New repository secret"
8. Add the secret:
   - **Name**: `PYPI_API_TOKEN` (must be exact)
   - **Value**: Paste the token from PyPI
9. Click "Add secret"

### 2. TEST_PYPI_API_TOKEN (Optional)

This token allows testing releases on Test PyPI before production.

**Setup Steps:**

1. Go to https://test.pypi.org and create an account
2. Navigate to Account Settings → API tokens
3. Create a token with project scope for "model-checker"
4. Add to GitHub Secrets as `TEST_PYPI_API_TOKEN`

## Workflow Overview

The release pipeline has two workflows:

### 1. Test Package Installation (`test-package.yml`)

- **Triggers**: Pushes to main/master, pull requests
- **Does NOT trigger on tags** (prevents duplicate runs)
- **Purpose**: Continuous testing of package installation
- **Test Matrix**: All Python versions (3.8-3.12) on all platforms

### 2. PyPI Release (`pypi-release.yml`)

- **Triggers**: Version tags (`v*.*.*`)
- **Purpose**: Build and publish releases to PyPI
- **Test Matrix**: Min/max Python (3.8, 3.12) on all platforms
- **Steps**:
  1. Validate version tag matches pyproject.toml
  2. Run tests on all platforms
  3. Build wheel and source distribution
  4. Upload to Test PyPI (if configured)
  5. Upload to Production PyPI
  6. Create GitHub Release

## Release Process

### Automated Release (Recommended)

1. Update version in `Code/pyproject.toml`
2. Run the release script:
   ```bash
   python run_update.py
   ```
3. Choose to automate git operations when prompted
4. The script will:
   - Commit version change
   - Create version tag
   - Push to GitHub
   - Trigger automatic PyPI upload

### Manual Release

1. Update version in `Code/pyproject.toml`
2. Commit and tag:
   ```bash
   git add Code/pyproject.toml
   git commit -m "Release version X.Y.Z"
   git tag vX.Y.Z
   git push origin master
   git push origin vX.Y.Z
   ```

## Monitoring Releases

### Check Workflow Status

- Go to https://github.com/benbrastmckie/ModelChecker/actions
- Look for the "PyPI Release" workflow run
- Check each job for success/failure

### Common Issues

#### Missing PYPI_API_TOKEN

**Symptom**: Workflow fails with "PYPI_API_TOKEN not configured"

**Fix**: Follow setup steps above to add the token

#### Version Already Exists

**Symptom**: PyPI upload fails with "version already exists"

**Fix**: Increment version number and create new release

#### Test Failures

**Symptom**: Tests fail on specific platform/Python combination

**Fix**:
- Check test output for specific failure
- Tests now have retry logic for flaky failures
- Consider platform-specific issues

#### Duplicate Workflow Runs

**Symptom**: Two workflows run for same tag push

**Fix**: Already fixed - test-package.yml now excludes tag triggers

## Workflow Improvements Made

1. **Prevented duplicate runs** - test-package.yml excludes tag triggers
2. **Added retry logic** - Tests retry once if they fail
3. **Better error messages** - Clear instructions when secrets are missing
4. **Test optimization** - Release tests only min/max Python versions
5. **Fail-fast disabled** - All platforms test even if one fails

## Testing the Setup

### Verify Secrets

Check if secrets are configured:

```bash
# This won't show the actual secret values (they're hidden)
gh secret list
```

### Test Release Workflow

Create a test tag without pushing to PyPI:

```bash
# Modify pypi-release.yml temporarily
# Comment out the PyPI upload steps
# Push a test tag
git tag v999.999.999
git push origin v999.999.999

# Watch the workflow
gh run watch

# Clean up test tag
git tag -d v999.999.999
git push origin :v999.999.999
```

## Support

If you encounter issues:

1. Check workflow logs in GitHub Actions
2. Verify all secrets are configured correctly
3. Ensure version numbers are incremented
4. Check PyPI status page: https://status.python.org/