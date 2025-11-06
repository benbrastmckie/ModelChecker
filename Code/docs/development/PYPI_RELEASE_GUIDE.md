# PyPI Release Guide

**Navigation**: [← Back to Development](../README.md) | [Package Testing →](PACKAGE_TESTING_GUIDE.md)

## Overview

This guide explains how to set up and use automated PyPI releases for the model-checker package. The system automatically publishes major and minor versions to PyPI while skipping patch releases.

## Release Strategy

### Semantic Versioning Rules

| Version Type | Example | Triggers PyPI Release | Use Case |
|-------------|---------|----------------------|----------|
| Major | 1.0.0 → 2.0.0 | ✅ Yes | Breaking changes |
| Minor | 1.0.0 → 1.1.0 | ✅ Yes | New features |
| Patch | 1.0.0 → 1.0.1 | ❌ No | Bug fixes |

### Why Skip Patch Releases?

- **Patches are frequent** - Small fixes don't need PyPI updates
- **Reduces noise** - Users only see significant updates
- **Testing flexibility** - Can iterate quickly on fixes
- **Manual option available** - Can still release patches if critical

## Setting Up PyPI Secrets

### Step 1: Create PyPI Account

1. Register at [PyPI.org](https://pypi.org/account/register/)
2. Verify your email address
3. Enable 2FA (recommended)

### Step 2: Generate API Token

1. Go to [PyPI Account Settings](https://pypi.org/manage/account/)
2. Scroll to "API tokens"
3. Click "Add API token"
4. Settings:
   - **Token name**: `model-checker-github-actions`
   - **Scope**: `Project: model-checker` (after first manual upload)
5. Copy the token (starts with `pypi-`)

### Step 3: Add Secret to GitHub

1. Navigate to your repository on GitHub
2. Go to Settings → Secrets and variables → Actions
3. Click "New repository secret"
4. Add the secret:
   - **Name**: `PYPI_API_TOKEN`
   - **Value**: The token from PyPI (including `pypi-` prefix)

### Step 4: Test PyPI Setup (Optional)

Repeat steps 1-3 for [Test PyPI](https://test.pypi.org/):
- Create separate account on Test PyPI
- Generate token for `model-checker` project
- Add as `TEST_PYPI_API_TOKEN` in GitHub

## Release Workflows

### Automatic Release (Recommended)

#### For Major/Minor Versions Only

1. **Update version** in `Code/pyproject.toml`:
   ```toml
   [project]
   version = "1.1.0"  # Minor version bump
   ```

2. **Commit and tag**:
   ```bash
   git add Code/pyproject.toml
   git commit -m "Release version 1.1.0"
   git tag v1.1.0
   git push origin main --tags
   ```

3. **Automatic process**:
   - GitHub Actions detects the `v1.1.0` tag
   - Runs full test suite across platforms
   - Builds and uploads to PyPI
   - Creates GitHub release

#### For Patch Versions

1. **Update version** in `Code/pyproject.toml`:
   ```toml
   [project]
   version = "1.0.1"  # Patch version
   ```

2. **Commit WITHOUT tag** (or with patch tag):
   ```bash
   git add Code/pyproject.toml
   git commit -m "Fix: correct import issue"
   git push origin main
   # No tag, or use v1.0.1 - won't trigger PyPI
   ```

3. **Result**: Changes are in repo but NOT on PyPI

### Manual Release (When Needed)

Use for critical patches or testing:

1. Go to Actions → PyPI Release workflow
2. Click "Run workflow"
3. Enter:
   - **Version**: `1.0.1`
   - **Release type**: `production` or `test-pypi-only`
4. Click "Run workflow"

## Version Management

### Before Release Checklist

- [ ] Update `Code/pyproject.toml` version
- [ ] Update `CHANGELOG.md` with changes
- [ ] Run local tests: `pytest Code/src/model_checker/theory_lib`
- [ ] Ensure all CI checks pass on main branch

### Version Numbering Guidelines

```python
# Major version (2.0.0) - Breaking changes
- Removed/renamed public APIs
- Changed fundamental behavior
- Incompatible file formats

# Minor version (1.1.0) - New features  
- Added new functionality
- New optional parameters
- Performance improvements

# Patch version (1.0.1) - Bug fixes
- Fixed bugs
- Documentation updates
- Security patches
```

## Monitoring Releases

### Verify PyPI Upload

```bash
# Check latest version on PyPI
pip index versions model-checker

# Install latest version
pip install --upgrade model-checker

# Verify version
python -c "import model_checker; print(model_checker.__version__)"
```

### PyPI Statistics

```bash
# Install pypistats
pip install pypistats

# View download statistics
pypistats recent model-checker
pypistats overall model-checker
```

### GitHub Release Page

- Auto-created for tagged releases
- Contains release notes and assets
- URL: `https://github.com/benbrastmckie/ModelChecker/releases`

## Troubleshooting

### Token Issues

**Error**: "Invalid or non-existent authentication"
- Verify token starts with `pypi-`
- Check token hasn't expired
- Ensure secret name is exactly `PYPI_API_TOKEN`

### Version Conflicts

**Error**: "Version already exists on PyPI"
- Can't overwrite existing versions
- Bump version number
- Use `--skip-existing` flag for safety

### Failed Tests Before Release

**Behavior**: Release stops if tests fail
- Fix failing tests
- Push fixes
- Re-tag or run manual workflow

## Emergency Procedures

### Yanking a Bad Release

```bash
# If a broken version was published
pip install twine
twine yank model-checker==1.1.0
# Users can still install if explicitly requested
```

### Rolling Back

1. Fix the issue in code
2. Release as patch (manually if needed)
3. Document in CHANGELOG as hotfix

## Best Practices

1. **Always test on Test PyPI first** for major releases
2. **Keep CHANGELOG.md updated** with every version
3. **Use release branches** for major versions
4. **Squash commits** before tagging releases
5. **Never force push tags** after release

## Quick Reference

### Release Commands

```bash
# Major/Minor release (auto-publishes)
git tag v1.1.0
git push origin v1.1.0

# Patch release (no auto-publish)
git tag v1.0.1
git push origin v1.0.1

# Delete local tag (if needed)
git tag -d v1.1.0

# Delete remote tag (careful!)
git push origin --delete v1.1.0
```

### Manual Release via GitHub UI

1. Actions tab
2. "PyPI Release" workflow
3. "Run workflow"
4. Enter version and type
5. Monitor progress

## Security Notes

- **Never commit tokens** to repository
- **Use GitHub Secrets** exclusively
- **Rotate tokens** periodically
- **Limit token scope** to single project
- **Enable 2FA** on PyPI account