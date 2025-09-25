# GitHub Actions Workflow

## Single Unified Release Workflow

This project uses a **single workflow** (`release.yml`) that handles ALL releases - major, minor, and patch.

## How It Works

1. **Trigger**: When you push a version tag (e.g., `v1.2.8`), the workflow automatically starts
2. **Test**: Runs basic package tests on all platforms (Windows, Mac, Linux) with Python 3.8 and 3.12
3. **Publish**: If ALL tests pass, automatically uploads to PyPI
4. **Release**: Creates a GitHub release

## Release Process

### Using run_update.py (Recommended)

```bash
python Code/run_update.py
```

This script will:
1. Update version in pyproject.toml
2. Run tests locally
3. Commit and tag the changes
4. Push to GitHub (triggering the workflow)

### Manual Release

```bash
# 1. Update version in Code/pyproject.toml
# 2. Commit and tag
git add Code/pyproject.toml
git commit -m "Release version X.Y.Z"
git tag vX.Y.Z
git push origin main
git push origin vX.Y.Z
```

## Requirements

### GitHub Secret Required

- `PYPI_API_TOKEN`: Your PyPI API token
  - Get it from: https://pypi.org/manage/account/token/
  - Add it at: Settings → Secrets and variables → Actions
  - Name must be exactly: `PYPI_API_TOKEN`

## Workflow Details

- **File**: `.github/workflows/release.yml`
- **Triggers**: Version tags only (`v*.*.*`)
- **Tests**: Python 3.8 and 3.12 on all platforms
- **Fail-fast**: Stops immediately if any test fails
- **Upload**: Only happens if ALL tests pass

## Benefits of Single Workflow

1. **Simplicity**: One workflow to maintain
2. **Consistency**: All releases work the same way
3. **No duplicates**: Only one workflow runs per release
4. **Clear flow**: Test → Upload → Release

## Troubleshooting

### Tests Failed

If tests fail, the release stops. Fix the tests and push a new tag.

### PyPI Upload Failed

Check if `PYPI_API_TOKEN` is set in GitHub Secrets.

### Manual Upload

If needed, you can manually upload after tests pass:

```bash
cd Code
python -m build
twine upload dist/*X.Y.Z*
```