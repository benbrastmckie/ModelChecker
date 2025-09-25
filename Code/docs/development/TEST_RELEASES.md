# Test Release Process

This document explains how to use Test PyPI for testing releases before pushing to production.

## Overview

The `test_update.py` script allows you to upload development versions to Test PyPI, where you can test installations on other machines before making an official release.

## Workflow

### 1. Test Release (Test PyPI)

```bash
# From the Code directory
python test_update.py
```

This will:
- Run tests (optional)
- Increment version with a `.devYYYYMMDDHHMMSS` suffix
- Build the package
- Upload to Test PyPI
- Provide installation instructions

### 2. Install and Test

On your test machine:

```bash
pip install --index-url https://test.pypi.org/simple/ \
            --extra-index-url https://pypi.org/simple/ \
            model-checker==1.2.10.dev20240101123456
```

The `--extra-index-url` is needed because Test PyPI doesn't mirror dependencies from regular PyPI.

### 3. Official Release

Once testing is successful:

```bash
python run_update.py
```

This creates the official release and triggers GitHub Actions to upload to production PyPI.

## Setup Test PyPI

### First Time Setup

1. Create an account at https://test.pypi.org
2. Generate an API token: https://test.pypi.org/manage/account/token/
3. Set environment variable:
   ```bash
   export TEST_PYPI_API_TOKEN=pypi-AgEIcH...
   ```

### Optional: Add to shell profile

Add to `~/.bashrc` or `~/.zshrc`:
```bash
export TEST_PYPI_API_TOKEN=pypi-AgEIcH...
```

## Command Options

### test_update.py

- `--skip-tests`: Skip running tests before build
- `--no-git`: Don't prompt for git operations

### Examples

```bash
# Quick test release without running tests
python test_update.py --skip-tests

# Test release without git prompts
python test_update.py --no-git
```

## Benefits

1. **Safe Testing**: Test installations and functionality before production
2. **Version Management**: Dev versions don't interfere with production versions
3. **Multiple Iterations**: Test as many times as needed without affecting version numbers
4. **Cross-Machine Testing**: Install on different machines to verify compatibility

## Differences from Production

- Versions have `.devYYYYMMDDHHMMSS` suffix
- Uploaded to test.pypi.org instead of pypi.org
- Not triggered by GitHub Actions
- Can upload multiple times with same base version

## Troubleshooting

### Authentication Issues

If you see authentication errors:
1. Check your token is set: `echo $TEST_PYPI_API_TOKEN`
2. Verify token is valid at https://test.pypi.org/manage/account/token/
3. You can also authenticate interactively (twine will prompt for username/password)

### Installation Issues

If installation from Test PyPI fails:
1. Make sure to include both index URLs
2. Check the exact version number (including dev suffix)
3. Verify the package uploaded successfully: https://test.pypi.org/project/model-checker/

### Version Conflicts

If version already exists on Test PyPI:
- The script adds a timestamp to ensure uniqueness
- Each run creates a unique version like `1.2.10.dev20240101123456`