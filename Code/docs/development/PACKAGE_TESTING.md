# Package Testing and Release Guide

**Navigation**: [← Back to Development](../README.md) | [Maintenance Home](../README.md) | [Environment Setup →](ENVIRONMENT_SETUP.md)

**Related Documentation**: 
- [Environment Setup](ENVIRONMENT_SETUP.md) - Development environment configuration
- [Testing Framework](TESTING_FRAMEWORK.md) - Comprehensive testing methodology
- [PyPI Release Guide](PYPI_RELEASE_GUIDE.md) - Automated release process
- [GitHub Actions Workflows](../../.github/workflows/) - CI/CD configuration

## Table of Contents

1. [Overview](#overview)
2. [Philosophy](#philosophy)
3. [Local Testing](#local-testing)
4. [Automated Release Process](#automated-release-process)
5. [GitHub Actions Setup](#github-actions-setup)
6. [Test Matrix Configuration](#test-matrix-configuration)
7. [Pre-Release Checklist](#pre-release-checklist)
8. [Troubleshooting](#troubleshooting)
9. [Platform-Specific Notes](#platform-specific-notes)
10. [Success Metrics](#success-metrics)

## Overview

This guide establishes standards for testing and releasing the model-checker package to PyPI. It covers local development testing, continuous integration via GitHub Actions, and the complete release workflow.

**Core Principle**: Every release must pass all tests on all supported platforms (Linux, macOS, Windows) and Python versions (3.8-3.12) before publication.

## Philosophy

### Multi-Platform Testing Requirements

GitHub Actions provides the essential infrastructure for cross-platform validation:

- **Platform Coverage**: Linux (Ubuntu), macOS, Windows
- **Python Version Matrix**: 3.8, 3.9, 3.10, 3.11, 3.12
- **Installation Methods**: Wheel (`.whl`) and source distribution (`.tar.gz`)
- **Test Environments**: 15 unique platform/version combinations
- **Automated Validation**: Every push and pull request triggers full test suite

### Fail-Fast Release Process

The release process follows fail-fast principles:

1. **Local verification** before pushing (when possible)
2. **CI validation** across all platforms
3. **Test PyPI deployment** before production
4. **Production release** only after all checks pass

## Automated Release Process

### Using run_update.py Script

The `run_update.py` script provides an interactive release workflow:

```bash
# Navigate to Code directory
cd ModelChecker/Code

# Run the interactive release script
python run_update.py
```

#### Script Workflow

1. **Test Execution** (BEFORE version change)
   - Runs all tests using `run_tests.py`
   - If tests fail, offers options to abort or continue
   - Tests must pass for safe releases

2. **Version Selection**
   - Shows current version from `pyproject.toml`
   - Prompts for increment type:
     - **PATCH** (1.0.3 → 1.0.4): Bug fixes
     - **MINOR** (1.0.3 → 1.1.0): New features
     - **MAJOR** (1.0.3 → 2.0.0): Breaking changes

3. **Package Building**
   - Updates version in `pyproject.toml`
   - Builds wheel and source distributions
   - Validates with `twine check`

4. **Release Path**
   - **Major/Minor**: Provides git commands for automatic GitHub Actions release
   - **Patch**: Manual upload only (not auto-released)

#### Command Line Options

```bash
python run_update.py               # Full interactive process
python run_update.py --skip-tests  # Skip testing (not recommended)
python run_update.py --no-upload   # Build but don't upload
python run_update.py --test-pypi   # Upload to Test PyPI
```

### Automatic PyPI Releases (Major/Minor)

For major and minor versions, releases are automated via GitHub Actions:

1. **Version Tag Triggers Release**
   ```bash
   git tag v1.1.0  # Minor version ending in .0
   git push origin v1.1.0
   ```

2. **GitHub Actions Workflow** (`.github/workflows/pypi-release.yml`)
   - Detects version tags matching `v[0-9]+.[0-9]+.0`
   - Runs tests on all platforms
   - Uploads to PyPI if all tests pass

3. **Requirements for Automatic Release**
   - `PYPI_API_TOKEN` secret configured in repository
   - All tests passing on all 15 environments
   - Version tag matches pattern (x.y.0)

### Manual PyPI Upload

For patches or immediate release needs:

```bash
cd Code
twine upload dist/*
```

## Local Testing

### Standard Setup (macOS/Linux/Windows)

#### 1. Environment Preparation

```bash
# Navigate to package root
cd ModelChecker/Code

# Create isolated test environment
python -m venv test_env
source test_env/bin/activate  # Windows: test_env\Scripts\activate
```

#### 2. Build Verification

```bash
# Install build dependencies
pip install --upgrade pip build twine

# Build distributions
python -m build

# Verify build artifacts
ls -la dist/  # Should show .whl and .tar.gz files
twine check dist/*  # Validate package metadata
```

#### 3. Installation Testing

```bash
# Test wheel installation
pip install dist/*.whl
python -c "import model_checker; print(f'Version: {model_checker.__version__}')"
pip uninstall -y model-checker

# Test source distribution
pip install dist/*.tar.gz
python -c "import model_checker; print(f'Version: {model_checker.__version__}')"
```

#### 4. Test Suite Execution

```bash
# Install test dependencies
pip install pytest pytest-cov

# Run test suite
pytest src/model_checker/theory_lib -v --tb=short

# Clean up
deactivate
rm -rf test_env
```

## Platform-Specific Notes

### NixOS Development

NixOS requires special handling due to its declarative package management:

#### Building on NixOS

```bash
# Enter nix-shell with required packages
nix-shell -p python3Packages.build python3Packages.wheel python3Packages.setuptools

# Navigate to package directory
cd ModelChecker/Code

# Build distributions (within nix-shell)
python -m build

# Verify build artifacts
ls -la dist/
```

#### Testing Limitations

- **Cannot test pip install locally** - NixOS prevents direct pip installations
- **Must use GitHub Actions** - Rely on CI for installation verification
- **Can run unit tests** - Use nix-shell with pytest for local testing
- **Build artifacts are valid** - Distributions built on NixOS work on other platforms

### Windows Considerations

- Use forward slashes in paths or raw strings: `r"C:\path\to\file"`
- Activate virtual environments with: `venv\Scripts\activate.bat`
- Some tests may need platform-specific markers

### macOS Considerations

- May require Xcode Command Line Tools for some dependencies
- Use `python3` explicitly if system Python differs
- Check for Apple Silicon (M1/M2) compatibility with dependencies

## GitHub Actions Setup

### Workflow Configuration

The package testing workflow (`.github/workflows/test-package.yml`) provides comprehensive validation:

#### Core Features

```yaml
# Trigger conditions
on:
  push:
    branches: [main, master, develop]
  pull_request:
    branches: [main, master]
  workflow_dispatch:  # Manual trigger with options
```

#### Test Matrix Structure

```yaml
strategy:
  matrix:
    os: [ubuntu-latest, macos-latest, windows-latest]
    python-version: ['3.8', '3.9', '3.10', '3.11', '3.12']
```

### PyPI Secrets Configuration

#### Production PyPI Setup

1. **Create PyPI Account**
   - Register at [PyPI.org](https://pypi.org/)
   - Enable 2FA (recommended)
   - Verify email address

2. **Generate API Token**
   - Go to [Account Settings](https://pypi.org/manage/account/)
   - Navigate to "API tokens"
   - Create token named: `model-checker-github-actions`
   - Scope: Initially "Entire account", later limit to "model-checker"
   - Copy token (starts with `pypi-`)

3. **Add to GitHub Repository**
   - Go to repository Settings → Secrets and variables → Actions
   - Click "New repository secret"
   - Name: `PYPI_API_TOKEN`
   - Value: Your PyPI token

#### Test PyPI Setup (Optional)

1. **Create Test PyPI Account**
   - Register at [Test PyPI](https://test.pypi.org/)
   - Generate separate API token

2. **Add Test Secret**
   - Name: `TEST_PYPI_API_TOKEN`
   - Value: Your Test PyPI token

#### 3. Manual Deployment Testing

```bash
# Trigger via GitHub Actions UI:
# 1. Navigate to Actions tab
# 2. Select "Test Package Installation"
# 3. Click "Run workflow"
# 4. Enable "Test on Test PyPI" checkbox
# 5. Monitor progress in real-time
```

## Test Matrix Configuration

### Coverage Matrix

| Platform | Python Versions | Test Types |
|----------|----------------|------------|
| Ubuntu Latest | 3.8, 3.9, 3.10, 3.11, 3.12 | Build, Install, Import, CLI, Tests |
| macOS Latest | 3.8, 3.9, 3.10, 3.11, 3.12 | Build, Install, Import, CLI, Tests |
| Windows Latest | 3.8, 3.9, 3.10, 3.11, 3.12 | Build, Install, Import, CLI, Tests |

### Validation Steps per Environment

1. **Build Phase**
   - Create wheel (`.whl`)
   - Create source distribution (`.tar.gz`)
   - Validate with `twine check`

2. **Installation Phase**
   - Install from wheel
   - Verify imports and version
   - Uninstall cleanly
   - Install from source distribution
   - Re-verify functionality

3. **Functional Testing**
   - Import all public modules
   - Execute CLI commands
   - Run pytest suite
   - Collect coverage metrics

## Pre-Release Checklist

### Version Management

```toml
# Code/pyproject.toml
[project]
version = "1.0.4"  # Follow semantic versioning
```

### Release Workflow

#### Automated Workflow (Recommended)

Use `run_update.py` for interactive release process:

```bash
cd Code
python run_update.py
```

This handles:
- Running tests before version change
- Semantic version selection
- Building distributions
- Providing appropriate git commands

#### Manual Workflow

##### Phase 1: Pre-Release Validation

- [ ] Run tests with `python run_tests.py`
- [ ] Update version in `pyproject.toml`
- [ ] Update CHANGELOG.md with release notes
- [ ] Create release branch: `git checkout -b release/v1.0.4`

##### Phase 2: CI Validation

- [ ] Push release branch to GitHub
- [ ] Monitor GitHub Actions for all green checks
- [ ] Review test results across all 15 environments
- [ ] Verify no deprecation warnings or errors

##### Phase 3: Test PyPI Deployment

```bash
# Build fresh distributions
cd Code && rm -rf dist/
python -m build

# Validate packages
twine check dist/*

# Upload to Test PyPI
twine upload --repository testpypi dist/*

# Test installation (new virtual environment)
python -m venv test_install
source test_install/bin/activate
pip install --index-url https://test.pypi.org/simple/ \
            --extra-index-url https://pypi.org/simple/ \
            model-checker

# Verify functionality
python -c "import model_checker; print(model_checker.__version__)"
model-checker --help
```

##### Phase 4: Production Release

For **Major/Minor versions** (automatic):
```bash
# Tag and push (triggers GitHub Actions)
git tag v1.1.0
git push origin main --tags

# Monitor at: https://github.com/benbrastmckie/ModelChecker/actions
```

For **Patch versions** (manual):
```bash
# Manual upload with twine
cd Code
twine upload dist/*

# Verify on PyPI
pip install --upgrade model-checker
python -c "import model_checker; assert model_checker.__version__ == '1.0.4'"
```

##### Phase 5: Post-Release

- [ ] Create GitHub release with tag: `v1.0.4`
- [ ] Merge release branch to main
- [ ] Update documentation if needed
- [ ] Announce release (if applicable)

## Troubleshooting

### Common Build Issues

#### Import Errors Across Platforms

**Symptoms**: Package imports fail on specific platforms
**Solutions**:
```python
# Use pathlib for cross-platform paths
from pathlib import Path
config_path = Path(__file__).parent / "config.json"

# Avoid platform-specific imports
try:
    import platform_specific_module
except ImportError:
    platform_specific_module = None
```

#### Missing Dependencies

**Symptoms**: `ModuleNotFoundError` during installation
**Solutions**:
```toml
# pyproject.toml - Explicit dependency declaration
dependencies = [
    "z3-solver>=4.8.0",  # Pin minimum versions
    "networkx>=2.0",
]
```

#### Binary Package Issues

**Symptoms**: z3-solver or similar packages fail to install
**Solutions**:
- Document platform-specific installation steps
- Consider pure-Python alternatives
- Use `cibuildwheel` for complex binary distributions

### GitHub Actions Debugging

#### Adding Debug Output

```yaml
# .github/workflows/test-package.yml
- name: Debug Failed Environment
  if: failure()  # Only runs on failure
  run: |
    echo "Python: $(python --version)"
    echo "Pip: $(pip --version)"
    echo "Platform: ${{ runner.os }}"
    pip list
    ls -la Code/dist/
```

#### Accessing Failed Workflow Logs

1. Navigate to Actions tab → Failed workflow run
2. Click on failed job → Expand error step
3. Download logs: Settings gear → Download log archive
4. Search for platform-specific error patterns

### Platform-Specific Debugging

#### Windows Path Issues
```python
# Always use forward slashes or Path objects
from pathlib import Path
path = Path("Code") / "dist" / "*.whl"  # Works everywhere
```

#### macOS Dependency Issues
```bash
# May need Xcode tools
xcode-select --install
```

#### Linux Permission Issues
```bash
# Ensure executable permissions
chmod +x scripts/*.sh
```

## Success Metrics

### Build Quality Indicators

| Metric | Target | Measurement |
|--------|--------|-------------|
| Platform Success Rate | 100% | All 15 environments pass |
| Build Time | <5 minutes | GitHub Actions duration |
| Test Coverage | >85% | pytest-cov report |
| Installation Success | 100% | pip install verification |
| Import Success | 100% | Module import tests |

### Release Quality Gates

- **No failing tests** in any environment
- **No deprecation warnings** in Python 3.8+
- **Clean twine check** with no errors
- **Successful Test PyPI deployment**
- **Manual verification** on one platform

### Post-Release Monitoring

```bash
# Check PyPI statistics
pip install pypistats
pypistats recent model-checker

# Monitor GitHub issues for installation problems
# Review weekly for patterns

# Test latest release periodically
pip install --upgrade model-checker
python -c "import model_checker; model_checker.__version__"
```

## Maintenance Schedule

- **Before Each Release**: Full checklist completion
- **Weekly**: Review GitHub Actions for intermittent failures
- **Monthly**: Update GitHub Actions runner versions
- **Quarterly**: Review and update Python version matrix

## Workflow Files Reference

### Testing Workflow
- **File**: `.github/workflows/test-package.yml`
- **Triggers**: Push, PR, manual
- **Purpose**: Test across all platforms/Python versions

### Release Workflow  
- **File**: `.github/workflows/pypi-release.yml`
- **Triggers**: Version tags (v*.*.0), manual
- **Purpose**: Automated PyPI releases for major/minor versions

### Helper Scripts
- **`run_update.py`**: Interactive release management
- **`run_tests.py`**: Comprehensive test runner
- **`pyproject.toml`**: Package configuration and version

## Additional Resources

- [Python Packaging User Guide](https://packaging.python.org/)
- [GitHub Actions for Python](https://docs.github.com/en/actions/automating-builds-and-tests/building-and-testing-python)
- [Test PyPI](https://test.pypi.org/)
- [Semantic Versioning](https://semver.org/)
- [cibuildwheel Documentation](https://cibuildwheel.readthedocs.io/)
- [PyPI Release Guide](PYPI_RELEASE_GUIDE.md) - Detailed release documentation