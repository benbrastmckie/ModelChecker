# Environment Setup Guide

**Navigation**: [← Back to Development](../README.md) | [Maintenance Home](../../README.md) | [Development Workflow →](../implementation/DEVELOPMENT_WORKFLOW.md)

**Related Documentation**: 
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - Complete development process
- [Testing Framework](../core/TESTING_GUIDE.md) - Test environment setup
- [Quality Assurance](../../quality/README.md) - Development standards

## Overview

This guide provides comprehensive instructions for setting up a development environment for the ModelChecker framework. The setup process varies by platform and development approach, with special consideration for NixOS users.

## Requirements

### System Requirements

- **Python**: 3.8 or higher (check pyproject.toml for specific version)
- **Key Dependencies**: z3-solver, jupyter, pytest
- **Virtual Environment**: Recommended for isolated development
- **Platform Support**: Linux (primary), macOS, Windows, with NixOS-specific tooling

### Development Tools

- **Git**: For version control and collaboration
- **Text Editor/IDE**: VS Code, PyCharm, or equivalent with Python support
- **Terminal**: For running development commands and scripts
- **Optional**: direnv for automatic environment activation

## Standard Setup (pip)

For macOS, Windows, and non-NixOS Linux systems:

### 1. Repository Setup

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Verify you're in the correct directory
ls -la  # Should show src/, docs/, dev_cli.py, etc.
```

### 2. Virtual Environment Creation

```bash
# Create and activate virtual environment
python -m venv venv

# Activation varies by platform:
# On Windows:
venv\Scripts\activate
# On macOS/Linux:
source venv/bin/activate

# Verify activation (should show venv in prompt)
which python  # Should point to venv/bin/python
```

### 3. Package Installation

```bash
# Install in development mode
pip install -e .

# Install development dependencies manually
pip install pytest pytest-cov black mypy

# Optional: Install Jupyter dependencies
pip install -e ".[jupyter]"

# Verify installation
python -c "import model_checker; print('Installation successful')"
```

### 4. Verification

```bash
# Run test suites to verify setup
python test_package.py
python test_theories.py

# Test development CLI
./dev_cli.py --help

# Verify theory loading
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
```

## NixOS Setup

NixOS requires special handling due to its immutable package management system:

### 1. Repository Setup

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Verify nix configuration files exist
ls shell.nix .envrc  # Should exist for NixOS support
```

### 2. Development Shell

```bash
# Enter the development shell
nix-shell

# The shell.nix file automatically:
# - Sets PYTHONPATH to include local source code
# - Installs required dependencies (z3-solver, networkx, etc.)
# - Makes development scripts executable
```

### 3. Optional: Automatic Environment Activation

For convenience, set up automatic environment activation:

```bash
# Install direnv if you haven't already
nix-env -i direnv

# Allow the .envrc file once
direnv allow

# Environment will now activate automatically when entering directory
cd ..  # Leave directory
cd ModelChecker/Code  # Environment activates automatically
```

### 4. Verification

```bash
# Verify NixOS-specific setup
echo $PYTHONPATH  # Should include local src directory

# Run tests using NixOS wrapper scripts
./run_tests.py          # Run all tests
./run_tests.py logos    # Test specific theory
./run_tests.py --unit   # Unit tests only

# Test development CLI
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
```

## Development Environment Configuration

### Code Editor Setup

#### VS Code Configuration

Create `.vscode/settings.json`:

```json
{
    "python.defaultInterpreterPath": "./venv/bin/python",
    "python.linting.enabled": true,
    "python.linting.pylintEnabled": false,
    "python.linting.mypyEnabled": true,
    "python.formatting.provider": "black",
    "python.testing.pytestEnabled": true,
    "python.testing.unittestEnabled": false,
    "python.testing.pytestArgs": [
        "."
    ]
}
```

#### PyCharm Configuration

1. **Set Project Interpreter**: Point to `venv/bin/python`
2. **Enable Type Checking**: Configure mypy as external tool
3. **Set Test Runner**: Configure pytest as default test runner
4. **Code Style**: Import black configuration

### Environment Variables

For development convenience, set these environment variables:

```bash
# In your shell profile (.bashrc, .zshrc, etc.)
export MODELCHECKER_DEV=1
export PYTHONPATH="${PYTHONPATH}:/path/to/ModelChecker/Code/src"

# For debug output
export DEBUG_MODELCHECKER=1

# For testing
export MODELCHECKER_TEST_MODE=1
```

### Git Configuration

Configure git for the project:

```bash
# Set up git hooks (if available)
git config core.hooksPath .githooks

# Configure line endings (important for cross-platform development)
git config core.autocrlf input  # On Linux/macOS
git config core.autocrlf true   # On Windows
```

## Platform-Specific Considerations

### Linux (Ubuntu/Debian)

```bash
# Install system dependencies
sudo apt-get update
sudo apt-get install python3-dev python3-venv git

# Install Z3 system-wide (alternative to pip)
sudo apt-get install z3

# For Jupyter notebook support
sudo apt-get install nodejs npm
```

### macOS

```bash
# Using Homebrew
brew install python git z3

# For M1 Macs, ensure compatibility
arch -arm64 pip install z3-solver

# For Jupyter notebook support
brew install node npm
```

### Windows

```powershell
# Using Python from Microsoft Store or python.org
# Ensure pip and venv are available

# Install Git for Windows
# https://git-scm.com/download/win

# For Jupyter notebook support
# Install Node.js from https://nodejs.org/
```

## Dependency Management

### Core Dependencies

The framework requires these core dependencies:

```python
# From pyproject.toml
z3-solver>=4.12.0    # SMT solver
networkx>=2.8        # Graph algorithms
typing-extensions    # Type hints for older Python versions
```

### Development Dependencies

For development work, install these additional packages:

```bash
# Testing
pip install pytest pytest-cov pytest-xdist

# Code quality
pip install black mypy flake8 isort

# Documentation
pip install sphinx sphinx-rtd-theme

# Jupyter development
pip install jupyter notebook ipywidgets
```

### Dependency Conflicts

If you encounter dependency conflicts:

```bash
# Check for conflicts
pip check

# Create clean environment
rm -rf venv
python -m venv venv
source venv/bin/activate  # or venv\Scripts\activate on Windows
pip install -e .

# For specific version constraints
pip install "z3-solver>=4.12.0,<5.0.0"
```

## Troubleshooting

### Common Setup Issues

#### Import Errors

```bash
# If you get "No module named model_checker"
# Ensure you're in the Code directory and installed with -e flag
pwd  # Should show .../ModelChecker/Code
pip install -e .

# Check PYTHONPATH
python -c "import sys; print('\n'.join(sys.path))"
```

#### Z3 Solver Issues

```bash
# Test Z3 installation
python -c "import z3; print(z3.get_version_string())"

# If Z3 fails to import
pip uninstall z3-solver
pip install z3-solver

# For system-wide Z3 (Linux)
sudo apt-get install z3
python -c "import z3"
```

#### Path Issues on NixOS

```bash
# Verify PYTHONPATH is set correctly
echo $PYTHONPATH  # Should include src directory

# If not in nix-shell, enter it
nix-shell

# If direnv not working
direnv allow
```

#### Permission Issues

```bash
# Make scripts executable
chmod +x dev_cli.py run_tests.py

# For NixOS
chmod +x *.py *.sh
```

### Platform-Specific Issues

#### Windows Path Issues

```bash
# Use forward slashes in Python paths
# Use the Windows-appropriate venv activation script
# Ensure Python is in PATH
```

#### macOS SSL Issues

```bash
# If pip fails with SSL errors
pip install --trusted-host pypi.org --trusted-host files.pythonhosted.org z3-solver

# Or update certificates
/Applications/Python\ 3.x/Install\ Certificates.command
```

#### Linux Package Manager Issues

```bash
# If system Python conflicts with pip
python3 -m venv venv  # Use python3 explicitly
source venv/bin/activate
python -m pip install --upgrade pip
```

## Testing Your Setup

### Verification Checklist

Run through this checklist to verify your setup:

```bash
# 1. Basic Python functionality
python -c "import model_checker; print('✓ ModelChecker imports')"

# 2. Z3 solver functionality
python -c "import z3; s = z3.Solver(); print('✓ Z3 working')"

# 3. Test suite execution
python test_package.py  # Should pass all tests
python test_theories.py  # Should pass all tests

# 4. Development CLI functionality
./dev_cli.py --help  # Should show help text
./dev_cli.py src/model_checker/theory_lib/logos/examples.py  # Should run examples

# 5. Theory loading
python -c "from model_checker.theory_lib.logos import logos_theory; print('✓ Theory loading')"
```

### Performance Testing

```bash
# Test solver performance
time ./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# Should complete in reasonable time (< 30 seconds)
# If slow, check Z3 installation and system resources
```

## Development Workflow Integration

### Daily Development Routine

```bash
# 1. Activate environment
source venv/bin/activate  # or enter nix-shell

# 2. Update from remote
git pull origin main

# 3. Run tests before starting work
./run_tests.py --unit

# 4. Start development work
# ... make changes ...

# 5. Test changes
./run_tests.py --package --components modified_component
./dev_cli.py test_examples.py

# 6. Commit and push
git add -A
git commit -m "Description of changes"
git push
```

### Environment Maintenance

```bash
# Regularly update dependencies
pip list --outdated
pip install --upgrade package_name

# Clean up environment periodically
pip cache purge
# Or recreate venv from scratch if needed
```

## See Also

- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - Complete development process
- [Testing Framework](../core/TESTING_GUIDE.md) - Test setup and execution
- [Feature Implementation](FEATURE_IMPLEMENTATION.md) - Implementation guidelines
- [Quality Assurance](../../quality/README.md) - Code quality standards

---

**Navigation**: [← Back to Development](../README.md) | [Maintenance Home](../../README.md) | [Development Workflow →](../implementation/DEVELOPMENT_WORKFLOW.md)