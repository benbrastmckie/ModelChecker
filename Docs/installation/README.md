# Installation Documentation: Setup and Configuration Guides

[← Back to Docs](../README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Getting Started →](GETTING_STARTED.md)

## Directory Structure

```
installation/
├── README.md                       # This file - installation documentation hub
├── BASIC_INSTALLATION.md           # Standard pip installation guide
├── GETTING_STARTED.md              # First steps after installation
├── TROUBLESHOOTING.md              # Platform-specific troubleshooting
├── VIRTUAL_ENVIRONMENTS.md         # Virtual environment setup guide
├── JUPYTER_SETUP.md                # Jupyter notebook configuration
└── DEVELOPER_SETUP.md              # Development environment setup
```

## Overview

This directory provides **comprehensive installation guides** for the ModelChecker framework, organized by use case to help users quickly find the information they need. Each guide focuses on a specific installation scenario, from basic pip installation to full development setup with Jupyter integration.

The documentation covers **6 installation scenarios**: standard pip installation, troubleshooting common issues, virtual environment setup, Jupyter notebook configuration, getting started guide, and developer environment setup. This modular approach ensures users can follow only the guides relevant to their needs without navigating unrelated content.

Installation options range from the simple `pip install model-checker` for basic usage to complete development environments with editable installs and testing frameworks. Special attention is given to **platform-specific considerations** (Windows, macOS, Linux, NixOS) and **Python environment management** to ensure successful installation across diverse systems.

## Theory Examples

### Basic Installation Verification

After installing ModelChecker, verify it's working:

```python
# Test basic import
from model_checker import get_theory

# Load a theory
theory = get_theory('logos')

# Quick validity check
premises = ["A", "A \\rightarrow B"]
conclusions = ["B"]
result = theory.check_validity(premises, conclusions)
print(f"Valid: {not result}")  # Should print: Valid: True
```

### Command-Line Usage

```bash
# Verify installation
model-checker --version

# Run an example
model-checker examples/modus_ponens.py

# With specific settings
model-checker examples/test.py --contingent --save json
```

### Development Setup Test

```bash
# Clone and install for development
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code
pip install -e .

# Run tests
./run_tests.py --unit
```

For complete examples, see [Getting Started](GETTING_STARTED.md).

## Subdirectories

This directory contains only installation guide files (no subdirectories). Each guide serves a specific installation need:

### Installation Guides

- **[BASIC_INSTALLATION.md](BASIC_INSTALLATION.md)** - Standard pip installation for most users, including prerequisites, installation options, and Python setup
- **[GETTING_STARTED.md](GETTING_STARTED.md)** - First steps after installation, including creating examples, understanding output, and common workflows
- **[TROUBLESHOOTING.md](TROUBLESHOOTING.md)** - Solutions for platform-specific issues, common errors, and debugging installation problems
- **[VIRTUAL_ENVIRONMENTS.md](VIRTUAL_ENVIRONMENTS.md)** - Creating isolated Python environments for clean installations and project management
- **[JUPYTER_SETUP.md](JUPYTER_SETUP.md)** - Configuring Jupyter notebooks with widgets for interactive ModelChecker development
- **[DEVELOPER_SETUP.md](DEVELOPER_SETUP.md)** - Complete development environment with editable installs, testing setup, and contribution preparation

## Documentation

### For New Users
- **[Basic Installation](BASIC_INSTALLATION.md)** - Start here for standard installation
- **[Getting Started](GETTING_STARTED.md)** - First steps and simple examples
- **[Troubleshooting](TROUBLESHOOTING.md)** - When things go wrong

### For Jupyter Users
- **[Jupyter Setup](JUPYTER_SETUP.md)** - Complete notebook configuration
- **[Virtual Environments](VIRTUAL_ENVIRONMENTS.md)** - Recommended for Jupyter
- **[Interactive Notebooks](../../Code/src/model_checker/theory_lib/logos/notebooks/)** - Example notebooks

### For Developers
- **[Developer Setup](DEVELOPER_SETUP.md)** - Full development environment
- **[Development Guide](../../Code/docs/DEVELOPMENT.md)** - Contribution workflow
- **[Testing Guide](../../Code/docs/TESTS.md)** - Running the test suite

## Key Features

### Multiple Installation Methods
- **Standard**: `pip install model-checker` - Basic installation
- **Jupyter**: `pip install model-checker[jupyter]` - With notebook support
- **All**: `pip install model-checker[all]` - Everything included
- **Development**: Editable install from cloned repository

### Platform Support
- **Windows** - Special considerations for `py` vs `python`
- **macOS** - Certificate updates and Homebrew options
- **Linux** - Distribution-specific package managers
- **NixOS** - Declarative `shell.nix` configuration

### Environment Management
- Virtual environment creation and activation
- Jupyter kernel registration
- Requirements file generation
- Clean uninstallation procedures

## References

### Installation Resources
- [Python Downloads](https://www.python.org/downloads/) - Official Python installers
- [pip Documentation](https://pip.pypa.io/) - Python package installer guide
- [Virtual Environments](https://docs.python.org/3/tutorial/venv.html) - Python venv documentation

### Related Documentation
- **[Usage Guide](../usage/README.md)** - Using ModelChecker after installation
- **[Theory Library](../../Code/src/model_checker/theory_lib/README.md)** - Available theories
- **[Architecture](../architecture/README.md)** - How ModelChecker works

---

[← Back to Docs](../README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md)