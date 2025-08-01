# Installation Documentation

[← Back to Docs](../README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Developer Setup →](DEVELOPER_SETUP.md)

## Overview

This directory contains modular installation guides for the ModelChecker framework. Each guide focuses on a specific installation scenario, allowing users to find exactly what they need without wading through unrelated information.

## Directory Structure

```
installation/
├── README.md                 # This file - installation documentation hub
├── BASIC_INSTALLATION.md     # Standard pip installation guide
├── TROUBLESHOOTING.md        # Platform-specific troubleshooting
├── VIRTUAL_ENVIRONMENTS.md   # Virtual environment setup guide
├── JUPYTER_SETUP.md          # Jupyter notebook configuration
└── DEVELOPER_SETUP.md        # Development environment setup
```

## Quick Navigation

### For New Users

1. **[Basic Installation](BASIC_INSTALLATION.md)** - Standard pip installation with options
2. **[Troubleshooting](TROUBLESHOOTING.md)** - Solutions for common installation issues
3. **[Virtual Environments](VIRTUAL_ENVIRONMENTS.md)** - Recommended for clean installations

### For Jupyter Users

- **[Jupyter Setup](JUPYTER_SETUP.md)** - Complete Jupyter notebook configuration and widget setup

### For Developers

- **[Developer Setup](DEVELOPER_SETUP.md)** - Clone repository, editable installation, and development tools

## Installation Overview

### Prerequisites

- **Python 3.8 or higher** - Check with `python --version`
- **pip** - Usually comes with Python
- **Z3 solver** - Installed automatically with ModelChecker

### Installation Methods

1. **Standard Installation** - `pip install model-checker`
2. **Jupyter Support** - `pip install model-checker[jupyter]`
3. **Everything** - `pip install model-checker[all]`
4. **Development Setup** - Clone repository and editable install

### Platform Notes

- **Windows**: May need to use `py` instead of `python`
- **macOS**: May need to update certificates
- **Linux**: May need to install pip separately
- **NixOS**: Use repository's `shell.nix` instead of `pip`

## Quick Start

For most users:

```bash
pip install model-checker
model-checker --version
```

Need help? See **[Troubleshooting](TROUBLESHOOTING.md)** for platform-specific solutions.

## Table of Contents

1. [Basic Installation](BASIC_INSTALLATION.md) - Standard installation guide
2. [Troubleshooting](TROUBLESHOOTING.md) - Platform-specific issues and solutions
3. [Virtual Environments](VIRTUAL_ENVIRONMENTS.md) - Isolated Python environments
4. [Jupyter Setup](JUPYTER_SETUP.md) - Notebook integration and widgets
5. [Developer Setup](DEVELOPER_SETUP.md) - Contributing and development

## Related Documentation

- **[Getting Started](../GETTING_STARTED.md)** - First steps after installation
- **[Development Guide](../../Code/docs/DEVELOPMENT.md)** - Development workflow
- **[Technical Documentation](../../Code/docs/README.md)** - Architecture and internals

---

[← Back to Docs](../README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Getting Started →](../GETTING_STARTED.md)
