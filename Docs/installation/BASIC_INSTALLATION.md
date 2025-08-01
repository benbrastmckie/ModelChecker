# Basic Installation Guide

[← Back to Installation](README.md) | [Troubleshooting →](TROUBLESHOOTING.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md)

## Overview

This guide covers the standard installation of ModelChecker using pip, Python's package installer. For development setup or Jupyter configuration, see the specialized guides.

**NixOS Users**: Do not use pip installation. See [NixOS Installation](#nixos-installation) for the correct approach.

## Prerequisites

Before installing ModelChecker, ensure you have:

- **Python 3.8 or higher** installed
- **pip** package manager (usually comes with Python)

To check your Python version:

```bash
python --version
# or
python3 --version
```

If Python is not installed, see [Installing Python](#installing-python) below.

## Installation Options

### Basic Installation

```bash
pip install model-checker
```

If you get "command not found", try:
- `python -m pip install model-checker`
- `python3 -m pip install model-checker`

### Installation with Extras

**Jupyter Support** (`[jupyter]`):
```bash
pip install model-checker[jupyter]
```
**Includes**: `ipywidgets`, `jupyter`, `matplotlib`, `ipython`, `networkx` for interactive notebooks and visualization

**All Features** (`[all]`):
```bash
pip install model-checker[all]
```
**Includes**: Currently the same as the `[jupyter]` option (all available extras)

## Verification

After installation, verify ModelChecker is working:

```bash
model-checker --version
```

This should display the installed version number.

## Updating ModelChecker

To update to the latest version:

```bash
pip install --upgrade model-checker
```

Or use the built-in command:

```bash
model-checker --upgrade
```

## Installing Python

### Windows

1. Download from [python.org/downloads](https://www.python.org/downloads/)
2. Run the installer
3. **Important**: Check "Add Python to PATH"

Or install from Microsoft Store (search for "Python")

### macOS

**Option 1**: Official installer from [python.org](https://www.python.org/downloads/)

**Option 2**: Using Homebrew
```bash
brew install python
```

### Linux

**Ubuntu/Debian**:
```bash
sudo apt update
sudo apt install python3 python3-pip
```

**Fedora/CentOS/RHEL**:
```bash
sudo dnf install python3 python3-pip
```

**Arch Linux**:
```bash
sudo pacman -S python python-pip
```

## NixOS Installation

NixOS users should use the repository's `shell.nix` configuration instead of pip:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter the Nix shell environment
nix-shell

# Run examples using the development CLI
./dev_cli.py examples/my_example.py
```

The `nix-shell` command automatically:
- Sets up Python with all required dependencies
- Configures the correct PYTHONPATH
- Provides access to development tools
- Ensures compatibility with NixOS's unique package management

For more details on NixOS development, see [Developer Setup](DEVELOPER_SETUP.md#nixos-development).

## Next Steps

- **Having issues?** See [Troubleshooting](TROUBLESHOOTING.md)
- **Want isolation?** Set up a [Virtual Environment](VIRTUAL_ENVIRONMENTS.md)
- **Using notebooks?** Configure [Jupyter Setup](JUPYTER_SETUP.md)
- **Ready to use?** Follow the [Getting Started Guide](../GETTING_STARTED.md)

## Quick Command Reference

| Task | Command |
|------|---------|
| Install | `pip install model-checker` |
| Install with Jupyter | `pip install model-checker[jupyter]` |
| Install all extras | `pip install model-checker[all]` |
| Verify installation | `model-checker --version` |
| Update | `pip install --upgrade model-checker` |
| Uninstall | `pip uninstall model-checker` |

---

[← Back to Installation](README.md) | [Troubleshooting →](TROUBLESHOOTING.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md)
