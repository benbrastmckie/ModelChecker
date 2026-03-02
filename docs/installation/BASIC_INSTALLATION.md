# Basic Installation Guide

[← Back to Installation](README.md) | [Troubleshooting →](TROUBLESHOOTING.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md)

## Overview

This guide covers the standard installation of ModelChecker using pip, Python's package installer. For development setup or Jupyter configuration, see the specialized guides.

**NixOS Users**: Do not use pip installation. See [NixOS Installation](#nixos-installation) for the correct approach.

## Why Installation is Simple

ModelChecker has minimal dependencies, making installation straightforward:

- **Python 3.8 or higher** - The programming language
- **z3-solver** - For constraint solving (automatically installed)
- **networkx** - For graph operations (automatically installed)

That's it! No complex system requirements, no compilation needed, no database setup. Just three components that pip handles automatically.

## What is pip?

Pip is Python's package installer - a tool that downloads and installs Python packages from the internet. It's like an app store for Python libraries. When you install Python, pip usually comes included.

**Why we use pip:**
- Downloads packages from PyPI (Python Package Index)
- Automatically handles dependencies
- Works on all operating systems
- Standard tool used by millions of Python developers

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

## Understanding Python Versions

Python version numbers like "3.8" or "3.11" indicate different releases of the language. ModelChecker requires version 3.8 or higher because it uses modern Python features.

**Why version matters:**
- Newer versions have better features and performance
- ModelChecker uses features introduced in Python 3.8
- Most systems now have Python 3.8+ installed

**Common version issues:**
- Multiple Python versions installed (use `python3` explicitly)
- Old system Python (upgrade or use virtual environment)
- Python 2 vs Python 3 (always use Python 3)

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

## What Gets Installed?

When you run `pip install model-checker`, here's what happens:

1. **ModelChecker package** - The main framework code
2. **z3-solver** - Microsoft's theorem prover for constraint solving
3. **networkx** - Library for working with graphs and networks

These install into your Python's site-packages directory. The `model-checker` command becomes available system-wide.

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

NixOS users cannot use pip directly due to the operating system's unique package management. Use the provided shell.nix instead:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter the Nix shell environment
nix-shell

# Run examples using the development CLI
./dev_cli.py examples/my_example.py
```

The `shell.nix` provides everything you need:
- Python with all required dependencies
- Correct PYTHONPATH configuration  
- Development tools and scripts
- Compatibility with NixOS's immutable design

For more details on NixOS development, see [Developer Setup](DEVELOPER_SETUP.md#nixos-development).

## Optional: Nix on Other Platforms

While NixOS users must use nix-shell, the Nix package manager is also available on macOS, Linux, and Windows (WSL2) for those who prefer reproducible environments. However, given ModelChecker's minimal dependencies, standard pip installation works perfectly for most users.

## Common Beginner Mistakes

### Using Wrong Python Version
**Problem**: "Command not found" or "Python 2.7" appears  
**Solution**: Use `python3` instead of `python`, or check your PATH

### Not Activating Virtual Environment
**Problem**: Package installs but can't be imported  
**Solution**: Activate your virtual environment first, or install globally with `--user`

### Permission Issues  
**Problem**: "Permission denied" during installation  
**Solution**: Use `pip install --user model-checker` or use a virtual environment

### Path Problems
**Problem**: `model-checker` command not found after installation  
**Solution**: Ensure Python's Scripts/bin directory is in your PATH

## Next Steps

- **Having issues?** See [Troubleshooting](TROUBLESHOOTING.md)
- **Want isolation?** Set up a [Virtual Environment](VIRTUAL_ENVIRONMENTS.md)
- **Using notebooks?** Configure [Jupyter Setup](JUPYTER_SETUP.md)
- **Ready to use?** Follow the [Getting Started Guide](GETTING_STARTED.md)

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
