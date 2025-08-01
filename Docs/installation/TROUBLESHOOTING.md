# Installation Troubleshooting Guide

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Developer Setup →](DEVELOPER_SETUP.md)

## Overview

This guide provides platform-specific solutions for common installation issues. Find your operating system below for targeted troubleshooting steps.

## Quick Diagnosis

**Common symptoms and solutions:**

| Symptom | Solution |
|---------|----------|
| `pip: command not found` | Try `python -m pip` or see [pip issues](#pip-command-not-found) |
| `Permission denied` | Use `--user` flag or [virtual environment](VIRTUAL_ENVIRONMENTS.md) |
| `model-checker: command not found` | See [PATH issues](#path-issues) |
| SSL/Certificate errors | See [your platform](#platform-specific-issues) section |
| Z3 solver errors | See [Z3 issues](#z3-solver-issues) |

## Platform-Specific Issues

### macOS

**Permission errors:**
```bash
pip install --user model-checker
```

**SSL certificate errors:**
```bash
# Update certificates
/Applications/Python\ 3.x/Install\ Certificates.command
```

**Multiple Python versions:**
```bash
# Use python3 explicitly
python3 -m pip install model-checker
```

### Windows

**"pip not recognized":**
1. Ensure Python was added to PATH during installation
2. Try using `py` instead:
   ```bash
   py -m pip install model-checker
   ```

**Permission errors:**
```bash
pip install --user model-checker
```

**Using WSL (Windows Subsystem for Linux):**
- Follow the Linux instructions below

### Linux

**Permission errors:**
```bash
# Install for current user only
pip install --user model-checker
```

**Missing pip:**
```bash
# Ubuntu/Debian
sudo apt install python3-pip

# Fedora/CentOS/RHEL
sudo dnf install python3-pip

# Arch Linux
sudo pacman -S python-pip
```

### NixOS

For NixOS installation, see [Basic Installation Guide](BASIC_INSTALLATION.md#nixos-installation).

**Common NixOS Issues**:
- Import errors: Use provided scripts (`dev_cli.py`, `run_tests.py`) instead of direct Python imports
- Missing dependencies: Ensure you're in the `nix-shell` environment
- Path issues: The `shell.nix` automatically configures PYTHONPATH

See [Developer Setup](DEVELOPER_SETUP.md#nixos-development) for advanced usage.

## Common Issues

### pip command not found

**Try these alternatives:**
```bash
python -m pip install model-checker
python3 -m pip install model-checker
py -m pip install model-checker  # Windows
```

**Still not working?**
- Verify Python installation: `python --version`
- Reinstall Python with pip included
- Check PATH environment variable

### PATH Issues

**"model-checker: command not found" after installation**

1. Try running as a Python module:
   ```bash
   python -m model_checker
   ```

2. Install with --user flag:
   ```bash
   pip install --user model-checker
   ```

3. Add user bin directory to PATH:
   ```bash
   # Linux/macOS
   export PATH="$HOME/.local/bin:$PATH"
   
   # Add to ~/.bashrc or ~/.zshrc to make permanent
   ```

### Z3 Solver Issues

**Basic Z3 installation:**
```bash
pip install z3-solver
```

**Binary compatibility issues:**
```bash
# Force compilation from source
pip install z3-solver --no-binary :all:
```

**Timeout errors:**
- Not an installation issue
- Adjust `max_time` in your example settings

### Import Errors

**"No module named 'model_checker'":**
1. Verify installation: `pip show model-checker`
2. Check Python environment matches pip
3. Ensure not in wrong directory

**NixOS import errors:**
- Use provided scripts: `dev_cli.py`, `run_tests.py`
- Don't use direct Python imports

## Getting Help

### Before asking for help:

1. **Check Python version:**
   ```bash
   python --version  # Must be 3.8+
   ```

2. **Verify pip installation:**
   ```bash
   pip --version
   ```

3. **Check installation:**
   ```bash
   pip show model-checker
   ```

### Where to get help:

- **GitHub Issues**: [Report bugs](https://github.com/benbrastmckie/ModelChecker/issues)
- **Documentation**: [Full docs](https://github.com/benbrastmckie/ModelChecker)
- **Development Setup**: See [Developer Setup](DEVELOPER_SETUP.md)

## Prevention Tips

1. **Use virtual environments** - See [Virtual Environments Guide](VIRTUAL_ENVIRONMENTS.md)
2. **Keep Python updated** - Use Python 3.8 or newer
3. **Install as user** - Avoid system-wide installation issues
4. **Check requirements** - Ensure all prerequisites are met

---

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md)