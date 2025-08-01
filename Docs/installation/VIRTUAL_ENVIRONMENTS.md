# Virtual Environments Guide

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Jupyter Setup →](JUPYTER_SETUP.md)

## Overview

Virtual environments provide isolated Python installations, preventing package conflicts and ensuring clean, reproducible setups. This guide covers creating and managing virtual environments for ModelChecker.

**NixOS Users**: See [NixOS Project Isolation](#nixos-project-isolation) for the Nix approach to environment isolation.

## Why Use Virtual Environments?

- **Isolation**: Keep ModelChecker dependencies separate from other projects
- **No conflicts**: Avoid version conflicts between packages
- **Clean uninstall**: Remove everything by deleting one directory
- **No admin rights**: Install packages without system permissions
- **Reproducibility**: Share exact environment specifications

## Quick Start

```bash
# Create virtual environment
python -m venv modelchecker-env

# Activate it
source modelchecker-env/bin/activate  # Linux/macOS
modelchecker-env\Scripts\activate     # Windows

# Install ModelChecker
pip install model-checker

# When done, deactivate
deactivate
```

## Creating Virtual Environments

### Using venv (Built-in)

**Create environment:**
```bash
python -m venv modelchecker-env
```

**With specific Python version:**
```bash
python3.9 -m venv modelchecker-env
```

### Using virtualenv (Third-party)

**Install virtualenv:**
```bash
pip install virtualenv
```

**Create environment:**
```bash
virtualenv modelchecker-env
```

### Using conda

**Create environment:**
```bash
conda create -n modelchecker python=3.9
conda activate modelchecker
```

## Activating Environments

### Linux/macOS

```bash
source modelchecker-env/bin/activate
```

### Windows

**Command Prompt:**
```cmd
modelchecker-env\Scripts\activate.bat
```

**PowerShell:**
```powershell
modelchecker-env\Scripts\Activate.ps1
```

### Verification

When activated, your prompt shows the environment name:
```bash
(modelchecker-env) $ python --version
```

## Installing ModelChecker

With environment activated:

```bash
# Basic installation
pip install model-checker

# With Jupyter support
pip install model-checker[jupyter]

# For development work, clone the repository instead:
# See Developer Setup guide
```

## Managing Environments

### List installed packages
```bash
pip list
```

### Save environment
```bash
pip freeze > requirements.txt
```

### Recreate environment
```bash
pip install -r requirements.txt
```

### Deactivate environment
```bash
deactivate
```

### Delete environment
```bash
# Just delete the directory
rm -rf modelchecker-env  # Linux/macOS
rmdir /s modelchecker-env  # Windows
```

## Best Practices

### Project Structure

```
my-logic-project/
├── modelchecker-env/     # Virtual environment (don't commit)
├── examples.py           # Your ModelChecker examples
├── requirements.txt      # Package list (do commit)
└── .gitignore           # Exclude env from git
```

### .gitignore
```
modelchecker-env/
__pycache__/
*.pyc
```

### Naming Conventions

- Use descriptive names: `modelchecker-env`, `logic-env`
- Include Python version if needed: `mc-py39-env`
- Keep consistent across team

## Advanced Usage

### Multiple Environments

Create separate environments for different purposes:

```bash
# For development
python -m venv mc-dev-env

# For testing
python -m venv mc-test-env

# For specific project
python -m venv thesis-logic-env
```

### Environment Variables

Set project-specific variables:

```bash
# Linux/macOS (add to activate script)
export MODEL_CHECKER_SETTINGS="custom_settings.json"

# Windows (add to activate.bat)
set MODEL_CHECKER_SETTINGS=custom_settings.json
```

### Jupyter with Virtual Environments

```bash
# Install ipykernel in environment
pip install ipykernel

# Add environment to Jupyter
python -m ipykernel install --user --name=modelchecker

# Launch Jupyter
jupyter notebook
# Select "modelchecker" kernel
```

See [Jupyter Setup](JUPYTER_SETUP.md) for details.

## Troubleshooting

### "virtualenv: command not found"
```bash
pip install virtualenv
# or use built-in venv
python -m venv modelchecker-env
```

### Permission errors on Windows
```powershell
# Allow script execution
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

### Wrong Python version
```bash
# Specify exact Python
/usr/bin/python3.9 -m venv modelchecker-env
```

## NixOS Project Isolation

NixOS provides superior project isolation through its declarative package management. Instead of virtual environments, NixOS users should use Nix shells for project-specific dependencies.

### Using ModelChecker's shell.nix

The repository includes a `shell.nix` that provides complete isolation:

```bash
# Clone and enter the project
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter isolated Nix shell
nix-shell
```

The `shell.nix` provides:
- **Complete isolation** - Dependencies are isolated from system packages
- **Reproducibility** - Exact versions specified in `shell.nix`
- **No conflicts** - Each project has its own dependency tree
- **Automatic cleanup** - Dependencies garbage collected when not in use

### Per-Project Nix Shells

For multiple ModelChecker projects with different requirements:

```bash
# Project 1: Research work
cd ~/research/logic-project
nix-shell ~/ModelChecker/Code/shell.nix

# Project 2: Teaching materials  
cd ~/teaching/modal-logic
nix-shell ~/ModelChecker/Code/shell.nix --arg pythonVersion "3.9"
```

### Custom Nix Environments

Create a project-specific `shell.nix`:

```nix
# my-project/shell.nix
{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    python39
    python39Packages.z3
    # Add project-specific dependencies
  ];
  
  shellHook = ''
    export PYTHONPATH="${../ModelChecker/Code/src}:$PYTHONPATH"
    echo "Entered ModelChecker environment for my-project"
  '';
}
```

### Advantages Over Virtual Environments

1. **System-wide caching** - Packages shared across projects when versions match
2. **Atomic updates** - Rollback to previous environments instantly
3. **Multi-language** - Mix Python, system tools, and other languages
4. **True isolation** - Even system libraries are isolated
5. **No activation needed** - Just `nix-shell` and you're ready

### Direnv Integration

For automatic environment switching (like virtualenv activation):

```bash
# Install direnv
nix-env -i direnv

# Create .envrc in your project
echo "use nix" > .envrc
direnv allow

# Now entering the directory activates the environment automatically
cd my-project  # Environment loads
cd ..          # Environment unloads
```

See [Developer Setup](DEVELOPER_SETUP.md#nixos-development) for more NixOS-specific details.

## Next Steps

- **Install ModelChecker**: Follow [Basic Installation](BASIC_INSTALLATION.md)
- **Configure Jupyter**: See [Jupyter Setup](JUPYTER_SETUP.md)
- **Start using**: Follow [Getting Started Guide](../GETTING_STARTED.md)

---

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Jupyter Setup →](JUPYTER_SETUP.md)