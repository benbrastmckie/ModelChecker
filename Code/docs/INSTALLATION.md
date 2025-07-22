# Installation Guide

## Requirements

- Python 3.x (check pyproject.toml for specific version)
- Z3 solver (installed automatically with pip)
- Virtual environment recommended

## Installation Methods

### Method 1: Development Installation (Recommended)

For development work, install in editable mode:

```bash
cd /path/to/ModelChecker/Code
pip install -e .
```

This allows you to make changes to the code without reinstalling.

### Method 2: Regular Installation

For regular use:

```bash
cd /path/to/ModelChecker/Code
pip install .
```

### Method 3: NixOS Installation

On NixOS, use the provided shell environment:

```bash
cd /path/to/ModelChecker/Code
nix-shell
```

This automatically sets up all dependencies and environment variables.

## Dependency Installation

The main dependencies will be installed automatically:
- z3-solver: SMT solver for model checking
- jupyter: For interactive notebooks
- ipywidgets: For interactive Jupyter widgets
- pytest: For running tests

## Verification

After installation, verify everything is working:

```bash
# Run tests
./run_tests.py

# Test a specific theory
./run_tests.py logos

# Run development CLI
./dev_cli.py examples/simple_example.py
```

## Jupyter Setup

To use Jupyter notebooks:

```bash
# Start Jupyter
./run_jupyter.sh

# Or manually
jupyter notebook
```

For widget support, you may need to enable extensions:
```bash
jupyter nbextension enable --py widgetsnbextension
```

## Troubleshooting

### Import Errors
- Always run commands from the project root directory
- On NixOS, use the provided scripts (dev_cli.py, run_tests.py) instead of direct Python commands

### Z3 Solver Issues
- If Z3 installation fails, try: `pip install z3-solver --no-binary :all:`
- For timeout issues, adjust max_time in settings

### Jupyter Widget Issues
- Ensure ipywidgets is installed: `pip install ipywidgets`
- Enable extensions: `jupyter nbextension enable --py widgetsnbextension`

### Virtual Environment Issues
- Create a fresh virtual environment: `python -m venv venv`
- Activate it: `source venv/bin/activate` (Linux/Mac)
- Reinstall: `pip install -e .`

## Platform-Specific Notes

### Linux (Primary Platform)
- Full support for all features
- Use provided shell scripts for best experience

### NixOS
- Use shell.nix for automatic environment setup
- PYTHONPATH is managed automatically
- Use provided wrapper scripts

### Other Platforms
- Basic functionality should work
- Some scripts may need adaptation
- Report issues on GitHub

## Next Steps

After installation:
1. Read the README.md for project overview
2. Check docs/DEVELOPMENT.md for development workflow
3. Explore theory examples with `./dev_cli.py`
4. Try Jupyter notebooks with `./run_jupyter.sh`