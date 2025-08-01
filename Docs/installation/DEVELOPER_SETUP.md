# Developer Setup Guide

[← Back to Installation](README.md) | [Jupyter Setup →](JUPYTER_SETUP.md) | [Development Guide →](../../Code/docs/DEVELOPMENT.md)

## Overview

This guide covers setting up a development environment for contributing to ModelChecker or creating custom semantic theories. For basic usage, see [Basic Installation](BASIC_INSTALLATION.md).

**NixOS Users**: Standard development methods will not work on NixOS. Skip to [NixOS Development](#nixos-development) for the correct approach.

## Prerequisites

- Python 3.8 or higher
- Git
- Basic command line knowledge

**Note**: NixOS users only need Git - all other dependencies are handled by `shell.nix`.

## NixOS Development

**NixOS users must use this approach** - standard pip/venv methods will not work on NixOS.

### Quick Start

```bash
# Clone and enter repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter Nix shell (handles all dependencies)
nix-shell

# Run examples
./dev_cli.py examples/my_example.py

# Run tests
./run_tests.py
```

### What shell.nix Provides

- Python with all dependencies pre-installed
- Correct PYTHONPATH configuration
- All development tools (pytest, black, mypy, etc.)
- No manual package installation needed
- Automatic environment activation

### Using direnv (Optional)

For automatic environment activation:

```bash
# Install direnv
nix-env -i direnv

# Enable in project
cd ModelChecker/Code
direnv allow

# Now environment activates automatically when entering directory
```

### NixOS Development Workflow

1. Always work within `nix-shell`
2. Use provided scripts (`dev_cli.py`, `run_tests.py`)
3. Never use `pip install` - all dependencies are managed by Nix
4. For new dependencies, update `shell.nix`

For more NixOS-specific details, see the `shell.nix` file in the Code directory.

## Standard Development Installation

**Important**: The following instructions are for non-NixOS systems only.

### 1. Clone the Repository

```bash
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code
```

### 2. Create Virtual Environment

```bash
python -m venv dev-env
source dev-env/bin/activate  # Linux/macOS
# or
dev-env\Scripts\activate     # Windows
```

See [Virtual Environments Guide](VIRTUAL_ENVIRONMENTS.md) for details.

### 3. Install in Development Mode

```bash
# Editable installation
pip install -e .

# For testing and building packages, install additional tools:
pip install pytest pytest-cov build twine
```

The `-e` flag creates an "editable" installation:
- Changes to source code take effect immediately
- No need to reinstall after modifications
- Ideal for development work

### 4. Verify Installation

```bash
# Run tests
./run_tests.py

# Check development CLI
./dev_cli.py --help
```

## Development Tools

### Recommended Development Dependencies

Install these tools for a complete development environment:

```bash
pip install pytest pytest-cov    # Testing framework and coverage
pip install black                 # Code formatter
pip install mypy                  # Type checker
pip install flake8               # Linting
pip install pre-commit           # Git hooks
```

### Development CLI

The `dev_cli.py` script provides development utilities:

```bash
# Run example without installation
./dev_cli.py examples/my_example.py

# Debug with constraint output
./dev_cli.py -p -z examples/debug.py

# Create new theory template
./dev_cli.py -l my_new_theory

# Run with profiling
./dev_cli.py --profile examples/slow.py
```

## Project Structure

```
ModelChecker/
├── Code/
│   ├── src/model_checker/      # Source code
│   │   ├── __init__.py
│   │   ├── builder/           # Project builder
│   │   ├── settings/          # Configuration
│   │   ├── theory_lib/        # Semantic theories
│   │   └── utils/             # Utilities
│   ├── docs/                  # Technical documentation
│   ├── tests/                 # Integration tests
│   ├── dev_cli.py            # Development CLI
│   ├── run_tests.py          # Test runner
│   ├── setup.py              # Package configuration
│   └── shell.nix             # NixOS configuration
└── Docs/                      # User documentation
```

## Testing

### Running Tests

```bash
# All tests
./run_tests.py

# Specific theory
./run_tests.py logos

# Unit tests only
./run_tests.py --unit

# With coverage
./run_tests.py --coverage
```

### Test Organization

```
theory_lib/my_theory/
├── tests/
│   ├── test_examples.py      # Example validation
│   ├── test_semantic.py      # Semantic tests
│   └── test_operators.py     # Operator tests
```

See [Testing Guide](../../Code/docs/TESTS.md) for comprehensive testing documentation.

## Code Standards

### Formatting

```bash
# Format code with black
black src/

# Check without modifying
black --check src/
```

### Type Checking

```bash
# Run mypy
mypy src/model_checker/

# Strict mode
mypy --strict src/model_checker/
```

### Linting

```bash
# Run flake8
flake8 src/

# With specific rules
flake8 --max-line-length=88 src/
```

See [Style Guide](../../Code/docs/STYLE_GUIDE.md) for coding standards.

## Creating New Theories

### 1. Generate Template

```bash
./dev_cli.py -l my_theory
```

This creates:
```
theory_lib/my_theory/
├── __init__.py
├── semantic.py          # Semantic implementation
├── operators.py         # Operator definitions
├── examples.py          # Example formulas
├── tests/              # Test directory
└── README.md           # Documentation
```

### 2. Implement Semantics

Edit `semantic.py`:
```python
class MyTheorySemantics(AbstractSemantics):
    def evaluate_proposition(self, prop, world):
        # Implementation
        pass
```

### 3. Add Tests

Create `tests/test_examples.py`:
```python
def test_my_operator():
    # Test implementation
    pass
```

### 4. Document

Update `README.md` following [MAINTENANCE.md](../../Code/MAINTENANCE.md) standards.


## Git Workflow

### Pre-commit Hooks

```bash
# Install hooks
pre-commit install

# Run manually
pre-commit run --all-files
```

### Branch Strategy

```bash
# Feature branch
git checkout -b feature/new-operator

# Make changes
git add -A
git commit -m "Add new operator implementation"

# Push to fork
git push origin feature/new-operator
```

See [Development Guide](../../Code/docs/DEVELOPMENT.md) for contribution guidelines.

## Debugging

### Using VS Code

`.vscode/launch.json`:
```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "name": "Debug Example",
            "type": "python",
            "request": "launch",
            "program": "${workspaceFolder}/Code/dev_cli.py",
            "args": ["examples/debug.py", "-p", "-z"],
            "cwd": "${workspaceFolder}/Code"
        }
    ]
}
```

### Using pdb

```python
# Add breakpoint in code
import pdb; pdb.set_trace()
```

### Performance Profiling

```bash
# Profile example
python -m cProfile -o profile.stats dev_cli.py examples/slow.py

# Analyze
python -m pstats profile.stats
```

## Common Development Tasks

### Update Dependencies

```bash
# Upgrade package
pip install --upgrade package_name

# Update requirements
pip freeze > requirements-dev.txt
```

### Build Documentation

```bash
# Build docs locally
cd docs/
make html
```

### Release Process

1. Update version in `setup.py`
2. Update CHANGELOG
3. Run full test suite
4. Create tagged release
5. Build and upload to PyPI

## Troubleshooting

### Import errors in development

```bash
# Ensure editable install
pip install -e .

# Check PYTHONPATH
echo $PYTHONPATH
```

### Tests failing locally

```bash
# Clean build artifacts
find . -type d -name __pycache__ -exec rm -rf {} +
find . -type f -name "*.pyc" -delete

# Reinstall
pip install -e .
```

## Next Steps

- **Read guidelines**: [Development Guide](../../Code/docs/DEVELOPMENT.md)
- **Understand architecture**: [Architecture Docs](../../Code/docs/ARCHITECTURE.md)
- **Explore theories**: [Theory Library](../../Code/src/model_checker/theory_lib/README.md)
- **Start contributing**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)

---

[← Back to Installation](README.md) | [Jupyter Setup →](JUPYTER_SETUP.md) | [Development Guide →](../../Code/docs/DEVELOPMENT.md)