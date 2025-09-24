# Developer Setup Guide

[← Back to Installation](README.md) | [Jupyter Setup →](JUPYTER_SETUP.md) | [Development Guide →](../../Code/docs/DEVELOPMENT.md)

## Overview

This guide covers setting up a development environment for contributing to ModelChecker or creating custom semantic theories. For basic usage, see [Basic Installation](BASIC_INSTALLATION.md).

## Simple Development Setup (Recommended)

ModelChecker has minimal dependencies, making development setup straightforward:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Install in development mode
pip install -e .

# That's it! Run tests to verify
./run_tests.py --unit
```

This simple approach works because:
- Only two dependencies: z3-solver and networkx
- No complex build requirements
- Editable install means changes take effect immediately
- Development scripts are included in the repository

## Available Development Scripts

- `./dev_cli.py` - Run examples with local code
- `./run_tests.py` - Run test suites
- `./run_update.py` - Version management
- `./run_jupyter.sh` - Launch Jupyter with proper environment

## Prerequisites

- Python 3.8 or higher
- Git
- Basic command line knowledge

## Optional: Virtual Environment

If you prefer to isolate dependencies (though with only z3-solver and networkx, conflicts are unlikely):

```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
pip install -e .
```

See [Virtual Environments Guide](VIRTUAL_ENVIRONMENTS.md) for more details.

## Optional: Nix Environment

For those who prefer reproducible environments, a shell.nix is provided:

```bash
nix-shell  # If you have Nix installed
```

This is particularly useful for:
- NixOS users (who must use this approach)
- Teams wanting identical environments
- CI/CD pipelines

But it's not necessary for general development given the simple dependencies.

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

## Development Tools and Testing

### Core Development Tools

The repository includes essential development scripts:

```bash
# Run examples without full installation
./dev_cli.py examples/my_example.py

# Run with debugging output
./dev_cli.py -p -z examples/debug.py

# Run test suites
./run_tests.py          # All tests
./run_tests.py --unit   # Unit tests only
./run_tests.py logos    # Specific theory
```

### Optional Development Dependencies

For a more complete development environment, you may want:

```bash
pip install pytest pytest-cov    # Testing framework and coverage
pip install black                 # Code formatter
pip install mypy                  # Type checker
pip install flake8               # Linting
pip install pre-commit           # Git hooks
```

These are optional - the core development work only needs the base installation.

### Using the Development CLI

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

## Working Without Installation

You can work on ModelChecker without installing it system-wide:

```bash
# Clone and enter directory
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Run directly with dev CLI
./dev_cli.py examples/test.py

# The dev_cli.py automatically sets up paths
```

This approach is perfect for:
- Quick testing of changes
- Running examples
- Debugging issues
- Theory development

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

Update `README.md` following documentation standards:
- **[Documentation Standards](../maintenance/quality/DOCUMENTATION_STANDARDS.md)** - General principles
- **[README Standards](../maintenance/quality/README_STANDARDS.md)** - README-specific requirements
- **[Theory README Template](../maintenance/templates/THEORY_README.md)** - Theory documentation template


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
- **Understand architecture**: [Architecture Docs](../../Code/docs/PIPELINE.md)
- **Explore theories**: [Theory Library](../../Code/src/model_checker/theory_lib/README.md)
- **Start contributing**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)

---

[← Back to Installation](README.md) | [Jupyter Setup →](JUPYTER_SETUP.md) | [Development Guide →](../../Code/docs/DEVELOPMENT.md)