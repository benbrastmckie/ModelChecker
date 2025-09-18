# Development Guide

[← Back to Technical Docs](README.md) | [Architecture →](ARCHITECTURE.md) | [Testing →](TESTS.md)

## Table of Contents

1. [Environment Setup](#environment-setup)
2. [Development Workflow](#development-workflow)
3. [Testing Commands](#testing-commands)
4. [Development Commands](#development-commands)
5. [Git Workflow](#git-workflow)
6. [Common Development Tasks](#common-development-tasks)
7. [Error Handling](#error-handling)
8. [Known Challenges](#known-challenges)
9. [Contributing Guidelines](#contributing-guidelines)

## Environment Setup

### Requirements

- **Python**: 3.8 or higher (check pyproject.toml for specific version)
- **Key Dependencies**: z3-solver, jupyter, pytest
- **Virtual Environment**: Recommended for isolated development
- **Platform Support**: Linux (primary), macOS, Windows, with NixOS-specific tooling

### Standard Setup (pip)

For macOS, Windows, and non-NixOS Linux:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Create and activate virtual environment
python -m venv venv
# On Windows:
venv\Scripts\activate
# On macOS/Linux:
source venv/bin/activate

# Install in development mode
pip install -e .

# Install development dependencies manually
pip install pytest pytest-cov black mypy

# Optional: Install Jupyter dependencies
pip install -e ".[jupyter]"

# Verify installation
python test_package.py
python test_theories.py
```

### NixOS Setup

NixOS requires special handling due to its immutable package management:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter the development shell
nix-shell
```

The provided `shell.nix` file automatically:

- Sets PYTHONPATH to include local source code
- Installs required dependencies (z3-solver, networkx, etc.)
- Makes development scripts executable

For automatic environment activation:

```bash
# Install direnv if you haven't already
nix-env -i direnv

# Allow the .envrc file once
direnv allow

# Environment activates automatically when entering directory
```

## Development Workflow

### Project Structure

```
Code/
├── src/model_checker/      # Main package source
│   ├── theory_lib/        # Semantic theories
│   ├── builder/           # Model construction
│   ├── iterate/           # Model iteration
│   ├── jupyter/           # Jupyter integration
│   └── settings/          # Configuration management
├── tests/                 # Integration tests
├── docs/                  # Technical documentation
└── dev_cli.py            # Development CLI
```

### Code Standards

Follow the standards in [MAINTENANCE.md](../MAINTENANCE.md):

- Formula formatting (capital letters, proper parentheses)
- Examples.py structure (see [EXAMPLES.md](EXAMPLES.md))
- Documentation standards (comprehensive README structure)
- No emojis anywhere in code or documentation

## Testing Commands

Always run tests to ensure changes don't break existing functionality:

### Theory Tests

```bash
# Run all theory tests
python test_theories.py

# Test specific theories
python test_theories.py --theories logos bimodal

# Run with verbose output
python test_theories.py -v

# Stop on first failure
python test_theories.py -x
```

### Package Tests

```bash
# Run all non-theory component tests
python test_package.py

# Test specific components
python test_package.py --components builder settings

# List available components
python test_package.py --list

# Run Z3 isolation tests
python test_package.py --components utils.tests
```

### Test Organization

- **test_theories.py**: For all theory_lib tests
- **test_package.py**: For all other component tests
- **Do not create standalone test runners**

### NixOS Testing

On NixOS, always use the provided scripts rather than direct Python commands:

```bash
./run_tests.py          # Run all tests
./run_tests.py logos    # Test specific theory
./run_tests.py --unit   # Unit tests only
```

## Development Commands

### Development CLI

The development CLI is the primary tool for running examples during development:

```bash
# Basic usage (always specify target file)
./dev_cli.py examples/simple_example.py

# Show constraints
./dev_cli.py -p examples/my_example.py

# Show Z3 output
./dev_cli.py -z examples/my_example.py

# Combine flags
./dev_cli.py -p -z examples/my_example.py

# Create new theory from template
./dev_cli.py -l logos my_new_theory
```

### Other Development Tools

```bash
# Package update with testing
python run_update.py

# Run Jupyter notebooks
./run_jupyter.sh

# Run specific example file
model-checker examples.py
```

For detailed documentation on advanced features like iterate settings, theory comparison, maximize mode, and debugging flags, see [TOOLS.md](TOOLS.md).

## Git Workflow

### Branch Strategy

- **Main branch**: master
- **Feature branches**: feature/description
- **Bug fixes**: fix/description
- **Documentation**: docs/description

### Commit Requirements

1. **Test before commit**: Run both test suites
2. **Commit messages**: Use present tense, be descriptive
3. **Breaking changes**: Acceptable per design philosophy
4. **Reference issues**: Include issue numbers when applicable

### Pull Request Process

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Ensure all tests pass
5. Update documentation as needed
6. Submit pull request with clear description

## Common Development Tasks

### Adding a New Theory

1. Create directory structure:

   ```bash
   mkdir -p src/model_checker/theory_lib/new_theory/{docs,tests,notebooks}
   ```

2. Implement required files:

   - `semantic.py`: Core semantic implementation
   - `operators.py`: Operator definitions
   - `examples.py`: Example formulas
   - `__init__.py`: Theory registration
   - `README.md`: Theory documentation

3. Register in `theory_lib/__init__.py`:

   ```python
   AVAILABLE_THEORIES.append('new_theory')
   ```

4. Create tests in `tests/` subdirectory:

   **Required**: Include a test for project generation:
   ```python
   # new_theory/tests/integration/test_project_generation.py
   def test_new_theory_project_generation():
       """Verify BuildProject works with this theory."""
       project = BuildProject('new_theory')
       # Test project generation succeeds
   ```

5. Verify with:
   ```bash
   python test_theories.py --theories new_theory
   ```

### Testing Philosophy: Theory Independence

**Important Principle**: Maintain strict separation between theory-specific and infrastructure tests:

- **Theory-specific tests** (in `theory_lib/*/tests/`):
  - Should test theory-specific functionality
  - MUST include project generation tests
  - May reference their own theory by name
  - Should verify theory-specific examples work

- **Infrastructure tests** (in `builder/tests/`, `output/tests/`, etc.):
  - Should be theory-agnostic
  - Should NOT reference specific theories by name (logos, exclusion, etc.)
  - Should use mock theories or parameterized tests
  - Should test generic functionality that works across all theories

This separation ensures that:
- New theories can be added without modifying infrastructure tests
- Theory structures can evolve independently
- Infrastructure remains flexible and maintainable

### Adding a New Operator

1. In the theory's `operators.py`:

   ```python
   # For primitive operators
   class NewOperator(syntactic.Operator):
       name = "\\new"
       arity = 2

       def true_at(self, leftarg, rightarg, eval_point):
           # Define truth conditions
           pass

   # For defined operators
   class DefinedOperator(syntactic.DefinedOperator):
       name = "\\defined"
       arity = 1

       def derived_definition(self, arg):
           # Return operator tree
           pass
   ```

2. Register in operator collection

3. Add test cases in `examples.py`

### Working with Jupyter Integration

1. Start Jupyter server:

   ```bash
   ./run_jupyter.sh
   ```

2. Use high-level functions:

   ```python
   from model_checker import check_formula, find_countermodel
   from model_checker.jupyter import ModelExplorer

   # Interactive exploration
   explorer = ModelExplorer()
   explorer.display()
   ```

3. Navigate to theory-specific notebooks for demos

## Error Handling

### Common Error Patterns

#### Z3 Solver Issues

- **Timeout errors**: Adjust `max_time` setting
- **Bitvector capacity**: Reduce model complexity
- **Undecidable structures**: Simplify logical formulas

#### Path and Import Issues

- **Import errors**: Run from project root directory
- **NixOS paths**: Use provided scripts, not direct Python
- **Module loading**: Check PYTHONPATH configuration

#### Theory-Specific Issues

- **World reference errors**: Use consistent world IDs
- **Theory compatibility**: Use adapter system for conversion
- **Operator conflicts**: Check operator namespaces

#### Jupyter Issues

- **Widget display**: Enable nbextensions
- **Kernel problems**: Restart kernel for import issues
- **Path issues**: Ensure correct environment activation

### Debugging Tools

1. Check logs and error messages
2. Use debugging tools in `jupyter/debug/`
3. Review debug logging in `__main__.py` and `cli.py`
4. Follow systematic approach in `jupyter/debug/DEBUGGING.md`

## Known Challenges

### Theory Compatibility

Different theories may have incompatible operators or semantics. Use the theory adapter system for conversion between theories.

### NixOS Path Management

PYTHONPATH management is critical on NixOS. Always use provided scripts (`run_jupyter.sh`, `dev_cli.py`) instead of direct commands.

### Z3 Solver Limitations

- Complex models may hit solver timeouts
- Some logical structures may be undecidable
- Bitvector arithmetic has capacity limits

### Platform-Specific Issues

- **Windows**: Path separators and line endings
- **macOS**: SSL certificates for package installation
- **Linux**: Distribution-specific package names

## Contributing Guidelines

### Code Quality

1. Follow [MAINTENANCE.md](../MAINTENANCE.md) standards
2. Write comprehensive docstrings
3. Include type hints where appropriate
4. Add unit tests for new functionality

### Documentation

1. Update relevant README files
2. Include docstrings for all public APIs
3. Add examples for new features
4. Follow comprehensive documentation standards for README files

### Testing

1. Write tests for all new features
2. Ensure 100% pass rate before submitting
3. Include both positive and negative test cases
4. Document test purpose and expectations

### Review Process

1. Code review by maintainers
2. All tests must pass
3. Documentation must be complete
4. Follow project coding standards

### Licensing

When creating new theories based on existing ones:

1. Review [License Inheritance Guidelines](LICENSE_INHERITANCE.md)
2. Maintain proper attribution to original authors
3. Document your novel contributions
4. Ensure GPL-3.0 compatibility

For more details on the dual licensing structure (static framework license vs inheritable theory licenses), see the complete [License Inheritance Guidelines](LICENSE_INHERITANCE.md).

---

[← Back to Technical Docs](README.md) | [Architecture →](ARCHITECTURE.md) | [Testing →](TESTS.md)
