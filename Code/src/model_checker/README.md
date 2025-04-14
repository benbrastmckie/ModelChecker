# ModelChecker

The ModelChecker is a programmatic semantics framework for implementing and comparing logical theories, with a focus on modal, counterfactual, and hyperintensional logic. It provides tooling for defining semantic theories, testing logical principles, and finding countermodels.

## API Architecture

The ModelChecker framework follows a modular architecture designed to separate core functionality from theory-specific implementations:

### Core Components

1. **Builder Module** (`builder.py`)

   - `BuildExample`: Creates a model from a named example within a theory
   - `BuildModule`: Loads and runs examples from a specific module
   - `BuildProject`: Creates new theory implementations from templates

2. **Model Module** (`model.py`)

   - `ModelConstraints`: Core model checking and constraint solving
   - `ModelDefaults`: Base class for semantic model implementations
   - `SemanticDefaults`: Base semantics with default implementations
   - `PropositionDefaults`: Base proposition class for formula evaluation

3. **Syntactic Module** (`syntactic.py`)

   - `Syntax`: Parses and processes logical formulas
   - `Operator`: Base class for logical operators
   - `DefinedOperator`: Base class for operators defined in terms of primitives

4. **Utils Module** (`utils.py`)

   - Helper functions for common operations
   - Theory loading via `get_theory()`
   - Example loading via `get_example()`
   - Testing via `run_test()`

5. **Main Module** (`__main__.py`)

   - Command-line interface and entry points
   - Argument parsing and dispatch

6. **Settings Package** (`settings/`)

   - Centralized settings management system
   - Theory-specific default settings
   - Validation and warning systems for unknown settings
   - Command-line flag integration
   - See [Settings Documentation](settings/README.md) for details

7. **Jupyter Package** (`jupyter/`)
   - Interactive exploration of logical models in notebooks
   - Formula checking, countermodel finding, and visualization
   - Support for Unicode and LaTeX notation
   - Theory-specific adapters for consistent interfaces
   - See [Jupyter Integration Documentation](jupyter/README.md) for details

### Theory Library

The `theory_lib` package contains specific implementations of logical theories:

1. **Theory Registry** (`theory_lib/__init__.py`)

   - Central registry of available theories
   - Lazy loading of theory implementations
   - Utilities for discovering and accessing theories

2. **Individual Theories**
   - Each theory follows a standardized structure:
     - `semantic.py`: Core semantic framework implementation
     - `operators.py`: Operator definitions and semantics
     - `examples.py`: Test cases and examples
     - `test/`: Unit tests for the theory

### API Flow

The typical API usage flow follows these steps:

1. **Theory Selection**: Get a theory via `get_theory()`
2. **Model Building**: Create a model with `BuildExample` or `BuildModule`
3. **Formula Evaluation**: Check formulas using the model's methods
4. **Result Analysis**: Analyze results and possibly find countermodels

```python
# A typical workflow might look like:
from model_checker import BuildExample, get_theory

# 1. Load a theory
theory = get_theory("default")

# 2. Create a model
model = BuildExample("simple_modal", theory)

# 3. Check a formula
result = model.check_formula("\\Box p -> p")

# 4. Analyze the result
print(f"Formula is {'valid' if result else 'invalid'}")
```

### Object Hierarchy

The object hierarchy for model checking flows as follows:

1. **BuildExample/BuildModule**: Top-level coordination
2. **ModelConstraints**: Constraint generation and solving
3. **Syntax**: Formula parsing and normalization
4. **Theory-specific semantics**: Semantic interpretation
5. **Theory-specific proposition**: Formula evaluation
6. **Theory-specific operators**: Operator behavior

### Extension Points

The framework is designed to be extended in several ways:

1. **New Theories**: Add new theory directories to `theory_lib/`
2. **New Operators**: Subclass `Operator` or `DefinedOperator`
3. **New Semantics**: Subclass `SemanticDefaults`
4. **New Interfaces**: Add new builders or integration points

### Theory-Specific Design

Each theory in the ModelChecker framework is designed to be self-contained with its own appropriate defaults and settings. This design follows several key principles:

1. **Relevance Principle**: Theories should only define settings that are relevant to their specific semantics. For example:

   - Temporal theories like `bimodal` include time-related settings like `M` (number of time points)
   - Visualization settings like `align_vertically` only appear in theories where they make sense

2. **Clear Defaults**: Each theory defines its own default settings via:

   - `DEFAULT_EXAMPLE_SETTINGS`: For example-specific settings
   - `DEFAULT_GENERAL_SETTINGS`: For general output and behavior settings

3. **Warning System**: The framework warns about unknown settings only when:
   - A user explicitly provides a command-line flag that doesn't correspond to a setting in the theory
   - A user includes a setting in their configuration that isn't defined in the theory's defaults

For detailed information about settings management and theory-specific settings:

- [Settings System Documentation](settings/README.md)
- [Theory Library Documentation](theory_lib/README.md#theory-specific-settings)

## Development

This section provides information for contributors who want to develop or extend the ModelChecker framework.

### Development Scripts

The repository includes several utility scripts that help with development, testing, and releasing:

#### 1. Running Theory Tests (`test_theories.py`)

The `test_theories.py` script automatically discovers and runs tests for all registered theories in the framework. It uses the centralized `AVAILABLE_THEORIES` registry in `theory_lib/__init__.py` to determine which theories to test.

```bash
# Run tests for all registered theories
./test_theories.py

# Run tests for specific theories
./test_theories.py --theories default exclusion

# Run tests with verbose output
./test_theories.py -v

# Run tests with failfast (stop after first failure)
./test_theories.py -x
```

The script searches for test directories within each theory directory and runs pytest on them. It provides a summary of test results at the end.

#### 2. Running Package Component Tests (`test_package.py`)

The `test_package.py` script runs tests for non-theory package components like `builder`, `settings`, etc.

```bash
# Run tests for all components
./test_package.py

# Run tests for specific components
./test_package.py --components builder settings

# List available testable components
./test_package.py --list

# Run with verbose output
./test_package.py -v

# Run with failfast (stop after first failure)
./test_package.py -x
```

The script dynamically discovers components with test directories and provides a consistent interface for running their tests.

#### 3. Package Updates (`run_update.py`)

The `run_update.py` script manages version updates, testing, building, and uploading to PyPI:

```bash
# Regular update (with prompts for testing)
./run_update.py

# Skip version increment but still run tests and upload
./run_update.py --no-version

# Skip the upload step (useful for testing the build process)
./run_update.py --no-upload
```

The script:

1. Updates version numbers in pyproject.toml and __init__.py
2. Runs package component tests (using test_package.py)
3. Runs theory tests (using test_theories.py)
4. Builds the package
5. Uploads to PyPI using twine

#### 3. Development CLI (`dev_cli.py`)

The `dev_cli.py` script provides a development-mode CLI that uses the local source code:

```bash
# Run the development CLI with an example file
./dev_cli.py examples.py

# Run with CLI flags
./dev_cli.py -v
```

This script ensures that your local source code is used instead of any installed package version, which is particularly useful during development.

### NixOS Development

Developing on NixOS requires special consideration due to its immutable package management system. This section covers NixOS-specific setup.

#### Shell Environment

The repository includes a `shell.nix` file that defines the development environment:

```bash
# Enter the development environment
nix-shell

# With direnv installed (automatic environment activation)
# First, allow the .envrc file once:
direnv allow
# Then the environment will be automatically loaded when you enter the directory
```

The shell environment sets up all necessary dependencies and environment variables, especially `PYTHONPATH`, to ensure that the local source code is used.

#### Path Resolution

On NixOS, package installation in development mode (`pip install -e .`) may not work as expected due to read-only filesystem restrictions. The development scripts address this by:

1. Using explicit `PYTHONPATH` settings to prioritize local source code
2. Providing wrapper scripts that manage the correct Python import paths
3. Using importlib for dynamic imports instead of relying on installed packages

#### Using dev_cli.py on NixOS

The `dev_cli.py` script is particularly important on NixOS since it:

1. Correctly sets `sys.path` to prioritize local source code
2. Enables running the CLI without modifying system packages
3. Works seamlessly with the nix-shell environment

```bash
# Inside the nix-shell (or with direnv enabled)
./dev_cli.py path/to/example.py
```

### Adding New Theories

To add a new theory to the framework:

1. Create a new directory under `src/model_checker/theory_lib/`
2. Implement the required files (semantic.py, operators.py, examples.py)
3. Add test files in a `test/` subdirectory
4. Add your theory name to the `AVAILABLE_THEORIES` list in `theory_lib/__init__.py`:

```python
# In theory_lib/__init__.py
AVAILABLE_THEORIES = [
    'default',
    'exclusion',
    'imposition',
    'your_new_theory',  # Add your theory here
]
```

Once registered, your theory will be automatically discovered by the development scripts, tests will be run during CI/CD processes, and users will be able to access it with the `-l` flag.

## Jupyter Notebook Integration

The ModelChecker framework includes comprehensive Jupyter notebook integration, allowing interactive exploration of logical models and theories in a user-friendly environment.

### Overview

Jupyter notebooks provide an ideal environment for working with logical theories by combining:

- Interactive formula checking and evaluation
- Visual representation of models and countermodels
- Rich documentation with explanatory text and examples
- Experimental workflow for theory development and comparison

The `jupyter` package in ModelChecker offers both high-level functions for quick tasks and interactive components for deeper exploration:

```python
# Basic formula checking
from model_checker import check_formula
check_formula("p → (q → p)")

# Interactive exploration
from model_checker import ModelExplorer
explorer = ModelExplorer()
explorer.display()
```

### Key Features

- **Formula Checking**: Verify validity of formulas with optional premises
- **Countermodel Finding**: Search for models that falsify a formula
- **Interactive UI**: Customizable widgets for theory exploration
- **Visualization**: Both text and graph-based visualization options
- **Unicode Support**: Work directly with logical symbols (→, ∧, ∨, □, ◇, etc.)
- **Theory-Specific Extensions**: Adapters for different semantic theories
- **Example Libraries**: Access to pre-defined examples from theories

### Use Cases

1. **Theory Development**: Experiment with semantic theories interactively
2. **Teaching**: Create interactive demonstrations of logical concepts
3. **Research**: Explore relationships between different logical systems
4. **Documentation**: Create rich, interactive documentation for theories

For detailed information about the Jupyter integration, including installation, usage examples, and customization options, see the [Jupyter Integration Documentation](jupyter/README.md).
