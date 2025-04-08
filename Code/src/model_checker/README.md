# Model-Checker

TODO: expand

## Development

This section provides information for contributors who want to develop or extend the ModelChecker framework.

### Development Scripts

The repository includes several utility scripts that help with development, testing, and releasing:

#### 1. Running Tests (`run_tests.py`)

The `run_tests.py` script automatically discovers and runs tests for all registered theories in the framework. It uses the centralized `AVAILABLE_THEORIES` registry in `theory_lib/__init__.py` to determine which theories to test.

```bash
# Run tests for all registered theories
./run_tests.py

# Run tests for specific theories
./run_tests.py --theories default exclusion

# Run tests with verbose output
./run_tests.py -v

# List all registered theories
./run_tests.py --list
```

The script searches for test directories within each theory directory and runs pytest on them. It provides a summary of test results at the end.

#### 2. Package Updates (`update.py`)

The `update.py` script manages version updates, testing, building, and uploading to PyPI:

```bash
# Regular update (with prompts for testing)
./update.py

# Skip version increment but still run tests and upload
./update.py --no-version

# Skip the upload step (useful for testing the build process)
./update.py --no-upload
```

The script:
1. Updates version numbers in pyproject.toml and __init__.py
2. Runs tests for all registered theories (using run_tests.py)
3. Builds the package
4. Uploads to PyPI using twine

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
