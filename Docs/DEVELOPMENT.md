# ModelChecker Development Guide

This guide provides comprehensive instructions for developing and contributing to the ModelChecker project, whether you're using pip or NixOS.

## Table of Contents

- [Setting Up Development Environment](#setting-up-development-environment)
  - [Standard Setup (pip)](#standard-setup-pip)
  - [NixOS Setup](#nixos-setup)
- [Development Workflow](#development-workflow)
  - [Running Tests](#running-tests)
  - [Using the Development CLI](#using-the-development-cli)
  - [Working with Jupyter Integration](#working-with-jupyter-integration)
- [GitHub Workflow and Pull Requests](#github-workflow-and-pull-requests)
- [Common Development Tasks](#common-development-tasks)
  - [Adding Dependencies](#adding-dependencies)
  - [Adding a New Theory](#adding-a-new-theory)
- [Documentation Guide](#documentation-guide)

## Setting Up Development Environment

### Standard Setup (pip)

Follow these instructions for macOS, Windows, and non-NixOS Linux:

1. **Clone the repository**:
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   ```

2. **Create a virtual environment** (recommended):
   ```bash
   python -m venv venv
   # On Windows:
   venv\Scripts\activate
   # On macOS/Linux:
   source venv/bin/activate
   ```

3. **Install in development mode**:
   ```bash
   pip install -e .
   ```

4. **Install development dependencies**:
   ```bash
   pip install -e ".[dev]"
   ```

5. **Install Jupyter dependencies** (optional, for notebook work):
   ```bash
   pip install -e ".[jupyter]"
   ```

6. **Verify the installation**:
   ```bash
   python test_package.py
   python test_theories.py
   ```

### NixOS Setup

NixOS requires special handling due to its immutable package management:

1. **Clone the repository**:
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   ```

2. **Enter the development shell**:
   ```bash
   nix-shell
   ```
   
   The provided `shell.nix` file sets up the correct environment automatically, including:
   - Setting PYTHONPATH to include local source code
   - Installing required dependencies (z3-solver, networkx, etc.)
   - Making development scripts executable

3. **For automatic environment activation** (optional):
   ```bash
   # Install direnv if you haven't already
   nix-env -i direnv
   
   # Allow the .envrc file once
   direnv allow
   
   # Now the environment will activate automatically when you enter the directory
   ```

## Development Workflow

### Running Tests

Always run tests to ensure your changes don't break existing functionality:

1. **Testing all theories**:
   ```bash
   # Test all registered theories
   python test_theories.py
   
   # Test specific theories
   python test_theories.py --theories default bimodal
   
   # Verbose output
   python test_theories.py -v
   
   # Stop at first failure
   python test_theories.py -x
   ```

2. **Testing non-theory components**:
   ```bash
   # Test all package components
   python test_package.py
   
   # Test specific components
   python test_package.py --components builder settings
   
   # List available testable components
   python test_package.py --list
   ```

### Using the Development CLI

The development CLI allows testing without relying on installed packages:

```bash
# Run with an example file
./dev_cli.py path/to/examples.py

# Show constraints
./dev_cli.py -p path/to/examples.py

# Show Z3 output
./dev_cli.py -z path/to/examples.py

# Combine flags
./dev_cli.py -p -z path/to/examples.py
```

### Working with Jupyter Integration

For interactive development with Jupyter notebooks:

1. **Launch Jupyter with ModelChecker support**:
   ```bash
   # Using the provided script
   ./run_jupyter.sh
   
   # Or manually
   jupyter notebook
   ```

2. **Fix missing dependency errors** (like networkx):
   ```bash
   # For pip installations
   pip install networkx
   
   # For NixOS, networkx is already included in shell.nix
   ```

3. **Launch specific theory notebooks**:
   ```bash
   jupyter notebook src/model_checker/theory_lib/default/notebooks/default_demo.ipynb
   ```

## GitHub Workflow and Pull Requests

To contribute changes back to the ModelChecker project:

1. **Fork the repository** on GitHub.

2. **Create a feature branch**:
   ```bash
   git checkout -b feature/my-new-feature
   ```

3. **Make your changes**, ensuring:
   - All tests pass
   - Documentation is updated
   - Code follows project conventions

4. **Commit your changes**:
   ```bash
   git add .
   git commit -m "Add my new feature"
   ```

5. **Push to your fork**:
   ```bash
   git push origin feature/my-new-feature
   ```

6. **Create a pull request**:
   - Go to the [ModelChecker repository](https://github.com/benbrastmckie/ModelChecker)
   - Click "New pull request"
   - Select "compare across forks"
   - Choose your fork and branch
   - Fill in the PR template with details about your changes
   - Submit the PR

7. **Respond to feedback** from maintainers during code review.

## Common Development Tasks

### Adding Dependencies

If your changes require new dependencies:

1. **Add to `pyproject.toml`**:
   ```toml
   # Core dependencies
   dependencies = [
       "z3-solver>=4.8.0",
       "networkx>=2.0",
       "your-new-dependency>=1.0.0",
   ]
   
   # Or as an optional dependency
   [project.optional-dependencies]
   jupyter = [
       "ipywidgets>=7.0.0",
       "your-optional-dependency>=2.0.0",
   ]
   ```

2. **Update `shell.nix`** for NixOS developers:
   ```nix
   buildInputs = with pkgs; [
     python3
     python3Packages.z3
     python3Packages.setuptools
     python3Packages.pip
     python3Packages.networkx
     python3Packages.your-new-dependency
   ];
   ```

3. **Document the dependency** in relevant README files.

### Adding a New Theory

To add a new semantic theory to the framework:

1. **Create the theory directory structure**:
   ```
   src/model_checker/theory_lib/your_theory/
   ├── __init__.py
   ├── semantic.py
   ├── operators.py
   ├── examples.py
   ├── README.md
   └── test/
       └── test_your_theory.py
   ```

2. **Implement required components** following the architecture in [Theory Library Documentation](../theory_lib/README.md).

3. **Register the theory** in `theory_lib/__init__.py`:
   ```python
   AVAILABLE_THEORIES = [
       'default',
       'exclusion',
       'imposition',
       'your_theory',  # Add your theory here
   ]
   ```

4. **Write tests** in the `test/` directory.

5. **Create example notebooks** in a `notebooks/` directory (optional but recommended).

## Documentation Guide

The ModelChecker project uses several key documentation files:

- [**ModelChecker README**](../README.md): Main architecture and API overview
- [**Theory Library Documentation**](../theory_lib/README.md): Theory implementation guide and standards
- [**Settings Documentation**](../settings/README.md): Settings management system
- [**Jupyter Integration**](../jupyter/README.md): Interactive notebook features

When updating documentation:

1. Keep cross-references between documents updated
2. Add examples for new features
3. Update tables of contents when adding sections
4. Include code examples for API changes

## Z3 Solver State Management

The ModelChecker uses Z3 solver for constraint solving. Proper management of Z3 solver state is critical for ensuring that examples run independently and don't affect each other's results or performance.

### Key Considerations

1. **Z3 Context Isolation**: The most critical aspect of Z3 solver state management is resetting the Z3 context between examples:
   ```python
   # CRITICAL: Reset Z3 context between examples to prevent state leakage
   import z3
   if hasattr(z3, '_main_ctx'):
       z3._main_ctx = None
   import gc
   gc.collect()
   ```
   
   Without this step, examples can interfere with each other, causing timeouts or incorrect results.

2. **Resource Cleanup**: Z3 solver resources should be properly cleaned up after each example run:
   ```python
   # Always clean up Z3 resources when done
   solver = None
   model = None
   import gc
   gc.collect()
   ```

3. **Theory-specific Caches**: Semantic theories should implement `_reset_global_state()` to clear any caches:
   ```python
   def _reset_global_state(self):
       super()._reset_global_state()  # Call parent implementation
       self._theory_specific_cache = {}  # Reset any caches
   ```

4. **Model Structure Initialization**: When implementing a custom ModelStructure, ensure proper garbage collection:
   ```python
   def __init__(self, model_constraints, max_time):
       # Force garbage collection before initialization
       import gc
       gc.collect()
       
       # Initialize parent class
       super().__init__(model_constraints, max_time)
       
       # Your initialization code
       # ...
       
       # Force garbage collection again after initialization
       gc.collect()
   ```

5. **Example Isolation**: When running multiple examples, ensure each gets a fresh Z3 context:
   ```python
   for example_name, example_case in examples.items():
       # Reset Z3 context to create a fresh environment for this example
       import z3
       if hasattr(z3, '_main_ctx'):
           z3._main_ctx = None
       gc.collect()
       
       try:
           # Process the example with a fresh Z3 context
           process_example(example_name, example_case)
       finally:
           # Force cleanup
           gc.collect()
   ```

For a detailed implementation overview, see `theory_lib/notes/separation.md`.

---

For more detailed information, refer to:
- [ModelChecker API Documentation](../README.md)
- [Theory Library Documentation](../theory_lib/README.md)
