# ModelChecker Debugging Tools

This directory contains tools and resources for debugging the ModelChecker framework, especially the Jupyter integration.

## Contents

### Diagnostic Scripts

- **jupyter_test.py**: A comprehensive diagnostic script that checks your environment, Python path, and ModelChecker installation.
  ```bash
  python jupyter_test.py
  ```

- **debug_notebook.py**: A script that tests specific components of the Jupyter integration separately.
  ```bash
  python debug_notebook.py
  ```

### Test Notebooks

- **simple_test.ipynb**: A minimal Jupyter notebook for isolating issues with ModelChecker's Jupyter integration.
  ```bash
  jupyter notebook simple_test.ipynb
  ```

- **demo_notebook_fixed.ipynb**: An enhanced version of the standard demo notebook with robust error handling and diagnostics.
  ```bash
  jupyter notebook demo_notebook_fixed.ipynb
  ```

## Usage

These tools are designed to help you identify and fix issues with the ModelChecker Jupyter integration. They are particularly useful in the following situations:

1. **Environment Issues**: If you're having trouble importing ModelChecker in Jupyter, run `jupyter_test.py` to diagnose path and import problems.

2. **Component Failures**: If specific features aren't working, use `debug_notebook.py` to test components individually.

3. **Interactive Testing**: Use `simple_test.ipynb` to test basic functionality in a clean notebook environment.

4. **Advanced Debugging**: Use `demo_notebook_fixed.ipynb` for a complete walkthrough with robust error handling.

## Documentation

For more detailed debugging information, see:

- `/src/model_checker/jupyter/debug/DEBUGGING.md`: Comprehensive debugging workflow
- `/src/model_checker/jupyter/TROUBLESHOOTING.md`: Common issues and solutions
- `/src/model_checker/jupyter/NixOS_jupyter.md`: NixOS-specific guidance

## For Developers

When adding new features to ModelChecker, especially to the Jupyter integration, consider adding appropriate tests to these debugging tools to ensure compatibility and robustness.
