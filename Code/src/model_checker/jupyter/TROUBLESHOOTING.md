# Troubleshooting ModelChecker Jupyter Integration

This guide helps you solve common issues when using ModelChecker in Jupyter notebooks.

## Common Issues and Solutions

### Import Errors

**Issue**: `ImportError: No module named 'model_checker'` or similar errors when trying to import ModelChecker.

**Solutions**:

1. **Check your Python path**:
   ```python
   import sys
   print(sys.path)
   ```
   The path to ModelChecker should be in the list.

2. **Add paths manually**:
   ```python
   import sys
   import os
   
   # Adjust these paths to your ModelChecker installation
   project_root = "/path/to/ModelChecker/Code"
   sys.path.insert(0, project_root)
   sys.path.insert(0, os.path.join(project_root, "src"))
   ```

3. **Use the environment setup function**:
   ```python
   from model_checker.jupyter.environment import setup_environment
   env_info = setup_environment()
   print(env_info)
   ```

4. **For NixOS users**:
   - Make sure you're running the notebook from within a nix-shell
   - Use the `run_jupyter.sh` script provided in the repository

### Missing Dependencies

**Issue**: Errors related to missing packages like ipywidgets, matplotlib, or networkx.

**Solutions**:

1. **Install the required dependencies**:
   ```bash
   pip install ipywidgets matplotlib networkx
   ```

2. **Enable ipywidgets extension** (if widgets don't display):
   ```bash
   jupyter nbextension enable --py widgetsnbextension
   ```

3. **Check installed versions**:
   ```python
   import ipywidgets
   import matplotlib
   import networkx
   
   print(f"ipywidgets: {ipywidgets.__version__}")
   print(f"matplotlib: {matplotlib.__version__}")
   print(f"networkx: {networkx.__version__}")
   ```

### Theory-Specific Issues

**Issue**: Errors when trying to use a specific theory like `exclusion` or `imposition`.

**Solutions**:

1. **Check available theories**:
   ```python
   from model_checker.jupyter.environment import get_available_theories
   print(get_available_theories())
   ```

2. **Verify theory imports**:
   ```python
   # For example, with the 'exclusion' theory
   try:
       from model_checker.theory_lib import exclusion
       print("Exclusion theory is available")
   except ImportError as e:
       print(f"Error importing exclusion theory: {e}")
   ```

3. **Check theory registration**:
   Make sure the theory is properly registered in `theory_lib/__init__.py` in the `AVAILABLE_THEORIES` list.

### Widget Display Issues

**Issue**: Interactive widgets not displaying or not working properly.

**Solutions**:

1. **Check ipywidgets installation**:
   ```python
   import ipywidgets
   print(ipywidgets.__version__)
   ```

2. **Use a compatible Jupyter environment**:
   - JupyterLab or Jupyter Notebook with ipywidgets support
   - Try using a different browser if widgets aren't displaying

3. **Verify widget output**:
   ```python
   from IPython.display import display
   import ipywidgets as widgets
   
   # Try a simple widget
   w = widgets.Text(value='Hello World')
   display(w)
   ```

### Formula Checking Issues

**Issue**: Errors when checking formulas with `check_formula()`.

**Solutions**:

1. **Check formula syntax**:
   - Make sure operators are properly formatted
   - Use parentheses around binary operators
   - For LaTeX syntax, use double backslashes in strings

2. **Try Unicode notation**:
   ```python
   # Instead of
   check_formula("\\Box p \\rightarrow p")
   
   # Try Unicode
   check_formula("□p → p")
   ```

3. **Simplify the formula** to isolate the issue:
   ```python
   # Try a simple propositional formula first
   check_formula("p → q")
   ```

### NixOS-Specific Issues

**Issue**: Problems with Python path or package loading on NixOS.

**Solutions**:

1. **Use the nix-shell environment**:
   ```bash
   cd /path/to/ModelChecker/Code
   nix-shell
   jupyter notebook
   ```

2. **Use the provided helper scripts**:
   ```bash
   cd /path/to/ModelChecker/Code
   ./run_jupyter.sh
   ```

3. **Check paths in nix-shell**:
   ```bash
   nix-shell
   python -c "import sys; print(sys.path)"
   ```

## Diagnostic Tools

### Environment Diagnostic

```python
from model_checker.jupyter.environment import get_diagnostic_info

# Print all diagnostic information
diag_info = get_diagnostic_info()
print(diag_info)
```

### Import Test

```python
# Test if ModelChecker is properly importable
import importlib
import sys

def test_import(module_name):
    try:
        if module_name in sys.modules:
            # Force reload if already imported
            importlib.reload(sys.modules[module_name])
        else:
            importlib.import_module(module_name)
        print(f"✓ Successfully imported {module_name}")
        return True
    except Exception as e:
        print(f"✗ Failed to import {module_name}: {str(e)}")
        return False

# Test key modules
test_import("model_checker")
test_import("model_checker.jupyter")
test_import("ipywidgets")
```

### Widget Test

```python
# Test if ipywidgets are working
from IPython.display import display
import ipywidgets as widgets

# Create a simple button widget
button = widgets.Button(description="Test Button")
display(button)

# If the button displays, widgets are working
```

## Creating a Minimal Test Notebook

If you're having persistent issues, create a simple test notebook with just these cells:

```python
# Cell 1: Environment setup
import sys
import os

# Add ModelChecker to path - adjust paths as needed
project_root = "/path/to/ModelChecker/Code"
if os.path.exists(project_root):
    sys.path.insert(0, project_root)
    sys.path.insert(0, os.path.join(project_root, "src"))
    print(f"Added paths: {project_root} and {os.path.join(project_root, 'src')}")

# Print current path
print("\nCurrent Python path:")
for p in sys.path:
    print(f"  {p}")
```

```python
# Cell 2: Try importing ModelChecker
try:
    import model_checker
    print(f"✓ Successfully imported model_checker from {model_checker.__file__}")
    print(f"  Version: {model_checker.__version__}")
except Exception as e:
    print(f"✗ Error importing model_checker: {str(e)}")
    import traceback
    traceback.print_exc()
```

```python
# Cell 3: Try importing Jupyter integration
try:
    from model_checker.jupyter import check_formula
    print("✓ Successfully imported Jupyter integration")
    
    # Try checking a simple formula
    result = check_formula("p → q")
    # This should display a result
except Exception as e:
    print(f"✗ Error with Jupyter integration: {str(e)}")
    import traceback
    traceback.print_exc()
```

## Getting Help

If you're still experiencing issues:

1. Check the [Github Issues](https://github.com/benbrastmckie/ModelChecker/issues) for similar problems
2. Create a new issue with:
   - Python version (`python --version`)
   - ModelChecker version (`import model_checker; print(model_checker.__version__)`)
   - Operating system (Windows, MacOS, Linux, NixOS)
   - Exact error message and traceback
   - A minimal code example that reproduces the issue

For NixOS-specific help, see [NixOS_jupyter.md](NixOS_jupyter.md).