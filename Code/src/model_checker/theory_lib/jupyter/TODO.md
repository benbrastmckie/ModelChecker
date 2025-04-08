# Jupyter Note Book Integration

Other relevant files to consult in the repository:
- `theory_lib/jupyter/README_jupyter.md` documents the current jupyter notebook integration

## TODOs

- revise `theory_lib/jupyter/jupyter_demo.ipynb` as needed to get its cells to run, looking at the `exclusion/examples.py` module for inspiration
- test `jupyter_demo.ipynb`, confirming that all cells are up and running
- adapt `theory_lib/exclusion/notebooks/exclusion_demo.ipynb` to work with the current integration of Jupyter notebooks used in the model-checker as described in `theory_lib/jupyter/README_jupyter.md`
- test `exclusion_demo.ipynb` confirming that all cells are running

## Issues

> Current problems to be solved to get `jupyter_demo.ipynb` and `exclusion_demo.ipynb`

### Importing Problems in `jupyter_demo.ipynb`

I have `jupyter_demo.ipynb` running. Here is the first cell:

```
from model_checker.notebook import InteractiveModelExplorer, check_formula
```

I'm getting the following error upon running the cell:

```
---------------------------------------------------------------------------
ModuleNotFoundError                       Traceback (most recent call last)
Cell In[1], line 1
----> 1 from model_checker.notebook import InteractiveModelExplorer, check_formula

ModuleNotFoundError: No module named 'model_checker.notebook'
```

### Importing Problems in `exclusion_demo.ipynb`

I have `exclusion_demo.ipynb` running. Here is the first cell:

```
import model_checker as mc
from model_checker.theory_lib import exclusion
# from model_checker import exxclusion
```

I'm getting the following error upon running the cell:

```
---------------------------------------------------------------------------
ModuleNotFoundError                       Traceback (most recent call last)
Cell In[1], line 2
      1 import model_checker as mc
----> 2 from model_checker.theory_lib import exclusion
      3 # from model_checker import exxclusion

ModuleNotFoundError: No module named 'model_checker.theory_lib'
```

## Implementation Plan (NixOS Environment)

### 1. Python Path Solution for NixOS Using a NixOS Development Shell

Since NixOS restricts traditional installation methods like `pip install -e .`, we need to modify the Python path directly to include our development code:

1. **Modify your shell.nix file** to include the development package:
   ```nix
   { pkgs ? import <nixpkgs> {} }:

   pkgs.mkShell {
     buildInputs = with pkgs; [
       python3
       python3Packages.ipykernel
       python3Packages.jupyter
       python3Packages.ipywidgets
       python3Packages.matplotlib
       python3Packages.networkx
       python3Packages.z3
     ];
     
     shellHook = ''
       export PYTHONPATH="$PWD/Code:$PYTHONPATH"
       export JUPYTER_PATH="$PWD/.jupyter:$JUPYTER_PATH"
     '';
   }
   ```

2. **Restart your development shell** and launch Jupyter from there

### 2. Fix Package Import Structure

Since we're using the development code directly (not the installed package), we need to ensure proper imports:

1. **Update `__init__.py`**:
   Ensure `notebook.py` is properly imported in the package:

   ```python
   # Add to __all__
   __all__ = [
       "model", "syntactic", "notebook",  # modules
       # ... existing entries
       "InteractiveModelExplorer", "check_formula", "check_formula_interactive"  # From notebook.py
   ]

   # Add explicit import
   from .notebook import InteractiveModelExplorer, check_formula, check_formula_interactive
   ```

2. **Fix any circular imports**:
   Make sure there are no circular imports that could prevent the modules from loading correctly.

### 3. Update Notebook Contents

1. **Modify `jupyter_demo.ipynb`**:
   - Add the sys.path modification at the top
   - Update import statements to match current package structure
   - Ensure example code matches current API

2. **Fix `exclusion_demo.ipynb`**:
   - Add the sys.path modification at the top
   - Update imports to use the current module structure
   - Fix any deprecated function calls or API changes

### 4. Specific Code Changes for Notebooks

1. **Add to the top of both notebooks**:
   ```python
   # Add project root to Python path
   import sys
   import os
   project_root = '/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code'
   if project_root not in sys.path:
       sys.path.insert(0, project_root)
   ```

2. **Update import statements in `jupyter_demo.ipynb`**:
   ```python
   # Original imports
   # from model_checker.notebook import InteractiveModelExplorer, check_formula
   
   # New imports
   from model_checker.notebook import InteractiveModelExplorer, check_formula
   # If above fails, try direct import:
   # import model_checker.notebook as nb
   # InteractiveModelExplorer = nb.InteractiveModelExplorer
   # check_formula = nb.check_formula
   ```

3. **Update import statements in `exclusion_demo.ipynb`**:
   ```python
   # Original imports
   # import model_checker as mc
   # from model_checker.theory_lib import exclusion
   
   # New imports with sys.path modification
   import model_checker as mc
   from model_checker.theory_lib import exclusion
   ```

### 5. Testing Workflow for NixOS

1. **Launch Jupyter within the proper environment**:
   ```bash
   cd /home/benjamin/Documents/Philosophy/Projects/ModelChecker
   # Either use nix-shell or direnv if configured
   jupyter notebook
   ```

2. **Check Python path in notebook**:
   Add a diagnostic cell to verify the Python path includes the project directory:
   ```python
   import sys
   print(sys.path)
   ```

3. **Test module imports**:
   ```python
   import model_checker
   print("Model checker version:", model_checker.__version__)
   print("Available modules:", dir(model_checker))
   ```

### 6. Troubleshooting Common NixOS Issues

1. **Module not found despite path modification**:
   - Check for `__pycache__` directories that might contain stale compiled code
   - Try `import importlib; importlib.reload(model_checker)` after path changes

2. **Permission issues**:
   - Ensure the notebook has proper file access permissions

3. **Version conflicts**:
   - Check if multiple versions are available on the path using:
   ```python
   import model_checker
   print(model_checker.__file__)
   ```

### Implementation Timeline

1. **Phase 1 (Environment Setup - Day 1)**:
   - Set up PYTHONPATH correctly for Jupyter
   - Update __init__.py to properly expose notebook module

2. **Phase 2 (Notebook Updates - Day 2)**:
   - Update both notebooks with sys.path modifications
   - Fix import statements and API usage

3. **Phase 3 (Testing - Day 3)**:
   - Test both notebooks from a clean Jupyter session
   - Address any remaining import issues

### Conclusion

The main issue appears to be a Python path configuration problem. By modifying the Python path to include our development code directly, rather than relying on package installation, we should be able to get the Jupyter integration working correctly in NixOS. This approach avoids the need to modify read-only directories in the Nix store.
