# Using ModelChecker with Jupyter in NixOS

This guide provides detailed instructions for setting up and using the ModelChecker package with Jupyter notebooks in NixOS.

## Introduction

NixOS has a different approach to package management compared to other Linux distributions. Since the typical `pip install -e .` approach doesn't work well in NixOS's immutable environment, we need to use Nix-specific tools and approaches.

## 1. Basic Requirements

To use ModelChecker with Jupyter notebooks, you need:

1. Python 3.8 or later
2. ModelChecker package available on the Python path
3. Jupyter and supporting libraries (ipywidgets, matplotlib, networkx)
4. Z3 theorem prover

## 2. Setup Instructions

### 2.1 Using the provided `shell.nix`

The ModelChecker repository includes a `shell.nix` file pre-configured with all the necessary dependencies for running ModelChecker with Jupyter notebooks.

#### Step 1: Enter the development shell

Navigate to the ModelChecker Code directory and enter the Nix shell:

```bash
cd /path/to/ModelChecker/Code
nix-shell
```

This will create a development environment with Python, Z3, Jupyter, and all the required dependencies.

#### Step 2: Start Jupyter Notebook

Once inside the Nix shell, you can start the Jupyter notebook server:

```bash
jupyter notebook
```

This will open a web browser with the Jupyter file explorer. Navigate to the example notebooks in one of these directories:
- `src/model_checker/theory_lib/jupyter/jupyter_demo.ipynb`
- `src/model_checker/theory_lib/exclusion/notebooks/exclusion_demo.ipynb`

### 2.2 Customizing `shell.nix` (if needed)

If you need to customize the environment, you can modify the `shell.nix` file:

```nix
{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    python3
    python3Packages.z3
    python3Packages.pytest
    python3Packages.jupyter
    python3Packages.notebook
    python3Packages.ipywidgets
    python3Packages.matplotlib
    python3Packages.networkx
    python3Packages.pip
    python3Packages.setuptools
    python3Packages.wheel
    # Add any other packages you need here
  ];
  
  shellHook = ''
    # Set up local development environment
    export PYTHONPATH="$PWD:$PWD/src:$PYTHONPATH"
    export PATH="$PWD:$PATH"
    
    # Make dev_cli.py executable
    chmod +x $PWD/dev_cli.py
    
    # Create symlink for notebook import (optional, helps in some environments)
    mkdir -p $HOME/.local/lib/python3.*/site-packages/model_checker
    ln -sf $PWD/src/model_checker/* $HOME/.local/lib/python3.*/site-packages/model_checker/ 2>/dev/null
    
    echo "ModelChecker development environment activated"
    echo "Run './dev_cli.py example.py' to use local source code"
    echo "Run 'jupyter notebook' to start Jupyter with model_checker available"
  '';
}
```

### 2.3 Using Home Manager

If you use Home Manager, you can add these packages to your configuration:

```nix
home.packages = with pkgs.python3Packages; [
  jupyter
  notebook
  ipywidgets
  matplotlib
  networkx
  z3
];
```

Then set up the environment in your Jupyter notebook using the first cell shown in the "Using ModelChecker in Jupyter Notebooks" section below.

### 2.4 Creating a Temporary Environment

You can create a temporary environment without modifying `shell.nix`:

```bash
nix-shell -p "python3.withPackages(ps: with ps; [ jupyter notebook ipywidgets matplotlib networkx z3 ])"
```

Then adjust your PYTHONPATH manually in the notebook:

```python
import sys
sys.path.insert(0, "/path/to/ModelChecker/Code")
sys.path.insert(0, "/path/to/ModelChecker/Code/src")
```

## 3. Using ModelChecker in Jupyter Notebooks

### First Cell Setup

Every notebook that uses ModelChecker should start with a setup cell to ensure the environment is properly configured:

```python
# Set up the environment for the model_checker package
import sys
import os
import importlib

# Helper function to setup imports
def setup_model_checker_env():
    # Try to find the ModelChecker project root
    possible_roots = [
        # If notebook is in the repo structure
        os.path.abspath(os.path.join(os.getcwd(), "../../../../../")),
        os.path.abspath(os.path.join(os.getcwd(), "../../../../")),
        os.path.abspath(os.path.join(os.getcwd(), "../../../")),
        os.path.abspath(os.path.join(os.getcwd(), "../../")),
        # Common installation paths
        os.path.expanduser("~/Documents/Philosophy/Projects/ModelChecker/Code"),
        os.path.expanduser("~/ModelChecker/Code"),
    ]
    
    project_root = None
    for path in possible_roots:
        if os.path.isdir(path) and os.path.isdir(os.path.join(path, "src", "model_checker")):
            project_root = path
            break
    
    if project_root is None:
        print("Could not find ModelChecker project root. Please specify the path manually.")
        return False
    
    # Add project root and src directory to path
    paths_to_add = [project_root, os.path.join(project_root, "src")]
    for path in paths_to_add:
        if path not in sys.path:
            sys.path.insert(0, path)
    
    # Try importing model_checker
    try:
        # If already imported, reload to ensure we're using the correct version
        if "model_checker" in sys.modules:
            importlib.reload(sys.modules["model_checker"])
        else:
            import model_checker
        
        print(f"Imported model_checker from {sys.modules['model_checker'].__file__}")
        return True
    except ImportError as e:
        print(f"Error importing model_checker: {e}")
        return False

# Run the setup
setup_success = setup_model_checker_env()

# Diagnostic information
if setup_success:
    import model_checker
    print(f"ModelChecker version: {model_checker.__version__}")
    print(f"ModelChecker location: {model_checker.__file__}")
else:
    print("Failed to set up ModelChecker environment")
```

### Importing ModelChecker

After the setup cell, you can import ModelChecker components:

```python
from model_checker.jupyter import InteractiveModelExplorer, check_formula
```

### Example: Checking a Formula

```python
# Check a simple propositional formula
check_formula("p → (q → p)")

# Check a modal formula
check_formula("□(p → q) → (□p → □q)")
```

### Example: Using the Interactive Explorer

```python
# Create an explorer with the default theory
explorer = InteractiveModelExplorer()

# Display the interactive UI
explorer.display()
```

## 4. Working with Different Theories

ModelChecker supports various logical theories. You can specify which theory to use:

```python
# Check in default theory
check_formula("□p → p", theory_name="default")

# Check in exclusion theory
check_formula("□p → p", theory_name="exclusion")
```

## 5. Customizing Settings

You can customize model settings:

```python
custom_settings = {
    'N': 4,              # Number of atomic propositions
    'max_time': 10,      # Maximum solving time in seconds
    'contingent': True,  # Use contingent valuations
    'non_empty': True,   # Ensure non-empty valuations
}

check_formula("p ∨ q ∨ r ∨ s", settings=custom_settings)
```

## 6. Troubleshooting

### Common Issues and Solutions

1. **Module Not Found Error**
   
   If you see `ModuleNotFoundError: No module named 'model_checker'`, check:
   - Are you running Jupyter from within the nix-shell?
   - Did the first setup cell run correctly?
   - Check the PYTHONPATH with `print(sys.path)` to ensure the ModelChecker paths are included

2. **Missing Dependencies**
   
   If you see errors about missing packages:
   - Update your shell.nix to include the required packages
   - Re-enter the nix-shell

3. **Old Module Version Used**
   
   If changes to your code aren't reflected:
   - Call `importlib.reload(model_checker)` to reload the module
   - Restart the Jupyter kernel (Kernel → Restart)

4. **Jupyter Widget Issues**
   
   If widgets aren't displaying:
   - Ensure ipywidgets is properly installed in your nix-shell
   - Try running `jupyter nbextension enable --py widgetsnbextension`

### Getting Help

For more help:
1. Check the ModelChecker [GitHub issues](https://github.com/benbrastmckie/ModelChecker/issues)
2. Consult the [Jupyter documentation](https://jupyter.org/documentation)
3. For NixOS-specific issues, check the [NixOS Wiki](https://nixos.wiki/wiki/Python)