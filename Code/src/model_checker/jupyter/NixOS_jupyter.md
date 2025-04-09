# Using ModelChecker with Jupyter on NixOS

This guide provides detailed instructions for setting up and using the ModelChecker Jupyter integration on NixOS, which requires special configuration due to the immutable nature of the Nix package manager.

## NixOS Setup Guide

### 1. Set Up Development Environment

First, clone the repository and enter the development environment:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter the nix-shell environment
nix-shell
```

The `nix-shell` command will create an isolated environment with all necessary dependencies based on the `shell.nix` file.

### 2. Set Up Python Path

NixOS doesn't allow modifying installed packages, so we need to set up the Python path correctly to use the local version of ModelChecker:

```bash
# Inside the nix-shell
export PYTHONPATH="$PWD:$PWD/src:$PYTHONPATH"
```

To make this persistent for your Jupyter sessions, we recommend creating a helper script:

```bash
# Create a script to launch Jupyter with the correct path
cat > run_jupyter.sh << 'EOF'
#!/usr/bin/env bash
export PYTHONPATH="$PWD:$PWD/src:$PYTHONPATH"
jupyter notebook "$@"
EOF

# Make it executable
chmod +x run_jupyter.sh
```

### 3. Launch Jupyter Notebook

Now you can launch Jupyter Notebook with the correct paths:

```bash
# Use the helper script
./run_jupyter.sh
```

This will open Jupyter in your browser with ModelChecker available for import.

## Alternative Setup Methods

### Using Symlinks (Advanced)

For a more permanent solution, you can create symlinks in your Python site-packages directory:

```bash
# Create a symlink script
cat > jupyter_link.py << 'EOF'
#!/usr/bin/env python3
import site
import os
import sys

def create_symlinks():
    """Create symlinks to the local ModelChecker in the site-packages directory."""
    site_packages = site.getsitepackages()[0]
    current_dir = os.path.abspath(os.path.dirname(__file__))
    src_dir = os.path.join(current_dir, 'src')
    
    # Create symlink for the package
    target = os.path.join(site_packages, 'model_checker')
    source = os.path.join(src_dir, 'model_checker')
    
    if os.path.exists(target):
        if os.path.islink(target):
            os.unlink(target)
        else:
            print(f"Error: {target} exists but is not a symlink")
            return False
    
    os.symlink(source, target)
    print(f"Created symlink: {source} -> {target}")
    
    return True

if __name__ == "__main__":
    if create_symlinks():
        print("Symlinks created successfully!")
        
        # Launch Jupyter if requested
        if "--launch" in sys.argv:
            os.system("jupyter notebook")
    else:
        print("Failed to create symlinks")
EOF

# Make it executable
chmod +x jupyter_link.py

# Run it
python jupyter_link.py
```

### Using direnv (Recommended)

If you use `direnv`, you can automate environment setup:

1. Install direnv through Nix if you haven't already:
   ```nix
   # In your configuration.nix
   environment.systemPackages = with pkgs; [
     direnv
   ];
   ```

2. Add this to a `.envrc` file in your ModelChecker directory:
   ```bash
   use_nix
   export PYTHONPATH=$PWD:$PWD/src:$PYTHONPATH
   ```

3. Allow the direnv configuration:
   ```bash
   direnv allow
   ```

Now whenever you enter the directory, the environment will be automatically set up.

## Troubleshooting NixOS Specific Issues

### Missing Dependencies

If you encounter dependency issues despite using nix-shell, try:

```bash
# Inside nix-shell
pip install --user ipywidgets matplotlib networkx
```

### Jupyter Extension Issues

If ipywidgets aren't displaying properly, you may need to enable the extension:

```bash
# Inside nix-shell
jupyter nbextension install --py widgetsnbextension --user
jupyter nbextension enable --py widgetsnbextension --user
```

### Python Path Issues

If you're still having import issues, check your Python path:

```python
import sys
print(sys.path)
```

Ensure that both the `ModelChecker/Code` and `ModelChecker/Code/src` directories are in the path.

You can manually add them in your notebook if needed:

```python
import sys
import os

# Add paths to the ModelChecker source
current_dir = os.getcwd()
possible_roots = [
    os.path.abspath(os.path.join(current_dir, "../..")),
    os.path.abspath(os.path.join(current_dir, "../../..")),
    "/home/username/ModelChecker/Code",  # Replace with your actual path
]

for path in possible_roots:
    if os.path.exists(os.path.join(path, "src", "model_checker")):
        sys.path.insert(0, path)
        sys.path.insert(0, os.path.join(path, "src"))
        print(f"Added ModelChecker paths: {path} and {os.path.join(path, 'src')}")
        break
```

### Using the Environment Module

The Jupyter integration includes an environment module to help with setup:

```python
from model_checker.jupyter.environment import setup_environment, get_diagnostic_info

# Set up environment
env_info = setup_environment()
print(env_info)

# Get detailed diagnostic information
diag_info = get_diagnostic_info()
print(diag_info)
```

## Example Notebook for NixOS

Here's a minimal example to verify your NixOS setup is working:

```python
# Verify imports work
import model_checker
from model_checker.jupyter import check_formula
from model_checker.jupyter.environment import get_diagnostic_info

# Print diagnostics
print(get_diagnostic_info())

# Check a simple formula
check_formula("p → q")

# If this works, your setup is complete!
```

## Running the Included Demo Notebook

The ModelChecker Jupyter integration includes a demo notebook that showcases all features:

```bash
# Inside nix-shell, with the correct PYTHONPATH
cd src/model_checker/jupyter
jupyter notebook demo_notebook.ipynb
```

This notebook demonstrates all the features of the integration and serves as a good starting point for your own notebooks.