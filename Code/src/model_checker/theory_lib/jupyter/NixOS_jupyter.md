# Using ModelChecker with Jupyter in NixOS

This guide provides detailed instructions for setting up and using the ModelChecker package with Jupyter notebooks in NixOS.

## Introduction

NixOS has a different approach to package management compared to other Linux distributions. Since the typical `pip install -e .` approach doesn't work well in NixOS's immutable environment, we've created a symlink-based workflow to make development with Jupyter more convenient.

## Quick Start

The simplest way to use ModelChecker with Jupyter notebooks in NixOS is:

1. Clone the repository:
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   ```

2. Run the provided script:
   ```bash
   ./run_jupyter.sh
   ```

This will:
- Enter a nix-shell with all needed dependencies
- Create symlinks to make model_checker importable in Python
- Launch Jupyter notebook
- Create an example notebook demonstrating the key features

## Manual Setup

If you prefer to set up things manually or need more control, follow these steps:

### 1. Enter the nix-shell

The repository includes a `shell.nix` file with the minimal dependencies required:

```bash
cd /path/to/ModelChecker/Code
nix-shell
```

### 2. Set up the Python path

Run the jupyter_link.py script to create symlinks:

```bash
./jupyter_link.py
```

### 3. Start Jupyter

Once inside the nix-shell with the symlinks set up:

```bash
jupyter notebook
```

### 4. Create a new notebook or open an existing one

You can now create a new notebook or use the provided example notebook that demonstrates the key features.

## Development Workflow

When working on ModelChecker with Jupyter notebooks:

1. Make changes to your ModelChecker code
2. The changes are automatically available in Jupyter, thanks to the symlinks
3. No need to run `pip install -e .` or restart the kernel after code changes

## Using ModelChecker in Jupyter Notebooks

### Basic Imports

To use ModelChecker in your notebooks:

```python
# Import the package
import model_checker

# Import the interactive tools
from model_checker.jupyter import check_formula, InteractiveModelExplorer
```

### Formula Checking

Use the `check_formula` function for simple formula checking:

```python
# Check a simple formula
check_formula("(A \\equiv A)")

# Check a more complex formula with custom settings
check_formula(
    "□(p → q) → (□p → □q)",
    theory_name="default",
    premises=["p"],
    settings={'N': 4, 'max_time': 10}
)
```

### Interactive Explorer

For more interactive exploration:

```python
# Create an interactive explorer
explorer = InteractiveModelExplorer()

# Display the interactive UI
explorer.display()
```

The interactive explorer provides UI controls for:
- Formula input
- Premises input
- Theory selection
- Model settings
- Finding alternative models
- Visualization options

## Troubleshooting

### Common Issues

1. **"No module named 'model_checker'"**
   - Run `./jupyter_link.py` again to recreate the symlinks
   - Make sure you're running Jupyter from the nix-shell

2. **Missing dependencies**
   - Make sure you're in the nix-shell when running Jupyter
   - Check that the shell.nix file includes all necessary packages

3. **Jupyter widgets not displaying**
   - Run `jupyter nbextension enable --py widgetsnbextension --sys-prefix` in the nix-shell
   - Ensure that ipywidgets is in the shell.nix buildInputs

4. **Changes to code not reflected in Jupyter**
   - Try restarting the kernel (Kernel → Restart)
   - Run `import importlib; importlib.reload(model_checker)` in a notebook cell

### File Paths

If you move your notebooks out of the ModelChecker directory, you'll need to adjust the setup. Either:

1. Run `jupyter_link.py` from the ModelChecker/Code directory before starting Jupyter
2. Use a notebook with a first cell that modifies sys.path to include the ModelChecker code

## Advanced Usage

### Testing New Features

To test new features you're developing:

1. Make changes to the ModelChecker source code
2. Use Jupyter notebooks to interactively test these changes
3. Document your findings in the notebooks
4. When satisfied, write proper unit tests in the test/ directory

### Multiple Theory Support

To compare different semantic theories:

```python
# Check a formula in different theories
check_formula("□p → p", theory_name="default")
check_formula("□p → p", theory_name="exclusion")
```

### Exporting Results

You can export your notebooks and results:

```bash
# Convert to HTML
jupyter nbconvert --to html your_notebook.ipynb

# Convert to PDF (requires LaTeX)
jupyter nbconvert --to pdf your_notebook.ipynb
```

## Contributing

If you improve the Jupyter integration:

1. Update this documentation with any new features
2. Test your changes on both NixOS and other operating systems
3. Submit your changes via a pull request