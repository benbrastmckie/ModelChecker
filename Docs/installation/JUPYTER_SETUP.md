# Jupyter Setup Guide

[← Back to Installation](README.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md) | [Developer Setup →](DEVELOPER_SETUP.md)

## Overview

This guide covers setting up Jupyter notebooks for interactive ModelChecker development. Jupyter provides an excellent environment for exploring logical theories, visualizing models, and creating educational materials.

## Prerequisites

- ModelChecker installed (see [Basic Installation](BASIC_INSTALLATION.md))
- Python 3.8 or higher

## Installation

### Quick Install

Install ModelChecker with Jupyter support:

```bash
pip install model-checker[jupyter]
```

This includes:
- `jupyter` - Notebook server
- `ipywidgets` - Interactive widgets
- `notebook` - Classic interface
- Visualization dependencies

### Manual Installation

If you already have ModelChecker:

```bash
pip install jupyter ipywidgets
```

## Starting Jupyter

### Basic Launch

```bash
jupyter notebook
```

This opens Jupyter in your default browser.

### Using Project Scripts

If you cloned the repository:

```bash
cd ModelChecker/Code
./run_jupyter.sh
```

This script:
- Sets correct Python path
- Enables all extensions
- Opens in the right directory

## Enabling Widgets

Interactive widgets require activation:

### Classic Notebook

```bash
jupyter nbextension enable --py widgetsnbextension
```

### JupyterLab

```bash
jupyter labextension install @jupyter-widgets/jupyterlab-manager
```

### Verification

Test widgets are working:

```python
import ipywidgets as widgets
widgets.IntSlider(value=5, min=0, max=10)
```

## ModelChecker in Notebooks

### Basic Usage

```python
# Import ModelChecker
from model_checker import get_theory, iterate_models

# Load a theory
theory = get_theory('logos')

# Create and test formulas
premises = ["A", "(A \\rightarrow B)"]
conclusions = ["B"]

# Check validity
result = theory.check_validity(premises, conclusions)
```

### Interactive Exploration

```python
from model_checker.jupyter import ModelExplorer

# Create interactive model explorer
explorer = ModelExplorer(theory)
explorer.show()
```

### Available Notebooks

The repository includes example notebooks:

```
Code/src/model_checker/theory_lib/
├── logos/notebooks/      # Hyperintensional logic tutorials
├── exclusion/notebooks/  # Unilateral semantics examples
├── imposition/notebooks/ # Counterfactual reasoning
└── bimodal/notebooks/    # Temporal-modal logic
```

## Virtual Environments with Jupyter

### Adding Environment to Jupyter

1. Activate your virtual environment:
   ```bash
   source modelchecker-env/bin/activate  # Linux/macOS
   ```

2. Install ipykernel:
   ```bash
   pip install ipykernel
   ```

3. Add kernel to Jupyter:
   ```bash
   python -m ipykernel install --user --name=modelchecker --display-name="ModelChecker"
   ```

4. Launch Jupyter and select the "ModelChecker" kernel

### Managing Kernels

List available kernels:
```bash
jupyter kernelspec list
```

Remove a kernel:
```bash
jupyter kernelspec uninstall modelchecker
```

## Configuration

### Jupyter Config

Create config file:
```bash
jupyter notebook --generate-config
```

Common settings (`~/.jupyter/jupyter_notebook_config.py`):
```python
# Default directory
c.NotebookApp.notebook_dir = '/path/to/projects'

# Disable token authentication (local use only)
c.NotebookApp.token = ''

# Auto-reload modules
c.InteractiveShellApp.extensions = ['autoreload']
c.InteractiveShellApp.exec_lines = ['%autoreload 2']
```

### Notebook Extensions

Install useful extensions:
```bash
pip install jupyter_contrib_nbextensions
jupyter contrib nbextension install --user
```

Recommended extensions:
- Table of Contents
- Variable Inspector
- Code Folding
- Execute Time

## Troubleshooting

### Widgets not displaying

**Classic Notebook:**
```bash
jupyter nbextension enable --py widgetsnbextension --sys-prefix
```

**JupyterLab:**
```bash
jupyter labextension install @jupyter-widgets/jupyterlab-manager
jupyter lab build
```

### Kernel dies immediately

- Check ModelChecker installation: `pip show model-checker`
- Verify Python version matches
- Try creating new environment

### Import errors

```python
# Add to notebook
import sys
sys.path.append('/path/to/ModelChecker/Code/src')
```

### Performance issues

- Reduce model size (`N` parameter)
- Limit iteration count
- Use `%%time` magic to profile cells

## Best Practices

### Notebook Organization

```
my-logic-research/
├── notebooks/
│   ├── 01_introduction.ipynb
│   ├── 02_modal_logic.ipynb
│   └── 03_counterfactuals.ipynb
├── examples/
│   └── custom_theory.py
└── requirements.txt
```

### Clear Output Before Sharing

```bash
jupyter nbconvert --clear-output --inplace notebook.ipynb
```

### Version Control

Add to `.gitignore`:
```
.ipynb_checkpoints/
*/.ipynb_checkpoints/*
```

## Advanced Features

### Custom Widgets

Create interactive formula builders:

```python
from ipywidgets import interact

@interact(n=(2, 10), contingent=True, non_empty=True)
def explore_models(n, contingent, non_empty):
    settings = {'N': n, 'contingent': contingent, 'non_empty': non_empty}
    # Run model checker with settings
```

### Visualization

```python
from model_checker.visualization import draw_model

# Visualize countermodels
if model:
    draw_model(model)
```

## Next Steps

- **Explore examples**: Check theory-specific notebooks
- **Getting started**: Follow [Getting Started Guide](../GETTING_STARTED.md)
- **Development**: See [Developer Setup](DEVELOPER_SETUP.md)

---

[← Back to Installation](README.md) | [Virtual Environments →](VIRTUAL_ENVIRONMENTS.md) | [Developer Setup →](DEVELOPER_SETUP.md)