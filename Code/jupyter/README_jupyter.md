# ModelChecker Jupyter Integration

This document provides detailed instructions for using ModelChecker in Jupyter notebooks, including setup, installation, workflow, and usage examples.

## Installation Guide

### 1. Basic Requirements

To use ModelChecker with Jupyter notebooks, you need:

1. Python 3.8 or later
2. ModelChecker package installed
3. Jupyter and supporting libraries

### 2. Step-by-Step Installation

#### Install Jupyter and Required Libraries

```bash
# Install Jupyter Notebook
pip install jupyter notebook

# Install required dependencies for ModelChecker Jupyter integration
pip install ipywidgets matplotlib networkx
```

#### Verify Installation

After installation, verify that everything is installed correctly:

```bash
# Check that Jupyter is installed
jupyter --version

# Check that ipywidgets is installed
pip list | grep ipywidgets

# Check that ModelChecker is installed
pip list | grep model-checker
```

### 3. Installing from Development Source

If you're working directly from the repository:

```bash
# Clone repository (if you haven't already)
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker

# Install in development mode
cd Code
pip install -e .
```

## Workflow Guide

### 1. Starting a Jupyter Server

Navigate to your project directory and start the Jupyter server:

```bash
# Navigate to the project directory
cd /path/to/ModelChecker

# Start the Jupyter server
jupyter notebook
```

This will open a web browser showing the Jupyter file explorer. Navigate to the `Code/jupyter` directory to find the example notebooks.

### 2. Working with Jupyter Notebooks

#### 2.1 Basic Controls

- **Run a cell**: Click on a cell and press `Shift+Enter`
- **Create a new cell**: Click the `+` button in the toolbar
- **Change cell type**: Use the dropdown in the toolbar to select Markdown or Code
- **Save notebook**: Press `Ctrl+S` or use File → Save

#### 2.2 Cell Types

- **Code cells**: Contain Python code that you can execute
- **Markdown cells**: Contain formatted text, helpful for documentation

#### 2.3 Common Keyboard Shortcuts

- `Shift+Enter`: Run the current cell and move to the next
- `Ctrl+Enter`: Run the current cell and stay on it
- `Alt+Enter`: Run the current cell and insert a new one below
- `Esc` then `A`: Insert cell above current cell
- `Esc` then `B`: Insert cell below current cell
- `Esc` then `D,D` (press D twice): Delete current cell

### 3. Using ModelChecker in Jupyter

#### 3.1 Basic Formula Checking

```python
from model_checker.notebook import check_formula

# Check a simple propositional formula
check_formula("p → (q → p)")

# Check a modal formula
check_formula("□(p → q) → (□p → □q)")

# Check validity with premises
check_formula("q", premises=["p", "p → q"])
```

#### 3.2 Interactive Explorer

```python
from model_checker.notebook import InteractiveModelExplorer

# Create and display the explorer
explorer = InteractiveModelExplorer()
explorer.display()
```

## Workflow for NeoVim Users

If you prefer to use NeoVim for your work, there are several approaches to integrate Jupyter notebooks into your workflow.

### 1. Using Jupyter Alongside NeoVim

The simplest approach is to have Jupyter running in a separate terminal or browser window while editing code in NeoVim.

```bash
# Start Jupyter in a separate terminal
jupyter notebook
```

Then work on your Python modules in NeoVim and use the notebook for interactive testing.

### 2. Jupyter Integration Plugins for NeoVim

#### 2.1 jupyter-vim Plugin

This plugin allows you to connect to a Jupyter kernel from NeoVim.

Installation with vim-plug:
```vim
" Add to your init.vim or .vimrc
Plug 'jupyter-vim/jupyter-vim'
```

Basic usage:
```
:JupyterConnect                " Connect to a running Jupyter kernel
:JupyterRunCell                " Run the current cell (defined by ##)
:JupyterRunFile                " Run the current file
```

#### 2.2 magma-nvim Plugin

Magma provides inline execution results directly in NeoVim.

Installation with vim-plug:
```vim
" Add to your init.vim or .vimrc
Plug 'dccsillag/magma-nvim'
```

Basic usage:
```
:MagmaInit                     " Initialize Magma
:MagmaEvaluateOperator         " Evaluate a selection
:MagmaEvaluateLine             " Evaluate the current line
:MagmaEvaluateVisual           " Evaluate the visual selection
```

### 3. Using Terminal Multiplexers

You can use tmux or NeoVim's built-in terminal split to have Jupyter and NeoVim running side by side.

#### 3.1 With tmux:

```bash
# Start a new tmux session
tmux new -s jupyter

# Split the window
# Ctrl+b then %

# Start NeoVim in one pane
nvim

# Start Jupyter in the other pane
jupyter notebook
```

#### 3.2 With NeoVim terminal:

```
# In NeoVim
:vsplit
:terminal jupyter notebook
```

## Example Workflows

### 1. Development Workflow

1. **Edit code** in NeoVim:
   - Make changes to ModelChecker source files
   - Implement new features or fix bugs

2. **Test interactively** in Jupyter:
   - Import the modified modules
   - Try out new functions
   - Visualize results

3. **Document findings**:
   - Add markdown cells explaining the behavior
   - Save example notebooks demonstrating features

### 2. Research Workflow

1. **Formulate logical problems**:
   - Define premises and formulas to check
   - Choose appropriate semantic theories

2. **Explore with interactive tool**:
   - Use the InteractiveModelExplorer
   - Try different settings and theories
   - Find and analyze countermodels

3. **Document results**:
   - Save interesting models
   - Export visualizations
   - Document findings in markdown cells

### 3. Teaching Workflow

1. **Create example notebooks**:
   - Demonstrate logical concepts
   - Provide exercises for students

2. **Guide interactive exploration**:
   - Show how different formulas behave in various theories
   - Illustrate countermodels

3. **Share and discuss**:
   - Export notebooks to share with students
   - Use visualizations in presentations

## ModelChecker Jupyter Features

### 1. Formula Checking

The `check_formula` function provides a simple way to check the validity of a formula:

```python
check_formula(formula, theory_name="default", premises=None, settings=None)
```

Parameters:
- `formula`: The formula to check
- `theory_name`: The semantic theory to use (default, exclusion, etc.)
- `premises`: Optional list of premises
- `settings`: Optional dict of settings

Returns:
- An HTML display object showing the result

### 2. Interactive Explorer

The `InteractiveModelExplorer` class provides a widget-based interface for model exploration:

```python
explorer = InteractiveModelExplorer(theory_name="default")
explorer.display()
```

UI Components:
- **Formula input**: Text field for the formula to check
- **Premises input**: Textarea for multiple premise entry
- **Theory selector**: Dropdown to select semantic theory
- **Settings panel**: Controls for N, max_time, etc.
- **Control buttons**: Check Formula and Find Next Model
- **Visualization selector**: Switch between text and graph views

### 3. Visualization Options

Two visualization modes are available:

1. **Text Output**: Shows the full model details as formatted text
2. **Graph Visualization**: Displays a graphical representation of the model

To switch, use the radio buttons in the explorer UI.

## Troubleshooting

### Common Issues and Solutions

1. **Jupyter fails to start**:
   ```
   Solution: Check that jupyter is installed: pip install jupyter
   ```

2. **Widgets not displaying**:
   ```
   Solution: Install and enable widgets: pip install ipywidgets
   ```

3. **ImportError when importing ModelChecker**:
   ```
   Solution: Ensure ModelChecker is installed: pip install -e .
   ```

4. **Visualization not working**:
   ```
   Solution: Install matplotlib and networkx: pip install matplotlib networkx
   ```

5. **NeoVim plugin errors**:
   ```
   Solution: Check plugin documentation and requirements
   ```

### Getting Help

If you encounter issues:

1. Check the ModelChecker [GitHub issues](https://github.com/benbrastmckie/ModelChecker/issues)
2. Consult the [Jupyter documentation](https://jupyter.org/documentation)
3. For NeoVim integration issues, refer to the specific plugin documentation

## Advanced Topics

### 1. Converting Notebooks

You can convert notebooks to other formats:

```bash
# Convert to HTML
jupyter nbconvert --to html notebook.ipynb

# Convert to PDF
jupyter nbconvert --to pdf notebook.ipynb

# Convert to Python script
jupyter nbconvert --to python notebook.ipynb
```

### 2. Customizing Jupyter

Customize your Jupyter environment:

```bash
# Install a theme
pip install jupyterthemes
jt -t monokai -f fira -fs 12 -nf ptsans -nfs 12 -N -kl
```

### 3. Remote Access

Access Jupyter remotely:

```bash
# Start Jupyter with specific IP and port
jupyter notebook --ip=0.0.0.0 --port=8888 --no-browser
```

## Further Resources

- [Jupyter Documentation](https://jupyter.org/documentation)
- [ipywidgets Documentation](https://ipywidgets.readthedocs.io/)
- [NetworkX Documentation](https://networkx.org/documentation/stable/)
- [Matplotlib Documentation](https://matplotlib.org/stable/users/index.html)
- [NeoVim Jupyter Plugin](https://github.com/jupyter-vim/jupyter-vim)
- [ModelChecker GitHub](https://github.com/benbrastmckie/ModelChecker)

## Example Notebook

The `jupyter_demo.ipynb` notebook in this directory provides a complete demonstration of all features of the ModelChecker Jupyter integration.