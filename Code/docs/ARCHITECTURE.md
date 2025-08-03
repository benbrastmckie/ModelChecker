# Project Architecture

The ModelChecker implements a modular framework for logical model checking with the following architecture:

## Core Components

1. **Builder System** (`builder.py`)
   - `BuildExample`: Creates and executes individual model checking examples
   - `BuildModule`: Manages multiple examples across different theories
   - `BuildProject`: Creates new theory implementations from templates

2. **Model System** (`model.py`)
   - `ModelConstraints`: Core constraint generation for model checking
   - `ModelDefaults`: Base implementation for model structures
   - `SemanticDefaults`: Fundamental semantic operations (fusion, part-hood, etc.)
   - `PropositionDefaults`: Base proposition class for formula evaluation

3. **Syntactic System** (`syntactic.py`)
   - `Syntax`: Parses formulas and builds logical structures
   - `Sentence`: Represents logical formulas with metadata
   - `Operator`: Base class for logical operators
   - `DefinedOperator`: Complex operators defined using primitives
   - `OperatorCollection`: Registry system for operator management

4. **Utilities** (`utils.py`)
   - Theory loading and registration
   - Example loading and execution
   - Common helper functions
   - Path management utilities

5. **Command-line Interface** (`__main__.py`, `cli.py`)
   - Command-line argument processing
   - Project initialization
   - Example execution
   - Error handling and output formatting

## Theory Library

The `theory_lib/` package contains implementations of specific semantic theories:

1. **Default Theory**: Standard bilateral truthmaker semantics
   - `semantic.py`: Core semantic model implementation
   - `operators.py`: Definition of logical operators
   - `examples.py`: Demonstration examples
   - `test/`: Unit tests for theory validation

2. **Exclusion Theory**: Unilateral semantics with exclusion relations
   - Same structure as default theory

3. **Imposition Theory**: Semantics with imposition relations
   - Same structure as default theory

4. **Bimodal Theory**: Bimodal semantics for counterfactuals (experimental)
   - Same structure as default theory

Each theory is registered in `theory_lib/__init__.py` for discovery and lazy loading.

## Jupyter Integration

The `jupyter/` package provides interactive notebook capabilities:

1. **Public API** (`__init__.py`)
   - High-level functions: `check_formula`, `find_countermodel`, etc.
   - UI Components: `ModelExplorer`, `FormulaChecker`
   - Display functions for visualization

2. **Component Modules**
   - `interactive.py`: Interactive UI components
   - `display.py`: Model visualization utilities
   - `unicode.py`: Unicode/LaTeX notation conversion
   - `adapters.py`: Theory-specific visualization adapters
   - `environment.py`: Environment setup and configuration
   - `utils.py`: Jupyter-specific utilities

3. **Debugging Tools** (`debug/`)
   - Diagnostic tools for troubleshooting
   - Error capture utilities
   - Testing notebooks

4. **Demo Notebooks** (`notebooks/`)
   - Basic usage examples
   - Advanced features demonstrations

## Development Tools

1. **Testing Tools** (`run_tests.py`)
   - Automatic test discovery and execution
   - Theory-specific test runners

2. **Package Management** (`run_update.py`)
   - Version management
   - Package building and deployment

3. **Development CLI** (`dev_cli.py`)
   - Local development interface
   - Path configuration for development mode

4. **NixOS Support** (`shell.nix`)
   - Development environment definition
   - Path management for NixOS systems

## Key Search Paths

- Core implementations: `src/model_checker/`
- Theory definitions: `src/model_checker/theory_lib/`
- Jupyter integrations: `src/model_checker/jupyter/`

## Documentation Reference

### Core Documentation

| Document Path                            | Description                           | When to Use                              |
| ---------------------------------------- | ------------------------------------- | ---------------------------------------- |
| `README.md`                              | Project overview, installation, usage | Start here for general overview          |
| `src/model_checker/README.md`            | API architecture, components          | Understanding architecture               |
| `src/model_checker/theory_lib/README.md` | Theory library overview               | Adding/modifying theories                |
| `src/model_checker/jupyter/README.md`    | Jupyter integration                   | Interactive usage                        |
| `../Docs/TOOLS.md`                       | Advanced tools and features           | Using iterate, maximize, debugging flags |

### Theory Documentation

| Document Path                                       | Description               | When to Use                           |
| --------------------------------------------------- | ------------------------- | ------------------------------------- |
| `src/model_checker/theory_lib/logos/README.md`      | Logos theory details      | Working with hyperintensional logic   |
| `src/model_checker/theory_lib/bimodal/README.md`    | Bimodal theory details    | Working with temporal counterfactuals |
| `src/model_checker/theory_lib/exclusion/README.md`  | Exclusion theory details  | Working with exclusion semantics      |
| `src/model_checker/theory_lib/imposition/README.md` | Imposition theory details | Working with imposition semantics     |

### Jupyter and Troubleshooting

| Document Path                                  | Description                 | When to Use                 |
| ---------------------------------------------- | --------------------------- | --------------------------- |
| `src/model_checker/jupyter/TROUBLESHOOTING.md` | Common issues and solutions | Fixing integration problems |
| `src/model_checker/jupyter/NixOS_jupyter.md`   | NixOS setup guide           | Setting up on NixOS         |
| `src/model_checker/jupyter/debug/DEBUGGING.md` | Debugging workflow          | Systematic troubleshooting  |

### Interactive Notebooks

| Document Path                                                           | Description           | When to Use                      |
| ----------------------------------------------------------------------- | --------------------- | -------------------------------- |
| `src/model_checker/jupyter/notebooks/basic_demo.ipynb`                  | Basic usage examples  | Getting started with notebooks   |
| `src/model_checker/jupyter/notebooks/options_demo.ipynb`                | Advanced options      | Learning advanced features       |
| `src/model_checker/theory_lib/logos/notebooks/logos_demo.ipynb`         | Logos theory demo     | Exploring hyperintensional logic |
| `src/model_checker/theory_lib/exclusion/notebooks/exclusion_demo.ipynb` | Exclusion theory demo | Exploring exclusion semantics    |
