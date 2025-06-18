# ModelChecker

The ModelChecker is a programmatic semantic framework for implementing and comparing logical theories, with a focus on modal, counterfactual, and hyperintensional logic.
It provides tooling for defining semantic theories, testing logical principles, and finding countermodels.

## API Architecture

The ModelChecker framework follows a modular architecture designed to separate core functionality from theory-specific implementations:

### Core Components

> TO BE UPDATED SOON...

1. **Builder Module** (`builder.py`)

   - `BuildExample`: Creates a model from a named example within a theory
   - `BuildModule`: Loads and runs examples from a specific module
   - `BuildProject`: Creates new theory implementations from templates

2. **Model Module** (`model.py`)

   - `ModelConstraints`: Core model checking and constraint solving
   - `ModelDefaults`: Base class for semantic model implementations
   - `SemanticDefaults`: Base semantics with default implementations
   - `PropositionDefaults`: Base proposition class for formula evaluation

3. **Syntactic Module** (`syntactic.py`)

   - `Syntax`: Parses and processes logical formulas
   - `Operator`: Base class for logical operators
   - `DefinedOperator`: Base class for operators defined in terms of primitives

4. **Utils Module** (`utils.py`)

   - Helper functions for common operations
   - Theory loading via `get_theory()`
   - Example loading via `get_example()`
   - Testing via `run_test()`

5. **Main Module** (`__main__.py`)

   - Command-line interface and entry points
   - Argument parsing and dispatch

6. **Settings Package** (`settings/`)

   - Centralized settings management system
   - Theory-specific default settings
   - Validation and warning systems for unknown settings
   - Command-line flag integration
   - See [Settings Documentation](settings/README.md) for details

7. **Jupyter Package** (`jupyter/`)
   - Interactive exploration of logical models in notebooks
   - Formula checking, countermodel finding, and visualization
   - Support for Unicode and LaTeX notation
   - Theory-specific adapters for consistent interfaces
   - See [Jupyter Integration Documentation](jupyter/README.md) for details

### TheoryLib

The `TheoryLib` contains programmatic semantic theories for fragment langages:

1. **Theory Registry** (`theory_lib/__init__.py`)
   - Central registry of available theories
   - Lazy loading of theory implementations
   - Utilities for discovering and accessing theories

2. **Individual Theories**
   - Each theory follows a standardized structure:
     - `semantic.py`: Core semantic framework implementation
     - `operators.py`: Operator definitions and semantics
     - `examples.py`: Test cases and examples
     - `test/`: Unit tests for the theory

### API Flow

The typical API usage flow follows these steps:

1. **Theory Selection**: Get a theory via `get_theory()`
2. **Model Building**: Create a model with `BuildExample` or `BuildModule`
3. **Formula Evaluation**: Check formulas using the model's methods
4. **Result Analysis**: Analyze results and possibly find countermodels

```python
# A typical workflow might look like:
from model_checker import BuildExample, get_theory

# 1. Load a theory
theory = get_theory("logos")

# 2. Create a model
model = BuildExample("simple_modal", theory)

# 3. Check a formula
result = model.check_formula("(\\Box A \\rightarrow A)")

# 4. Analyze the result
print(f"Formula is {'valid' if result else 'invalid'}")
```

### Object Hierarchy

The object hierarchy for model checking flows as follows:

1. **BuildExample/BuildModule**: Top-level coordination
2. **ModelConstraints**: Constraint generation and solving
3. **Syntax**: Formula parsing and normalization
4. **Theory-specific semantics**: Semantic interpretation
5. **Theory-specific proposition**: Formula evaluation
6. **Theory-specific operators**: Operator behavior

### Extension Points

The framework is designed to be extended in several ways:

1. **New Theories**: Add new theory directories to `theory_lib/`
2. **New Operators**: Subclass `Operator` or `DefinedOperator`
3. **New Semantics**: Subclass `SemanticDefaults`
4. **New Interfaces**: Add new builders or integration points

### Import Strategies

When working with theory implementations, you have two primary import strategies:

1. **Local Imports** - For modifying and customizing a theory:
   ```python
   # When working in a generated project
   from semantic import SemanticClass
   from operators import my_operators
   ```

2. **Package Imports** - For using the original implementations:
   ```python
   # Accessing theory from the main package
   from model_checker.theory_lib.default import Semantics, default_operators
   ```

This flexibility allows you to both experiment with modifications in standalone projects and compare against original implementations. When you generate a new project with `model-checker -l theory_name`, the generated files include import handling code that makes local imports work correctly.

For more details on import strategies and theory customization, see the [Theory Library Documentation](theory_lib/README.md#import-strategies).

### Theory-Specific Design

Each theory in the ModelChecker framework is designed to be self-contained with its own appropriate defaults and settings. This design follows several key principles:

1. **Relevance Principle**: Theories should only define settings that are relevant to their specific semantics. For example:

   - Temporal theories like `bimodal` include time-related settings like `M` (number of time points)
   - Visualization settings like `align_vertically` only appear in theories where they make sense

2. **Clear Defaults**: Each theory defines its own default settings via:

   - `DEFAULT_EXAMPLE_SETTINGS`: For example-specific settings
   - `DEFAULT_GENERAL_SETTINGS`: For general output and behavior settings

3. **Warning System**: The framework warns about unknown settings only when:
   - A user explicitly provides a command-line flag that doesn't correspond to a setting in the theory
   - A user includes a setting in their configuration that isn't defined in the theory's defaults

For detailed information about settings management and theory-specific settings:

- [Settings System Documentation](settings/README.md)
- [Theory Library Documentation](theory_lib/README.md#theory-specific-settings)

### Adding New Theories

To add a new theory to the framework:

1. Create a new directory under `src/model_checker/theory_lib/`
2. Implement the required files (semantic.py, operators.py, examples.py)
3. Add test files in a `test/` subdirectory
4. Add your theory name to the `AVAILABLE_THEORIES` list in `theory_lib/__init__.py`:

```python
# In theory_lib/__init__.py
AVAILABLE_THEORIES = [
    'logos',
    'exclusion',
    'imposition',
    'your_new_theory',  # Add your theory here
]
```

Once registered, your theory will be automatically discovered by the development scripts, tests will be run during CI/CD processes, and users will be able to access it with the `-l` flag.

## Jupyter Notebook Integration

The ModelChecker framework includes comprehensive Jupyter notebook integration, allowing interactive exploration of logical models and theories in a user-friendly environment.

### Overview

Jupyter notebooks provide an ideal environment for working with logical theories by combining:

- Interactive formula checking and evaluation
- Visual representation of models and countermodels
- Rich documentation with explanatory text and examples
- Experimental workflow for theory development and comparison

The `jupyter` package in ModelChecker offers both high-level functions for quick tasks and interactive components for deeper exploration:

```python
# Basic formula checking
from model_checker import check_formula
check_formula("(p \\rightarrow (q \\rightarrow p))")

# Interactive exploration
from model_checker import ModelExplorer
explorer = ModelExplorer()
explorer.display()
```

### Key Features

- **Formula Checking**: Verify validity of formulas with optional premises
- **Countermodel Finding**: Search for models that falsify a formula
- **Interactive UI**: Customizable widgets for theory exploration
- **Visualization**: Both text and graph-based visualization options
- **Unicode Support**: Work directly with logical symbols (→, ∧, ∨, □, ◇, etc.)
- **Theory-Specific Extensions**: Adapters for different semantic theories
- **Example Libraries**: Access to pre-defined examples from theories

### Use Cases

1. **Theory Development**: Experiment with semantic theories interactively
2. **Teaching**: Create interactive demonstrations of logical concepts
3. **Research**: Explore relationships between different logical systems
4. **Documentation**: Create rich, interactive documentation for theories

For detailed information about the Jupyter integration, including installation, usage examples, and customization options, see the [Jupyter Integration Documentation](jupyter/README.md).
