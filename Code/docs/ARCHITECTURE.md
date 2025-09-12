# Technical Architecture Reference

[← Back to Technical Docs](README.md) | [Development Guide →](DEVELOPMENT.md) | [Methodology Architecture →](../../Docs/methodology/ARCHITECTURE.md)

> **Note**: This document provides a technical reference for developers. For a comprehensive educational overview of the architecture and design philosophy, see the [Methodology Architecture Guide](../../Docs/methodology/ARCHITECTURE.md).

## Table of Contents

1. [Overview](#overview)
2. [Core Components](#core-components)
3. [Package Structure](#package-structure)
4. [Data Flow](#data-flow)
5. [Theory Library](#theory-library)
6. [Iterator System](#iterator-system)
7. [Settings Architecture](#settings-architecture)
8. [Jupyter Integration](#jupyter-integration)
9. [Development Tools](#development-tools)
10. [Extension Points](#extension-points)
11. [Performance Considerations](#performance-considerations)
12. [Documentation Map](#documentation-map)

## Overview

The ModelChecker implements a modular, extensible framework for logical model checking using SMT solving. The architecture separates concerns across multiple layers:

- **Syntax Layer**: Formula parsing and AST construction
- **Semantic Layer**: Theory-specific constraint generation
- **Solving Layer**: Z3 SMT solver integration
- **Presentation Layer**: CLI and output formatting

Key architectural principles:
- **Theory Agnostic Core**: Base framework supports arbitrary semantic theories
- **Pipeline Architecture**: Clear data flow from input formulas to model output
- **Extensible Design**: New theories and operators can be added without modifying core
- **Clean Interfaces**: Well-defined contracts between components

## Core Components

### Builder System (`builder/`)

The builder package orchestrates the entire model checking pipeline:

```
builder/
├── module.py       # BuildModule: Manages example execution across theories
├── example.py      # BuildExample: Executes individual model checking
├── project.py      # BuildProject: Generates new theory implementations
├── progress.py     # Progress tracking for long operations
├── validation.py   # Parameter validation utilities
└── settings.py     # SettingsManager: Hierarchical configuration
```

**Key Classes**:
- `BuildModule`: Entry point for example execution, handles theory loading and comparison
- `BuildExample`: Coordinates pipeline from premises/conclusions to model results
- `BuildProject`: Template-based generation of new theory projects
- `SettingsManager`: Validates and merges settings from multiple sources

### Model System (`model.py`)

Core semantic framework and constraint generation:

```python
# Base Classes
SemanticDefaults      # Fundamental semantic operations (fusion, parthood)
PropositionDefaults   # Atomic proposition constraint generation
ModelConstraints      # Bridges syntax and semantics
ModelDefaults         # Z3 solving and result interpretation

# Key Methods
semantic.setup_z3_primitives()    # Define Z3 functions
proposition.proposition_constraints()  # Generate atomic constraints
model.solve()                     # Run Z3 solver
model.print_model_structure()     # Display results
```

### Syntactic System (`syntactic.py`)

Parsing and AST management:

```python
# Core Classes
Syntax              # Coordinates parsing and sentence management
Sentence            # Represents parsed formulas with metadata
Operator            # Base class for logical operators
DefinedOperator     # Complex operators via primitive definitions
OperatorCollection  # Registry for operator discovery

# Parsing Flow
1. Tokenization: "A ∧ B" → ["(", "A", "∧", "B", ")"]
2. Parsing: tokens → ["∧", "A", "B"] (prefix notation)
3. Sentence Creation: AST → Sentence objects
4. Operator Resolution: Link operators to semantic implementations
```

### Iterator System (`iterate/`)

Framework for finding multiple distinct models:

```
iterate/
├── core.py         # BaseModelIterator: Theory-agnostic framework
├── progress.py     # Real-time progress tracking
├── stats.py        # Model diversity statistics
├── graph_utils.py  # Graph-based isomorphism detection
└── parallel.py     # Parallel constraint generation
```

### Settings System (`settings/`)

Hierarchical configuration management:

```
settings/
├── settings.py     # Core settings definitions and validation
├── defaults.py     # System-wide default values
└── theory/         # Theory-specific setting definitions
```

## Package Structure

```
src/model_checker/
├── __init__.py           # Package exports and version
├── __main__.py           # CLI entry point
├── model.py              # Core semantic framework
├── syntactic.py          # Parsing and AST
├── utils.py              # Shared utilities
├── builder/              # Pipeline orchestration
├── iterate/              # Model iteration system
├── settings/             # Configuration management
├── theory_lib/           # Semantic theory implementations
│   ├── __init__.py       # Theory registry
│   ├── logos/            # Hyperintensional semantics
│   ├── exclusion/        # Unilateral exclusion semantics
│   ├── imposition/       # Fine's imposition theory
│   ├── bimodal/          # Temporal-modal logic
│   └── default/          # Classical semantics
└── jupyter/              # Interactive notebook support
```

## Data Flow

The system follows a unidirectional data flow:

```
1. Input Processing
   Input Formula → Tokenizer → Parser → AST

2. Semantic Processing  
   AST → Sentence Objects → Operator Resolution → Constraints

3. Solving
   Constraints → Z3 Solver → Model/UNSAT

4. Interpretation
   Model → Value Extraction → Sentence Evaluation → Output
```

**Detailed Pipeline**:

```python
# 1. Module Loading
BuildModule(args) → Load theory modules → Extract examples

# 2. Example Execution
BuildExample(module, theory, example) → {
    Parse premises/conclusions
    Create ModelConstraints
    Solve with Z3
    Interpret results
}

# 3. Iteration (if requested)
ModelIterator(example) → {
    Find initial model
    Generate difference constraints
    Find additional models
    Check isomorphism
}

# 4. Output Generation
ModelStructure.print_info() → Formatted display
```

## Theory Library

Each theory follows a standard structure:

```
theory_lib/<theory_name>/
├── __init__.py          # Theory exports and registration
├── semantic.py          # Core semantic implementation
├── operators.py         # Operator definitions
├── examples.py          # Standard test examples
├── iterate.py           # Theory-specific iteration
├── tests/               # Unit tests
│   ├── test_semantic.py
│   ├── test_operators.py
│   └── test_examples.py
├── docs/                # Theory documentation
│   ├── README.md
│   ├── API_REFERENCE.md
│   └── USER_GUIDE.md
└── subtheories/         # Optional modular extensions
```

**Theory Registration**:

```python
# theory_lib/__init__.py
AVAILABLE_THEORIES = {
    'logos': 'model_checker.theory_lib.logos',
    'exclusion': 'model_checker.theory_lib.exclusion',
    'imposition': 'model_checker.theory_lib.imposition',
    'bimodal': 'model_checker.theory_lib.bimodal',
    'default': 'model_checker.theory_lib.default'
}
```

## Iterator System

The iteration system finds multiple semantically distinct models:

**Architecture**:
```python
BaseModelIterator (abstract)
├── LogosModelIterator      # Hyperintensional differences
├── ExclusionModelIterator  # Exclusion relation variations
├── DefaultModelIterator    # Classical valuation changes
├── BimodalModelIterator    # Temporal-modal variations
└── ImpositionModelIterator # Imposition relation changes
```

**Key Methods**:
```python
# Abstract methods each theory must implement
_calculate_differences()      # Identify semantic differences
_create_difference_constraint()  # Ensure new models differ
_create_non_isomorphic_constraint()  # Avoid structural duplicates
_create_stronger_constraint()  # Escape isomorphism loops
```

## Settings Architecture

Settings follow a clear precedence hierarchy:

```
1. Command-line flags (highest priority)
   --N=5 --verbose

2. Example-specific settings
   EXAMPLE_settings = {'N': 4}

3. Module general_settings
   general_settings = {'max_time': 10}

4. Theory defaults
   DEFAULT_EXAMPLE_SETTINGS = {'contingent': True}

5. System defaults (lowest priority)
   DEFAULT_GENERAL_SETTINGS = {'N': 3}
```

**Validation Flow**:
```python
SettingsManager → Determine valid settings for theory
              → Merge settings with precedence
              → Validate types and constraints
              → Warn about unknown settings
```

## Jupyter Integration

The jupyter package provides interactive capabilities:

```
jupyter/
├── __init__.py          # Public API exports
├── interactive.py       # UI components
├── display.py           # Model visualization
├── unicode.py           # LaTeX/Unicode conversion
├── adapters.py          # Theory-specific display
├── environment.py       # Notebook environment setup
├── debug/               # Debugging utilities
└── notebooks/           # Example notebooks
```

**Key Features**:
- Interactive formula checking
- Model exploration UI
- Theory comparison tools
- Debug visualizations

## Development Tools

### Testing Infrastructure

```bash
# Test runner with unified interface
./run_tests.py                    # All tests
./run_tests.py --unit             # Unit tests only
./run_tests.py --examples         # Example validation
./run_tests.py logos modal        # Specific theory/subtheory
```

### Development CLI

```bash
# Local development without installation
./dev_cli.py examples/test.py
./dev_cli.py -l logos my_theory   # Generate new theory
./dev_cli.py --iso-debug          # Debug isomorphism
```

### Build Tools

```bash
# Package management
./run_update.py                   # Update version and build
python -m build                   # Build distribution
twine upload dist/*               # Upload to PyPI
```

## Extension Points

The framework provides multiple extension mechanisms:

### 1. New Theories

```python
# Implement four base classes
class MySemantics(SemanticDefaults):
    def setup_z3_primitives(self):
        # Define theory-specific Z3 functions
        
class MyProposition(PropositionDefaults):
    def proposition_constraints(self, letter):
        # Theory-specific atomic constraints
        
class MyModel(ModelDefaults):
    def print_model_structure(self, output):
        # Custom output formatting
        
class MyIterator(BaseModelIterator):
    def _calculate_differences(self, new, prev):
        # Theory-specific difference detection
```

### 2. New Operators

```python
class MyOperator(Operator):
    def __init__(self, semantics):
        self.symbol = "\\myop"
        self.arity = 2
        
    def true_at(self, world, sentence, eval_point):
        # Define truth conditions
        
# Register in operator collection
operators["\\myop"] = MyOperator
```

### 3. Custom Settings

```python
# Define in theory's semantic.py
DEFAULT_EXAMPLE_SETTINGS = {
    'my_setting': True,
    'my_threshold': 5
}

# Validate in get_settings_validation()
def get_settings_validation():
    return {
        'my_setting': bool,
        'my_threshold': int
    }
```

## Performance Considerations

### Memory Management
- Lazy theory loading reduces startup time
- Z3 context isolation prevents memory leaks
- Incremental solving for complex constraints

### Optimization Strategies
- State space pruning based on reachability
- Constraint ordering (simple constraints first)
- Parallel constraint generation for iteration
- Caching for isomorphism detection

### Profiling Points
- `BuildExample.__init__`: Pipeline setup
- `ModelDefaults.solve()`: Z3 solving time
- `ModelIterator.iterate()`: Iteration overhead
- `Syntax.create_sentences()`: Parsing complexity

## Documentation Map

### Core Documentation

| Document | Purpose | Location |
|----------|---------|----------|
| Package README | API overview | `src/model_checker/README.md` |
| Theory Library Guide | Theory implementation | `theory_lib/README.md` |
| Iterator Documentation | Model iteration system | `iterate/README.md` |
| Settings Documentation | Configuration system | `settings/README.md` |

### Theory Documentation

| Theory | Main README | API Reference | User Guide |
|--------|-------------|---------------|------------|
| Logos | `theory_lib/logos/README.md` | `logos/docs/API_REFERENCE.md` | `logos/docs/USER_GUIDE.md` |
| Exclusion | `theory_lib/exclusion/README.md` | `exclusion/docs/API_REFERENCE.md` | `exclusion/docs/USER_GUIDE.md` |
| Imposition | `theory_lib/imposition/README.md` | `imposition/docs/API_REFERENCE.md` | `imposition/docs/USER_GUIDE.md` |
| Bimodal | `theory_lib/bimodal/README.md` | `bimodal/docs/API_REFERENCE.md` | `bimodal/docs/USER_GUIDE.md` |

### Development Guides

| Guide | Purpose | Location |
|-------|---------|----------|
| Development Guide | Contributing workflow | `docs/DEVELOPMENT.md` |
| Testing Guide | Test infrastructure | `docs/TESTS.md` |
| Examples Guide | Creating examples | `docs/EXAMPLES.md` |
| Maintenance Standards | Code quality | `MAINTENANCE.md` |

---

[← Back to Technical Docs](README.md) | [Development Guide →](DEVELOPMENT.md) | [Methodology Architecture →](../../Docs/ARCHITECTURE.md)