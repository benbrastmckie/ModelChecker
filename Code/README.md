This package draws on the [Z3](https://github.com/Z3Prover/z3) SMT solver to provide a unified programmatic semantics and methodology for developing modular semantic theories and exploring their logics.
Rather than computing whether a given sentence is a logical consequence of some set of sentences by hand, these resources allow users to establish logical consequence over finite models, finding readable countermodels if there are any.
Whereas logic has traditionally focused on small language fragments, this project develops a unified semantics for the Logos, a language of thought for AI agents to plan and reason to promote transparent and verifiable reasoning that can be trusted.

In addition to the unified semantics for the Logos, this package provides support for users to develop their own programmatic semantic theories.
The [`TheoryLib`](src/model_checker/theory_lib/) includes the semantic theories that are available for users to import or use as a template to develop novel theories that can be contributed to the `TheoryLib` by pull request.

You can find more information about development [here](docs/DEVELOPMENT.md) and the background semantic theory provided for the Logos [here](http://www.benbrastmckie.com/research#access).
The semantics and logic for counterfactual conditionals is developed in this [paper](https://link.springer.com/article/10.1007/s10992-025-09793-8).

## Quick Start

### Installation

Basic installation with core functionality:
```bash
pip install model-checker
```

Installation with Jupyter support:
```bash
pip install model-checker[jupyter]
```

Development installation from source:
```bash
git clone https://github.com/benbrastmckie/ModelChecker
cd ModelChecker/Code
pip install -e .[dev]
```

### Command Line Usage

Create a new theory project:
```bash
model-checker
```

Create a project from existing theory:
```bash
model-checker -l logos
```

Check an example file:
```bash
model-checker examples/counterfactual_logic.py
```

### Python API Usage

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Get a theory
theory = logos.get_theory()

# Create and check a model
model = BuildExample("my_example", theory)
result = model.check_formula("\\Box p \\rightarrow p")

if result:
    print("Formula is valid")
else:
    print("Found countermodel:")
    model.print_countermodel()
```

### Jupyter Notebook Usage

```python
from model_checker.jupyter import check_formula, ModelExplorer

# Quick formula check
check_formula("(p \\wedge q) \\equiv (q \\wedge p)")

# Interactive exploration
explorer = ModelExplorer()
explorer.display()
```

For comprehensive Jupyter integration documentation, see:
- [Jupyter Integration Guide](examples/README_jupyter.md)
- [Interactive Notebooks](src/model_checker/theory_lib/logos/notebooks/README.md)
- [Example Notebooks](notebooks/)

## Development

For complete development documentation, see:
- [Development Guide](docs/DEVELOPMENT.md) - Comprehensive development workflow
- [Architecture Documentation](ARCHITECTURE.md) - System design and patterns
- [Maintenance Standards](MAINTENANCE.md) - Coding and documentation guidelines

### Running Tests

Run all tests:
```bash
./run_tests.py
```

Run theory-specific tests:
```bash
./test_theories.py --theories logos exclusion
```

Run package component tests:
```bash
./test_package.py --components utils builder
```

For detailed testing documentation, see [Unit Tests Guide](../Docs/UNIT_TESTS.md).

### Creating a New Theory

Use the development CLI to create a new theory:
```bash
./dev_cli.py -l my_new_theory
```

This creates a complete theory template with:
- Semantic implementation skeleton
- Operator definitions
- Example formulas
- Test structure
- Documentation templates

For theory development guidance, see:
- [Theory Library Documentation](src/model_checker/theory_lib/README.md)
- [Theory Architecture Patterns](src/model_checker/theory_lib/README.md#theory-architecture-patterns)

### Development Tools

Debug an example with constraint printing:
```bash
./dev_cli.py -p -z examples/my_example.py
```

Launch Jupyter for interactive development:
```bash
./run_jupyter.sh
```

For advanced debugging and tools documentation, see [Tools Guide](../Docs/TOOLS.md).

## Package Architecture

ModelChecker follows a modular architecture with clear separation between:

1. **Core Framework** (`src/model_checker/`) - Base classes and interfaces
2. **Theory Library** (`src/model_checker/theory_lib/`) - Semantic theory implementations
3. **Utilities** (`src/model_checker/utils/`) - Helper functions and tools
4. **Jupyter Integration** (`src/model_checker/jupyter/`) - Interactive features

For detailed architecture documentation, see [ARCHITECTURE.md](ARCHITECTURE.md).

## Contributing

We welcome contributions! Please:

1. Read [MAINTENANCE.md](MAINTENANCE.md) for coding standards
2. Follow [STYLE_GUIDE.md](STYLE_GUIDE.md) for Python style
3. See [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md) for workflow
4. Ensure all tests pass before submitting PRs
5. Include documentation for new features

## Related Documentation

- [Project Overview](../README.md) - Main project documentation
- [Installation Guide](../Docs/INSTALLATION.md) - Detailed installation instructions
- [Theory Library](src/model_checker/theory_lib/README.md) - Available theories
- [API Reference](src/model_checker/README.md) - Complete API documentation
- [Hyperintensional Semantics](../Docs/HYPERINTENSIONAL.md) - Theoretical background
