# Usage Documentation: Practical ModelChecker Workflows

[← Back to Docs](../README.md) | [Start Here: Project Setup →](PROJECT.md) | [Workflow Overview →](WORKFLOW.md)

## Quick Start Path

Follow this recommended reading order to get up and running quickly:

1. **[PROJECT.md](PROJECT.md)** - Create your first project (Start here!)
2. **[WORKFLOW.md](WORKFLOW.md)** - Understand the complete workflow
3. **[EXAMPLES.md](EXAMPLES.md)** - Write your logical formulas
4. **[SETTINGS.md](SETTINGS.md)** - Configure your analysis
5. **[SEMANTICS.md](SEMANTICS.md)** - Test semantic properties
6. **[OUTPUT.md](OUTPUT.md)** - Save and share results
7. **[TOOLS.md](TOOLS.md)** - Advanced tools and theory comparison

## Overview

This directory provides **practical usage guides** organized in a learning progression from basic project setup to advanced semantic comparison. Each guide builds on the previous ones, creating a complete learning path for ModelChecker users.

### What You'll Learn

- **Getting Started** (PROJECT + WORKFLOW): Set up a project and run your first analysis
- **Core Skills** (EXAMPLES + SETTINGS): Write logical formulas and configure semantic settings
- **Advanced Techniques** (CONSTRAINTS + OUTPUT): Test properties and save results
- **Research Tools** (COMPARE_THEORIES): Compare different semantic frameworks

## Theory Examples

### Basic Validity Checking

Run a simple validity check from the command line:

```bash
# Create an example file
cat > modus_ponens.py << 'EOF'
from model_checker.theory_lib.logos import get_theory

theory = get_theory()

MP_premises = ["A", "A \\rightarrow B"]
MP_conclusions = ["B"]
MP_settings = {'N': 3}
MP_example = [MP_premises, MP_conclusions, MP_settings]

example_range = {"MP": MP_example}
semantic_theories = {"logos": theory}
EOF

# Run the example
model-checker modus_ponens.py
```

### Theory Comparison

Compare how different theories handle the same inference:

```python
# In compare_example.py
from model_checker.theory_lib.logos import get_theory as get_logos
from model_checker.theory_lib.exclusion import get_theory as get_exclusion

# Same logical inference
INFERENCE_premises = ["A \\vee B", "\\neg A"]
INFERENCE_conclusions = ["B"]
INFERENCE_settings = {'N': 3}
INFERENCE_example = [INFERENCE_premises, INFERENCE_conclusions, INFERENCE_settings]

# Compare theories
semantic_theories = {
    "Logos": get_logos(),
    "Exclusion": get_exclusion()
}
example_range = {"INFERENCE": INFERENCE_example}
```

### Debugging with Constraints

```bash
# Show generated constraints
model-checker examples/test.py --print-constraints

# Show Z3 model details
model-checker examples/test.py --print-z3

# Include impossible states in output
model-checker examples/test.py --print-impossible
```

For complete workflow patterns, see [WORKFLOW.md](WORKFLOW.md).

## Subdirectories

This directory contains only usage guide files (no subdirectories). Each guide addresses specific usage scenarios:

### Usage Guides

- **[WORKFLOW.md](WORKFLOW.md)** - Comprehensive guide covering all aspects of ModelChecker usage, from basic example running to advanced debugging, performance optimization, and integration patterns

- **[PROJECT.md](PROJECT.md)** - Step-by-step guide to creating new theory projects, copying from existing theories, and developing custom semantics with local project files

- **[EXAMPLES.md](EXAMPLES.md)** - Detailed guide to writing example files, including structure requirements, formula syntax, and common patterns

- **[SETTINGS.md](SETTINGS.md)** - Complete settings documentation, including hierarchy, core and theory-specific settings, command-line overrides, and common configurations

- **[OUTPUT.md](OUTPUT.md)** - Complete documentation of output formats (JSON, Markdown, Notebook), saving options, directory structure, and practical examples

- **[TOOLS.md](TOOLS.md)** - Advanced ModelChecker features including iterate setting, theory comparison, maximize flag, and debugging tools

- **[SEMANTICS.md](SEMANTICS.md)** - Advanced methodology for testing semantic constraints through countermodel search, proving properties by absence, and discovering minimal axiom sets

## Documentation

### For New Users
- **[Getting Started](../installation/GETTING_STARTED.md)** - First steps after installation
- **[Basic Workflows](WORKFLOW.md#basic-workflows)** - Running examples
- **[Writing Examples](EXAMPLES.md)** - Creating example files
- **[Troubleshooting](WORKFLOW.md#troubleshooting)** - Common issues

### For Researchers
- **[ModelChecker Tools](TOOLS.md)** - Advanced features and comparative semantics
- **[Constraint Testing](SEMANTICS.md)** - Testing semantic properties
- **[Performance Optimization](WORKFLOW.md#performance-optimization)** - Large-scale testing
- **[Architecture](../architecture/README.md)** - Theoretical foundations

### For Developers
- **[Creating Projects](PROJECT.md)** - New theory development
- **[Development Workflows](WORKFLOW.md#theory-development-workflow)** - Building theories
- **[Integration Patterns](WORKFLOW.md#integration-patterns)** - CI/CD and automation
- **[Technical Docs](../../Code/docs/README.md)** - Implementation details

## Key Features

### Comprehensive Workflows
- **Basic Usage** - Running single examples and batch testing
- **Development** - Creating new theories from templates
- **Debugging** - Constraint inspection and unsat core analysis
- **Performance** - Optimization strategies and settings tuning

### Theory Comparison
- **Import Patterns** - Avoiding circular dependencies
- **Translation Dictionaries** - Mapping between operator notations
- **Comparison Setup** - Configuring multiple theories
- **Result Interpretation** - Understanding theory differences

### Constraint Testing
- **Proof by Absence** - Using countermodel search for proofs
- **Theory Settings** - Implementing test-specific configurations
- **Constraint Negation** - Testing property satisfaction
- **Minimal Axioms** - Discovering logical dependencies

### Practical Tools
- **Command-line flags** for debugging and output control
- **Settings management** for performance tuning
- **Integration patterns** for automation
- **Common recipes** for frequent tasks

## References

### Framework Documentation
- **[Installation Guide](../installation/README.md)** - Setup instructions
- **[Architecture Guide](../architecture/README.md)** - How ModelChecker works
- **[Theory Library](../../Code/src/model_checker/theory_lib/README.md)** - Available theories

### Related Resources
- **[Development Guide](../../Code/docs/DEVELOPMENT.md)** - Contributing new theories
- **[API Reference](../../Code/src/model_checker/README.md)** - Programming interface
- **[Examples](../../Code/docs/EXAMPLES.md)** - Example file structure

---

[← Back to Docs](../README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)
