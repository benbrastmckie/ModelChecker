# Usage Documentation: Practical ModelChecker Workflows

[← Back to Docs](../README.md) | [Workflow →](WORKFLOW.md) | [Constraints →](CONSTRAINTS.md)

## Directory Structure

```
usage/
├── README.md                       # This file - usage documentation hub
├── WORKFLOW.md                     # Comprehensive usage patterns and workflows
├── COMPARE_THEORIES.md             # Theory comparison guide and patterns
└── CONSTRAINTS.md                  # Testing semantic constraints methodology
```

## Overview

This directory provides **practical usage guides** for working with the ModelChecker framework, focusing on real-world workflows and theory comparison techniques. The documentation bridges the gap between installation and advanced development, showing how to effectively use ModelChecker for logical investigation and research.

The usage guides cover **3 complementary aspects**: comprehensive workflows for all ModelChecker features, specialized guidance for comparing semantic theories, and advanced techniques for testing whether constraints are automatically satisfied by semantic definitions. Together, these documents enable users to run examples, debug formulas, optimize performance, and systematically compare how different semantic theories handle the same logical principles.

Whether you're validating logical arguments, exploring countermodels, developing new theories, or conducting comparative semantic research, these guides provide the practical knowledge needed to use ModelChecker effectively. The documentation emphasizes **hands-on examples**, **command-line techniques**, and **real-world problem-solving** approaches.

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

# Find multiple models
model-checker examples/test.py --iterate=3
```

For complete workflow patterns, see [WORKFLOW.md](WORKFLOW.md).

## Subdirectories

This directory contains only usage guide files (no subdirectories). Each guide addresses specific usage scenarios:

### Usage Guides

- **[WORKFLOW.md](WORKFLOW.md)** - Comprehensive guide covering all aspects of ModelChecker usage, from basic example running to advanced debugging, performance optimization, and integration patterns

- **[COMPARE_THEORIES.md](COMPARE_THEORIES.md)** - Specialized guide for comparing semantic theories, including import patterns, avoiding circular dependencies, and interpreting comparison results

- **[CONSTRAINTS.md](CONSTRAINTS.md)** - Advanced methodology for testing semantic constraints through countermodel search, proving properties by absence, and discovering minimal axiom sets

## Documentation

### For New Users
- **[Getting Started](../installation/GETTING_STARTED.md)** - First steps after installation
- **[Basic Workflows](WORKFLOW.md#basic-workflows)** - Running examples
- **[Troubleshooting](WORKFLOW.md#troubleshooting)** - Common issues

### For Researchers
- **[Theory Comparison](COMPARE_THEORIES.md)** - Comparative semantics
- **[Performance Optimization](WORKFLOW.md#performance-optimization)** - Large-scale testing
- **[Methodology](../methodology/README.md)** - Theoretical foundations

### For Developers
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
- **[Methodology Guide](../methodology/README.md)** - How ModelChecker works
- **[Theory Library](../../Code/src/model_checker/theory_lib/README.md)** - Available theories

### Related Resources
- **[Development Guide](../../Code/docs/DEVELOPMENT.md)** - Contributing new theories
- **[API Reference](../../Code/src/model_checker/README.md)** - Programming interface
- **[Examples](../../Code/docs/EXAMPLES.md)** - Example file structure

---

[← Back to Docs](../README.md) | [Workflow →](WORKFLOW.md) | [Constraints →](CONSTRAINTS.md)