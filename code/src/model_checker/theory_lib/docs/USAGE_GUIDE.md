# Theory Library Usage Guide

[← Back to Theory Library](../README.md) | [Architecture Guide →](THEORY_ARCHITECTURE.md) | [Contributing Guide →](CONTRIBUTING.md)

## Table of Contents

1. [Import Strategies](#import-strategies)
2. [Basic Usage Examples](#basic-usage-examples)
3. [Theory Selection and Configuration](#theory-selection-and-configuration)
4. [Comparing Theories](#comparing-theories)
5. [Advanced Usage Patterns](#advanced-usage-patterns)

## Import Strategies

Theory projects support two primary import strategies, each with different use cases:

### 1. Local Module Imports (for Generated Projects)

When you generate a new theory project with `model-checker -l bimodal`, the examples.py file uses local imports:

```python
# Standard imports
import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Direct imports from local modules
from semantic import BimodalStructure, BimodalSemantics, BimodalProposition
from operators import bimodal_operators
```

**Benefits:**
- Simple, direct imports from files in the same directory
- Projects can be run directly with `model-checker examples.py`
- Changes to the local files are immediately reflected
- Ideal for development and experimentation

**When to use:**
- When you want to modify and experiment with a theory
- When creating a standalone project
- When running the examples.py file directly

### 2. Package Imports (for Comparison)

To compare your modified theory with the original implementation, you can use package imports:

```python
# Import from the core package
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalSemantics,
    BimodalProposition
)
from model_checker.theory_lib.bimodal import bimodal_operators

# Or more generally
from model_checker import get_theory
from model_checker.theory_lib import get_examples

# Load the original theory
theory = get_theory("bimodal")
```

**Benefits:**
- Access to the original implementations for comparison
- Consistency with the package's versioned APIs
- Clear separation between your modifications and the original

**When to use:**
- When comparing your modifications to the original
- When extending the original without modifying it
- When using multiple theories together

## Basic Usage Examples

### Simple Formula Checking

```python
from model_checker import get_theory
from model_checker.theory_lib import get_examples

# Load a theory
theory = get_theory("logos")  # or "exclusion", "imposition", "bimodal"

# Get examples from the theory
examples = get_examples("logos")

# Example: Create a counterfactual example file
# Save as: counterfactual_example.py
from model_checker.theory_lib.logos import get_theory

# Define examples
counterfactual_validity = [
    [],                              # No premises
    ["(A \\boxright B)"],            # Check if this is a theorem
    {'N': 3, 'expectation': True}    # Expect countermodel
]

counterfactual_modus_ponens = [
    ["A", "(A \\boxright B)"],       # Premises
    ["B"],                           # Conclusion
    {'N': 3, 'expectation': False}   # Expect validity
]

test_example_range = {
    "cf_validity": counterfactual_validity,
    "cf_modus_ponens": counterfactual_modus_ponens,
}

semantic_theories = {"logos": get_theory()}

# Run with: model-checker counterfactual_example.py
```

### Using the Standard Examples.py Structure

```python
# Save as: modal_logic_examples.py
import os
import sys

current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from model_checker.theory_lib.logos import get_theory

# Define the K axiom example
k_axiom_example = [
    ["\\Box A", "\\Box (A \\rightarrow B)"],  # Premises
    ["\\Box B"],                              # Conclusion
    {'N': 3, 'expectation': False}            # Should be valid
]

# Define the T axiom example  
t_axiom_example = [
    ["\\Box A"],                              # Premise
    ["A"],                                    # Conclusion
    {'N': 3, 'expectation': False}            # Should be valid
]

test_example_range = {
    "k_axiom": k_axiom_example,
    "t_axiom": t_axiom_example,
}

semantic_theories = {
    "logos": get_theory(),
}

# Run with: model-checker modal_logic_examples.py
```

## Theory Selection and Configuration

### Custom Settings

```python
# Define custom settings for your examples
settings = {
    "N": 4,               # Number of atomic states
    "contingent": True,   # Require contingent valuations
    "non_empty": True,    # Require non-empty verifiers/falsifiers
    "disjoint": False,    # Allow overlapping verifiers/falsifiers
    "max_time": 5         # Maximum solving time (seconds)
}

# Use custom settings in your examples.py file
example_with_settings = [
    ["\\Box A"],
    ["A"],
    settings  # Custom settings for this example
]
```

### Selective Subtheory Loading

For theories with modular architecture (like Logos):

```python
from model_checker.theory_lib import logos

# Load specific subtheories only
theory = logos.get_theory(['extensional', 'counterfactual'])  # Only load specific subtheories

# Full theory (all subtheories)
full_theory = logos.get_theory()  # All available subtheories
```

### Theory-Specific Configuration

Each theory has its own relevant settings:

```python
# Bimodal theory with temporal settings
bimodal_settings = {
    "N": 3,                    # Atomic states
    "M": 4,                    # Time points
    "align_vertically": True   # Display format
}

# Exclusion theory with unilateral settings
exclusion_settings = {
    "non_empty": True,         # Non-empty verifier sets
    "fusion_closure": False    # Fusion closure constraints
}
```

## Comparing Theories

For comprehensive guidance on theory comparison, avoiding circular imports, and advanced multi-theory setups, see **[Theory Comparison Guide](../../../../Docs/usage/COMPARE_THEORIES.md)**.

### Cross-Theory Analysis

```python
from model_checker import BuildModule

# Create a module to compare theories
module = BuildModule("comparison")

# Add theories to compare
module.add_theory("logos")
module.add_theory("exclusion")

# Run tests across theories
module.run_tests(["test1", "test2"])
```

### Formula Testing Across Theories

```python
# Save as: theory_comparison.py
from model_checker.theory_lib import logos, exclusion, imposition, bimodal

# Test double negation elimination across theories
double_negation = [
    [],                                  # No premises
    ["(\\neg \\neg A \\rightarrow A)"],      # Double negation elimination
    {'N': 3}                             # Settings
]

# Define examples for each theory
test_example_range = {
    "double_negation": double_negation,
}

# Load all theories for comparison
semantic_theories = {
    "logos": logos.get_theory(),
    "exclusion": exclusion.get_theory(),
    "imposition": imposition.get_theory(),
    "bimodal": bimodal.bimodal_theory,
}

# Run with: model-checker theory_comparison.py
# The output will show which theories validate double negation
```

## Advanced Usage Patterns

### Model Iteration

Find multiple models to explore different counterexamples:

```python
from model_checker import BuildExample, get_theory

theory = get_theory("logos")
model = BuildExample("iteration_test", theory, settings={
    "N": 4,
    "iterate": 5  # Find 5 different models
})

model.add_premises(["p"])
model.add_conclusions(["\\Box p"])

# Get all models
models = model.get_all_models()
for i, model_result in enumerate(models):
    print(f"Model {i+1}: {model_result}")
```

### Interactive Exploration

For Jupyter notebook usage:

```python
from model_checker import ModelExplorer

# Interactive widget-based exploration
explorer = ModelExplorer()
explorer.display()

# Or use the standard examples.py workflow for formula checking
# See the Examples Standard documentation for details
```

### Custom Constraint Analysis

```python
from model_checker import BuildExample, get_theory

theory = get_theory("logos")
model = BuildExample("custom_analysis", theory)

# Add complex premises
model.add_premises([
    "\\Box (p \\rightarrow q)",
    "(p \\boxright r)",
    "\\neg (q \\wedge r)"
])

# Check multiple conclusions
conclusions = ["\\neg p", "\\neg \\Box q", "\\neg (p \\boxright s)"]
for conclusion in conclusions:
    result = model.check_formula(conclusion)
    print(f"{conclusion}: {'Valid' if result else 'Invalid'}")
```

---

[← Back to Theory Library](../README.md) | [Architecture Guide →](THEORY_ARCHITECTURE.md) | [Contributing Guide →](CONTRIBUTING.md)