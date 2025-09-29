# ModelChecker Tools Guide

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)

## Table of Contents

1. [Overview](#overview)
2. [Using the Iterate Setting](#using-the-iterate-setting)
   - [Basic Usage](#basic-usage)
   - [How It Works](#how-it-works)
   - [Theory-Specific Differences](#theory-specific-differences)
   - [Advanced Settings](#advanced-settings)
3. [Comparing Multiple Theories](#comparing-multiple-theories)
   - [Core Principles](#core-principles)
   - [Import Order Matters](#import-order-matters)
   - [Theory Independence](#theory-independence)
   - [Translation Dictionaries](#translation-dictionaries)
4. [Using the Maximize Flag](#using-the-maximize-flag)
5. [Debugging and Output Flags](#debugging-and-output-flags)
6. [Implementation Guidelines](#implementation-guidelines)
   - [Setting Up Comparisons](#setting-up-comparisons)
   - [Avoiding Circular Imports](#avoiding-circular-imports)
7. [Examples](#examples)
8. [Common Pitfalls](#common-pitfalls)
9. [Related Documentation](#related-documentation)

## Overview

This guide explains advanced features of the ModelChecker for exploring logical theories, finding multiple models, and comparing different semantic frameworks. These tools are essential for researchers and developers working with complex logical theories and requiring detailed model analysis.

**Architecture Context**: For understanding how these tools fit into the complete system, see [Pipeline Architecture](../architecture/PIPELINE.md). For the iteration system's design, see [Iterate Architecture](../architecture/ITERATE.md).

## Using the Iterate Setting

The `iterate` setting allows you to find multiple semantically distinct models for a logical formula. This is useful for exploring the full space of possible models and understanding how different interpretations can satisfy the same logical constraints.

**Architecture Deep Dive**: For the complete design and implementation of the iteration system, including isomorphism detection and constraint strengthening, see [Iterate Architecture](../architecture/ITERATE.md).

### Basic Usage

In any theory's example file, add the `iterate` setting to request multiple models:

```python
# Example from logos theory
LOGOS_CM_1_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'max_time': 5,
    'iterate': 3,        # Find up to 3 distinct models total (including initial model)
    'expectation': True,
}
```

### How It Works

When `iterate` is set to a value greater than 1:

1. The system finds the first model normally
2. For each additional model, it:
   - Adds constraints ensuring the new model differs from previous ones
   - Searches for a structurally distinct solution
   - Displays differences between consecutive models

### Example Output

```bash
MODEL 1/3
========================================
EXAMPLE LOGOS_CM_1: there is a countermodel.
[First model details...]

Finding 3 models: [████████████████████] 2/3 (checked 4) 0.8s

MODEL 2/3
=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:
  w1 verifies A: True → False
  w2.s1 verifies B: False → True

State Changes:
  (w1, s2) exists: True → False

[Second model details...]

MODEL 3/3
=== DIFFERENCES FROM PREVIOUS MODEL ===
Part-of Changes:
  s1 ⊝ s3: True → False

Verification Changes:
  w2 verifies C: False → True

[Third model details...]

Found 3/3 distinct models.
```

### Theory-Specific Differences

Each theory defines what makes models "semantically distinct":

- **Logos Theory**: Different verification/falsification patterns, world structures, state configurations
- **Exclusion Theory**: Different exclusion relations between states, witness structures
- **Bimodal Theory**: Different temporal/modal accessibility relations
- **Imposition Theory**: Different imposition relations and counterfactual patterns

### Advanced Settings

The iteration system uses these internal controls:

```python
settings = {
    'iterate': 5,                    # Maximum models to find (including initial)
    'max_time': 30,                  # Overall timeout for the search
}
```

**Note**: The iteration system automatically handles isomorphism detection and constraint strengthening internally. No additional configuration is needed beyond the `iterate` setting.

## Comparing Multiple Theories

The ModelChecker framework enables systematic comparison of different semantic theories by running the same logical examples across multiple theories.

Theory comparison is essential for:
- **Research validation**: Testing how different semantic frameworks handle the same logical principles
- **Theoretical insights**: Understanding where theories agree and disagree
- **Framework development**: Ensuring new theories integrate properly with existing ones

**Architecture References**:
- [Theory Library Architecture](../architecture/THEORY_LIB.md) - How theories are organized and loaded
- [Builder Architecture](../architecture/BUILDER.md) - How multiple theories are coordinated during comparison

## Using the Maximize Flag

The maximize flag (`-m` or `--maximize`) enables a special comparison mode that tests the scalability of different semantic theories.

### What It Does

Instead of finding a single model, maximize mode:
1. Starts with the initial N (number of worlds) specified in settings
2. If a model is found within the time limit, increments N and tries again
3. Continues until the solver times out
4. Reports the maximum N each theory could handle

### Usage

```bash
model-checker -m examples_file.py
model-checker --maximize examples_file.py

# Or in the example file:
general_settings = {
    "maximize": True,
}
```

### Example Output

```
========================================
EXAMPLE = antecedent_strengthening
  Premises:
    NOT A
    (A BOXRIGHT C)
  Conclusions:
    ((A AND B) BOXRIGHT C)

ImpositionSemantics (Fine):
  RUN TIME = 0.23, MAX TIME = 5, N = 4.
  RUN TIME = 0.89, MAX TIME = 5, N = 5.
  RUN TIME = 3.45, MAX TIME = 5, N = 6.
ImpositionSemantics (Fine): TIMED OUT
  RUN TIME = 5.01, MAX TIME = 5, N = 7.

LogosSemantics (Brast-McKie):
  RUN TIME = 0.18, MAX TIME = 5, N = 4.
  RUN TIME = 0.52, MAX TIME = 5, N = 5.
  RUN TIME = 1.89, MAX TIME = 5, N = 6.
  RUN TIME = 4.21, MAX TIME = 5, N = 7.
LogosSemantics (Brast-McKie): TIMED OUT
  RUN TIME = 5.02, MAX TIME = 5, N = 8.
========================================
```

### Use Cases

1. **Performance Benchmarking**: Compare computational efficiency of theories
2. **Theory Development**: Test if optimizations improve scalability
3. **Research**: Empirically study complexity of different semantic frameworks
4. **Debugging**: Identify when theories struggle with larger models

## Debugging and Output Flags

### Project Creation with Subtheories

For the logos theory, you can select specific subtheories when creating projects:

```bash
# Create project with specific subtheories (default loads all)
model-checker -l logos --subtheory modal         # Modal logic only (+ dependencies)
model-checker -l logos --subtheory counterfactual constitutive  # Multiple
model-checker -l logos -st extensional           # Just extensional operators
```

### Essential Debugging Flags

```bash
# Show generated constraints
model-checker examples.py --print-constraints
model-checker examples.py -p  # Short form

# Show Z3 solver details
model-checker examples.py --print-z3
model-checker examples.py -z  # Short form

# Show impossible states
model-checker examples.py --print-impossible
model-checker examples.py -i  # Short form

# Combine all debug output
model-checker examples.py -p -z -i
```

### Understanding Debug Output

**Constraints Output** (`-p`):
- Shows the logical constraints generated from your formulas
- Useful for understanding how semantics translate to Z3
- Helps identify over-constraining issues

**Z3 Output** (`-z`):
- Displays the complete Z3 model when found
- Shows variable assignments and function definitions
- Essential for debugging unexpected results

**Impossible States** (`-i`):
- Lists states that cannot exist given the constraints
- Helps understand semantic restrictions
- Useful for verifying theory behavior

## Core Principles

### Import Order Matters

The key to avoiding circular imports is understanding Python's import mechanism and structuring imports carefully:

1. **Core components** (semantics, operators, propositions) should never import from theory_lib
2. **Theory implementations** can import from other theories for comparison
3. **Example files** are the proper place for cross-theory imports

```python
# GOOD: Import hierarchy
# 1. Core components (no theory imports)
# 2. Theory modules (can import from core)
# 3. Examples (can import from theories)

# BAD: Circular dependencies
# Core -> Theory -> Core (circular!)
```

### Theory Independence

Each theory should be independently functional:
- Can run standalone without importing other theories
- Defines its own semantic components completely
- Only imports other theories when explicit comparison is needed

### Translation Dictionaries

When comparing theories with different operator symbols, use translation dictionaries to map between notations:

```python
# Map operators from one theory to another
exclusion_to_logos = {
    # If operators differ, map them here
    "NOT": "\\neg",
    "AND": "\\wedge",
    "OR": "\\vee"
}
```

## Comparison Patterns

### Independent Theory Pattern (Exclusion)

The exclusion theory demonstrates comparing completely independent theories:

```python
# In exclusion/examples.py

# Import own theory components first
from .semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition
from .operators import witness_operators
from .semantic import WitnessStructure

# Import logos theory components for comparison
from model_checker.theory_lib.logos import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
    LogosOperatorRegistry,
)

# Create operator registry for logos
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['extensional'])  # Only load needed subtheories

# Define both theories
unilateral_theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}  # No translation needed within own theory
}

logos_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": logos_registry.get_operators(),
    "dictionary": exclusion_to_logos  # Translation dictionary if needed
}

# Enable comparison
semantic_theories = {
    "BernardChampollion": unilateral_theory,  # Exclusion theory
    "Brast-McKie": logos_theory,              # Logos for comparison
}
```

### Dependent Theory Pattern (Imposition)

The imposition theory demonstrates comparing a theory that extends another theory (in this case, logos):

```python
# In imposition/__init__.py
# Re-export logos components to avoid direct imports in semantic.py
from model_checker.theory_lib.logos import (
    LogosProposition as Proposition,
    LogosModelStructure as ModelStructure,
)

# In imposition/examples.py
from .semantic import ImpositionSemantics
from .operators import imposition_operators
from . import Proposition, ModelStructure  # Import via __init__.py

# Import logos for comparison
from model_checker.theory_lib.logos import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
    LogosOperatorRegistry,
)

# Since imposition extends logos, setup is simpler
imposition_theory = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,  # Actually LogosProposition
    "model": ModelStructure,     # Actually LogosModelStructure
    "operators": imposition_operators,
    "dictionary": {}
}

logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['modal', 'counterfactual'])

logos_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": logos_registry.get_operators(),
    "dictionary": {}  # No translation needed - same operators
}

semantic_theories = {
    "Fine": imposition_theory,
    "Brast-McKie": logos_theory,
}
```

## Implementation Guidelines

### Setting Up Comparisons

1. **Identify Shared Components**: Determine which components can be reused
2. **Plan Import Structure**: Design imports to avoid cycles
3. **Use __init__.py**: Re-export components to control import paths
4. **Test Incrementally**: Add one import at a time and test

### Avoiding Circular Imports

**DO:**
- Import comparison theories only in examples.py files
- Use relative imports within a theory
- Re-export through __init__.py to control access
- Keep core components independent

**DON'T:**
- Import theory_lib in core semantic classes
- Create mutual dependencies between theories
- Import examples.py from other modules
- Use star imports that might create hidden dependencies

### Testing Comparisons

Always test that comparisons work correctly:

```bash
# Test exclusion theory with logos comparison
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py

# Test imposition theory with logos comparison  
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py

# Run tests to ensure no import errors
./run_tests.py exclusion imposition

# Run specific comparison examples
model-checker src/model_checker/theory_lib/exclusion/examples.py
```

### Saving Comparison Results

When comparing theories, save outputs for analysis:

```bash
# Save comparison results as Markdown
model-checker comparison_examples.py --save markdown

# Save detailed JSON for programmatic analysis
model-checker comparison_examples.py --save json --verbose

# Generate notebook for interactive exploration
model-checker comparison_examples.py --save notebook

# Save all formats for comprehensive documentation
model-checker comparison_examples.py --save all --output-dir comparisons/
```

The output will organize results by theory, making it easy to compare:
```
output/
├── Logos_examples/
│   ├── TEST_1/
│   │   └── summary.md
│   └── TEST_2/
│       └── summary.md
├── Exclusion_examples/
│   ├── TEST_1/
│   │   └── summary.md
│   └── TEST_2/
│       └── summary.md
└── combined_output.md  # Side-by-side comparison
```

## Examples

### Basic Comparison Setup

Minimal setup for comparing two theories:

```python
# In my_theory/examples.py
from .semantic import MySemantics, MyProposition, MyModel
from .operators import my_operators

# Import theory to compare with
from model_checker.theory_lib.other_theory import (
    OtherSemantics,
    OtherProposition,
    OtherModel,
    other_operators,
)

my_theory = {
    "semantics": MySemantics,
    "proposition": MyProposition,
    "model": MyModel,
    "operators": my_operators,
    "dictionary": {}
}

other_theory = {
    "semantics": OtherSemantics,
    "proposition": OtherProposition,
    "model": OtherModel,
    "operators": other_operators,
    "dictionary": {}  # Add translations if operators differ
}

semantic_theories = {
    "MyTheory": my_theory,
    "OtherTheory": other_theory,
}
```

### Advanced Multi-Theory Comparison

Comparing multiple theories with different operator sets:

```python
# Define translation dictionaries
theory_a_to_logos = {
    "special_op": "\\Box",  # Map special_op to Box
}

theory_b_to_logos = {
    "custom_neg": "\\neg",  # Map custom_neg to standard negation
}

# Set up multiple theories
semantic_theories = {
    "TheoryA": theory_a,
    "TheoryB": theory_b,
    "Logos": logos_theory,  # Common comparison baseline
}
```

## Best Practices

### For Iterate
- Start with small iterate values (2-3) to understand the model space
- Use larger values only when exploring specific semantic phenomena
- Monitor performance as iterate values increase

### For Theory Comparison
- Ensure operator translations are semantically appropriate
- Test theories on standard examples first
- Document any unexpected behavioral differences

### For Maximize Mode
- Use consistent time limits across comparisons
- Run multiple examples to get a comprehensive view
- Consider both worst-case and average-case performance

## Common Pitfalls

1. **Circular Import at Module Level**
   ```python
   # BAD: In theory_a/semantic.py
   from model_checker.theory_lib.theory_b import SomeClass
   
   # GOOD: Only import in examples.py
   ```

2. **Importing Examples from Other Modules**
   ```python
   # BAD: In theory_a/tests/test_semantic.py
   from ..examples import semantic_theories
   
   # GOOD: Define test theories independently
   ```

3. **Missing Translation Dictionary**
   ```python
   # BAD: Different operators without translation
   theory_a_operators = {"AND": ...}
   theory_b_operators = {"\\wedge": ...}
   
   # GOOD: Include translation
   a_to_b = {"AND": "\\wedge"}
   ```

4. **Forgetting Operator Registry for Logos**
   ```python
   # BAD: Using logos operators directly
   "operators": logos_operators  # This might not exist

   # GOOD: Use registry
   logos_registry = LogosOperatorRegistry()
   logos_registry.load_subtheories(['modal'])
   "operators": logos_registry.get_operators()
   ```

5. **Misunderstanding iterate behavior**
   ```python
   # Iterate finds UP TO N models, not exactly N
   'iterate': 5  # May find 1-5 models depending on existence
   ```

## Related Documentation

### Usage Guides
- [Workflow Guide](WORKFLOW.md) - Complete usage patterns
- [Examples Guide](EXAMPLES.md) - Writing example files for comparisons
- [Output Guide](OUTPUT.md) - Saving and formatting comparison results
- [Constraints Testing](SEMANTICS.md) - Testing semantic properties

### Theory-Specific Guides
- [Exclusion Theory](../Code/src/model_checker/theory_lib/exclusion/README.md) - Unilateral semantics implementation
- [Imposition Theory](../Code/src/model_checker/theory_lib/imposition/README.md) - Fine's imposition semantics
- [Logos Theory](../Code/src/model_checker/theory_lib/logos/README.md) - Hyperintensional framework

### Framework Documentation
- [Theory Library Overview](../Code/src/model_checker/theory_lib/README.md) - Available theories and architecture
- [Contributing New Theories](../Code/src/model_checker/theory_lib/docs/CONTRIBUTING.md) - How to add new theories
- [Development Guide](../Code/docs/DEVELOPMENT.md) - General development workflow

### Technical References
- [Iterate Architecture](../architecture/ITERATE.md) - Complete iteration system design
- [Output Architecture](../architecture/OUTPUT.md) - How comparison results are generated
- [Builder Architecture](../architecture/BUILDER.md) - Pipeline coordination for comparisons
- [Theory Library Architecture](../architecture/THEORY_LIB.md) - Theory organization and management
- [Implementation Details](../../Code/src/model_checker/builder/README.md) - Code-level documentation

---

[← Back to Docs](../README.md) | [Workflow →](WORKFLOW.md) | [Getting Started →](../installation/GETTING_STARTED.md)