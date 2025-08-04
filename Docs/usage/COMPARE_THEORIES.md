# Theory Comparison Guide

[← Back to Docs](../README.md) | [Workflow →](WORKFLOW.md) | [Getting Started →](../installation/GETTING_STARTED.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Core Principles](#core-principles)
   - [Import Order Matters](#import-order-matters)
   - [Theory Independence](#theory-independence)
   - [Translation Dictionaries](#translation-dictionaries)
3. [Comparison Patterns](#comparison-patterns)
   - [Independent Theory Pattern](#independent-theory-pattern-exclusion)
   - [Dependent Theory Pattern](#dependent-theory-pattern-imposition)
4. [Implementation Guidelines](#implementation-guidelines)
   - [Setting Up Comparisons](#setting-up-comparisons)
   - [Avoiding Circular Imports](#avoiding-circular-imports)
   - [Testing Comparisons](#testing-comparisons)
5. [Examples](#examples)
   - [Basic Comparison Setup](#basic-comparison-setup)
   - [Advanced Multi-Theory Comparison](#advanced-multi-theory-comparison)
6. [Common Pitfalls](#common-pitfalls)
7. [Related Documentation](#related-documentation)

## Introduction

The ModelChecker framework enables systematic comparison of different semantic theories by running the same logical examples across multiple theories. This guide explains how to properly set up theory comparisons while avoiding circular dependencies.

Theory comparison is essential for:
- **Research validation**: Testing how different semantic frameworks handle the same logical principles
- **Theoretical insights**: Understanding where theories agree and disagree
- **Framework development**: Ensuring new theories integrate properly with existing ones

## Core Principles

### Import Order Matters

The key to avoiding circular imports is understanding Python's import mechanism and structuring imports carefully:

1. **Core components** (semantics, operators, propositions) should never import from theory_lib
2. **Theory implementations** can import from other theories for comparison
3. **Example files** are the proper place for cross-theory imports

```python
# ✓ GOOD: Import hierarchy
# 1. Core components (no theory imports)
# 2. Theory modules (can import from core)
# 3. Examples (can import from theories)

# ✗ BAD: Circular dependencies
# Core → Theory → Core (circular!)
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

## Related Documentation

### Theory-Specific Guides
- [Exclusion Theory](../Code/src/model_checker/theory_lib/exclusion/README.md) - Unilateral semantics implementation
- [Imposition Theory](../Code/src/model_checker/theory_lib/imposition/README.md) - Fine's imposition semantics
- [Logos Theory](../Code/src/model_checker/theory_lib/logos/README.md) - Hyperintensional framework

### Framework Documentation
- [Theory Library Overview](../Code/src/model_checker/theory_lib/README.md) - Available theories and architecture
- [Contributing New Theories](../Code/src/model_checker/theory_lib/docs/CONTRIBUTING.md) - How to add new theories
- [Development Guide](../Code/docs/DEVELOPMENT.md) - General development workflow

### Technical References
- [Builder Architecture](../Code/src/model_checker/builder/README.md) - How examples are built and executed
- [AI Assistant Guide](../Code/CLAUDE.md) - Development standards and practices

---

[← Back to Docs](../README.md) | [Workflow →](WORKFLOW.md) | [Getting Started →](../installation/GETTING_STARTED.md)