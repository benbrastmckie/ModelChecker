# Logos Theory: Unified Hyperintensional Semantic Framework

[← Back to Theory Library](../README.md) | [Documentation →](docs/README.md) | [Subtheories →](subtheories/README.md)

## Directory Structure

```
logos/
├── README.md               # This file - logos theory overview
├── __init__.py            # Theory initialization and public API
├── semantic.py            # Core hyperintensional semantic framework
├── operators.py           # Operator registry and loading system
├── examples.py            # Unified examples collection (177 examples)
├── iterate.py             # Model iteration functionality
├── docs/                  # Comprehensive documentation
│   ├── README.md          # Documentation hub and navigation
│   ├── API_REFERENCE.md   # Complete API documentation
│   ├── ARCHITECTURE.md    # Technical design and implementation
│   ├── ITERATE.md         # Model iteration guide
│   ├── SETTINGS.md        # Configuration options
│   └── USER_GUIDE.md      # Practical usage guide
├── notebooks/             # Interactive tutorials
│   └── README.md          # Notebook navigation guide
├── tests/                 # Core theory tests
│   ├── README.md          # Test documentation and methodology
│   ├── __init__.py        # Test module initialization
│   └── test_logos_examples.py  # Cross-subtheory integration tests
└── subtheories/           # Modular operator groups (see subtheories/README.md)
    ├── README.md          # Subtheory coordination and overview
    ├── extensional/       # Extensional operators (7 operators, 25 examples)
    ├── modal/            # Necessity and possibility (4 operators, 21 examples)
    ├── constitutive/     # Content relations (5 operators, 40 examples)
    ├── counterfactual/   # Counterfactual conditionals (2 operators, 74 examples)
    └── relevance/        # Relevance logic (1 operator, 17 examples)
```

## Overview

The **Logos Theory** implements hyperintensional semantics through a unified framework of 19 logical operators organized into 5 modular subtheories. Built on bilateral truthmaker semantics, Logos enables fine-grained semantic distinctions between propositions that are necessarily equivalent, capturing differences in content and subject-matter that intensional semantic frameworks overlook.

Within the ModelChecker framework, Logos serves as the most comprehensive semantic theory, providing a complete "formal language of thought" for analyzing logical relationships. The modular architecture allows selective loading of subtheories based on analysis needs, with automatic dependency resolution ensuring semantic coherence. This design supports both focused investigations using specific operators and comprehensive analyses leveraging the full hyperintensional framework.

The theory's examples demonstrate valid and invalid inference patterns across extensional, modal, constitutive, counterfactual, and relevance domains, validating both individual operator behavior and cross-subtheory interactions.

## Quick Start

```python
# Standard imports
import os
import sys

# Add current directory to path for imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import theory components
from model_checker.theory_lib import logos

# Option 1: Load complete theory (all subtheories)
full_theory = logos.get_theory()

# Option 2: Load specific subtheories for focused analysis
# Modal logic only (includes extensional as dependency)
modal_theory = logos.get_theory(['modal'])

# Counterfactual reasoning (includes extensional)
counterfactual_theory = logos.get_theory(['counterfactual'])

# Multiple subtheories
constitutive_theory = logos.get_theory(['modal', 'constitutive'])

# Define examples following naming convention
LOG_TH_1_premises = []
LOG_TH_1_conclusions = ["(\\neg \\neg A \\rightarrow A)"]
LOG_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
LOG_TH_1_example = [
    LOG_TH_1_premises,
    LOG_TH_1_conclusions,
    LOG_TH_1_settings,
]

MOD_TH_1_premises = ["\\Box A"]
MOD_TH_1_conclusions = ["A"]
MOD_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
MOD_TH_1_example = [
    MOD_TH_1_premises,
    MOD_TH_1_conclusions,
    MOD_TH_1_settings,
]

# Collection of all examples (used by test framework)
unit_tests = {
    "LOG_TH_1": LOG_TH_1_example,  # Double negation elimination
    "MOD_TH_1": MOD_TH_1_example,  # T-axiom theorem
}

# The framework expects this to be named 'example_range'
example_range = {
    "LOG_TH_1": LOG_TH_1_example,  # Run specific examples
    "MOD_TH_1": MOD_TH_1_example,
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

# Define semantic theories to use
# Can use full theory or selective subtheory loading
semantic_theories = {
    "modal_only": modal_theory,           # Just modal operators
    "full_logos": full_theory,            # All operators
    # "counterfactual": counterfactual_theory,  # Uncomment to add
}

# Make module executable
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
```

## Subdirectories

### [docs/](docs/)

Comprehensive documentation hub containing theoretical foundations, API specifications, and practical guides. Includes technical architecture details explaining the bilateral semantic implementation, complete API reference for all 19 operators, model iteration documentation, configuration settings guide, and user-friendly introduction to hyperintensional logic. Essential resource for understanding both theoretical principles and practical usage. See [docs/README.md](docs/README.md) for navigation.

### [subtheories/](subtheories/)

Modular operator organization with 5 specialized subtheories: extensional (extensional operators), modal (necessity and possibility), constitutive (content relations including ground, essence, and identity), counterfactual (conditional reasoning), and relevance (content-sensitive logic). Each subtheory includes comprehensive documentation, examples, and tests. Automatic dependency resolution ensures semantic coherence. See [subtheories/README.md](subtheories/README.md) for detailed operator coverage.

### [notebooks/](notebooks/)

Interactive Jupyter notebooks providing hands-on tutorials for hyperintensional reasoning. Includes theory introduction, operator exploration across all subtheories, semantic distinction demonstrations, and practical problem-solving examples. Ideal for learning through experimentation and visualization of semantic concepts. See [notebooks/README.md](notebooks/README.md) for tutorial navigation.

### [tests/](tests/)

Comprehensive test suite validating the unified Logos theory implementation. Contains cross-subtheory integration tests ensuring operators work correctly together, semantic coherence validation, and the complete 177-example test collection. Tests verify both individual operator behavior and complex interactions between subtheories. See [tests/README.md](tests/README.md) for testing methodology.

## Documentation

### For New Users

- **[User Guide](docs/USER_GUIDE.md)** - Introduction to hyperintensional semantics with practical examples
- **[Interactive Notebooks](notebooks/README.md)** - Hands-on tutorials for learning operator usage
- **[Quick Start Examples](#quick-start)** - Basic code patterns for common tasks

### For Researchers

- **[Architecture Guide](docs/ARCHITECTURE.md)** - Bilateral truthmaker semantics implementation
- **[Subtheory Documentation](subtheories/README.md)** - Detailed operator specifications and theory
- **[Academic References](#references)** - Primary sources on hyperintensional logic

### For Developers

- **[API Reference](docs/API_REFERENCE.md)** - Complete function and class documentation
- **[Test Documentation](tests/README.md)** - Testing methodology and example structure
- **[Settings Configuration](docs/SETTINGS.md)** - Model configuration and solver parameters

## Operator Summary

The Logos theory provides **19 operators** across **5 subtheories**:

### Primitive Operators (7)

**Extensional** (3):
- Negation (¬) - Truth reversal
- Conjunction (∧) - Joint truth requirement
- Top (⊤) - Universal truth

**Modal** (1):
- Necessity (□) - Truth at all worlds

**Constitutive** (3):
- Identity (≡) - Same verifiers and falsifiers
- Ground (≤) - Sufficient condition relation
- Relevance (≼) - Content connection relation

### Defined Operators (12)

**Extensional** (4):
- Disjunction (∨) - Alternative truth
- Implication (→) - Conditional truth
- Biconditional (↔) - Mutual implication
- Bottom (⊥) - Universal falsity

**Modal** (3):
- Possibility (◇) - Truth at some world
- Counterfactual Necessity (CFBox) - Counterfactual from ⊤
- Counterfactual Possibility (CFDiamond) - Might counterfactual from ⊤

**Constitutive** (2):
- Essence (⊑) - Necessary condition relation
- Subject Matter (⊓) - Common content

**Counterfactual** (2):
- Must Counterfactual (□→) - Would be the case
- Might Counterfactual (◇→) - Could be the case

**Relevance** (1):
- Relevance (≺) - Imported from constitutive

## Semantic Theory

### Bilateral Truthmaker Semantics

Logos implements a bilateral semantics where propositions are characterized by:

- **Verifiers**: States that make the proposition true
- **Falsifiers**: States that make the proposition false

This creates a non-Boolean algebraic structure enabling distinctions between:
- Logically equivalent propositions: `A ∧ B` vs `B ∧ A`
- Necessarily equivalent propositions: `□A` vs `¬◇¬A`
- Different grounding structures: `A` vs `A ∨ (B ∧ ¬B)`

### Key Innovations

1. **Hyperintensional Distinctions**: Captures content differences invisible to classical logic
2. **Modular Architecture**: Selective operator loading with automatic dependencies
3. **Cross-Domain Integration**: Unified treatment of modal, counterfactual, and relevance logic
4. **Bilateral Evaluation**: Both verification and falsification conditions

### Theoretical Applications

- Philosophy of language: Analyzing propositional content and aboutness
- Metaphysics: Grounding and essence relations
- Logic: Non-classical inference patterns and relevance logic
- AI/Cognitive Science: Formal models of thought and reasoning

## Examples

### Example Categories

The Logos theory includes **118 comprehensive examples** organized by subtheory:

- **Extensional**: 14 examples (7 countermodels, 7 theorems)
- **Modal**: 18 examples (4 countermodels, 14 theorems)
- **Constitutive**: 33 examples (18 countermodels, 15 theorems)
- **Counterfactual**: 33 examples (21 countermodels, 12 theorems)
- **Relevance**: 20 examples (11 countermodels, 9 theorems)

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/examples.py

# Run specific subtheory examples
model-checker src/model_checker/theory_lib/logos/subtheories/modal/examples.py
```

#### Programmatic Access

```python
from model_checker.theory_lib.logos.examples import (
    test_example_range,     # All examples
    logos_cm_examples,      # All countermodel examples
    logos_th_examples       # All theorem examples
)

# Access specific example
example = test_example_range['MOD_TH_5']  # Modal K axiom
premises, conclusions, settings = example

# Run with custom settings
from model_checker import BuildExample
model = BuildExample("test", logos.get_theory())
result = model.check_validity(premises, conclusions, settings)
```

## Testing

The Logos theory includes comprehensive testing across multiple levels:

```bash
# Run all Logos tests
pytest src/model_checker/theory_lib/logos/tests/

# Run subtheory tests
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/

# Integration testing
python test_theories.py --theories logos --examples

# Specific example testing
python test_theories.py --theories logos --examples MOD_TH_5 CON_CM_1
```

## References

### Primary Sources

- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.
- Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). _Journal of Philosophical Logic_, 50, 1471-1503.

### Theoretical Foundations

- Fine, K. (2017). ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y). _Journal of Philosophical Logic_, 46, 625-674.
- Fine, K. (2017). ["A Theory of Truthmaker Content II: Subject-matter, Common Content, Remainder and Ground"](https://link.springer.com/article/10.1007/s10992-016-9423-1). _Journal of Philosophical Logic_, 46, 675-702.
- Fine, K. (2017). ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22). In _A Companion to the Philosophy of Language_ (2nd ed.). Wiley-Blackwell.

### Related Resources

- **[Theory Library Overview](../README.md)** - Comparison of ModelChecker's four semantic theories
- **[Hyperintensional Semantics Guide](../../../../../Docs/HYPERINTENSIONAL.md)** - Introduction to truthmaker semantics
- **[ModelChecker Architecture](../../../README.md)** - Core framework design and capabilities

---

[← Back to Theory Library](../README.md) | [Documentation →](docs/README.md) | [Subtheories →](subtheories/README.md)
