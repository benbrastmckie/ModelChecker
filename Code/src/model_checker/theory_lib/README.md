# Theory Library: Semantic Theory Collection

[← Back to ModelChecker API](../README.md) | [Usage Guide →](docs/USAGE_GUIDE.md) | [Contributing →](docs/CONTRIBUTING.md)

## Directory Structure
```
theory_lib/
├── README.md               # This file - theory library overview
├── __init__.py            # Theory registration and loading functions
├── docs/                  # Documentation hub (see docs/README.md)
│   ├── README.md          # Documentation navigation guide
│   ├── USAGE_GUIDE.md     # Practical usage patterns and examples
│   ├── CONTRIBUTING.md    # Theory implementation and contribution guide
│   └── THEORY_ARCHITECTURE.md # Architecture patterns and design principles
├── tests/                 # Infrastructure tests (see tests/README.md)
├── logos/                 # Hyperintensional semantics (see logos/README.md)
├── exclusion/             # Unilateral semantics (see exclusion/README.md)
├── imposition/            # Fine's counterfactual semantics (see imposition/README.md)
└── bimodal/               # Temporal-modal logic (see bimodal/README.md)
```

## Overview

The **Theory Library** provides a collection of computational semantic theories implemented using Z3 constraint solving, enabling automated verification of logical arguments and discovery of countermodels across different semantic frameworks.

The library supports **4 semantic theories** with over 25 logical operators, following a **modular architecture** that allows comparison between theories, extension with new implementations, and standardized testing procedures.

Each theory implements common interface patterns while preserving unique semantic characteristics, enabling researchers to explore different approaches to modal, counterfactual, and hyperintensional logic within a unified computational framework.

## Quick Start

```python
from model_checker import get_theory, check_formula, BuildExample

# Basic formula checking across theories
formula = "\\neg \\neg p \\rightarrow p"  # Double negation elimination
theories = ["logos", "exclusion", "imposition", "bimodal"]

for theory_name in theories:
    result = check_formula(formula, theory_name=theory_name)
    print(f"{theory_name}: {'Valid' if result else 'Invalid'}")

# Theory-specific usage
theory = get_theory("logos")
model = BuildExample("modal_test", theory)
result = model.check_formula("\\Box p \\rightarrow p")  # T axiom
print(f"T axiom: {'valid' if result else 'invalid'}")

# Selective subtheory loading (for modular theories)
from model_checker.theory_lib import logos
modal_theory = logos.get_theory(['extensional', 'modal'])
```

## Available Theories

### Architecture Patterns

The ModelChecker supports two primary theory architectures optimized for different semantic complexity levels:

**Simple Pattern** (focused theories): Single-file operator implementations for theories with cohesive operator sets
**Modular Pattern** (complex theories): Subtheory organization for theories with large, categorizable operator collections

### Logos Theory (Modular Pattern)
**Hyperintensional bilateral semantics** with 20+ operators across 5 subtheories

- **Author**: Benjamin Brast-McKie
- **Architecture**: Modular (5 subtheories: extensional, modal, constitutive, counterfactual, relevance)
- **Key Features**: Truthmaker semantics, selective subtheory loading, comprehensive operator coverage
- **Papers**: Brast-McKie (2021, 2025) on identity, aboutness, and counterfactual worlds
- **Usage**: `logos.get_theory(['extensional', 'modal'])` for selective loading

More information: [logos/README.md](logos/README.md) | [Interactive Notebooks](logos/notebooks/README.md)

### Exclusion Theory (Simple Pattern)
**Unilateral semantics** with witness-based exclusion operations

- **Authors**: Lucas Champollion & Paul Bernard (theory), Miguel Buitrago & Benjamin Brast-McKie (implementation)
- **Architecture**: Simple (4 operators in unified implementation)
- **Key Features**: Witness predicates, exclusion-based negation, architectural innovations
- **Paper**: Bernard & Champollion "Exclusion Counterfactuals"
- **Significance**: Complete computational realization of unilateral semantics

More information: [exclusion/README.md](exclusion/README.md) | [Interactive Notebooks](exclusion/notebooks/README.md)

### Imposition Theory
**Fine's truthmaker semantics** for counterfactual reasoning

- **Author**: Kit Fine (theory), Benjamin Brast-McKie (implementation)
- **Key Features**: Imposition operator, could operator, distinctive counterfactual approach
- **Papers**: Fine (2012) on counterfactuals without possible worlds, truth-conditional content
- **Focus**: Alternative approach to counterfactual semantics through truthmaker framework

More information: [imposition/README.md](imposition/README.md) | [Interactive Notebooks](imposition/notebooks/README.md)

### Bimodal Theory
**Temporal-modal interaction** with world history semantics

- **Author**: Benjamin Brast-McKie
- **Key Features**: Tense and circumstantial modality interaction, world history semantics
- **Focus**: Complex interactions between temporal and modal operators
- **Applications**: Temporal logic with modal embedding

More information: [bimodal/README.md](bimodal/README.md) | [Documentation](bimodal/docs/README.md)

## Subdirectories

### [docs/](docs/README.md)
Comprehensive documentation hub with **usage guides**, **architecture documentation**, **contribution guidelines**, and **implementation patterns**. Organized for different user types from beginners implementing their first theory to researchers comparing semantic approaches.

### [tests/](tests/README.md)
Infrastructure testing suite covering **theory discovery**, **metadata management**, **cross-theory compatibility**, and **common functionality**. Complements theory-specific tests with framework-level validation.

### Individual Theory Directories
Each theory directory contains **complete implementations** with semantic classes, operators, examples, comprehensive documentation, test suites, and interactive Jupyter notebooks for hands-on exploration.

## Documentation

### For New Users
- **[Usage Guide](docs/USAGE_GUIDE.md)** - Import strategies, basic examples, and configuration patterns
- **[Individual Theory READMEs](logos/README.md)** - Theory-specific documentation and quick start guides
- **[Interactive Notebooks](logos/notebooks/README.md)** - Hands-on tutorials and explorations

### For Researchers
- **[Theory Architecture Guide](docs/THEORY_ARCHITECTURE.md)** - Simple vs Modular patterns and design principles
- **[Comparison Examples](docs/USAGE_GUIDE.md#comparing-theories)** - Cross-theory analysis and formula testing
- **[Academic References](#references)** - Primary literature and theoretical foundations

### For Developers
- **[Contributing Guide](docs/CONTRIBUTING.md)** - Complete implementation workflow and requirements
- **[Testing Framework](tests/README.md#theory-testing-framework-guide)** - Comprehensive testing patterns
- **[API Integration](../README.md)** - Framework-level interfaces and coordination

## References

### Implementation Documentation
- Theory library implements 4 semantic theories with standardized interfaces and modular architecture
- Cross-theory comparison enabled through unified constraint-solving infrastructure

### Related Resources
- **[ModelChecker API](../README.md)** - Core framework documentation and 3-layer architecture
- **[Builder Package](../builder/README.md)** - Model construction and theory coordination
- **[Settings Management](../settings/README.md)** - Configuration system and theory-specific parameters

---

[← Back to ModelChecker API](../README.md) | [Usage Guide →](docs/USAGE_GUIDE.md) | [Contributing →](docs/CONTRIBUTING.md)