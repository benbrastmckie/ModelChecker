# Theory Library: Semantic Theory Collection

[← Back to ModelChecker API](../README.md) | [Usage Guide →](docs/USAGE_GUIDE.md) | [Contributing →](docs/CONTRIBUTING.md)

## Directory Structure

```
theory_lib/
├── README.md                    # This file - theory library overview
├── __init__.py                  # Theory registration and loading functions
├── docs/                        # Documentation hub (see docs/README.md)
│   ├── README.md                # Documentation navigation guide
│   ├── USAGE_GUIDE.md           # Practical usage patterns and examples
│   ├── CONTRIBUTING.md          # Theory implementation and contribution guide
│   └── THEORY_ARCHITECTURE.md   # Architecture patterns and design principles
├── tests/                       # Infrastructure tests (see tests/README.md)
├── logos/                       # Hyperintensional semantics (see logos/README.md)
├── exclusion/                   # Unilateral semantics (see exclusion/README.md)
├── imposition/                  # Fine's counterfactual semantics (see imposition/README.md)
└── bimodal/                     # Temporal-modal logic (see bimodal/README.md)
```

## Overview

The **Theory Library** provides a collection of computational semantic theories implemented using Z3 constraint solving, enabling automated verification of logical arguments and discovery of countermodels across different semantic frameworks.

The library supports **4 semantic theories** with over 25 logical operators, following a **modular architecture** that allows comparison between theories, extension with new implementations, and standardized testing procedures.

Each theory implements common interface patterns while preserving unique semantic characteristics, enabling researchers to explore different approaches to modal, counterfactual, and hyperintensional logic within a unified computational framework.

## Available Theories

The theory library provides four semantic theories implementing different approaches to modal, counterfactual, and hyperintensional logic. Each theory includes comprehensive documentation, test suites, and interactive notebooks.

### Logos Theory: Unified Hyperintensional Semantics

**Hyperintensional bilateral semantics** with 19+ operators organized into 5 modular subtheories for flexible semantic exploration.

**Documentation**: [logos/README.md](logos/README.md) | [Subtheories Guide](logos/subtheories/README.md) | [Interactive Notebooks](logos/notebooks/README.md)

**Theory Metadata**:
- **Author**: Benjamin Brast-McKie
- **Implementation**: Benjamin Brast-McKie, Miguel Buitrago
- **Architecture**: Modular (5 subtheories with selective loading)
- **Key Features**: Bilateral truthmaker semantics, selective subtheory loading, comprehensive operator coverage
- **Papers**:
  - Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). _Journal of Philosophical Logic_, 50, 1471-1503.
  - Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.
- **Usage**: `logos.get_theory(['extensional', 'modal'])` for selective subtheory loading

#### Logos Subtheories

##### 1. Extensional Subtheory

**Classical logical operators** (`¬`, `∧`, `∨`, `→`, `↔`, `⊤`, `⊥`) implemented with hyperintensional truthmaker semantics, enabling fine-grained content distinctions even for basic connectives.

**Documentation**: [logos/subtheories/extensional/README.md](logos/subtheories/extensional/README.md) | [Examples](logos/subtheories/extensional/examples.py) | [Notebooks](logos/subtheories/extensional/notebooks/README.md)

- **Operators**: 7 (3 primitive, 4 defined)
- **Examples**: 14 test cases
- **Key Feature**: Foundation for all other Logos subtheories

##### 2. Modal Subtheory

**Necessity and possibility operators** (`□`, `◇`, `CFBox`, `CFDiamond`) providing S5 modal logic within hyperintensional framework, distinguishing necessarily equivalent formulas by content.

**Documentation**: [logos/subtheories/modal/README.md](logos/subtheories/modal/README.md) | [Examples](logos/subtheories/modal/examples.py) | [Notebooks](logos/subtheories/modal/notebooks/README.md)

- **Operators**: 4 (1 primitive, 1 defined, 2 imported from counterfactual)
- **Examples**: 18 test cases
- **Key Feature**: Hyperintensional S5 modal logic with axiom validation

##### 3. Constitutive Subtheory

**Content relationship operators** (`≡`, `≤`, `⊑`, `⪯`, `⇒`) for identity, grounding, essence, relevance, and reduction, enabling fine-grained analysis of propositional content and dependencies.

**Documentation**: [logos/subtheories/constitutive/README.md](logos/subtheories/constitutive/README.md) | [Examples](logos/subtheories/constitutive/examples.py) | [Notebooks](logos/subtheories/constitutive/notebooks/README.md)

- **Operators**: 5 (4 primitive, 1 defined)
- **Examples**: 33 test cases
- **Key Feature**: Hyperintensional content relationships and grounding semantics
- **Primary Source**: Brast-McKie, B. (2021). "Identity and Aboutness"

##### 4. Counterfactual Subtheory

**Counterfactual conditionals** (`□→`, `◇→`) implementing alternative worlds semantics for would-counterfactuals and could-counterfactuals with non-monotonic reasoning.

**Documentation**: [logos/subtheories/counterfactual/README.md](logos/subtheories/counterfactual/README.md) | [Examples](logos/subtheories/counterfactual/examples.py) | [Notebooks](logos/subtheories/counterfactual/notebooks/README.md)

- **Operators**: 2 (1 primitive, 1 defined)
- **Examples**: 37 test cases
- **Key Feature**: Alternative worlds semantics without primitive imposition relations
- **Primary Source**: Brast-McKie, B. (2025). "Counterfactual Worlds"

##### 5. Relevance Subtheory

**Relevance operator** (`⪯`) imported from constitutive subtheory, providing content-sensitive relevance logic avoiding paradoxes of classical implication.

**Documentation**: [logos/subtheories/relevance/README.md](logos/subtheories/relevance/README.md) | [Examples](logos/subtheories/relevance/examples.py) | [Notebooks](logos/subtheories/relevance/notebooks/README.md)

- **Operators**: 1 (imported from constitutive)
- **Examples**: 20 test cases
- **Key Feature**: Relevance logic through fusion closure conditions

---

### Imposition Theory: Fine's Counterfactual Semantics

**Kit Fine's truthmaker semantics** for counterfactual reasoning using primitive imposition relations, providing an alternative approach to counterfactuals without possible worlds.

**Documentation**: [imposition/README.md](imposition/README.md) | [API Reference](imposition/docs/API_REFERENCE.md) | [Interactive Notebooks](imposition/notebooks/README.md)

**Theory Metadata**:
- **Author**: Kit Fine
- **Implementation**: Benjamin Brast-McKie
- **Operators**: 11 total (2 imposition-specific + 9 inherited from Logos)
- **Examples**: 120 test cases
- **Key Features**: Primitive imposition operation, bilateral conditions, extends Logos framework
- **Papers**:
  - Fine, K. (2012). ["Counterfactuals without Possible Worlds"](https://doi.org/10.5840/jphil2012109312). _Journal of Philosophy_, 109(3), 221-246.
  - Fine, K. (2012). ["A Difficulty for the Possible Worlds Analysis of Counterfactuals"](https://www.jstor.org/stable/41485149). _Synthese_, 189(1), 29-57.
- **Focus**: State-based counterfactual semantics through imposition relations

---

### Exclusion Theory: Unilateral Exclusion Semantics

**Unilateral semantics** implementing Bernard and Champollion's exclusion-based negation with witness predicate architecture, providing complete computational realization of unilateral truthmaker semantics.

**Documentation**: [exclusion/README.md](exclusion/README.md) | [Architecture Guide](exclusion/docs/ARCHITECTURE.md) | [Interactive Notebooks](exclusion/notebooks/README.md)

**Theory Metadata**:
- **Authors**: Lucas Champollion & Paul Bernard
- **Implementation**: Benjamin Brast-McKie, Miguel Buitrago
- **Operators**: 4 (`¬`, `∧`, `∨`, `≡`)
- **Examples**: 38 test cases (22 countermodels, 16 theorems)
- **Architecture**: Simple pattern with witness predicate innovations
- **Key Features**: Witness predicates for complex quantification, exclusion-based negation, verifiers without falsifiers
- **Paper**: Champollion, L., & Bernard, P. (2024). ["Negation and Modality in Unilateral Truthmaker Semantics"](https://doi.org/10.1007/s10988-023-09407-z). _Linguistics and Philosophy_.
- **Significance**: First complete computational realization of unilateral semantics
- **Success Rate**: 100% (38/38 examples)

---

### Bimodal Theory: Temporal-Modal Interaction (Under Development)

**Temporal-modal logic** combining tense operators with circumstantial modality through world history semantics for exploring complex temporal-modal interactions.

**Documentation**: [bimodal/README.md](bimodal/README.md) | [Settings Guide](bimodal/docs/SETTINGS.md)

**Theory Metadata**:
- **Author**: Benjamin Brast-McKie
- **Implementation**: Benjamin Brast-McKie
- **Operators**: 15 total (9 primitive, 6 defined) across 3 categories
- **Examples**: 22 test cases
- **Key Features**: World history semantics, temporal operators (`Future`, `Past`), modal operators (`□`, `◇`), time-shift relations
- **Focus**: Interaction between temporal and modal operators with lawful world histories
- **Status**: Under active development

**Note**: This theory is currently under development and may undergo significant changes. The bimodal semantics explores how temporal and modal operators interact when world histories evolve over time with lawful transitions between world states.

## Subdirectories

### [docs/](docs/README.md)

Comprehensive documentation hub with **usage guides**, **architecture documentation**, **contribution guidelines**, and **implementation patterns**. Organized for different user types from beginners implementing their first theory to researchers comparing semantic approaches.

### [tests/](tests/README.md)

Infrastructure testing suite covering **theory discovery**, **metadata management**, **cross-theory compatibility**, and **common functionality**. Complements theory-specific tests with framework-level validation.

**Important Testing Principle**: Each theory MUST include its own `tests/` directory with theory-specific tests, including verification that project generation works correctly. Infrastructure packages (`builder/`, `output/`, etc.) should maintain theory independence by using mock theories or parameterized tests rather than referencing specific theories by name.

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
- **[Examples Standard](../../docs/EXAMPLES.md)** - Standard form for examples.py files

## Theory Completeness Requirements

### Notebook Template Requirement

**All complete theories MUST provide a notebook template** for generating executable Jupyter notebooks from examples. This is a core requirement for theory completeness.

#### Template Location
`src/model_checker/theory_lib/{theory}/notebook_template.py`

#### Template Requirements
Each theory must provide a `NotebookTemplate` subclass that implements:
1. `get_imports()` - Returns list of import statements needed for the theory
2. `get_theory_setup(examples)` - Generates theory setup code based on examples
3. Optional: `format_example()` - Custom example formatting if needed

#### Example Template Structure
```python
from model_checker.theory_lib.base_template import NotebookTemplate

class MyTheoryNotebookTemplate(NotebookTemplate):
    def get_imports(self):
        return [
            "import sys",
            "from model_checker.jupyter import create_build_example",
            "from model_checker.theory_lib.mytheory.semantic import MySemantics",
            # ... other imports
        ]
    
    def get_theory_setup(self, examples):
        # Analyze examples if needed
        # Generate and return setup code
        return "theory = {...}"
```

See existing templates in logos/, exclusion/, and imposition/ for complete examples.

## References

### Implementation Documentation

- Theory library implements 4 semantic theories with standardized interfaces and modular architecture
- Cross-theory comparison enabled through unified constraint-solving infrastructure

### Related Resources

- **[ModelChecker API](../README.md)** - Core framework documentation and 3-layer architecture
- **[Builder Package](../builder/README.md)** - Model construction and theory coordination
- **[Settings Management](../settings/README.md)** - Configuration system and theory-specific parameters

## See Also

### Conceptual Documentation
- **[Hyperintensional Semantics](../../../../Docs/theory/HYPERINTENSIONAL.md)** - Truthmaker semantics concepts
- **[Theory References](../../../../Docs/theory/REFERENCES.md)** - Academic sources and background
- **[Z3 Background](../../../../Docs/theory/Z3_BACKGROUND.md)** - SMT solver foundations

### Technical Documentation
- **[Technical Architecture](../../../docs/ARCHITECTURE.md)** - Theory integration architecture
- **[Implementation Guide](../../../docs/IMPLEMENTATION.md)** - How to implement new theories
- **[Testing Guide](../../../docs/TESTS.md)** - Testing semantic theories

### Related Components
- **[Builder Package](../builder/README.md)** - Orchestrates theory execution
- **[Iterate Package](../iterate/README.md)** - Theory-specific iteration implementations
- **[Settings Package](../settings/README.md)** - Theory-specific configuration

---

[← Back to ModelChecker API](../README.md) | [Usage Guide →](docs/USAGE_GUIDE.md) | [Contributing →](docs/CONTRIBUTING.md)
