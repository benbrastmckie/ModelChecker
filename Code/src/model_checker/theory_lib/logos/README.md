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

The theory's 118 test examples demonstrate valid and invalid inference patterns across extensional, modal, constitutive, counterfactual, and relevance domains, validating both individual operator behavior and cross-subtheory interactions.

## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load complete theory (all 5 subtheories, 19 operators)
theory = logos.get_theory()
model = BuildExample("hyperintensional_test", theory)

# Test basic modal logic principles
result1 = model.check_validity(      # T axiom: necessity implies truth
  ["\\Box A"],                       # Premises
  ["A"]                              # Conclusions
)
result2 = model.check_validity(      # Invalid: possibility doesn't imply necessity
  ["\\Diamond A"],                   # Premises
  ["\\Box A"]                        # Conclusions
)
result3 = model.check_validity(      # Hyperintensional distinction
  ["(A \\leftrightarrow B)"],         # Premises: logical equivalence
  ["(A \\equiv B)"]                   # Conclusions: propositional identity
)

print(f"T axiom: {result1}")         # No countermodel found (valid)
print(f"Possibility to necessity: {result2}")  # Countermodel found (invalid)
print(f"Equivalence to identity: {result3}")   # Countermodel found (invalid)

# Selective subtheory loading for focused analysis
modal_theory = logos.get_theory(['modal'])          # Loads extensional + modal
cf_theory = logos.get_theory(['counterfactual'])    # Loads extensional + counterfactual
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
# Run all 118 examples
model-checker src/model_checker/theory_lib/logos/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/examples.py

# Run specific subtheory examples
model-checker src/model_checker/theory_lib/logos/subtheories/modal/examples.py
```

#### Programmatic Access

```python
from model_checker.theory_lib.logos.examples import (
    test_example_range,     # All 118 examples
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

## Semantic Theory

### Bilateral Truthmaker Semantics

Logos implements Kit Fine's truthmaker semantics where propositions are characterized by:

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

## Integration

### Theory Loading

```python
# Complete theory
full_theory = logos.get_theory()

# Selective loading
modal_only = logos.get_theory(['modal'])  # Includes extensional dependency
relevance_focus = logos.get_theory(['relevance'])  # Includes constitutive + extensional

# Check dependencies
from model_checker.theory_lib.logos import SUBTHEORY_DEPENDENCIES
print(SUBTHEORY_DEPENDENCIES['modal'])  # ['extensional']
```

### Cross-Theory Comparison

```python
# Compare with other ModelChecker theories
from model_checker.theory_lib import logos, exclusion

logos_theory = logos.get_theory()
exclusion_theory = exclusion.get_theory()

# Test same formula in different theories
formula = "(A \\rightarrow (B \\rightarrow A))"
logos_result = BuildExample("logos_test", logos_theory).check_formula(formula)
exclusion_result = BuildExample("exclusion_test", exclusion_theory).check_formula(formula)
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
