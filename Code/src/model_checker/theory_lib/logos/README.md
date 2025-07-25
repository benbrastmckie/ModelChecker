# Logos Theory: Unified Formal Language of Thought

[← Back to Theory Library](../README.md) | [Documentation →](docs/README.md) | [Subtheories →](subtheories/README.md)

## Directory Structure
```
logos/
├── README.md               # This file
├── __init__.py            # Theory initialization and interfaces
├── semantic.py            # Core semantic framework
├── operators.py           # Operator registry and loading
├── examples.py            # Cross-subtheory examples
├── iterate.py             # Model iteration functionality
├── docs/                  # Comprehensive documentation
├── notebooks/             # Interactive tutorials
├── tests/                 # Core theory tests
└── subtheories/           # Modular operator groups
    ├── extensional/       # Truth-functional operators
    ├── modal/            # Necessity and possibility
    ├── constitutive/     # Content relations
    ├── counterfactual/   # Counterfactual conditionals
    └── relevance/        # Relevance logic
```

## Overview

The **Logos Semantic Theory** provides a complete computational realization of **bilateral hyperintensional semantics**, implementing truthmaker semantics through a modular architecture with 20+ logical operators across 5 interoperable subtheories. This unified formal language of thought enables fine-grained semantic distinctions invisible to classical and intensional logic.

### Core Features
- **20+ logical operators** spanning extensional, modal, constitutive, counterfactual, and relevance domains
- **Modular subtheory system** with selective loading and automatic dependency resolution
- **Hyperintensional semantics** distinguishing content beyond logical equivalence  
- **Bilateral evaluation** using both verifiers and falsifiers for comprehensive semantic analysis

### Theoretical Foundation
Logos implements **truthmaker semantics** where propositions are evaluated at partial states rather than total possible worlds. This creates a **non-interlaced bilattice structure** enabling semantic distinctions between necessarily equivalent propositions based on their content and subject matter.

### Integration Context
As one of four semantic theories in the ModelChecker framework, Logos provides the most comprehensive operator coverage while maintaining clean modular architecture for selective feature loading and cross-theory comparative analysis.


## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load the theory (all subtheories by default)
theory = logos.get_theory()

# Check a formula
model = BuildExample("example", theory)
result = model.check_formula("\\Box p \\rightarrow p")
print(f"T axiom is {'valid' if result else 'invalid'}")

# Load specific subtheories
modal_theory = logos.get_theory(['extensional', 'modal'])
```

## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load complete theory (all 5 subtheories)
theory = logos.get_theory()
model = BuildExample("hyperintensional_test", theory)

# Test semantic distinction between equivalent formulas
result1 = model.check_formula("\\Box p \\rightarrow p")  # T axiom
result2 = model.check_formula("\\neg \\Diamond \\neg p \\rightarrow p")  # Equivalent
# Both valid but different hyperintensional content

# Selective subtheory loading
modal_theory = logos.get_theory(['extensional', 'modal'])
cf_theory = logos.get_theory(['extensional', 'counterfactual'])

# Cross-subtheory interaction
full_theory = logos.get_theory()  # All subtheories with dependencies
example = BuildExample("mixed_modal_cf", full_theory)
```

```bash
# Test complete theory with examples
./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# Generate new project template
./dev_cli.py -l logos my_hyperintensional_project

# Run comprehensive tests
./run_tests.py logos
```

## Files in This Directory

### README.md
This comprehensive theory overview documenting modular architecture, hyperintensional semantics implementation, and integration with the ModelChecker framework's 3-layer system.

### __init__.py
Theory registration interface providing `get_theory()` function with selective subtheory loading, dependency resolution, and operator registry management.

### semantic.py
Core semantic framework implementing bilateral hyperintensional semantics with verifier/falsifier evaluation, state space generation, and Z3 constraint integration.

### operators.py
Operator registry and loading system coordinating 20+ operators across all subtheories with consistent interface patterns and dependency management.

### examples.py
Cross-subtheory test examples demonstrating operator interactions, semantic principles, and comprehensive validation coverage across all logical domains.

### iterate.py
Model iteration functionality enabling multiple distinct model discovery with semantic difference constraints and theory-specific optimization patterns.

## Subdirectories

### [docs/](docs/README.md)
Comprehensive documentation hub with **user guides**, **technical architecture**, **API references**, and **configuration documentation** for complete theory understanding and practical usage.

### [subtheories/](subtheories/README.md)
Modular operator system with **5 specialized domains**: extensional (7 operators), modal (4 operators), constitutive (5 operators), counterfactual (4 operators), and relevance (1 operator). Each provides focused logical capabilities with clean interfaces.

### [notebooks/](notebooks/README.md)
Interactive tutorial collection with **hyperintensional semantics introduction**, **operator usage examples**, **advanced configuration**, and **research applications** for hands-on learning.

### [tests/](tests/README.md)
Comprehensive test suite with **unit tests**, **integration tests**, **cross-subtheory validation**, and **regression testing** ensuring semantic correctness and framework compatibility.

## Hyperintensional Semantics Architecture

### Bilateral Evaluation System

Logos implements **truthmaker semantics** where propositions are evaluated using both **verifiers** (states that make them true) and **falsifiers** (states that make them false). This creates a **non-interlaced bilattice structure** rather than classical Boolean logic:

```python
# Classical logic: necessarily equivalent propositions are identical
"2+2=4" ≡ "all bachelors are unmarried"  # Both necessarily true

# Hyperintensional logic: different content despite logical equivalence
logos_theory = get_theory("logos")
math_truth = model.evaluate_at_state("2+2=4", state_3)
analytic_truth = model.evaluate_at_state("all bachelors are unmarried", state_3)
# Different verifier/falsifier patterns despite both being necessary
```

### Partial State Evaluation

Unlike possible worlds semantics, hyperintensional evaluation occurs at **partial states** that may be incomplete:

```python
# Partial state s₁ might verify "p ∧ q" without verifying "p ∧ q ∧ r"
partial_state = {"atomic_props": ["p", "q"], "size": 2}
result = theory.evaluate("p \\wedge q", partial_state)  # True
result = theory.evaluate("p \\wedge q \\wedge r", partial_state)  # Undefined
```

### Semantic Distinction Examples

**Content Differences** between necessarily equivalent formulas:
- `"p ∧ q"` vs `"q ∧ p"`: Same verifiers, different syntactic content
- `"□p"` vs `"¬◇¬p"`: Equivalent but different modal content
- `"A ≡ B"` vs `"A ≤ B ∧ B ≤ A"`: Same truth conditions, different constitutive relations

**Subject Matter Sensitivity**:
```python
# Mathematical vs. logical content
formula1 = "2+2=4 \\rightarrow (p \\vee \\neg p)"
formula2 = "(q \\wedge \\neg q) \\rightarrow (p \\vee \\neg p)"
# Both valid, but different subject matter involvement
```

### Modular Architecture Benefits

**Selective Loading** for targeted analysis:
```python
# Modal reasoning only
modal_theory = logos.get_theory(['extensional', 'modal'])
result = model.check_formula("\\Box(p \\rightarrow q) \\rightarrow (\\Box p \\rightarrow \\Box q)")

# Counterfactual analysis  
cf_theory = logos.get_theory(['extensional', 'counterfactual'])
result = model.check_formula("(p \\boxright q) \\rightarrow \\neg(p \\boxright \\neg q)")

# Full hyperintensional system
full_theory = logos.get_theory()  # All 5 subtheories
```

**Automatic Dependency Resolution**:
```python
# Requesting 'modal' automatically includes 'extensional'
theory = logos.get_theory(['modal'])  # Loads extensional + modal

# Dependency chain: extensional → modal, constitutive → relevance
dependencies = logos.get_dependency_chain(['relevance'])
# Returns: ['extensional', 'constitutive', 'relevance']
```

## Documentation

### For New Users
- **[User Guide](docs/USER_GUIDE.md)** - Practical introduction to hyperintensional semantics and operator usage
- **[Interactive Notebooks](notebooks/README.md)** - Hands-on tutorials with executable examples and semantic explorations
- **[Quick Start Examples](examples.py)** - Ready-to-run code demonstrations across all subtheories

### For Researchers
- **[Architecture Guide](docs/ARCHITECTURE.md)** - Technical design, bilateral semantics implementation, and theoretical foundations
- **[API Reference](docs/API_REFERENCE.md)** - Complete function documentation with semantic specifications
- **[Academic References](#references)** - Primary literature on truthmaker semantics and hyperintensional logic

### For Developers
- **[Subtheory Development](subtheories/README.md)** - Modular operator system and extension patterns
- **[Test Documentation](tests/README.md)** - Comprehensive testing methodology and validation procedures
- **[Settings Configuration](docs/SETTINGS.md)** - Complete configuration options and theory-specific parameters



## References

### Implementation Documentation
- Logos theory implements bilateral hyperintensional semantics with 20+ operators across modular subtheories
- Semantic architecture documented with practical examples and theoretical foundations

### Related Resources
- **[Theory Library Overview](../README.md)** - Comparison across four semantic theories
- **[ModelChecker Framework](../../../README.md)** - Core framework documentation and 3-layer architecture
- **[Hyperintensional Semantics Guide](../../../../../Docs/HYPERINTENSIONAL.md)** - Comprehensive introduction to truthmaker semantics

### Academic References

**Primary Sources**:
- Brast-McKie (2025) ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic
- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic

**Theoretical Foundation**:
- Fine (2017) ["A Theory of Truthmaker Content I & II"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Wiley-Blackwell

---

[← Back to Theory Library](../README.md) | [Documentation →](docs/README.md) | [Subtheories →](subtheories/README.md)
