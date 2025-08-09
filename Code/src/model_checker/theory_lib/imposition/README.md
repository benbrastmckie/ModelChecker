# Imposition Theory: Kit Fine's Counterfactual Semantics

[← Back to Theories](../README.md) | [Documentation →](docs/README.md) | [API Reference →](docs/API_REFERENCE.md)

## Directory Structure

```
imposition/
├── README.md           # This file - theory overview
├── __init__.py         # Public API and theory registration
├── semantic.py         # ImpositionSemantics implementation
├── operators.py        # Counterfactual operators (▷, ◇▷)
├── examples.py         # 120 test examples
├── iterate.py          # Model iteration for counterfactuals
├── docs/               # Comprehensive documentation
├── notebooks/          # Interactive Jupyter examples
├── tests/              # Unit and integration tests
└── talk/               # Presentation materials
```

## Overview

### Notation

Throughout this documentation, we use the notation `a -->_w b` to represent the imposition relation, which should be read as:
- `a` is the state being imposed
- `w` is the world being imposed on (subscript)
- `b` is the resulting world
- Reading: "b is the result of imposing a on w"

For example, `□ -->_a b` means "b is the result of imposing the null state □ on world a".

### Introduction

The **Imposition Theory** implements Kit Fine's counterfactual semantics without possible worlds, using a primitive imposition relation within the ModelChecker framework. This theory evaluates counterfactuals through imposing verifier states on evaluation worlds to generate alternative outcomes. Within the theory library ecosystem, imposition extends the Logos hyperintensional foundation. This implementation serves researchers exploring counterfactual logic, developers building counterfactual reasoning systems, and students learning alternative approaches to conditional semantics beyond the traditional possible worlds framework.

## Core Components

### Semantic Framework

**ImpositionSemantics** extends the Logos semantics with:

- Imposition operation: `impose(state, world) → outcome`
- Alternative world calculation for counterfactuals
- Bilateral verification/falsification conditions
- Fine's frame constraints (inclusion, actuality, etc.)

### Operators

The theory provides **11 operators** total:

**Imposition-Specific** (2 operators):

- `\\boxright`: Must-counterfactual ("if A then must B")
- `\\diamondright`: Might-counterfactual ("if A then might B")

**Inherited from Logos** (9 operators):

| Category | Operator | Symbol | LaTeX | Description |
|----------|----------|--------|-------|-------------|
| **Extensional** | Negation | ¬ | `\\neg` | Truth reversal |
| **Extensional** | Conjunction | ∧ | `\\wedge` | Joint truth requirement |
| **Extensional** | Disjunction | ∨ | `\\vee` | Alternative truth |
| **Extensional** | Implication | → | `\\rightarrow` | Conditional truth |
| **Extensional** | Biconditional | ↔ | `\\leftrightarrow` | Mutual implication |
| **Extensional** | Top | ⊤ | `\\top` | Universal truth |
| **Extensional** | Bottom | ⊥ | `\\bot` | Universal falsity |
| **Modal** | Necessity | □ | `\\Box` | Truth at all worlds |
| **Modal** | Possibility | ◇ | `\\Diamond` | Truth at some world |

### Truth Conditions

The imposition semantics evaluates counterfactuals through a primitive imposition relation that connects states, worlds, and outcomes.

**Must-Counterfactual**: `A \\boxright B`

- **True at world w**: For all verifiers x of A and all outcome worlds u such that imposition(x, w, u) holds, B is true at u
- **False at world w**: There exists a verifier x of A and an outcome world u such that imposition(x, w, u) holds and B is false at u

In informal terms: "If A then must B" is true at a world when imposing any way of making A true on that world always results in B being true. It's false when there's at least one way of imposing A that results in B being false.

**Might-Counterfactual**: `A \\diamondright B` := `\\neg(A \\boxright \\neg B)`

- Defined as the dual of must-counterfactual
- True when it's not the case that imposing A must yield ¬B
- Informally: "If A then might B" is true when there's at least one way of imposing A that allows B to be true

## Subdirectories

### [docs/](docs/)

Comprehensive documentation suite including **user guide** with tutorial examples, **API reference** with complete function documentation, **architecture guide** explaining design patterns, **model iteration** documentation, and **settings guide** for configuration options. All documentation follows maintenance standards. See [docs/README.md](docs/README.md) for complete documentation navigation.

### [notebooks/](notebooks/)

Interactive Jupyter notebook collection demonstrating counterfactual reasoning with visualizations. Includes basic operator tutorials, model exploration notebooks, theory comparison examples, and debugging workflows. Designed for hands-on learning and experimentation. See [notebooks/README.md](notebooks/README.md) for notebook descriptions.

### [tests/](tests/)

Comprehensive test suite validating all 120 examples from examples.py. Includes unit tests for semantic primitives, integration tests for counterfactual operators, property-based testing for logical principles, and performance benchmarks. Tests ensure theoretical correctness and implementation reliability. See [tests/README.md](tests/README.md) for testing methodology.

## Advanced Features

### Model Iteration

The imposition theory supports finding multiple distinct models through the `iterate` setting. When enabled, the framework explores the semantic space of counterfactual structures, finding models that satisfy the same constraints while differing in their imposition patterns, verification conditions, or alternative world structures.

```python
# Find multiple models using the iterate setting
settings = {
    'N': 4,
    'iterate': 5,  # Find up to 5 distinct models
    'max_time': 2,
    # ... other settings
}
```

Each iteration generates a new model with different state assignments, imposition relations, or counterfactual truth values while maintaining the validity or invalidity of the target inference. This capability is particularly useful for exploring the flexibility of Fine's imposition semantics and understanding how different state configurations can satisfy the same counterfactual constraints. See [docs/ITERATE.md](docs/ITERATE.md) for comprehensive model iteration documentation.

### Theory Comparison

The imposition theory can be compared with other semantic theories in the ModelChecker framework, particularly with the Logos counterfactual semantics. Both theories evaluate counterfactuals but use different approaches:

- **Imposition**: Uses a primitive imposition relation to generate alternative worlds
- **Logos**: Uses alternative world-states based on possibility and parthood

To explore these differences, you can test the same counterfactual inferences in both theories using the `maximize` setting in general_settings or by loading multiple theories in the same example file. For comprehensive theory comparison capabilities, see the [Theory Library documentation](../README.md#comparing-theories).

## Documentation

### For New Users

- **[User Guide](docs/USER_GUIDE.md)** - Tutorial introduction to imposition semantics with step-by-step examples
- **[Examples](examples.py)** - Complete collection of validated examples
- **[Interactive Notebooks](notebooks/)** - Hands-on Jupyter tutorials with visualizations

### For Researchers

- **[Example Collection](examples.py)** - comprehensive counterfactual test cases
- **[Semantic Implementation](semantic.py)** - Fine's semantics implemented in Z3
- **[Academic References](#references)** - Primary sources and theoretical foundations

### For Developers

- **[API Reference](docs/API_REFERENCE.md)** - Complete function and class documentation
- **[Architecture Guide](docs/ARCHITECTURE.md)** - Design patterns and implementation details
- **[Test Suite](tests/)** - Comprehensive validation and testing methodology

## Key Insights

1. **State-Based Semantics**: Counterfactuals without possible worlds
2. **Imposition Operation**: Core semantic primitive for alternatives
3. **Bilateral Conditions**: Both verification and falsification matter
4. **Extends Logos**: Reuses hyperintensional infrastructure

## References

### Theory Documentation

- **[Documentation Hub](docs/README.md)** - Complete documentation index
- **[Theory Library](../README.md)** - All available theories
- **[Logos Theory](../logos/)** - Parent hyperintensional theory

### Academic References

- Fine, K. (2012). ["Counterfactuals without Possible Worlds"](https://doi.org/10.5840/jphil2012109312). _Journal of Philosophy_, 109(3), 221-246.
- Fine, K. (2012). ["A Difficulty for the Possible Worlds Analysis of Counterfactuals"](https://www.jstor.org/stable/41485149). _Synthese_, 189(1), 29-57.
- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.

---

[← Back to Theories](../README.md) | [Documentation →](docs/README.md) | [API Reference →](docs/API_REFERENCE.md)
