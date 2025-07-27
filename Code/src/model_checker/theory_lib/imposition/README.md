# Imposition Theory: Kit Fine's Counterfactual Semantics

[← Back to Theories](../README.md) | [Documentation →](docs/README.md) | [API Reference →](docs/API_REFERENCE.md)

## Directory Structure

```
imposition/
├── README.md           # This file - theory overview
├── __init__.py         # Public API and theory registration
├── semantic.py         # ImpositionSemantics implementation
├── operators.py        # Counterfactual operators (▷, ◇▷)
├── examples.py         # 32 test examples
├── iterate.py          # Model iteration for counterfactuals
├── docs/               # Comprehensive documentation
├── notebooks/          # Interactive Jupyter examples
├── tests/              # Unit and integration tests
└── talk/               # Presentation materials
```

## Overview

The **Imposition Theory** implements Kit Fine's counterfactual semantics without possible worlds, using a primitive imposition relation within the ModelChecker framework. This theory evaluates counterfactuals through imposing verifier states on evaluation worlds to generate alternative outcomes. Within the theory library ecosystem, imposition extends the Logos hyperintensional foundation. This implementation serves researchers exploring counterfactual logic, developers building counterfactual reasoning systems, and students learning alternative approaches to conditional semantics beyond the traditional possible worlds framework.

```python
# Basic counterfactual reasoning
from model_checker.theory_lib.imposition import get_theory
from model_checker import BuildExample

# Test counterfactual modus ponens
theory = get_theory()
example = BuildExample("cf_mp", theory,
    premises=['A', 'A \\boxright B'],  # A is true, if A then must B
    conclusions=['B']                    # Therefore B
)

result = example.check_validity()
print(f"Valid: {result}")  # True

# Find countermodel to antecedent strengthening
counter = BuildExample("ant_str", theory,
    premises=['A \\boxright C'],
    conclusions=['(A \\wedge B) \\boxright C'],
    settings={'N': 3, 'expectation': False}
)
counter.print_model()  # Shows countermodel
```

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

- Extensional: ¬, ∧, ∨, →, ↔, ⊤, ⊥ (7 operators)
- Modal: □, ◇ (2 operators)

### Truth Conditions

**Must-Counterfactual**: `A \\boxright B`

- Verified by `x` when: Some part of `x` imposes A-verifiers on the evaluation world, yielding a world where B is verified
- Falsified by `x` when: Some part of `x` imposes A-verifiers on the evaluation world, yielding a world where B is falsified

**Might-Counterfactual**: `A \\diamondright B` := `\\neg(A \\boxright \\neg B)`

- Defined as the dual of must-counterfactual
- True when it's not the case that imposing A must yield ¬B

### Examples

The theory includes **32 comprehensive test examples**:

- **21 Countermodels**: Invalid counterfactual principles (antecedent strengthening, transitivity failures, etc.)
- **11 Theorems**: Valid counterfactual principles (modus ponens, contraposition, etc.)

## Settings

Key configuration options:

```python
settings = {
    'N': 3,               # Number of atomic states (2^N total states)
    'contingent': False,  # Require contingent propositions
    'non_empty': False,   # Prevent empty verifier/falsifier sets
    'disjoint': False,    # Require disjoint atomic propositions
    'max_time': 1,        # Z3 solver timeout in seconds
    'iterate': 1,         # Number of models to find
    'expectation': None   # Expected result (True/False/None)
}
```

See [docs/SETTINGS.md](docs/SETTINGS.md) for complete documentation.

## Subdirectories

### [docs/](docs/)

Comprehensive documentation suite including **user guide** with tutorial examples, **API reference** with complete function documentation, **architecture guide** explaining design patterns, **model iteration** documentation, and **settings guide** for configuration options. All documentation follows 9-section MAINTENANCE.md standards. See [docs/README.md](docs/README.md) for complete documentation navigation.

### [notebooks/](notebooks/)

Interactive Jupyter notebook collection demonstrating counterfactual reasoning with visualizations. Includes basic operator tutorials, model exploration notebooks, theory comparison examples, and debugging workflows. Designed for hands-on learning and experimentation. See [notebooks/README.md](notebooks/README.md) for notebook descriptions.

### [tests/](tests/)

Comprehensive test suite validating all 32 examples from examples.py. Includes unit tests for semantic primitives, integration tests for counterfactual operators, property-based testing for logical principles, and performance benchmarks. Tests ensure theoretical correctness and implementation reliability. See [tests/README.md](tests/README.md) for testing methodology.

## Advanced Features

### Model Iteration

Find multiple counterfactual models:

```python
from model_checker.theory_lib.imposition import iterate_example

# Find 5 different models
models = iterate_example(example, max_iterations=5)
for i, model in enumerate(models):
    print(f"\nModel {i+1}:")
    model.print_model_differences()
```

### Theory Comparison

Compare with other semantic theories:

```python
# Test same formula in different theories
from model_checker.theory_lib.logos import get_theory as get_logos

for theory_name, theory_func in [("Logos", get_logos), ("Imposition", get_theory)]:
    theory = theory_func()
    example = BuildExample(f"{theory_name}_test", theory, example_case)
    print(f"{theory_name}: {example.check_validity()}")
```

## Documentation

### For New Users

- **[User Guide](docs/USER_GUIDE.md)** - Tutorial introduction to imposition semantics with step-by-step examples
- **[Quick Start](#overview)** - Basic usage examples for counterfactual reasoning
- **[Interactive Notebooks](notebooks/)** - Hands-on Jupyter tutorials with visualizations

### For Researchers

- **[Example Collection](examples.py)** - 32 comprehensive counterfactual test cases
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
5. **32 Test Cases**: Comprehensive validation suite

## References

### Theory Documentation

- **[Documentation Hub](docs/README.md)** - Complete documentation index
- **[Theory Library](../README.md)** - All available theories
- **[Logos Theory](../logos/)** - Parent hyperintensional theory

### Academic References

- Fine, K. (2012). "Counterfactuals without Possible Worlds"
- Fine, K. (2017). "Truthmaker Semantics"
- ModelChecker framework documentation

---

[← Back to Theories](../README.md) | [Documentation →](docs/README.md) | [API Reference →](docs/API_REFERENCE.md)
