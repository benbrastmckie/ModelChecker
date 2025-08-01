# Documentation Hub: Comprehensive Guide to Imposition Theory

[← Back to Theory](../README.md) | [API Reference →](API_REFERENCE.md) | [User Guide →](USER_GUIDE.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # Design and implementation 
├── ITERATE.md         # Model iteration for counterfactuals
├── README.md          # This file - documentation hub
├── SETTINGS.md        # Configuration parameters
└── USER_GUIDE.md      # Tutorial and introduction
```

## Overview

The **Documentation Hub** provides comprehensive resources for understanding and using Kit Fine's imposition theory within the ModelChecker framework. This collection covers technical references, architectural design, user tutorials, and configuration guides for counterfactual reasoning without possible worlds.

Within the imposition theory framework, this documentation explains how counterfactuals are evaluated through state imposition operations that generate alternative worlds. The theory implements Fine's innovative semantics where "if A then must B" is analyzed through imposing verifiers of A on evaluation worlds.

This hub serves developers, researchers, and students working with counterfactual logic, providing pathways to learn the theory, implement systems, and explore semantic models.

## Documentation

### Learning Path
1. **[User Guide](USER_GUIDE.md)** - Tutorial introduction to counterfactual reasoning
2. **[API Reference](API_REFERENCE.md)** - Complete technical reference
3. **[Settings](SETTINGS.md)** - Configuration parameters and options
4. **[Model Iteration](ITERATE.md)** - Finding multiple counterfactual models
5. **[Architecture](ARCHITECTURE.md)** - Design and implementation details

### Technical Reference
**[API Reference](API_REFERENCE.md)**
- Complete function and class documentation
- Operator specifications (11 total)
- Type definitions and settings
- 32 example test cases

### User Resources
**[User Guide](USER_GUIDE.md)**
- Tutorial introduction
- Common usage patterns
- Tips and troubleshooting
- Interactive examples

### Implementation Details
**[Architecture](ARCHITECTURE.md)**
- Design patterns and decisions
- Class hierarchy and integration
- Performance considerations
- Extension points

### Configuration
**[Settings](SETTINGS.md)**
- Model parameters (N, constraints)
- Solver configuration
- Iteration settings
- Theory-specific options

### Advanced Features
**[Model Iteration](ITERATE.md)**
- Finding multiple models
- Difference tracking
- Performance optimization
- Custom iteration strategies

## Key Concepts

### Semantic Framework

1. **State Imposition**: Core operation imposing states on worlds
2. **Alternative Worlds**: Outcomes of imposition operations
3. **Bilateral Semantics**: Verification and falsification conditions
4. **Hyperintensional Base**: Built on truthmaker semantics

### Operators

**Imposition Operators** (2):
- `\\boxright` (↪): Must-counterfactual
- `\\diamondright` (⟂): Might-counterfactual

**Inherited Operators** (9):
- Extensional: ¬, ∧, ∨, →, ↔, ⊤, ⊥
- Modal: □, ◇

### Truth Conditions

```python
# Must-counterfactual: A ↪ B
# Verified when imposing A-verifiers yields B-verifiers
# Falsified when imposing A-verifiers yields B-falsifiers

# Might-counterfactual: A ⟂ B := ¬(A ↪ ¬B)
# Possibility under imposition
```

## Usage Examples

### Basic Validity Testing
```python
# Test counterfactual modus ponens
example = BuildExample("cf_mp", theory,
    premises=['A', 'A \\boxright B'],
    conclusions=['B']
)
assert example.check_validity() == True
```

### Finding Countermodels
```python
# Antecedent strengthening (invalid)
counter = BuildExample("ant_str", theory,
    premises=['A \\boxright C'],
    conclusions=['(A \\wedge B) \\boxright C'],
    settings={'expectation': False}
)
counter.print_model()  # Shows countermodel
```

### Model Iteration
```python
from model_checker.theory_lib.imposition import iterate_example

models = iterate_example(example, max_iterations=5)
for model in models:
    model.print_model_differences()
```

## Documentation

### For Beginners
- **[User Guide](USER_GUIDE.md)** - Start here for tutorials
- **[Quick Start](#quick-start)** - Basic examples
- **[Key Concepts](#key-concepts)** - Core ideas

### For Developers
- **[API Reference](API_REFERENCE.md)** - Complete technical reference
- **[Architecture](ARCHITECTURE.md)** - Implementation details
- **[Settings](SETTINGS.md)** - Configuration options

### For Researchers
- **[Model Iteration](ITERATE.md)** - Exploring semantic space
- **[Truth Conditions](#truth-conditions)** - Formal semantics
- **[Examples](../examples.py)** - 32 test cases

## Navigation Guide

1. **New to counterfactuals?** → [User Guide](USER_GUIDE.md)
2. **Need API details?** → [API Reference](API_REFERENCE.md)
3. **Configuring models?** → [Settings](SETTINGS.md)
4. **Multiple models?** → [Model Iteration](ITERATE.md)
5. **Implementation?** → [Architecture](ARCHITECTURE.md)

## References

### Theory Resources
- **[Imposition Theory](../README.md)** - Main theory documentation
- **[Interactive Notebooks](../notebooks/)** - Jupyter examples
- **[Test Suite](../tests/)** - Validation tests

### Framework Resources
- **[Theory Library](../../README.md)** - All available theories
- **[Logos Theory](../../logos/)** - Parent hyperintensional theory
- **[ModelChecker](../../../../README.md)** - Main framework

---

[← Back to Theory](../README.md) | [API Reference →](API_REFERENCE.md) | [User Guide →](USER_GUIDE.md)