# LOGOS: A Unified Formal Language of Thought

The **Logos Semantic Theory** is a modular implementation of bilateral hyperintensional semantics, providing a unified and extensible formal language of thought. It implements truthmaker semantics with 20+ logical operators across multiple interoperable subtheories, enabling fine-grained semantic distinctions invisible to classical logic.

## Overview

The Logos theory provides:

- **20 logical operators** across 5 main subtheories
- **Modular architecture** for selective operator loading
- **Hyperintensional semantics** distinguishing content beyond logical equivalence
- **Dynamic theory composition** with automatic dependency resolution

For detailed documentation, see:

- **[User Guide](docs/USER_GUIDE.md)** - Practical usage and examples
- **[Architecture](docs/ARCHITECTURE.md)** - System design and implementation
- **[Settings Reference](docs/SETTINGS.md)** - Complete configuration options
- **[Documentation Hub](docs/README.md)** - All documentation resources

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

For installation and setup, see the [Installation Guide](../../../../docs/INSTALLATION.md).

## Subtheories

The Logos theory is organized into modular subtheories:

### [Extensional](subtheories/extensional/)

Truth-functional operators: ¬, ∧, ∨, →, ↔, ⊤, ⊥

### [Modal](subtheories/modal/)

Necessity and possibility: □, ◇, CFBox, CFDiamond

### [Constitutive](subtheories/constitutive/)

Content relationships: ≡, ≤, ⊑, ≼, ⇒

### [Counterfactual](subtheories/counterfactual/)

Hypothetical reasoning: □→, ◇→, imposition, could

### [Relevance](subtheories/relevance/)

Relevance logic: Additional operators for relevance-sensitive reasoning

Each subtheory includes its own documentation, examples, and tests.

## Key Features

### Hyperintensional Semantics

The Logos implements hyperintensional semantics where sentences are evaluated at partial states rather than total possible worlds. This allows the theory to distinguish between necessarily equivalent propositions based on their content. For instance, "2+2=4" and "all bachelors are unmarried" are both necessary truths, but they have different subject matters as witnessed by their different verifiers and falsifiers. The framework forms a non-interlaced bilattice rather than a Boolean lattice, enabling fine-grained semantic distinctions invisible to classical and intensional logics. See the [main theory documentation](../../../README.md#hyperintensional-semantics) and [Architecture Guide](docs/ARCHITECTURE.md#semantic-framework) for technical details.

### Modular Loading

Load only the operators you need:

```python
# Just modal logic
theory = logos.get_theory(['extensional', 'modal'])

# Everything except relevance
theory = logos.get_theory(['extensional', 'modal', 'constitutive', 'counterfactual'])
```

### Model Iteration

Find multiple distinct models:

```python
settings = {'N': 4, 'iterate': 5}
model = BuildExample("example", theory, settings=settings)
```

See [Model Iteration Documentation](docs/ITERATE.md) for advanced features.

## Documentation

### For New Users

- Start with the **[User Guide](docs/USER_GUIDE.md)**
- Explore **[Interactive Notebooks](notebooks/)**
- Review **[Settings Documentation](docs/SETTINGS.md)**

### For Researchers

- Read the **[Architecture Guide](docs/ARCHITECTURE.md)**
- Study **[Test Examples](tests/)**
- Review **[Academic References](#references)**

### For Developers

- See **[Contributing Guidelines](#contributing)**
- Review **[API Documentation](docs/README.md#api-reference)**
- Check **[Development Guide](../../../docs/DEVELOPMENT.md)**

## Testing

The Logos theory includes comprehensive tests:

```bash
# Run all tests
python test_theories.py --theories logos

# Run specific subtheory tests
python test_theories.py --theories logos --modal --examples

# Run unit tests
pytest src/model_checker/theory_lib/logos/tests/
```

See [Test Documentation](tests/README.md) for details.

## Contributing

We welcome contributions! Common tasks include:

- Adding new operators to existing subtheories
- Creating new subtheories
- Improving documentation
- Adding test cases

See the [Contributing Section](#contributing) below for detailed guidelines.

### Adding New Operators

1. Implement in appropriate subtheory's `operators.py`
2. Add to `get_operators()` function
3. Create test examples
4. Update documentation

### Creating New Subtheories

1. Create directory structure in `subtheories/`
2. Implement operators and examples
3. Register in `SUBTHEORY_INFO`
4. Add tests and documentation

For detailed instructions, see the [Architecture Guide](docs/ARCHITECTURE.md#extension-patterns).

## References

### Primary Sources

- Brast-McKie (2025) ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic
- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic

### Theoretical Foundation

- Fine (2017) ["A Theory of Truthmaker Content I & II"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Wiley-Blackwell

## Related Resources

- **[Exclusion Theory](../exclusion/)** - Unilateral semantics implementation
- **[Imposition Theory](../imposition/)** - Fine's counterfactual semantics
- **[ModelChecker Documentation](../../../README.md)** - Framework documentation

## License

Part of the ModelChecker package. See `LICENSE.md` for details.
