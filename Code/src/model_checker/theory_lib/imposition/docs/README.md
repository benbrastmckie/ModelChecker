# Imposition Theory Documentation Hub

Welcome to the comprehensive documentation for Kit Fine's imposition theory implementation in ModelChecker. This hub provides complete documentation for understanding, using, and extending the imposition theory.

## Overview

The imposition theory implements Kit Fine's distinctive counterfactual semantics through the imposition operation, which imposes a state upon a world to create alternative worlds. This approach enables sophisticated counterfactual reasoning within a hyperintensional framework.

## Documentation Index

### Core Documentation

- **[API Reference](API_REFERENCE.md)** - Complete API documentation for all classes, functions, and operators
- **[User Guide](USER_GUIDE.md)** - Practical guide for using imposition theory in your projects
- **[Architecture](ARCHITECTURE.md)** - Technical implementation details and design decisions
- **[Settings Guide](SETTINGS.md)** - Configuration options and their effects
- **[Model Iteration](ITERATE.md)** - Finding and exploring multiple models

### Quick Links

- **Getting Started**: See the [User Guide](USER_GUIDE.md) for basic usage
- **Available Operators**: Check the [API Reference](API_REFERENCE.md#operators) for operator list
- **Example Formulas**: Browse [examples.py](../examples.py) for working examples
- **Configuration**: See [Settings Guide](SETTINGS.md) for all options

## Getting Started

If you're new to the imposition theory, we recommend reading the documentation in this order:

1. **[User Guide](USER_GUIDE.md)** - Learn the basics and common usage patterns
2. **[API Reference](API_REFERENCE.md)** - Understand the available functions and classes
3. **[Settings Guide](SETTINGS.md)** - Configure the theory for your needs
4. **[Model Iteration](ITERATE.md)** - Explore multiple models for formulas
5. **[Architecture](ARCHITECTURE.md)** - Dive into implementation details

## Key Concepts

The imposition theory introduces several distinctive concepts:

- **Imposition Operation**: The core semantic operation that imposes states on worlds
- **Alternative Worlds**: Worlds generated through the imposition operation
- **Verifiers and Falsifiers**: States that make propositions true or false
- **Counterfactual Operators**: `\\imposition` (must) and `\\could` (might)

## Related Documentation

- **[Theory Library](../../README.md)** - Overview of all available theories
- **[Logos Theory](../../logos/docs/README.md)** - Parent theory with hyperintensional semantics
- **[ModelChecker Guide](../../../../README.md)** - Main framework documentation

## Contributing

When contributing to the imposition theory documentation:

1. Use LaTeX notation in all code examples (e.g., `\\imposition`, not Unicode)
2. Test all code examples before documenting them
3. Cross-reference related documentation
4. Follow the style guide in [MAINTENANCE.md](../../../../../MAINTENANCE.md)

## Questions?

If you have questions about the imposition theory:

1. Check the [User Guide](USER_GUIDE.md) for common usage patterns
2. Review the [API Reference](API_REFERENCE.md) for detailed function documentation
3. See the [Architecture](ARCHITECTURE.md) for implementation questions
4. Explore the [examples](../examples.py) for working code