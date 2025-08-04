# Bimodal Theory Documentation Hub

Welcome to the comprehensive documentation for the Bimodal theory implementation in ModelChecker. This directory contains all technical documentation, guides, and references for understanding and using the bimodal temporal-modal logic framework.

## Quick Navigation

### Essential Documentation

- **[API Reference](API_REFERENCE.md)** - Complete API documentation for all classes, functions, and operators
- **[User Guide](USER_GUIDE.md)** - Practical guide for using bimodal logic with examples and patterns
- **[Architecture](ARCHITECTURE.md)** - Technical implementation details and design decisions
- **[Settings Reference](SETTINGS.md)** - Configuration options and performance tuning
- **[Model Iteration](ITERATE.md)** - Guide to finding multiple distinct models

### Getting Started

If you're new to the bimodal theory:

1. Start with the **[User Guide](USER_GUIDE.md)** for practical examples
2. Review the **[Settings Reference](SETTINGS.md)** to understand configuration
3. Explore **[API Reference](API_REFERENCE.md)** for detailed function documentation
4. For advanced usage, see **[Model Iteration](ITERATE.md)**

### For Developers

If you're extending or modifying the bimodal theory:

1. Read the **[Architecture Guide](ARCHITECTURE.md)** first
2. Review the **[API Reference](API_REFERENCE.md)** for integration points
3. Check **[Settings Reference](SETTINGS.md)** for adding new configuration options
4. See **[Model Iteration](ITERATE.md)** for iterator implementation details

## Documentation Overview

### API_REFERENCE.md
Complete reference for all public APIs including:
- Core functions (`get_theory()`, `get_examples()`)
- Classes (`BimodalSemantics`, `BimodalProposition`, `BimodalStructure`)
- Operators (temporal, modal, extensional)
- Model iteration functions
- Type definitions and constants

### USER_GUIDE.md
Practical guide covering:
- Basic usage patterns for temporal-modal reasoning
- Operator syntax and semantics
- Common formula patterns
- Troubleshooting tips
- Integration with ModelChecker

### ARCHITECTURE.md
Technical deep-dive including:
- World history semantics implementation
- Time interval management
- Task relation constraints
- Modal accessibility
- Performance optimizations

### SETTINGS.md
Configuration reference with:
- Core settings (N, M, max_time)
- Bimodal-specific settings (align_vertically)
- Performance impact analysis
- Example configurations

### ITERATE.md
Model iteration guide covering:
- Finding multiple models for formulas
- Difference detection algorithms
- Isomorphism checking
- Performance considerations

## Theory Overview

The bimodal theory combines temporal and modal operators to reason about:
- What is true at different **times** (temporal dimension)
- What is true in different **possible worlds** (modal dimension)
- How truth values evolve across world histories

Key innovations:
- World histories as sequences of states over time
- Time intervals with negative time support
- Sophisticated constraint generation for temporal-modal interactions
- Efficient model iteration with theory-specific optimizations

## Related Documentation

- **[Theory README](../README.md)** - Overview and quick start
- **[Examples](../examples.py)** - Extensive test cases with documentation
- **[Tests](../tests/)** - Unit and integration tests

## Contributing

When adding or modifying documentation:
1. Follow the structure defined in the [maintenance standards](../../../../../Docs/maintenance/README.md)
2. Use LaTeX notation (\\Box, \\Future) in code examples
3. Avoid emojis and Unicode in code
4. Test all code examples
5. Cross-reference related documentation

## Support

For questions or issues:
- Check the **[User Guide](USER_GUIDE.md)** troubleshooting section
- Review **[examples.py](../examples.py)** for working examples
- See the main **[ModelChecker documentation](../../../../README.md)**