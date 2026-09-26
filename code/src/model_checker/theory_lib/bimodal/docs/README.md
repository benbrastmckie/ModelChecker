# Bimodal Theory Documentation Hub

Welcome to the comprehensive documentation for the Bimodal theory implementation in ModelChecker. This directory contains all technical documentation, guides, and references for understanding and using the bimodal temporal-modal logic framework.

## Quick Navigation

### Essential Documentation

- **[API Reference](API_REFERENCE.md)** - Complete API documentation for all classes, functions, and operators
- **[User Guide](USER_GUIDE.md)** - Practical guide for using bimodal logic with examples and patterns
- **[Architecture](ARCHITECTURE.md)** - Technical implementation details and design decisions
- **[Settings Reference](SETTINGS.md)** - Configuration options and performance tuning
- **[Model Iteration](ITERATE.md)** - Guide to finding multiple distinct models
- **[Adequacy](ADEQUACY.md)** - States and proves the soundness correspondence between the
  witness-family certificate design (implemented in `semantic/`) and the paper's task semantics;
  states the open adequacy (converse) direction without asserting it. Never a validity claim.

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
- The witness-family certificate search and the quantifier-free variable layer
- The two-phase constraint emission and the independent re-check (obligation S3)
- The (SOUND) theorem, its four lemmas, and the Lean citation table
- Why the design is ℤ-time only, and the retired designs it replaced

### SETTINGS.md
Configuration reference with:
- Core settings (`back`, `mid`, `fwd`, `max_witnesses`, `max_time`)
- Why there is no bimodal-specific general (display) setting any more
- Example configurations

### ITERATE.md
Model iteration guide covering:
- Finding multiple certificates for formulas via label/guess blocking clauses
- Rotation/permutation-invariant isomorphism detection and orbit exclusion
  (`semantic/symmetry.py`'s shared group definition)
- The three shared-iterator extension points this theory's live `iterate: N > 1` path relies on

### ADEQUACY.md
The soundness correspondence between certificates and the paper's task semantics:
- The certificate definition and its four conditions
- The (SOUND) statement, its full proof, and the Lean citation table
- The proved re-check windows and the presentation/re-verification protocol
- The (ADEQ) direction, recorded as open with its deciding tests named

## Theory Overview

The bimodal theory combines temporal and modal operators to reason about:
- What is true at different **times** (temporal dimension, discrete ℤ)
- What is true in different **possible worlds** (modal dimension, certified histories)
- How truth values evolve across world histories

Key design points:
- A countermodel is a finite, checkable **witness-family certificate** — a box guess plus a
  small family of labelled bi-infinite lassos — not a fixed finite frame
- The certificate denotes an infinite **certified `ShiftSet` model** by construction; Box ranges
  over exactly the certified histories
- The Z3 search is fully quantifier-free: no `ForAll`/`Exists`, no MBQI, no E-matching pattern
- Every found certificate is independently re-checked by a pure-Python checker before being
  reported, and can be round-tripped through BimodalLogic's own `lake exe check_certificate`
- Validity is never reported — only "a certificate was/was not found within the configured
  bounds"

## Related Documentation

- **[Theory README](../README.md)** - Overview and quick start
- **[Examples](../examples.py)** - Extensive test cases with documentation
- **[Tests](../tests/)** - Unit and integration tests

## Contributing

When adding or modifying documentation:
1. Follow the structure defined in the [documentation standards](../../../../../code/docs/standards/README.md)
2. Use LaTeX notation (\\Box, \\Future) in code examples
3. Avoid emojis and Unicode in code
4. Test all code examples
5. Cross-reference related documentation

## Support

For questions or issues:
- Check the **[User Guide](USER_GUIDE.md)** troubleshooting section
- Review **[examples.py](../examples.py)** for working examples
- See the main **[ModelChecker documentation](../../../../README.md)**