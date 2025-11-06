# Contracts: System Contracts and Guarantees

[← Back to Docs](../README.md) | [ITERATOR_CONTRACTS →](ITERATOR_CONTRACTS.md) | [THEORY_LICENSING →](THEORY_LICENSING.md)

## Directory Structure

```
contracts/
├── ITERATOR_CONTRACTS.md         # Iteration engine guarantees
└── THEORY_LICENSING.md            # Theory licensing patterns
```

## Overview

The contracts directory defines system-level contracts and guarantees that different ModelChecker components must uphold. Unlike implementation guidelines, these documents specify formal behavioral contracts - the "what must be true" rather than "how to implement."

These contracts serve two purposes: architectural contracts that define component responsibilities and interactions, and licensing patterns that govern theory distribution and usage. Understanding these contracts is essential for both implementing components correctly and creating distributable theory packages.

Consult these documents when implementing iteration logic or packaging theories for distribution.

## Documents

### ITERATOR_CONTRACTS.md
- **Purpose**: Define formal contracts for model iteration engine
- **Use When**: Implementing or modifying iteration logic
- **Key Sections**:
  - Iterator mode contracts (verification vs counterexample)
  - Model enumeration guarantees
  - Termination conditions
  - Performance guarantees
  - Theory-specific iteration contracts

### THEORY_LICENSING.md
- **Purpose**: Specify licensing patterns for theory packages
- **Use When**: Creating distributable theory packages or understanding licensing
- **Key Sections**:
  - Theory package licensing requirements
  - Code reuse and attribution
  - Distribution guidelines
  - License compatibility
  - Third-party theory integration

## Learning Path

**Understanding system contracts**:

1. **Iteration work**: [ITERATOR_CONTRACTS.md](ITERATOR_CONTRACTS.md) - Formal iteration guarantees
2. **Theory distribution**: [THEORY_LICENSING.md](THEORY_LICENSING.md) - Licensing requirements

## Quick Reference

### Common Tasks

- **Implementing iteration?** → ITERATOR_CONTRACTS.md defines required guarantees
- **Distributing theory?** → THEORY_LICENSING.md specifies licensing patterns
- **Understanding iteration modes?** → ITERATOR_CONTRACTS.md explains verification vs counterexample
- **Reusing code?** → THEORY_LICENSING.md covers attribution requirements

### Iterator Contracts Summary

From [ITERATOR_CONTRACTS.md](ITERATOR_CONTRACTS.md):

**Verification Mode**:
- Must find counterexample if formula is not valid
- Must confirm validity if no counterexample exists
- Must terminate (no infinite loops)

**Counterexample Mode**:
- Must enumerate all satisfying models up to N
- Must respect model size constraints
- Must avoid duplicate models

**Performance**:
- Must complete verification within reasonable time
- Must handle common theory patterns efficiently

### Theory Licensing Principles

From [THEORY_LICENSING.md](THEORY_LICENSING.md):

- Theory packages should specify clear license
- Code reuse requires proper attribution
- Distribution must include license file
- Third-party theories must respect compatibility

## References

### Related Documentation Categories
- [Core Architecture](../core/ARCHITECTURE.md) - System design context
- [Iterator Implementation](../specific/ITERATOR.md) - How to implement iteration
- [Package Structure](../specific/PACKAGES.md) - Theory package organization

### Implementation Resources
- [Iterator Standards](../specific/ITERATOR.md) - Implementation patterns for iteration
- [Package Organization](../specific/PACKAGES.md) - How to structure theory packages

### Testing Contracts
- [Testing Standards](../core/TESTING.md) - How to verify contract compliance

[← Back to Docs](../README.md) | [ITERATOR_CONTRACTS →](ITERATOR_CONTRACTS.md)
