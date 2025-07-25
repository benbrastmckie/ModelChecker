# Relevance Subtheory: Content Relevance Operator

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure
```
relevance/
├── README.md               # This file - relevance subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (20 examples)
├── operators.py           # Relevance operator import (1 operator)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_relevance_examples.py  # Integration tests with 20 examples
```

## Overview

The **Relevance Subtheory** implements hyperintensional semantics for the relevance operator (⪯). All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond truth-functional equivalence or necessary equivalence.

Within the Logos framework, the relevance subtheory provides specialized exploration of relevance logic through the relevance operator, which is imported from the constitutive subtheory where it is defined alongside other content relationship operators. The relevance relation captures content relationships between propositions through fusion closure conditions on verifiers and falsifiers, enabling formal analysis of when propositions are appropriately connected by content. This subtheory's 20 carefully crafted examples demonstrate valid and invalid relevance principles while maintaining integration with all other hyperintensional operators.

## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load relevance subtheory (automatically loads constitutive and extensional)
theory = logos.get_theory(['relevance'])
model = BuildExample("relevance_example", theory)

# Test basic relevance principles
result1 = model.check_validity([], ["(A \\preceq A)"])  # Self-relevance
result2 = model.check_validity(["(A \\leq B)"], ["(A \\preceq B)"])  # Ground implies relevance
result3 = model.check_validity([], ["((A \\wedge B) \\preceq A)"])  # Invalid: antecedent strengthening

print(f"Self-relevance: {result1}")  # False (valid argument)
print(f"Ground implies relevance: {result2}")  # False (valid argument)  
print(f"Antecedent strengthening: {result3}")  # True (invalid argument)
```

## Subdirectories

### [tests/](tests/)
Comprehensive test suite with 20 integration examples focusing exclusively on the relevance operator. Includes countermodel examples (invalid relevance principles like antecedent strengthening, transitivity failure) and theorem examples (valid relevance principles like connections to grounding and essence). Tests demonstrate the hyperintensional nature of relevance logic. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users
- **[Quick Start](#quick-start)** - Basic relevance logic examples
- **[Operator Reference](#operator-reference)** - Complete guide to the relevance operator
- **[Testing Guide](tests/README.md)** - How to run and understand relevance tests

### For Researchers
- **[Theoretical Background](#theoretical-background)** - Fusion closure conditions and semantics
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid relevance patterns
- **[Integration](#integration)** - Connections with other hyperintensional operators

### For Developers
- **[Implementation Note](#implementation-note)** - Relevance operator import structure
- **[Examples Module](examples.py)** - Test cases and example formulas (20 examples)
- **[Integration Testing](tests/test_relevance_examples.py)** - Complete test implementation

## Theoretical Background

The relevance relation A � B (read as "A is relevant to B") is defined through two key conditions:

1. **Verifier Fusion Closure**: If x verifies A and y verifies B, then the fusion xy verifies B
2. **Falsifier Fusion Closure**: If x falsifies A and y falsifies B, then the fusion xy falsifies B

This captures the intuition that A is relevant to B when the content of A interacts appropriately with the content of B through state fusion operations.

The relevance relation is weaker than both grounding (d) and essence (�) relations, making it suitable for analyzing looser content connections between propositions.

## Operator

### Relevance Operator (�)

**Symbol**: `\\preceq`  
**Arity**: 2 (binary relation)  
**Name**: RelevanceOperator

The relevance operator implements the hyperintensional relevance relation where A � B means A is relevant to B.

**Truth Conditions**:
- A � B is true iff both verifier and falsifier fusion closure conditions hold
- A � B is false iff either fusion closure condition fails

**Extended Semantics**:
- Verified by the null state when the relevance relation holds
- Falsified by the null state when the relevance relation fails

## Example Categories

The relevance subtheory includes 20 carefully crafted examples divided into countermodels and theorems.

### Countermodel Examples

The countermodel examples (REL_CM_*) demonstrate where relevance principles fail:

| Example | Name | Description |
|---------|------|-------------|
| REL_CM_1 | ANTECEDENT STRENGTHENING | Tests whether (A ' B) � A |
| REL_CM_2 | ANTECEDENT WEAKENING | Tests whether (A ( B) � A |
| REL_CM_3 | RELEVANCE TRANSITIVITY | Tests whether A � B, B � C � A � C |
| REL_CM_4 | RELEVANT IMPLICATION: GROUND | Tests connection between relevance and grounding |
| REL_CM_5 | RELEVANT IMPLICATION: ESSENCE | Tests connection between relevance and essence |
| REL_CM_6 | RELEVANT IMPLICATION: IDENTITY | Tests connection between relevance and identity |
| REL_CM_7 | STRICT IMPLICATION | Tests whether �(A � B) � A � B |
| REL_CM_8 | REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION | Tests distributive properties |
| REL_CM_9 | REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION | Tests distributive properties |
| REL_CM_10 | CONJUNCTION INTRODUCTION | Tests whether A � B � A � (B ' C) |
| REL_CM_11 | DISJUNCTION INTRODUCTION | Tests whether A � B � A � (B ( C) |

### Theorem Examples

The theorem examples (REL_TH_*) demonstrate valid relevance principles:

| Example | Name | Description |
|---------|------|-------------|
| REL_TH_1 | RELEVANCE TO CONJUNCTION | Tests valid relevance to conjunction relations |
| REL_TH_2 | RELEVANCE TO DISJUNCTION | Tests valid relevance to disjunction relations |
| REL_TH_3 | CONJUNCTION TO RELEVANCE | Tests when conjunction implies relevance |
| REL_TH_4 | DISJUNCTION TO RELEVANCE | Tests when disjunction implies relevance |
| REL_TH_5 | CONJUNCTION INTRODUCTION | Tests valid conjunction introduction patterns |
| REL_TH_6 | DISJUNCTION INTRODUCTION | Tests valid disjunction introduction patterns |
| REL_TH_7 | GROUNDING RELEVANCE | Tests connections between grounding and relevance |
| REL_TH_8 | ESSENCE RELEVANCE | Tests connections between essence and relevance |
| REL_TH_9 | IDENTITY RELEVANCE | Tests connections between identity and relevance |

## Basic Usage

### Running Examples

From the command line:
```bash
# Run all relevance examples
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/relevance/examples.py

# Run specific examples by modifying the example_range in examples.py
```

### Example Structure

Each example follows the standard format:
```python
REL_CM_1_premises = []
REL_CM_1_conclusions = ['((A \\wedge B) \\preceq A)']
REL_CM_1_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
REL_CM_1_example = [REL_CM_1_premises, REL_CM_1_conclusions, REL_CM_1_settings]
```

### Integration with Other Operators

The relevance subtheory requires extensional operators (', (, �) and often works with constitutive operators (d, �, a). When used in the logos framework, dependencies are automatically loaded:

```python
# Relevance typically loads with constitutive dependencies
counterfactual_registry = LogosOperatorRegistry()
relevance_registry.load_subtheories(['extensional', 'constitutive', 'relevance'])
```

## Settings

The relevance subtheory uses standard logos settings with particular attention to:

| Setting | Typical Value | Purpose |
|---------|---------------|---------|
| `N` | 3-4 | Sufficient atomic states for relevance testing |
| `contingent` | True | Allows for non-trivial relevance relations |
| `non_null` | True | Prevents degenerate null-state-only verifiers |
| `non_empty` | True | Ensures meaningful proposition content |
| `disjoint` | False | Allows overlapping subject matters |
| `max_time` | 1-2 | Relevance examples typically solve quickly |

## Testing

The relevance subtheory includes **20 comprehensive test examples** covering relevance-sensitive logical principles through both countermodel and theorem examples. Tests validate content-based reasoning and demonstrate where classical logic fails in relevance-sensitive contexts.

```bash
# Run all relevance tests
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_CM_1"

# Run via project test runner
python test_theories.py --theories logos --relevance --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

### Verification Examples

The relevance examples serve as both documentation and tests:
- **Countermodel examples** verify that certain relevance inferences are invalid
- **Theorem examples** verify that certain relevance inferences are valid
- All examples include `expectation` settings for automated testing

## Integration

The relevance subtheory integrates seamlessly with:

1. **Extensional operators**: For basic logical operations within relevance formulas
2. **Constitutive operators**: For comparing relevance with grounding, essence, and identity
3. **Modal operators**: For analyzing relevance in modal contexts
4. **Counterfactual operators**: For studying relevance in counterfactual reasoning

### Dependency Chain

```
relevance � constitutive � extensional
```

This ensures that all necessary operators are available when working with relevance logic.

### Example Applications

The relevance subtheory is particularly useful for:

- Analyzing content relationships between propositions
- Testing logical principles in relevance logic
- Exploring connections between relevance and other hyperintensional relations
- Developing formal models of topic-sensitive reasoning
- Investigating the logical behavior of content-based inference patterns

The subtheory provides a solid foundation for formal work in relevance logic while maintaining integration with the broader logos semantic framework.

## Dependencies

The relevance subtheory depends on:
- **Constitutive subtheory**: Imports the `RelevanceOperator` from constitutive operators
- **Extensional subtheory**: Required by constitutive for basic logical operators

```python
# Automatic dependency loading
theory = logos.get_theory(['relevance'])  # Loads constitutive and extensional
```

## Testing

The relevance subtheory includes **20 comprehensive test examples** focusing exclusively on relevance logic principles through countermodel examples (invalid relevance inferences) and theorem examples (valid relevance principles).

```bash
# Run all relevance tests
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_CM_1"

# Run via project test runner
python test_theories.py --theories logos --relevance --examples
```

## References

### Primary Sources
- Anderson & Belnap (1975) ["Entailment: The Logic of Relevance and Necessity"](https://press.princeton.edu/books/hardcover/9780691072395/entailment-volume-i), Princeton University Press
- Dunn & Restall (2002) ["Relevance Logic"](https://plato.stanford.edu/entries/logic-relevance/), Stanford Encyclopedia of Philosophy
- Fine (2020) ["Truthmaker Semantics"](https://plato.stanford.edu/entries/truthmaker/), Stanford Encyclopedia of Philosophy

### Related Resources
- **[Constitutive Subtheory](../constitutive/)** - Where the relevance operator is defined
- **[Extensional Subtheory](../extensional/)** - Truth-functional foundation
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)