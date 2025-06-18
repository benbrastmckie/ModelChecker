# Relevance Logic Subtheory

The relevance subtheory implements relevance logic within the logos semantic framework. This subtheory focuses on the relevance relation between propositions, providing a hyperintensional account of when one proposition is relevant to another.

## Table of Contents

- [Overview](#overview)
- [Theoretical Background](#theoretical-background)
- [Operator](#operator)
- [Example Categories](#example-categories)
  - [Countermodel Examples](#countermodel-examples)
  - [Theorem Examples](#theorem-examples)
- [Basic Usage](#basic-usage)
- [Settings](#settings)
- [Testing](#testing)
- [Integration](#integration)

## Overview

The relevance subtheory extends the logos framework with the relevance operator (�), providing formal tools for analyzing when propositions are relevant to each other. The relevance relation is a fundamental hyperintensional notion that captures content relationships between propositions beyond mere truth-conditional connections.

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