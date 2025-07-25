# Extensional Subtheory: Truth-Functional Operators Foundation

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Logos Theory →](../../README.md)

## Directory Structure
```
extensional/
├── README.md               # This file - extensional subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases
├── operators.py           # Truth-functional operator definitions
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_extensional_examples.py  # Integration tests with 14 examples
```

## Overview

The **Extensional Subtheory** implements hyperintensional semantics for truth-functional operators (negation, conjunction, disjunction, material conditional, biconditional, top, bottom). All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond truth-functional equivalence or necessary equivalence.

Within the Logos framework, the extensional subtheory provides the foundational layer for all logical reasoning. While implementing classical truth-functional behavior, it does so within the hyperintensional semantic framework, enabling integration with modal, constitutive, counterfactual, and relevance operators. The seven operators (five primitive, two defined) maintain classical logical principles while supporting the fine-grained content distinctions required by other subtheories.

## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load extensional subtheory only
theory = logos.get_theory(['extensional'])
model = BuildExample("extensional_demo", theory)

# Test classical propositional logic principles
result1 = model.check_validity([], ["(p \\rightarrow p)"])  # Reflexivity - Valid
result2 = model.check_validity(["p", "(p \\rightarrow q)"], ["q"])  # Modus ponens - Valid
result3 = model.check_validity(["(p \\rightarrow q)", "q"], ["p"])  # Affirming consequent - Invalid

print(f"Reflexivity: {result1}")  # False (valid argument)
print(f"Modus ponens: {result2}")  # False (valid argument)  
print(f"Affirming consequent: {result3}")  # True (invalid argument)
```

## Subdirectories

### [tests/](tests/)
Comprehensive test suite with 14 integration examples covering all seven truth-functional operators. Includes both countermodel examples (invalid arguments) and theorem examples (valid arguments) to validate classical propositional logic principles. See [tests/README.md](tests/README.md) for complete testing methodology and debugging guidance.

## Documentation

### For New Users
- **[Quick Start](#quick-start)** - Basic usage examples with truth-functional reasoning
- **[Operator Reference](#operators)** - Complete list of truth-functional operators with semantics
- **[Testing Guide](tests/README.md)** - How to run and understand extensional tests

### For Researchers
- **[Classical Logic Foundation](#classical-logic-foundation)** - Theoretical background and principles
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid reasoning patterns
- **[Dependencies](#dependencies)** - How extensional operators support other subtheories

### For Developers
- **[Implementation Details](operators.py)** - Operator definitions and registry
- **[Examples Module](examples.py)** - Test cases and example formulas
- **[Integration Testing](tests/test_extensional_examples.py)** - Complete test implementation

## Operators

### Primitive Operators

#### Negation (`\\neg`, ¬)
- **Arity**: 1
- **Description**: Logical negation - flips truth value
- **Semantics**: ¬A is true iff A is false

```python
# Examples
model.check_validity(["p"], ["\\neg \\neg p"])  # Double negation - Valid
model.check_validity(["p", "\\neg p"], ["\\bot"])  # Contradiction - Valid
```

#### Conjunction (`\\wedge`, ∧)
- **Arity**: 2  
- **Description**: Logical AND - true when both arguments are true
- **Semantics**: A ∧ B is true iff both A and B are true

```python
# Examples
model.check_validity(["p", "q"], ["p \\wedge q"])  # Introduction - Valid
model.check_validity(["p \\wedge q"], ["p"])       # Elimination - Valid
```

#### Disjunction (`\\vee`, ∨)
- **Arity**: 2
- **Description**: Logical OR - true when at least one argument is true  
- **Semantics**: A ∨ B is true iff at least one of A or B is true

```python
# Examples  
model.check_validity(["p"], ["(p \\vee q)"])         # Introduction - Valid
model.check_validity([], ["(p \\vee \\neg p)"])      # Excluded middle - Valid
```

#### Top (`\\top`, ⊤)
- **Arity**: 0
- **Description**: Logical truth - always true
- **Semantics**: ⊤ is true in all models

```python
# Examples
model.check_validity([], ["\\top"])                # Tautology - Valid
model.check_validity(["\\top"], ["p \\vee \\neg p"])  # Truth implies tautology - Valid
```

#### Bottom (`\\bot`, ⊥)
- **Arity**: 0
- **Description**: Logical falsehood - always false
- **Semantics**: ⊥ is false in all models

```python
# Examples
model.check_validity(["\\bot"], ["p"])             # Ex falso quodlibet - Valid
model.check_validity(["p \\wedge \\neg p"], ["\\bot"])  # Contradiction - Valid
```

### Defined Operators

#### Material Conditional (`\\rightarrow`, →)
- **Arity**: 2
- **Description**: Material implication - false only when antecedent true and consequent false
- **Definition**: A → B ≡ ¬A ∨ B

```python
# Examples
model.check_validity(["p", "(p \\rightarrow q)"], ["q"])  # Modus ponens - Valid
model.check_validity(["\\neg q", "(p \\rightarrow q)"], ["\\neg p"])  # Modus tollens - Valid
```

#### Biconditional (`\\leftrightarrow`, ↔)
- **Arity**: 2
- **Description**: Logical equivalence - true when both sides have same truth value
- **Definition**: A ↔ B ≡ (A → B) ∧ (B → A)

```python
# Examples
model.check_validity(["(p \\leftrightarrow q)", "p"], ["q"])  # Forward direction - Valid
model.check_validity(["(p \\leftrightarrow q)", "q"], ["p"])  # Backward direction - Valid
```

## Classical Logic Foundation

The extensional subtheory implements complete classical propositional logic with standard truth-functional semantics. This provides the logical foundation for all hyperintensional reasoning in the Logos framework.

### Key Logical Properties

**Valid Inference Rules:**
- Modus Ponens: A → B, A ⊢ B
- Modus Tollens: A → B, ¬B ⊢ ¬A  
- Disjunctive Syllogism: A ∨ B, ¬A ⊢ B
- Hypothetical Syllogism: A → B, B → C ⊢ A → C

**Valid Logical Laws:**
- Law of Excluded Middle: ⊢ A ∨ ¬A
- Law of Non-Contradiction: ⊢ ¬(A ∧ ¬A)
- Double Negation: A ↔ ¬¬A
- De Morgan's Laws: ¬(A ∧ B) ↔ (¬A ∨ ¬B)

### Dependencies

The extensional subtheory serves as a foundation for other Logos subtheories:

- **Modal operators** build on extensional operators for necessity and possibility
- **Constitutive operators** use conjunction and negation for content relations
- **Counterfactual operators** extend material conditionals with hyperintensional semantics
- **Relevance operators** refine extensional implication with relevance constraints

## Testing

The extensional subtheory includes **14 comprehensive test examples** covering all seven truth-functional operators through both countermodel and theorem examples. Tests validate classical propositional logic principles and demonstrate the foundation for other subtheories.

```bash
# Run all extensional tests
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_TH_1"

# Run via project test runner  
python test_theories.py --theories logos --extensional --examples
```

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Logos Theory →](../../README.md)