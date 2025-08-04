# Exclusion Theory: Unilateral Exclusion Semantics

[← Back to Theory Library](../README.md) | [Documentation →](docs/README.md) | [Notebooks →](notebooks/README.md)

## Directory Structure

```
exclusion/
├── README.md               # This file - theory overview
├── __init__.py            # Theory registration and exports
├── semantic.py            # Core semantic implementation with witness predicates
├── operators.py           # Unilateral operators (¬, ∧, ∨, ≡)
├── examples.py            # 38 test examples (22 countermodels, 16 theorems)
├── docs/                  # Documentation directory (see docs/README.md)
├── tests/                 # Test suite (see tests/README.md)
├── notebooks/             # Interactive notebooks (see notebooks/README.md)
└── history/               # Implementation history (see history/IMPLEMENTATION_STORY.md)
```

## Overview

The **Exclusion Theory** implements Bernard and Champollion's unilateral exclusion semantics within the ModelChecker framework. This theory provides a complete computational realization of unilateral semantics, where propositions have only verifiers (no falsifiers) and negation emerges through a primitive exclusion relation between states.

The implementation features **4 logical operators** with witness predicate architecture that enables proper handling of the complex existential quantification required for unilateral negation. All 38 test examples execute correctly, demonstrating systematic differences between unilateral and classical logical systems.

This theory exemplifies how architectural innovation can solve fundamental computational barriers while preserving theoretical elegance, making Bernard and Champollion's formal semantics accessible for computational exploration and research.

## Theoretical Foundation

### Unilateral vs Bilateral Semantics

**Unilateral Semantics** (Bernard & Champollion):

- Propositions have only **verifiers** (states that make them true)
- No primitive notion of falsification
- Negation emerges through **exclusion relation** between states
- Requires **witness functions** for complex quantification

**Bilateral Semantics** (Fine, Brast-McKie):

- Propositions have both **verifiers and falsifiers**
- Negation swaps verifiers and falsifiers
- Direct computation without witness functions

### Core Definition

A state s verifies ¬φ iff there exist functions h, y such that:

1. **Exclusion**: ∀x ∈ Ver(φ): ∃y(x) ⊑ x where h(x) excludes y(x)
2. **Upper Bound**: ∀x ∈ Ver(φ): h(x) ⊑ s
3. **Minimality**: s is minimal satisfying conditions 1-2

### Semantic Relations

- **Exclusion**: `excludes(s1, s2)` - asymmetric exclusion relation
- **Conflict**: `conflicts(s1, s2)` - symmetric conflict relation
- **Part**: `is_part_of(s1, s2)` - mereological part relation

## Available Operators

| Operator        | Symbol | LaTeX     | Type      | Description                         |
| --------------- | ------ | --------- | --------- | ----------------------------------- |
| **Negation**    | ¬      | `\\neg`   | Primitive | Unilateral exclusion-based negation |
| **Conjunction** | ∧      | `\\wedge` | Primitive | Standard conjunction                |
| **Disjunction** | ∨      | `\\vee`   | Primitive | Standard disjunction                |
| **Identity**    | ≡      | `\\equiv` | Primitive | Verifier set equality               |

## Logical Behavior

### Classical Principles That Fail

- **Double Negation Elimination**: `¬¬A ⊢ A` ❌
- **DeMorgan's Laws**: `¬(A ∧ B) ⊢ (¬A ∨ ¬B)` ❌
- **Explosion**: `A, ¬A ⊢ B` ❌
- **Contraposition**: `(A → B) ⊢ (¬B → ¬A)` ❌

### Principles That Hold

- **Reflexivity**: `A ⊢ A` ✅
- **Conjunction Elimination**: `A ∧ B ⊢ A` ✅
- **Distribution**: `A ∧ (B ∨ C) ⊢ (A ∧ B) ∨ (A ∧ C)` ✅
- **Associativity**: `(A ∧ B) ∧ C ⊢ A ∧ (B ∧ C)` ✅

## Implementation Architecture

### Witness Predicate Pattern

The key innovation is treating witness functions as persistent model predicates:

```python
# Witness predicates persist in the model
h_pred = z3.Function('h_witness', BitVecSort, BitVecSort)
y_pred = z3.Function('y_witness', BitVecSort, BitVecSort)

# Queryable after solving
model.get_h_witness(formula, state)
model.get_y_witness(formula, state)
```

### Key Components

- **WitnessRegistry**: Manages witness predicate creation and identity
- **WitnessAwareModel**: Provides clean API for witness queries
- **ExclusionSemantics**: Implements three-condition negation semantics

## Subdirectories

### [docs/](docs/)

Comprehensive documentation including **user guide**, **API reference**, **architecture details**, and **settings documentation**. The documentation is organized for different audiences from beginners learning unilateral semantics to developers extending the implementation.

### [tests/](tests/)

Complete test suite with **38 examples** validating both countermodels and theorems. Tests demonstrate systematic differences between unilateral and classical logic, with 100% pass rate including previously problematic false premise cases.

### [notebooks/](notebooks/)

Interactive Jupyter notebooks providing **hands-on exploration** of unilateral semantics, **witness function visualization**, and **comparative analysis** with classical logic. Includes step-by-step tutorials for understanding exclusion-based negation.

### [history/](history/)

Detailed documentation of the **implementation journey**, **lessons learned**, and **strategies explored**. These documents provide insights into solving complex semantic implementation challenges and generalizable patterns for computational semantics.

## Documentation

### For New Users

- **[User Guide](docs/USER_GUIDE.md)** - Introduction to unilateral semantics
- **[Interactive Notebooks](notebooks/README.md)** - Hands-on tutorials
- **[Settings Guide](docs/SETTINGS.md)** - Configuration options

### For Researchers

- **[API Reference](docs/API_REFERENCE.md)** - Complete technical documentation
- **[Test Results](docs/DATA.md)** - Empirical validation data
- **[Theory Comparison](../README.md#comparing-theories)** - Cross-theory analysis

### For Developers

- **[Architecture Guide](docs/ARCHITECTURE.md)** - Witness predicate design
- **[Implementation History](history/README.md)** - Development journey
- **[Contributing](../docs/CONTRIBUTING.md)** - Extension guidelines

## Performance Characteristics

- **Success Rate**: 100% (38/38 examples)
- **Average Time**: ~0.005s per example (N=3)
- **Memory**: O(|formulas| × 2^N) for witnesses
- **Scalability**: Practical for N ≤ 4

## References

### Primary Sources

- Champollion, L., & Bernard, P. (2024). ["Negation and Modality in Unilateral Truthmaker Semantics"](https://doi.org/10.1007/s10988-023-09407-z). _Linguistics and Philosophy_.
- Fine, K. (2017). ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://doi.org/10.1007/s10992-016-9413-y). _Journal of Philosophical Logic_, 46(6), 625-674.
- Fine, K. (2017). ["A Theory of Truthmaker Content II: Subject-matter, Common Content, Remainder and Ground"](https://doi.org/10.1007/s10992-016-9423-1). _Journal of Philosophical Logic_, 46(6), 675-702.
- Fine, K. (2017). ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22). In _A Companion to the Philosophy of Language_ (2nd ed.). Wiley-Blackwell.

### Implementation Documentation

- Complete computational realization of Bernard-Champollion semantics
- Witness predicate architecture for handling existential quantification
- For implementation details, see [history/IMPLEMENTATION_STORY.md](history/IMPLEMENTATION_STORY.md)

## Related Resources

- **[Hyperintensional Semantics Guide](../../../../../Docs/theory/HYPERINTENSIONAL.md)** - Theoretical background
- **[Theory Library Overview](../README.md)** - Framework context
- **[ModelChecker API](../../README.md)** - Core framework documentation

## License

Licensed under GPL-3.0 as part of the ModelChecker framework.

---

[← Back to Theory Library](../README.md) | [User Guide →](docs/USER_GUIDE.md) | [Interactive Examples →](notebooks/README.md)
