# Hyperintensional Semantics in ModelChecker

## Table of Contents

1. [Introduction](#introduction)
2. [Core Concepts](#core-concepts)
   - [States and Fusion](#states-and-fusion)
   - [Possibility and Compatibility](#possibility-and-compatibility)
   - [Worlds and Evaluation](#worlds-and-evaluation)
3. [Truthmaker Semantics](#truthmaker-semantics)
   - [Verifiers and Falsifiers](#verifiers-and-falsifiers)
   - [Truth Conditions](#truth-conditions)
4. [Logical Operators](#logical-operators)
   - [Extensional Operators](#extensional-operators)
   - [Modal Operators](#modal-operators)
   - [Counterfactual Operators](#counterfactual-operators)
   - [Constitutive Operators](#constitutive-operators)
5. [Implementation in ModelChecker](#implementation-in-modelchecker)
6. [Examples and Applications](#examples-and-applications)
7. [Theoretical Background](#theoretical-background)
8. [References](#references)

## Introduction

Hyperintensional semantics provides a framework for making semantic distinctions that are invisible to classical intensional semantics. In ModelChecker, hyperintensional theories use **truthmaker semantics** where propositions are characterized by their verifiers and falsifiers, allowing for fine-grained content distinctions even between necessarily equivalent formulas.

The key insight is that sentences are evaluated at **states** which may be partial rather than total, fixing the truth values of only some sentence letters. This allows the framework to distinguish between different ways of making a sentence true or false.

## Core Concepts

### States and Fusion

States are the fundamental building blocks of hyperintensional semantics:

- **Representation**: States are modeled by bitvectors (e.g., `#b00101` has length 5)
- **State Fusion**: The operation `⊔` combines states using bitwise OR
  - Example: `#b00101 ⊔ #b11001 = #b11101`
- **Atomic States**: Exactly one bit set to 1 (e.g., `#b00100`)
- **Null State**: No bits set to 1 (e.g., `#b00000`)

**Notation in ModelChecker**:
```
States are named: a, b, c, ...
Fusions printed as: a.b (fusion of states a and b)
Part relation: a ≤ b iff a ⊔ b = b
```

### Possibility and Compatibility

The framework distinguishes between possible and impossible states:

- **Possible States**: States that can exist in the model
- **Impossible States**: States that cannot exist (e.g., contradictory combinations)
- **Constraints**:
  - The null state must be possible
  - Every part of a possible state must be possible
- **Compatibility**: States a and b are compatible iff a ⊔ b is possible

### Worlds and Evaluation

- **World State**: A possible state that is maximal with respect to compatibility
  - Contains every compatible state as a part
  - Represents a complete possible situation
- **Evaluation**: Formulas are evaluated at world states

## Truthmaker Semantics

### Verifiers and Falsifiers

Each proposition has two sets associated with it:

- **Verifiers**: States that make the proposition true
- **Falsifiers**: States that make the proposition false

**Key Properties**:
1. Both sets must be closed under fusion
2. For atomic propositions, verifiers and falsifiers must be incompatible
3. Every possible state must be compatible with either a verifier or falsifier

### Truth Conditions

A sentence is:
- **True at world w**: w contains a verifier as a part
- **False at world w**: w contains a falsifier as a part
- **Neither** (in non-bivalent theories): w contains neither

## Logical Operators

### Extensional Operators

**Negation (¬)**:
- Verifiers: The falsifiers of the negated sentence
- Falsifiers: The verifiers of the negated sentence

**Conjunction (∧)**:
- Verifiers: Pairwise fusions of verifiers for each conjunct
- Falsifiers: Falsifiers for either conjunct (or fusions thereof)

**Disjunction (∨)**:
- Verifiers: Verifiers for either disjunct (or fusions thereof)
- Falsifiers: Pairwise fusions of falsifiers for each disjunct

**Properties**:
- Conjunction and disjunction are dual (De Morgan laws hold)
- Idempotence laws hold
- Distribution and absorption laws do NOT hold

### Modal Operators

**Necessity (□)**:
- □A is true at w iff every world contains a verifier for A

**Possibility (◇)**:
- ◇A is true at w iff some world contains a verifier for A

### Counterfactual Operators

For counterfactuals, we need the concept of **alternative worlds**:

Given world w and state s, an **s-alternative to w** is any world that contains:
1. The state s
2. A maximal part of w that is compatible with s

**Must Counterfactual (□→)**:
- A □→ B is true at w iff B is true at all s-alternatives to w, for all verifiers s of A

**Might Counterfactual (◇→)**:
- A ◇→ B is true at w iff B is true at some s-alternative to w, for some verifier s of A

### Constitutive Operators

These operators capture hyperintensional relationships between propositions:

**Ground (≤)**: "A is sufficient for B"
- Every verifier for A is a verifier for B
- Fusion of falsifiers for A and B is a falsifier for B
- Every falsifier for B has a part that falsifies A

**Essence (⊑)**: "A is necessary for B"
- Fusion of verifiers for A and B is a verifier for B
- Every verifier for B has a part that verifies A
- Every falsifier for A is a falsifier for B

**Identity (≡)**: "A just is B"
- A and B have the same verifiers
- A and B have the same falsifiers

**Relevance (≼)**: "A is wholly relevant to B"
- Fusion of verifiers for A and B is a verifier for B
- Fusion of falsifiers for A and B is a falsifier for B

**Interdefinability**:
```
A ≤ B   :=  ¬A ⊑ ¬B  :=  (A ∨ B) ≡ B
A ⊑ B   :=  ¬A ≤ ¬B  :=  (A ∧ B) ≡ B
A ≡ B   :=  (A ≤ B) ∧ (B ≤ A)
A ≼ B   :=  (A ∧ B) ≤ B
```

## Implementation in ModelChecker

ModelChecker implements hyperintensional semantics through several theories:

### Logos Theory
The most comprehensive implementation with all operators:
```python
from model_checker.theory_lib import logos

# Load theory with all subtheories
theory = logos.get_theory()

# Check hyperintensional distinctions
model = BuildExample("hyperintensional", theory)
# p ∧ q and q ∧ p are necessarily equivalent but not identical
result = model.check_formula("(p \\wedge q) \\equiv (q \\wedge p)")
```

### Exclusion Theory
Implements unilateral semantics (a variant of hyperintensional semantics):
```python
from model_checker.theory_lib import exclusion
theory = exclusion.get_theory()
```

### Key Implementation Features

1. **Bitvector Representation**: States represented as Z3 bitvectors
2. **Efficient Fusion**: Bitwise OR for state combination
3. **Constraint Generation**: Automatic generation of semantic constraints
4. **Model Finding**: Z3 solver finds models satisfying all constraints

## Examples and Applications

### Example 1: Hyperintensional Distinctions
```python
# These are logically equivalent but hyperintensionally distinct
premises = ["p \\leftrightarrow q"]
conclusions = ["p \\equiv q"]  # Propositional identity
# This is invalid - logical equivalence doesn't ensure identity
```

### Example 2: Relevance Logic
```python
# Classical tautologies may fail when relevance is required
premises = []
conclusions = ["p \\to (q \\to p)"]  # May be invalid
# p is not relevant to "q → p"
```

### Example 3: Counterfactual Reasoning
```python
# Fine's semantics for counterfactuals
premises = ["\\neg p", "p \\boxright q"]
conclusions = ["p \\boxright r"]  # Doesn't follow
# Different verifiers for p may lead to different alternatives
```

### Applications

1. **Philosophy of Language**: Analyzing propositional content and aboutness
2. **Formal Epistemology**: Modeling knowledge and belief with fine-grained content
3. **Metaphysics**: Studying grounding and essence relations
4. **Logic**: Exploring non-classical logical systems

## Theoretical Background

The hyperintensional framework in ModelChecker builds on several key theoretical developments:

1. **Truthmaker Semantics**: Developed by Kit Fine, providing a framework where propositions are characterized by what makes them true/false rather than just their truth conditions

2. **Bilateral Propositions**: Unlike classical propositions that are sets of worlds, bilateral propositions have both verifier and falsifier states

3. **Non-Boolean Structure**: The space of hyperintensional propositions forms a non-interlaced bilattice rather than a Boolean algebra

4. **Content Sensitivity**: The framework captures distinctions in subject-matter and content that classical logic overlooks

## References

### Primary Sources

- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). *Journal of Philosophical Logic*.

- Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). *Journal of Philosophical Logic*, 50, 1471-1503.

- Fine, K. (2017). ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y). *Journal of Philosophical Logic*, 46, 625-674.

- Fine, K. (2017). ["A Theory of Truthmaker Content II: Subject-matter, Common Content, Remainder and Ground"](https://link.springer.com/article/10.1007/s10992-016-9423-1). *Journal of Philosophical Logic*, 46, 675-702.

- Fine, K. (2017). ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22). In *A Companion to the Philosophy of Language* (2nd ed.). Wiley-Blackwell.

### Related Documentation

- [Logos Theory Documentation](../Code/src/model_checker/theory_lib/logos/README.md)
- [Exclusion Theory Documentation](../Code/src/model_checker/theory_lib/exclusion/README.md)
- [ModelChecker Architecture](../Code/ARCHITECTURE.md)
- [Development Guide](../Code/docs/DEVELOPMENT.md)

---

[← Back to Documentation](README.md) | [ModelChecker README →](../Code/README.md)
