# The Three-Level Methodology for Programmatic Semantics

## Table of Contents

1. [Introduction](#introduction)
2. [The Three-Level Framework](#the-three-level-framework)
3. [Level 1: Syntax - Formula Representation](#level-1-syntax---formula-representation)
4. [Level 2: Truth-Conditions - Semantic Definitions](#level-2-truth-conditions---semantic-definitions)
5. [Level 3: Extensions - Model Structures](#level-3-extensions---model-structures)
6. [Information Flow Patterns](#information-flow-patterns)
7. [Comparative Examples](#comparative-examples)
8. [Methodological Significance](#methodological-significance)
9. [Further Reading](#further-reading)

## Introduction

The **ModelChecker** framework implements a systematic **three-level methodology** for computational semantics that enables logicians and linguists to implement, test, and compare complex semantic theories. This methodology provides a bridge between abstract logical theories and concrete computational implementations, making formal semantics accessible to researchers without extensive programming background.

This document explains the three-level approach using concrete examples from two implemented theories:

- **Logos Theory**: Bilateral semantics with verifiers and falsifiers
- **Exclusion Theory**: Unilateral semantics with only verifiers

> **Background Note**: This methodology uses Z3, a powerful automated theorem prover. For an introduction to Z3 and SMT solvers, see [Z3 Background](Z3_BACKGROUND.md).

## The Three-Level Framework

The methodology systematically transforms between three fundamental levels of semantic analysis:

```
Syntax Level          Truth-Conditions Level       Extensions Level
    |                         |                          |
    v                         v                          v
Formulas              Logical Constraints          Concrete Models
Operators        ->   Semantic Definitions    ->   State Assignments
AST Trees             Z3 Requirements              Model Checking
```

### Why Three Levels?

Traditional semantic theories often struggle with the gap between abstract definitions and concrete applications. The three-level methodology provides:

1. **Clarity**: Each level has distinct responsibilities and clear interfaces
2. **Modularity**: Changes at one level don't require rewriting others
3. **Testability**: Systematic exploration of logical relationships
4. **Comparability**: Direct comparison between different semantic theories

## Level 1: Syntax - Formula Representation

The **Syntax Level** handles how logical formulas are represented, parsed, and structured. This level is theory-agnostic so that the same parsing framework supports radically different semantic approaches.

### Basic Structure

All logical formulas in the ModelChecker are represented as **Abstract Syntax Trees (ASTs)** with:

- **Atomic propositions**: Basic sentence letters (`A`, `B`, `C`, ...) or (`ball_is_red`, `mary_loves_john`, ...)
- **Operators**: Logical connectives with defined arity and precedence
- **Complex formulas**: Recursive combinations of atoms and operators

### Example 1: Bilateral Semantics (Logos Theory)

The logos theory implements **20 logical operators** across four semantic domains:

```
# Extensional operators (classical logic)
\\neg A           # Negation: "not A"
A \\wedge B       # Conjunction: "A and B"
A \\vee B         # Disjunction: "A or B"
A \\rightarrow B  # Conditional: "if A then B"

# Modal operators (possible worlds)
\\Box A           # Necessity: "necessarily A"
\\Diamond A       # Possibility: "possibly A"

# Constitutive operators (hyperintensional)
A \\equiv B       # Identity: "A and B have the same content"
A \\leq B         # Ground: "A is grounded in B"
A \\sqsubseteq B  # Essence: "A is part of the essence of B"

# Counterfactual operators (counterfactual logic)
A \\boxright B    # Counterfactual: "if A were the case, B would be"
A \\diamondright B # Might counterfactual: "if A were the case, B might be"
```

### Example 2: Unilateral Semantics (Exclusion Theory)

The exclusion theory implements **5 operators** for unilateral (verifier-only) semantics:

```
# Unilateral operators (exclusion-based)
\\neg A   # CB preclusion: function-based exclusion
\\set_neg A    # Fine preclusion: set-based exclusion
A \\wedge B    # Unilateral conjunction
A \\vee B      # Unilateral disjunction
A \\equiv B    # Unilateral identity
```

### Key Insight: Syntax Independence

Notice that both theories use similar syntactic structuresthe difference lies in their **semantic interpretation**, not their surface syntax. This allows direct comparison: the same formula `A ' B` can be evaluated under both bilateral and unilateral semantics.

## Level 2: Truth-Conditions - Semantic Definitions

The **Truth-Conditions Level** translates abstract semantic definitions into precise logical constraints that can be processed by automated theorem provers. This is where the philosophical commitments of different theories become computationally explicit.

### Bilateral Truth-Conditions (Logos Theory)

Bilateral semantics treats propositions as having both **verifiers** (states that make them true) and **falsifiers** (states that make them false).

#### Example: Negation in Bilateral Semantics

```python
class NegationOperator(Operator):
    def true_at(self, argument, eval_point):
        """Negation is true when the argument is false"""
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Negation is false when the argument is true"""
        return self.semantics.true_at(argument, eval_point)

    def extended_verify(self, state, argument, eval_point):
        """A state verifies not A iff it falsifies A"""
        return self.semantics.extended_falsify(state, argument, eval_point)

    def extended_falsify(self, state, argument, eval_point):
        """A state falsifies not A iff it verifies A"""
        return self.semantics.extended_verify(state, argument, eval_point)
```

**Interpretation**: Negation is primitiveit simply swaps verifiers and falsifiers. If state `s` makes `A` true, then `s` makes `not A` false, and vice versa.

#### Example: Conjunction in Bilateral Semantics

```python
def extended_verify(self, state, leftarg, rightarg, eval_point):
    """A state verifies A'B iff it's the fusion of an A-verifier and B-verifier"""
    x = z3.BitVec("conj_x", self.semantics.N)
    y = z3.BitVec("conj_y", self.semantics.N)

    return Exists([x, y], z3.And(
        self.semantics.extended_verify(x, leftarg, eval_point),
        self.semantics.extended_verify(y, rightarg, eval_point),
        state == self.semantics.fusion(x, y)  # s = x + y (fusion)
    ))
```

**Interpretation**: A conjunction is verified by combining (fusing) a verifier of the first conjunct with a verifier of the second conjunct.

### Unilateral Truth-Conditions (Exclusion Theory)

Unilateral semantics treats propositions as having only **verifiers**. Negation is not primitive but emerges through **exclusion relations** between states.

#### Example: Exclusion in Unilateral Semantics (Champollion-Bernard)

```python
def extended_verify(self, state, argument, eval_point):
    """State verifies \\neg A via three-condition semantics"""

    # Get witness functions for this formula
    formula_str = f"\\neg({argument})"
    h_pred = self.semantics.witness_registry[f"{formula_str}_h"]
    y_pred = self.semantics.witness_registry[f"{formula_str}_y"]

    return z3.And(
        # Condition 1: Exclusion
        # For every verifier v of A, h(v) excludes y(v) where y(v) is part of v
        z3.ForAll([x], z3.Implies(
            self.semantics.extended_verify(x, argument, eval_point),
            z3.And(
                self.semantics.is_part_of(y_pred(x), x),
                self.semantics.excludes(h_pred(x), y_pred(x))
            )
        )),

        # Condition 2: Upper Bound
        # For every verifier v of A, h(v) is part of state
        z3.ForAll([x], z3.Implies(
            self.semantics.extended_verify(x, argument, eval_point),
            self.semantics.is_part_of(h_pred(x), state)
        )),

        # Condition 3: Minimality
        # state is the smallest satisfying conditions 1-2
        z3.ForAll([z], z3.Implies(
            z3.And(
                self.semantics.is_part_of(z, state),
                z != state,
                z3.ForAll([x], z3.Implies(
                    self.semantics.extended_verify(x, argument, eval_point),
                    self.semantics.is_part_of(h_pred(x), z)
                ))
            ),
            z3.Not(z3.ForAll([x], z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                z3.And(
                    self.semantics.is_part_of(y_pred(x), x),
                    self.semantics.excludes(h_pred(x), y_pred(x))
                )
            )))
        ))
    )
```

**Interpretation**: A state verifies `not A` (written `\\neg A`) if there exist witness functions `h` and `y` such that: (1) for every A-verifier, h maps it to something that excludes a part of it, (2) all h-values fit within the state, and (3) the state is minimal with this property.

### Key Difference: Complexity of Truth-Conditions

- **Bilateral**: Direct, primitive operations (swap verifiers/falsifiers)
- **Unilateral**: Complex existential quantification over functions requiring witness predicates

## Level 3: Extensions - Model Structures

The **Extensions Level** deals with concrete model structuresthe actual assignments of truth values to propositions in specific scenarios. This is where theoretical definitions meet computational reality.

### Bilateral Model Structure (Logos Theory)

Bilateral models include both verification and falsification relations:

```python
# Core model relations
verify(state, sentence)    # State verifies sentence
falsify(state, sentence)   # State falsifies sentence
fusion(state1, state2)     # Combine states
is_part_of(state1, state2) # Part-whole relation
compatible(state1, state2) # States can coexist

# Example model settings
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 16,           # 16 atomic states (2^16 = 65,536 total states)
    'contingent': True, # Allow contingent propositions
    'non_empty': True,  # Exclude empty state
    'non_null': True,   # Exclude null state
    'disjoint': True,   # Atomic states are disjoint
    'max_time': 10,  # Extended timeout for complex reasoning
}
```

### Unilateral Model Structure (Exclusion Theory)

Unilateral models include only verification (no falsification) plus exclusion relations:

```python
# Core model relations
verify(state, sentence)    # State verifies sentence (NO falsify!)
excludes(state1, state2)   # Exclusion relation between states
fusion(state1, state2)     # Combine states
is_part_of(state1, state2) # Part-whole relation

# Witness predicates for complex operators
h_pred(state) -> state      # Witness function h
y_pred(state) -> state      # Witness function y

# Example model settings
DEFAULT_EXAMPLE_SETTINGS = {
    'N': 3,             # 3 atomic states (2^3 = 8 total states)
    'possible': False,   # No possible worlds constraint
    'contingent': False, # No contingency requirement
    'non_empty': False,  # Allow empty state
    'non_null': False,   # Allow null state
    'disjoint': False,   # No disjointness requirement
    'max_time': 1,       # Fast timeout due to simpler models
}
```

### Model Output Examples

#### Bilateral Model (Logos)

```
State Space:
  001 = a
  010 = b
  011 = a.b (world)
  100 = c
  101 = a.c
  110 = b.c
  111 = a.b.c (world)

Verification:
  |A|⁺ = {a, a.b, a.c, a.b.c}    # A-verifiers
  |B|⁺ = {b, a.b, b.c, a.b.c}    # B-verifiers

Falsification:
  |A|⁻ = {b, c, b.c}            # A-falsifiers
  |B|⁻ = {a, c, a.c}            # B-falsifiers
```

#### Unilateral Model (Exclusion)

```
State Space:
  001 = a
  010 = b
  011 = a.b
  100 = c

Verification:
  |A| = {a, a.b}                # A-verifiers (no falsifiers!)
  |B| = {b, a.b}                # B-verifiers

Exclusion:
  a excludes b                  # Atomic exclusion
  b excludes a

Witness Functions for \\neg(A):
  h(a) = b      y(a) = a        # h maps a to its excluder b
  h(b) = a      y(b) = b        # h maps b to its excluder a
```

## Information Flow Patterns

Different semantic theories require different patterns of information flow between the three levels. This is a key architectural insight of the ModelChecker framework.

### Linear Flow (Bilateral Semantics)

Bilateral semantics work with **static linear information flow**:

```
Syntax -> Truth-Conditions -> Extensions
  |            |               |
  v            v               v
Parse       Generate        Solve &
formulas    constraints     evaluate
```

This works because:

- Verifiers and falsifiers are directly computable
- No circular dependencies between constraint generation and model evaluation
- Standard Z3 solving techniques suffice

### Circular Flow (Unilateral Semantics)

Unilateral semantics require **circular incremental information flow**:

```
Syntax <-> Truth-Conditions <-> Extensions
  ^            ^               ^
  |            |               |
Parse <->   Generate    <->   Solve &
formulas   constraints     evaluate
```

This is necessary because:

- Witness functions must be established during constraint generation
- But witness values are needed during truth evaluation
- Requires advanced "witness predicate" architecture

### Architectural Innovation

The exclusion theory's solution—**witness predicates as first-class model citizens**—enables circular flow by:

1. **Pre-declaring** witness functions during syntax analysis
2. **Constraining** their behavior during truth-condition generation
3. **Querying** their values during model evaluation

## Comparative Examples

### Example 1: Modus Ponens

**Bilateral Version (Logos)**:

```python
# A, A -> B entails B
premises = ['A', '(A \\rightarrow B)']
conclusions = ['B']
settings = {'N': 3, 'contingent': False}

# Result: THEOREM (no countermodel found)
# Reasoning: If A is verified and A->B is verified,
# then B must be verified by bilateral semantics
```

**Unilateral Version (Exclusion)**:

```python
# A, A -> B entails B (using unilateral conditional)
premises = ['A', '(A \\rightarrow B)']  # Would need unilateral ?
conclusions = ['B']
settings = {'N': 3, 'contingent': False}

# Result: Different behavior due to unilateral semantics
# (Exact result depends on unilateral conditional definition)
```

### Example 2: Double Negation

**Bilateral Version (Logos)**:

```python
# not not A entails A
premises = ['\\neg \\neg A']
conclusions = ['A']

# Result: THEOREM
# Reasoning: Negation swaps verifiers/falsifiers twice,
# returning to original assignment
```

**Unilateral Version (Exclusion)**:

```python
# \\neg \\neg A entails A
premises = ['\\neg \\neg A']
conclusions = ['A']

# Result: COUNTERMODEL FOUND
# Reasoning: Exclusion-based negation doesn't guarantee
# double negation elimination due to complex witness requirements
```

### Example 3: DeMorgan's Law

**Bilateral Version (Logos)**:

```python
# not(A and B) entails (not A or not B)
premises = ['\\neg (A \\wedge B)']
conclusions = ['(\\neg A \\vee \\neg B)']

# Result: THEOREM
# Reasoning: Standard classical logic behavior
```

**Unilateral Version (Exclusion)**:

```python
# \\neg (A \\wedge B) entails (\\neg A \\vee \\neg B)
premises = ['\\neg (A \\wedge B)']
conclusions = ['(\\neg A \\vee \\neg B)']

# Result: COUNTERMODEL FOUND
# Reasoning: Unilateral semantics invalidate classical DeMorgan's laws
```

## Methodological Significance

### For Logicians

The three-level methodology provides logicians with:

1. **Precision**: Define semantic primitives and manage definitions
2. **Exploration**: Systematic testing of logical principles
3. **Comparison**: Direct comparison between competing theories
4. **Discovery**: Automated countermodel generation reveals unexpected logical relationships

**Example Application**: Testing whether hyperintensional logics validate classical principles:

```python
# Test explosion principle in constitutive logic
premises = ['A', '\\neg A']           # Contradiction
conclusions = ['B']                   # Arbitrary conclusion
theory = 'logos_constitutive'

# Result: Depends on specific hyperintensional semantics
```

### For Linguists

The framework enables linguists to:

1. **Model Natural Language**: Implement semantic theories for natural language phenomena
2. **Test Compositionality**: Systematic exploration of meaning composition
3. **Compare Approaches**: Bilateral vs unilateral approaches to content
4. **Validate Theories**: Check whether linguistic theories have desired logical properties

### For Computational Semantics

The architecture demonstrates:

1. **Information Flow**: How computational architecture impacts semantic complexity
2. **Constraint Generation**: Translation from semantic definitions to solver constraints
3. **Model Exploration**: Automated discovery of semantic relationships
4. **Performance Analysis**: Computational complexity of different semantic approaches

## Implementation Guides

### Getting Started

1. **Choose Your Theory**:

   - Logos theory for bilateral/hyperintensional semantics
   - Exclusion theory for unilateral/exclusion semantics

2. **Run Examples**:

   ```bash
   # Bilateral semantics examples
   model-checker src/model_checker/theory_lib/logos/examples.py

   # Unilateral semantics examples
   model-checker src/model_checker/theory_lib/exclusion/examples.py
   ```

3. **Study Output**: Examine how formulas are parsed, constraints generated, and models found

4. **Modify Examples**: Change premises, conclusions, or settings to explore logical relationships

Follow the [Getting Started Guide](Code/docs/EXAMPLES.md) to create your first project and understand the framework basics.

### Theory-Specific Documentation

- **[Logos Theory Documentation](../src/model_checker/theory_lib/logos/README.md)**: Bilateral and hyperintensional semantics
- **[Exclusion Theory Documentation](../src/model_checker/theory_lib/exclusion/README.md)**: Unilateral semantics with witness predicates
- **[Witness Predicates Explained](../src/model_checker/theory_lib/exclusion/strategy2_witness/docs/WITNESS.md)**: Accessible introduction to complex semantic architectures
- **[Hyperintensional Semantics](HYPERINTENSIONAL.md)**: Overview of hyperintensional semantic theories implemented in the model-checker

## Further Reading

### Technical Background

- **[Z3 Background](Z3_BACKGROUND.md)**: Introduction to SMT solvers and Z3
- **[ModelChecker Architecture](../src/model_checker/README.md)**: Framework overview and API
- **[Theory Tools](TOOLS.md)**: Semantic tools for evaluating and comparing semantic theories
- **[Unit Tests](UNIT_TESTS.md)**: Background on defining and using unit tests to rapidly prototype theories
- **[Implementation Lessons](FINDINGS.md)**: Hard-won lessons from implementing complex semantic theories
