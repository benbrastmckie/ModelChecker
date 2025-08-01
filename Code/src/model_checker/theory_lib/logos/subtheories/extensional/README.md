# Extensional Subtheory: Extensional Operators Foundation

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure

```
extensional/
├── README.md               # This file - extensional subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (14 examples)
├── operators.py           # Extensional operator definitions (7 operators)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_extensional_examples.py  # Integration tests with 14 examples
```

## Overview

The **Extensional Subtheory** implements hyperintensional semantics for extensional operators (¬, ∧, ∨, →, ↔, ⊤, ⊥). All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond extensional equivalence or necessary equivalence.

Within the Logos framework, the extensional subtheory provides the foundational layer for all logical reasoning. While implementing classical extensional behavior, it does so within the hyperintensional semantic framework, enabling integration with modal, constitutive, counterfactual, and relevance operators. The seven operators (five primitive, two defined) maintain classical logical principles while supporting the fine-grained content distinctions required by other subtheories.

## Subdirectories

### [tests/](tests/)

Comprehensive test suite with 14 integration examples covering all seven extensional operators. Includes countermodel examples (invalid classical inferences) and theorem examples (valid classical principles) to validate classical propositional logic within the hyperintensional framework. Tests verify both extensional behavior and hyperintensional semantic implementation. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users

- **[Examples](examples.py)** - Complete collection of validated examples
- **[Operator Reference](#operator-reference)** - Complete guide to all seven extensional operators
- **[Testing Guide](tests/README.md)** - How to run and understand extensional tests

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Hyperintensional implementation of classical logic
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid reasoning patterns
- **[Academic References](#references)** - Theoretical foundations and related work

### For Developers

- **[Implementation Details](operators.py)** - Extensional operator definitions and semantics
- **[Examples Module](examples.py)** - Test cases and example formulas (14 examples)
- **[Integration Testing](tests/test_extensional_examples.py)** - Complete test implementation

## Operator Reference

The extensional subtheory provides seven operators: five primitive operators that directly implement truthmaker semantics, and two defined operators constructed from the primitives.

**Primitive Operators:**

- Negation (¬) - Logical negation
- Conjunction (∧) - Logical AND
- Disjunction (∨) - Logical OR
- Top (⊤) - Logical truth
- Bottom (⊥) - Logical falsehood

**Defined Operators:**

- Material Conditional (→) - `A → B := ¬A ∨ B`
- Biconditional (↔) - `A ↔ B := (A → B) ∧ (B → A)`

### Negation

**Symbol**: `\\neg` (displayed as ¬)
**Name**: Negation
**Arity**: 1 (unary)
**Type**: Primitive operator

**Meaning**: "It is not the case that A"

**Truth Conditions**: ¬A is true at a world when A is false at that world, and false when A is true.

**Usage Examples**:

```python
# Basic negation
'\\neg A'  # It is not the case that A

# Double negation
'\\neg \\neg A'  # It is not the case that it is not the case that A

# Negation in complex formulas
'\\neg (A \\wedge B)'  # It is not the case that both A and B
```

**Key Properties**:

- **Double Negation**: `¬¬A` is equivalent to `A`
- **Law of Non-Contradiction**: `¬(A ∧ ¬A)` is always valid
- **Law of Excluded Middle**: `A ∨ ¬A` is always valid
- **Hyperintensional**: Swaps verifiers and falsifiers

### Conjunction

**Symbol**: `\\wedge` (displayed as ∧)
**Name**: Conjunction
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "Both A and B"

**Truth Conditions**: A ∧ B is true at a world when both A is true and B is true at that world.

**Usage Examples**:

```python
# Basic conjunction
'(A \\wedge B)'  # Both A and B

# Conjunction introduction
# From A and B, infer (A ∧ B)

# Conjunction elimination
'((A \\wedge B) \\rightarrow A)'  # From A and B, we can infer A
```

**Key Properties**:

- **Commutativity**: `A \\wedge B` is equivalent to `B \\wedge A`
- **Associativity**: `(A \\wedge B) \\wedge C` is equivalent to `A \\wedge (B \\wedge C)`
- **Idempotence**: `A \\wedge A` is equivalent to `A`
- **Verifiers**: Product of verifier sets (fusion of verifiers from both conjuncts)

### Disjunction

**Symbol**: `\\vee` (displayed as ∨)
**Name**: Disjunction
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "Either A or B (or both)"

**Truth Conditions**: A ∨ B is true at a world when at least one of A or B is true at that world.

**Usage Examples**:

```python
# Basic disjunction
'(A \\vee B)'  # Either A or B (or both)

# Disjunction introduction
'(A \\rightarrow (A \\vee B))'  # From A, we can infer A or B

# Disjunctive syllogism
# From (A ∨ B) and ¬A, infer B
```

**Key Properties**:

- **Commutativity**: `A \\vee B` is equivalent to `B \\vee A`
- **Associativity**: `(A \\vee B) \\vee C` is equivalent to `A \\vee (B \\vee C)`
- **Idempotence**: `A \\vee A` is equivalent to `A`
- **Verifiers**: Coproduct of verifier sets (includes individual verifiers and their fusions)

### Top

**Symbol**: `\\top` (displayed as ⊤)
**Name**: Top (Tautology)
**Arity**: 0 (nullary)
**Type**: Primitive operator

**Meaning**: "The logical truth"

**Truth Conditions**: ⊤ is true at every world in every model.

**Usage Examples**:

```python
# Top is always true
'\\top'  # The logical truth

# Any tautology implies top
'((A \\vee \\neg A) \\rightarrow \\top)'  # Valid

# Top in conditionals
'(\\top \\rightarrow (A \\rightarrow A))'  # Valid
```

**Key Properties**:

- **Universal Truth**: Always true regardless of valuation
- **Identity for Conjunction**: `A \\wedge \\top` is equivalent to `A`
- **Absorbing for Disjunction**: `A \\vee \\top` is equivalent to `\\top`
- **Verifiers**: All states verify ⊤

### Bottom

**Symbol**: `\\bot` (displayed as ⊥)
**Name**: Bottom (Contradiction)
**Arity**: 0 (nullary)
**Type**: Primitive operator

**Meaning**: "The logical falsehood"

**Truth Conditions**: ⊥ is false at every world in every model.

**Usage Examples**:

```python
# Bottom is always false
'\\bot'  # The logical falsehood

# Contradiction implies bottom
'((A \\wedge \\neg A) \\rightarrow \\bot)'  # Valid

# Ex falso quodlibet
'(\\bot \\rightarrow A)'  # From falsehood, anything follows
```

**Key Properties**:

- **Universal Falsehood**: Always false regardless of valuation
- **Absorbing for Conjunction**: `A \\wedge \\bot` is equivalent to `\\bot`
- **Identity for Disjunction**: `A \\vee \\bot` is equivalent to `A`
- **Falsifiers**: Only the null state falsifies ⊥

### Material Conditional

**Symbol**: `\\rightarrow` (displayed as →)
**Name**: Material Conditional (Implication)
**Arity**: 2 (binary)
**Type**: Defined operator

**Meaning**: "If A then B"

**Definition**: `(A \\rightarrow B) := (\\neg A \\vee B)` - Defined as negation of antecedent or consequent.

**Usage Examples**:

```python
# Basic conditional
'(A \\rightarrow B)'  # If A then B

# Modus ponens
# From A and (A → B), infer B

# Modus tollens
# From ¬B and (A → B), infer ¬A

# Hypothetical syllogism
# From (A → B) and (B → C), infer (A → C)
```

**Key Properties**:

- **Truth Table**: False only when antecedent is true and consequent is false
- **Contrapositive**: `(A \\rightarrow B)` is equivalent to `(\\neg B \\rightarrow \\neg A)`
- **Exportation**: `((A \\wedge B) \\rightarrow C)` is equivalent to `(A \\rightarrow (B \\rightarrow C))`
- **Material**: No relevance requirement between antecedent and consequent

### Biconditional

**Symbol**: `\\leftrightarrow` (displayed as ↔)
**Name**: Biconditional
**Arity**: 2 (binary)
**Type**: Defined operator

**Meaning**: "A if and only if B"

**Definition**: `(A \\leftrightarrow B) := ((A \\rightarrow B) \\wedge (B \\rightarrow A))` - Defined as conjunction of both directions.

**Usage Examples**:

```python
# Basic biconditional
'(A \\leftrightarrow B)'  # A if and only if B

# Biconditional elimination (forward)
# From (A ↔ B) and A, infer B

# Biconditional elimination (backward)
# From (A ↔ B) and B, infer A

# Biconditional with negation
'((A \\leftrightarrow B) \\rightarrow (\\neg A \\leftrightarrow \\neg B))'  # Valid
```

**Key Properties**:

- **Truth Table**: True when both sides have the same truth value
- **Commutativity**: `(A \\leftrightarrow B)` is equivalent to `(B \\leftrightarrow A)`
- **Reflexivity**: `(A \\leftrightarrow A)` is always valid
- **Material Equivalence**: Extensional, not hyperintensional identity

## Examples

### Example Categories

The extensional subtheory includes **14 comprehensive examples** organized into two main categories, testing all seven extensional operators:

#### Countermodels (EXT*CM*\*): 2 Examples

Tests for **invalid** classical inferences, demonstrating common logical fallacies:

- **EXT_CM_1**: Denying the Antecedent (invalid inference)
- **EXT_CM_2**: Affirming the Consequent (invalid inference)

#### Theorems (EXT*TH*\*): 12 Examples

Tests for **valid** classical principles, confirming fundamental logical laws:

- **EXT_TH_1**: Modus Ponens
- **EXT_TH_2**: Modus Tollens
- **EXT_TH_3**: Conjunction Elimination
- **EXT_TH_4**: Disjunction Introduction
- **EXT_TH_5**: Double Negation Elimination
- **EXT_TH_6**: Law of Excluded Middle
- **EXT_TH_7**: De Morgan's Law 1
- **EXT_TH_8**: De Morgan's Law 2
- **EXT_TH_9**: Biconditional Forward
- **EXT_TH_10**: Biconditional Backward
- **EXT_TH_11**: Ex Falso Quodlibet
- **EXT_TH_12**: Disjunctive Syllogism

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/extensional/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/extensional/examples.py
```

#### Running Tests

The extensional subtheory includes **14 comprehensive test examples** covering all seven operators through both countermodel and theorem examples. Tests validate classical propositional logic principles within the hyperintensional framework.

```bash
# Run all extensional tests
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_CM_1"

# Run via project test runner
python test_theories.py --theories logos --extensional --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

### Example Structure

Each example follows the standard format:

```python
# EXT_TH_1: MODUS PONENS
EXT_TH_1_premises = ["A", "(A \\rightarrow B)"]
EXT_TH_1_conclusions = ["B"]
EXT_TH_1_settings = {
    'N' : 3,                    # Number of atomic states
    'contingent' : False,       # Allow non-contingent propositions
    'non_null' : True,          # Exclude null state
    'non_empty' : True,         # Require non-empty sets
    'disjoint' : False,         # Allow overlapping content
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models
    'expectation' : False,      # Expected result (False = no countermodel)
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]
```

## Semantic Theory

### Theoretical Background

The extensional subtheory implements classical propositional logic within the hyperintensional truthmaker semantic framework. While the operators behave extensionally, they are given a hyperintensional implementation using verifier and falsifier sets.

**Key Features**:

1. **Extensional Behavior**: Operators follow classical truth tables
2. **Hyperintensional Implementation**: Uses verifier/falsifier semantics
3. **Bilateral Semantics**: Both positive (verifiers) and negative (falsifiers) conditions
4. **Foundation Layer**: Provides base operators for all other subtheories

### Truth Conditions

#### Negation (¬A)

**Z3 Implementation** (from operators.py):

```python
# Truth conditions
def true_at(self, argument, eval_point):
    return self.semantics.false_at(argument, eval_point)

def false_at(self, argument, eval_point):
    return self.semantics.true_at(argument, eval_point)

# Verifier/falsifier conditions
def extended_verify(self, state, argument, eval_point):
    return self.semantics.extended_falsify(state, argument, eval_point)

def extended_falsify(self, state, argument, eval_point):
    return self.semantics.extended_verify(state, argument, eval_point)
```

#### Conjunction (A ∧ B)

**Z3 Implementation** (from operators.py):

```python
# Verification: fusion of verifiers from both conjuncts
def extended_verify(self, state, leftarg, rightarg, eval_point):
    return Exists([x, y],
        z3.And(
            sem.extended_verify(x, leftarg, eval_point),
            sem.extended_verify(y, rightarg, eval_point),
            state == sem.fusion(x, y)
        )
    )

# Falsification: either conjunct false or fusion of falsifiers
def extended_falsify(self, state, leftarg, rightarg, eval_point):
    return z3.Or(
        sem.extended_falsify(state, leftarg, eval_point),
        sem.extended_falsify(state, rightarg, eval_point),
        Exists([x, y],
            z3.And(
                sem.extended_falsify(x, leftarg, eval_point),
                sem.extended_falsify(y, rightarg, eval_point),
                state == sem.fusion(x, y)
            )
        )
    )
```

#### Disjunction (A ∨ B)

**Z3 Implementation** (from operators.py):

```python
# Verification: either disjunct true or fusion of verifiers
def extended_verify(self, state, leftarg, rightarg, eval_point):
    return z3.Or(
        sem.extended_verify(state, leftarg, eval_point),
        sem.extended_verify(state, rightarg, eval_point),
        Exists([x, y],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.extended_verify(y, rightarg, eval_point),
                state == sem.fusion(x, y)
            )
        )
    )

# Falsification: fusion of falsifiers from both disjuncts
def extended_falsify(self, state, leftarg, rightarg, eval_point):
    return Exists([x, y],
        z3.And(
            sem.extended_falsify(x, leftarg, eval_point),
            sem.extended_falsify(y, rightarg, eval_point),
            state == sem.fusion(x, y)
        )
    )
```

### Classical Logic Properties

The extensional operators satisfy all classical logical properties:

**Properties that HOLD**:

- Double Negation: `¬¬A := A`
- De Morgan's Laws: `¬(A ∧ B) := (¬A ∨ ¬B)`, `¬(A ∨ B) := (¬A ∧ ¬B)`
- Distribution: `A ∧ (B ∨ C) := (A ∧ B) ∨ (A ∧ C)`
- Absorption: `A ∨ (A ∧ B) := A`, `A ∧ (A ∨ B) := A`
- Law of Excluded Middle: `A ∨ ¬A`
- Law of Non-Contradiction: `¬(A ∧ ¬A)`

**Valid Inference Rules**:

- Modus Ponens: `A, A → B ⊢ B`
- Modus Tollens: `¬B, A → B ⊢ ¬A`
- Disjunctive Syllogism: `A ∨ B, ¬A ⊢ B`
- Hypothetical Syllogism: `A → B, B → C ⊢ A → C`

## Testing and Validation

### Theorem Examples

**Valid Principles** (should find no countermodels):

1. **EXT_TH_1 - Modus Ponens**:

   - `A, A → B ⊢ B`
   - From A and if A then B, we can infer B

2. **EXT_TH_6 - Law of Excluded Middle**:

   - `⊢ A ∨ ¬A`
   - Either A or not A is always true

3. **EXT_TH_7 - De Morgan's Law**:
   - `¬(A ∧ B) ⊢ ¬A ∨ ¬B`
   - Not (A and B) is equivalent to (not A) or (not B)

### Countermodel Examples

**Invalid Principles** (should find countermodels):

1. **EXT_CM_1 - Denying the Antecedent**:

   - `¬A, A → B ⊬ ¬B`
   - From not A and if A then B, we cannot infer not B

2. **EXT_CM_2 - Affirming the Consequent**:
   - `B, A → B ⊬ A`
   - From B and if A then B, we cannot infer A

## Integration

### Role as Foundation

The extensional subtheory serves as the foundation for all other Logos subtheories by providing:

- Basic logical connectives used in complex formulas
- Extensional behavior within hyperintensional semantics
- Standard logical inference patterns
- Classical logical laws and principles

### Used By Other Subtheories

```python
# Modal logic uses extensional operators
"\\Box (P \\rightarrow Q)"  # Necessarily, if P then Q

# Constitutive logic uses conjunction for reduction
"((A \\Rightarrow B) \\equiv ((A \\leq B) \\wedge (A \\sqsubseteq B)))"

# Counterfactual logic extends material conditional
"(P \\boxright Q)"  # If P were true, Q would be true

# All subtheories use negation for operator interdefinability
"((A \\leq B) \\equiv (\\neg A \\sqsubseteq \\neg B))"  # Ground-essence duality
```

### API Reference

#### Core Functions

```python
from model_checker.theory_lib.logos.subtheories.extensional import get_operators

# Get all extensional operators
operators = get_operators()
# Returns: {
#     "\\neg": NegationOperator,
#     "\\wedge": AndOperator,
#     "\\vee": OrOperator,
#     "\\top": TopOperator,
#     "\\bot": BotOperator,
#     "\\rightarrow": ConditionalOperator,
#     "\\leftrightarrow": BiconditionalOperator
# }
```

#### Example Collections

```python
from model_checker.theory_lib.logos.subtheories.extensional.examples import (
    extensional_cm_examples,     # 2 countermodel examples
    extensional_th_examples,     # 12 theorem examples
    extensional_examples,        # Combined 14 examples
)
```

#### Direct Operator Usage

```python
from model_checker.theory_lib.logos.subtheories.extensional.operators import (
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    ConditionalOperator,
    BiconditionalOperator
)
```

## Advanced Topics

### Hyperintensional Implementation

While the extensional operators behave extensionally, their implementation in the Logos framework is hyperintensional:

**Verifier/Falsifier Semantics**:

- Each operator specifies how verifiers and falsifiers combine
- Conjunction: verifiers are fusions of verifiers from both conjuncts
- Disjunction: falsifiers are fusions of falsifiers from both disjuncts
- Negation: swaps verifiers and falsifiers

**Integration Benefits**:

- Seamless integration with hyperintensional operators
- Consistent semantic framework across all subtheories
- Foundation for fine-grained content distinctions

### Material vs Hyperintensional Conditionals

The material conditional (→) in the extensional subtheory differs from hyperintensional conditionals:

**Material Conditional** (A → B):

- Extensional: false only when A true and B false
- No relevance requirement between antecedent and consequent
- Paradoxes of material implication apply

**Hyperintensional Conditionals** (e.g., A ≤ B):

- Subject-matter sensitive
- Relevance or grounding relationship required
- Avoid paradoxes through content sensitivity

## Dependencies

As the foundational subtheory, extensional has **no dependencies** on other subtheories. Instead, it provides operators used by:

- **Modal subtheory**: Uses all extensional operators in modal formulas
- **Constitutive subtheory**: Uses negation for operator duality, conjunction for reduction
- **Counterfactual subtheory**: Extends conditional with similarity semantics
- **Relevance subtheory**: Refines material conditional with relevance constraints

## Testing

The extensional subtheory includes **14 comprehensive test examples** covering all seven extensional operators through countermodel examples (invalid classical inferences) and theorem examples (valid classical principles).

```bash
# Run all extensional tests
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_TH_1"

# Run via project test runner
python test_theories.py --theories logos --extensional --examples
```

## References

### Primary Sources

- Church (1956) ["Introduction to Mathematical Logic"](https://press.princeton.edu/books/hardcover/9780691029061/introduction-to-mathematical-logic-volume-i), Princeton University Press
- Fine (2017) ["Truthmaker Semantics"](https://link.springer.com/referenceworkentry/10.1007/978-94-007-6600-6_20-1), in Blackwell Companion to Philosophy
- van Fraassen (1969) ["Facts and Tautological Entailments"](https://www.jstor.org/stable/2024563), Journal of Philosophy

### Related Resources

- **[Modal Subtheory](../modal/)** - Builds necessity and possibility on extensional foundation
- **[Constitutive Subtheory](../constitutive/)** - Uses extensional operators for content relations
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)
