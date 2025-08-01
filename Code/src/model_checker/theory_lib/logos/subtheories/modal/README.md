# Modal Subtheory: Necessity and Possibility Operators

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure

```
modal/
├── README.md               # This file - modal subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (18 examples)
├── operators.py           # Modal operator definitions (4 operators)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_modal_examples.py  # Integration tests with 18 examples
```

## Overview

The **Modal Subtheory** implements hyperintensional semantics for necessity (□) and possibility (◇), importing counterfactual necessity (CFBox) and counterfactual possibility (CFDiamond) from the `counterfactual/` theory. All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond extensional equivalence or necessary equivalence.

Within the Logos framework, the modal subtheory provides essential operators for reasoning about necessity and possibility. The four operators (one primitive, one defined, and two imported) integrate seamlessly with other hyperintensional operators while maintaining S5 modal logic principles including modal axioms and duality relationships. This provides analysis of modal claims alongside counterfactual, constitutive, and relevance reasoning within a unified semantic framework.

## Subdirectories

### [tests/](tests/)

Comprehensive test suite with 18 integration examples covering all four modal operators. Includes countermodel examples (invalid modal inferences) and theorem examples (valid modal principles) to validate S5 modal logic including K, T, 4, and 5 axioms. Tests verify both modal behavior and hyperintensional semantic implementation. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users

- **[Operator Reference](#operator-reference)** - Complete guide to all four modal operators
- **[Testing Guide](tests/README.md)** - How to run and understand modal logic tests

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Hyperintensional implementation of S5 modal logic
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid modal reasoning patterns
- **[Academic References](#references)** - Theoretical foundations and related work

### For Developers

- **[Implementation Details](operators.py)** - Modal operator definitions and truthmaker semantics
- **[Examples Module](examples.py)** - Test cases and example formulas (18 examples)
- **[Integration Testing](tests/test_modal_examples.py)** - Complete test implementation

## Operator Reference

The modal subtheory provides four operators: one primitive operator that directly implements truthmaker semantics, and three defined operators constructed from the primitives.

**Primitive Operator:**

- Necessity (□) - Modal necessity

**Defined Operators:**

- Possibility (◇) - `◇A := ¬□¬A`
- Counterfactual Necessity (CFBox) - `CFBox A := ⊤ □→ A`
- Counterfactual Possibility (CFDiamond) - `CFDiamond A := ⊤ ◇→ A`

### Necessity

**Symbol**: `\\Box` (displayed as □)
**Name**: Necessity
**Arity**: 1 (unary)
**Type**: Primitive operator

**Meaning**: "It is necessarily the case that A"

**Truth Conditions**: □A is true at a world when A is true at all possible worlds in the model.

**Usage Examples**:

```python
# Basic necessity
"\\Box p"  # It is necessarily the case that p

# Necessity with complex formulas
"\\Box (p \\rightarrow q)"  # It is necessarily the case that if p then q

# Nested modalities
"\\Box \\Box p"  # It is necessarily the case that necessarily p

# Necessity of tautologies
"\\Box (p \\vee \\neg p)"  # Necessarily, p or not p (always valid)
```

**Key Properties**:

- **K Axiom**: `□(A → B) → (□A → □B)`
- **T Axiom**: `□A → A`
- **B Axiom**: `A → □◇A`
- **4 Axiom**: `□A → □□A`

### Possibility

**Symbol**: `\\Diamond` (displayed as ◇)
**Name**: Possibility
**Arity**: 1 (unary)
**Type**: Defined operator

**Meaning**: "It is possibly the case that A"

**Definition**: `◇A := ¬□¬A` - Defined as the negation of the necessity of the negation.

**Usage Examples**:

```python
# Basic possibility
"\\Diamond p"  # It is possibly the case that p

# Possibility with complex formulas
"\\Diamond (p \\wedge q)"  # It is possibly the case that p and q

# Nested modalities
"\\Diamond \\Box p"  # It is possibly the case that necessarily p

# Possibility of contradictions
"\\Diamond (p \\wedge \\neg p)"  # Possibly, p and not p (always invalid)
```

**Key Properties**:

- **Dual of Necessity**: `\\Diamond A \\leftrightarrow \\neg \\Box \\neg A` (modal duality)
- **B Axiom**: `A \\rightarrow \\Box \\Diamond A` (seriality in S5)
- **Consistency**: `\\Diamond A` means A is consistent with the model
- **Existential**: True when A holds in at least one possible world

### Counterfactual Necessity

**Symbol**: `\\CFBox` (displayed as CFBox)
**Name**: Counterfactual Necessity
**Arity**: 1 (unary)
**Type**: Defined operator

**Meaning**: "Under counterfactual evaluation, it is necessarily the case that A"

**Definition**: `CFBox A := ⊤ □→ A` - Defined as the counterfactual conditional from top to A.

**Usage Examples**:

```python
# Counterfactual necessity
"\\CFBox p"  # Under counterfactual evaluation, necessarily p

# Relationship to standard necessity
"\\Box A \\leftrightarrow \\CFBox A"  # Currently equivalent

# Integration with counterfactuals
"\\CFBox (p \\rightarrow q)"  # Under counterfactual evaluation, necessarily if p then q
```

**Key Properties**:

- **Current Equivalence**: `\\CFBox A \\leftrightarrow \\Box A`
- **Placeholder**: Reserved for future counterfactual-specific semantics
- **Integration Ready**: Designed to connect modal and counterfactual reasoning
- **Preserves Modal Properties**: Inherits all properties of standard necessity

### Counterfactual Possibility

**Symbol**: `\\CFDiamond` (displayed as CFDiamond)
**Name**: Counterfactual Possibility
**Arity**: 1 (unary)
**Type**: Defined operator

**Meaning**: "Under counterfactual evaluation, it is possibly the case that A"

**Definition**: `CFDiamond A := ⊤ ◇→ A` - Defined as the might counterfactual from top to A.

**Usage Examples**:

```python
# Counterfactual possibility
"\\CFDiamond p"  # Under counterfactual evaluation, possibly p

# Relationship to standard possibility
"\\Diamond A \\leftrightarrow \\CFDiamond A"  # Currently equivalent

# Modal duality in counterfactual context
"\\CFDiamond A \\leftrightarrow \\neg \\CFBox \\neg A"  # Counterfactual modal duality preserved
```

**Key Properties**:

- **Current Equivalence**: `\\CFDiamond A \\leftrightarrow \\Diamond A`
- **Placeholder**: Reserved for future counterfactual-specific semantics
- **Maintains Duality**: `\\CFDiamond A \\leftrightarrow \\neg \\CFBox \\neg A`
- **Preserves Modal Properties**: Inherits all properties of standard possibility

## Examples

### Example Categories

The modal subtheory includes **18 comprehensive examples** organized into two main categories, testing all four modal operators:

#### Countermodels (MOD*CM*\*): 4 Examples

Tests for **invalid** modal arguments, demonstrating where modal principles fail:

- **MOD_CM_1**: Possibility Does Not Entail Necessity (invalid)
- **MOD_CM_2**: Possibility to Actuality (invalid)
- **MOD_CM_3**: Contingent Possibility (invalid)
- **MOD_CM_4**: Necessity to Possibility of Negation (invalid)

#### Theorems (MOD*TH*\*): 14 Examples

Tests for **valid** modal arguments, confirming S5 modal logic principles:

- **MOD_TH_1**: Necessity Distribution over Conjunction
- **MOD_TH_2**: Possibility Distribution over Disjunction
- **MOD_TH_3**: Modal Duality (Box to Diamond)
- **MOD_TH_4**: Modal Duality (Diamond to Box)
- **MOD_TH_5**: Modal K Axiom
- **MOD_TH_6**: T Axiom (Reflexivity)
- **MOD_TH_7**: 4 Axiom (Transitivity)
- **MOD_TH_8**: 5 Axiom (Euclidean Property)
- **MOD_TH_9**: Necessity of Tautologies
- **MOD_TH_10**: Possibility of Non-Contradictions
- **MOD_TH_11**: Counterfactual Necessity Equivalence
- **MOD_TH_12**: Counterfactual Possibility Equivalence
- **MOD_TH_13**: Counterfactual Modal Duality
- **MOD_TH_14**: Box Conjunction Distribution

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/modal/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/modal/examples.py
```

### Example Structure

Each example follows the standard format:

```python
# MOD_TH_5: MODAL K AXIOM
MOD_TH_5_premises = ['\\Box (A \\rightarrow B)', '\\Box A']  # What must be true
MOD_TH_5_conclusions = ['\\Box B']                           # What we're testing
MOD_TH_5_settings = {                                        # Model constraints
    'N' : 4,                                                # Number of atomic states
    'contingent' : False,                                   # Non-contingent propositions
    'non_null' : True,                                      # Exclude null state
    'non_empty' : True,                                     # Non-empty verifier/falsifier sets
    'disjoint' : False,                                     # Allow overlapping content
    'max_time' : 2,                                         # Solver timeout (seconds)
    'iterate' : 1,                                          # Number of models to find
    'expectation' : False,                                  # Expected result (False = valid)
}
MOD_TH_5_example = [MOD_TH_5_premises, MOD_TH_5_conclusions, MOD_TH_5_settings]
```


## Semantic Theory

### Theoretical Background

The modal subtheory implements S5 modal logic within the hyperintensional truthmaker semantic framework. While modal operators quantify over possible worlds, they are given a hyperintensional implementation using verifier and falsifier sets.

**Key Features**:

1. **World Quantification**: Modal operators quantify over possible world states
2. **Hyperintensional Implementation**: Uses verifier/falsifier semantics
3. **S5 Logic**: No accessibility relation guarantees an S5 modal logic
4. **Modal Duality**: Necessity and possibility as dual operators

### Truth Conditions

#### Necessity (□A)

**Z3 Implementation** (from operators.py):

```python
# Truth conditions
def true_at(self, argument, eval_point):
    """□A is true when A is true at all possible worlds"""
    sem = self.semantics
    u = z3.BitVec("t_nec_u", sem.N)
    return ForAll(
        u,
        z3.Implies(
            sem.is_world(u),
            sem.true_at(argument, {"world": u}),
        ),
    )

def false_at(self, argument, eval_point):
    """□A is false when A is false at some possible world"""
    sem = self.semantics
    u = z3.BitVec("t_nec_u", sem.N)
    return Exists(
        u,
        z3.And(
            sem.is_world(u),
            sem.false_at(argument, {"world": u}),
        ),
    )

# Verifier/falsifier conditions (hyperintensional)
def extended_verify(self, state, argument, eval_point):
    return z3.And(
        state == self.semantics.null_state,
        self.true_at(argument, eval_point)
    )

def extended_falsify(self, state, argument, eval_point):
    return z3.And(
        state == self.semantics.null_state,
        self.false_at(argument, eval_point)
    )
```

### Modal Logic Properties

The modal operators satisfy S5 modal logic properties:

**Properties that HOLD**:

- K Axiom: `□(A → B) → (□A → □B)`
- T Axiom: `□A → A`
- B Axiom: `A → □◇A`
- 4 Axiom: `□A → □□A`
- 5 Axiom: `◇A → □◇A`
- Modal Duality: `□A ↔ ¬◇¬A, ◇A ↔ ¬□¬A`

## Testing and Validation

### Theorem Examples

**Valid Principles** (should find no countermodels):

1. **MOD_TH_5 - Modal K Axiom**:

   - `□(A → B), □A ⊢ □B`
   - If necessarily A implies B, and necessarily A, then necessarily B

2. **MOD_TH_6 - T Axiom**:

   - `□A ⊢ A`
   - What is necessary is true

3. **MOD_TH_8 - 5 Axiom**:

   - `◇A ⊢ □◇A`
   - If possibly A, then necessarily possibly A

4. **MOD_TH_3 - Modal Duality**:
   - `□A ⊢ ¬◇¬A`
   - Necessity is equivalent to impossibility of negation

### Countermodel Examples

**Invalid Principles** (should find countermodels):

1. **MOD_CM_1 - Possibility Does Not Entail Necessity**:

   - `◇A ⊬ □A`
   - Being possibly true does not make something necessarily true

2. **MOD_CM_2 - Possibility to Actuality**:

   - `◇A ⊬ A`
   - Being possibly true does not make something actually true

3. **MOD_CM_3 - Contingent Possibility**:

   - `◇A, ◇¬A ⊬ ⊥`
   - Something can be both possibly true and possibly false

4. **MOD_CM_4 - Necessity to Possibility of Negation**:
   - `□A ⊬ ◇¬A`
   - What is necessary is not possibly false

### Logical Properties

**Valid Inference Rules**:

- K Axiom: `□(A → B), □A ⊢ □B`
- T Axiom: `□A ⊢ A`
- Necessitation: If `⊢ A` then `⊢ □A`
- Modal Duality: `□A ↔ ¬◇¬A` and `◇A ↔ ¬□¬A`

## Integration

### Dependencies

The modal subtheory depends on:

1. **Extensional subtheory** for:
   - `NegationOperator`: Required for defining possibility as negation of necessity of negation
   - Basic logical operators used in complex modal formulas

2. **Counterfactual subtheory** for:
   - `CFBox` and `CFDiamond` operators: Modal counterfactual operators
   - Integration of modal and counterfactual reasoning

```python
# Automatic dependency loading
theory = logos.get_theory(['modal'])  # Also loads extensional and counterfactual
```

### Usage with Other Subtheories

```python
# Combined with counterfactual logic
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['modal', 'counterfactual'])

# MOD_CF_1: MODAL AND COUNTERFACTUAL INTERACTION
MOD_CF_1_premises = ["\\Box P", "(P \\boxright Q)"]
MOD_CF_1_conclusions = ["\\Box Q"]
MOD_CF_1_settings = {
    'N' : 3,                    # Number of atomic states
    'contingent' : False,       # Allow non-contingent propositions
    'non_null' : False,         # Allow null state
    'non_empty' : False,        # Allow empty verifier/falsifier sets
    'disjoint' : False,         # Allow overlapping verifier/falsifier sets
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models to find
    'expectation' : True,       # Expected result (True = countermodel may be found)
}
MOD_CF_1_example = [
    MOD_CF_1_premises,
    MOD_CF_1_conclusions,
    MOD_CF_1_settings,
]

# Combined with constitutive operators
logos_registry2 = LogosOperatorRegistry()
logos_registry2.load_subtheories(['modal', 'constitutive'])

# MOD_CON_1: NECESSITY AND IDENTITY INTERACTION
MOD_CON_1_premises = ["\\Box P", "(P \\equiv Q)"]
MOD_CON_1_conclusions = ["\\Box Q"]
MOD_CON_1_settings = {
    'N' : 3,                    # Number of atomic states
    'contingent' : False,       # Allow non-contingent propositions
    'non_null' : False,         # Allow null state
    'non_empty' : False,        # Allow empty verifier/falsifier sets
    'disjoint' : False,         # Allow overlapping verifier/falsifier sets
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models to find
    'expectation' : False,      # Expected result (False = no countermodel)
}
MOD_CON_1_example = [
    MOD_CON_1_premises,
    MOD_CON_1_conclusions,
    MOD_CON_1_settings,
]
```

### API Reference

#### Core Functions

```python
from model_checker.theory_lib.logos.subtheories.modal import get_operators

# Get all modal operators
operators = get_operators()
# Returns: {
#     "\\Box": NecessityOperator,
#     "\\Diamond": PossibilityOperator,
#     "\\CFBox": CFNecessityOperator,
#     "\\CFDiamond": CFPossibilityOperator
# }
```

#### Example Collections

```python
from model_checker.theory_lib.logos.subtheories.modal.examples import (
    modal_cm_examples,      # 4 countermodel examples
    modal_th_examples,      # 14 theorem examples
    modal_examples,         # Combined 18 examples
)
```

#### Direct Operator Usage

```python
from model_checker.theory_lib.logos.subtheories.modal.operators import (
    NecessityOperator,
    PossibilityOperator,
    CFNecessityOperator,
    CFPossibilityOperator
)
```

## Advanced Topics

### Counterfactual Modal Operators

The CFBox and CFDiamond operators provide integration points for counterfactual reasoning:

**Current Implementation**:

```python
# Current definitions
"\\CFBox A"  # Defined as \\top \\boxright A
"\\CFDiamond A"  # Defined as \\top \\diamondright A
```

**Future Extensions**:

- Could implement counterfactual-specific modal semantics
- Enable context-sensitive modal evaluation
- Support modal reasoning within counterfactual scenarios

**Design Philosophy**:

```python
# Standard modal reasoning
"\\Box A \\rightarrow A"  # Necessity implies truth

# Counterfactual modal reasoning
"\\CFBox A \\rightarrow A"  # Currently equivalent

# Integration potential
"(\\top \\boxright A) \\equiv \\CFBox A"  # Current equivalence
```

### Extensional vs Modal

The modal subtheory reveals the distinction between extensional and modal operators:

**Extensional Operators** (extensional):

- Truth value depends only on truth values of components
- No world-relative evaluation
- Examples: and, or, not, implies

**Modal Operators** (intensional):

- Truth value depends on evaluation across possible worlds
- World-relative semantic clauses
- Quantification over world-states
- Examples: Box, Diamond, CFBox, CFDiamond

**Integration**:

```python
# Extensional: A or not A is always true
"(A \\vee \\neg A)"  # Tautology

# Modal: Necessarily A or not A
"\\Box (A \\vee \\neg A)"  # Necessary tautology

# Mixed: Possibly A and necessarily not A
"(\\Diamond A \\wedge \\Box \\neg A)"  # Inconsistent
```

## Dependencies

The modal subtheory depends on:

1. **Extensional subtheory** for:
   - `NegationOperator`: Required for defining possibility as negation of necessity of negation
   - Basic logical operators used in complex modal formulas

2. **Counterfactual subtheory** for:
   - `CFBox` and `CFDiamond` operators: Modal counterfactual operators
   - Integration of modal and counterfactual reasoning

```python
# Automatic dependency loading
theory = logos.get_theory(['modal'])  # Also loads extensional and counterfactual
```

## Testing

The modal subtheory includes **18 comprehensive test examples** covering all four modal operators through countermodel examples (invalid modal inferences) and theorem examples (valid S5 principles).

```bash
# Run all modal tests
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py -k "MOD_TH_5"

# Run via project test runner
python test_theories.py --theories logos --modal --examples
```

## References

### Primary Sources

- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.
- Kripke (1963) ["Semantical Analysis of Modal Logic"](https://doi.org/10.1007/BF01028024)

### Related Resources

- **[Extensional Subtheory](../extensional/)** - Extensional foundation for modal operators
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation
- **[Counterfactual Subtheory](../counterfactual/)** - Integration with counterfactual reasoning
- Hughes & Cresswell (1996) ["A New Introduction to Modal Logic"](https://www.routledge.com/A-New-Introduction-to-Modal-Logic/Hughes-Cresswell/p/book/9780415125994), Routledge

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)
