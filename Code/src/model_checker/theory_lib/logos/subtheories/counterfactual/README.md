# Counterfactual Subtheory: Hypothetical Reasoning Operators

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure

```
counterfactual/
├── README.md               # This file - counterfactual subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (33 examples)
├── operators.py           # Counterfactual operator definitions (2 operators)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_counterfactual_examples.py  # Integration tests with 33 examples
```

## Overview

The **Counterfactual Subtheory** implements hyperintensional semantics for counterfactual operators (counterfactual conditional, might counterfactual). All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond truth-functional equivalence or necessary equivalence.

Within the Logos framework, the counterfactual subtheory implements the semantics developed in Brast-McKie (2025) which defines an alternative worlds relation given a primitive space of states closed under parthood together with a semantic primitive for possibility. In addition to integrating seamlessly with modal, constitutive, and relevance operators, this theory is much more commutable and memory efficient than the imposition framework which posits a primitive three-place imposition relation in addition to possibility.

## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load counterfactual subtheory (automatically loads extensional dependency)
theory = logos.get_theory(['counterfactual'])
model = BuildExample("cf_example", theory)

# Test basic counterfactual principles
result1 = model.check_validity([], ["(A \\boxright A)"])  # Identity
result2 = model.check_validity(["A", "(A \\boxright B)"], ["B"])  # Modus ponens
result3 = model.check_validity(["(A \\boxright C)"], ["((A \\wedge B) \\boxright C)"])  # Invalid: strengthening

print(f"Counterfactual identity: {result1}")  # False (valid argument)
print(f"Counterfactual modus ponens: {result2}")  # False (valid argument)
print(f"Antecedent strengthening: {result3}")  # True (invalid argument)
```

## Subdirectories

### [tests/](tests/)

Comprehensive test suite with 33 integration examples covering both counterfactual operators. Includes countermodel examples (invalid classical principles like antecedent strengthening, contraposition, transitivity) and theorem examples (valid counterfactual principles like identity, modus ponens, weakened transitivity). Tests demonstrate the non-monotonic nature of counterfactual reasoning. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users

- **[Quick Start](#quick-start)** - Basic counterfactual reasoning examples
- **[Operator Reference](#operator-reference)** - Complete guide to counterfactual operators
- **[Testing Guide](tests/README.md)** - How to run and understand counterfactual tests

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Alternative worlds semantics and truth conditions
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid counterfactual patterns
- **[Academic References](#references)** - Primary sources and theoretical foundations

### For Developers

- **[Implementation Details](operators.py)** - Counterfactual operator definitions
- **[Examples Module](examples.py)** - Test cases and example formulas (33 examples)
- **[Integration Testing](tests/test_counterfactual_examples.py)** - Complete test implementation

## Operator Reference

### Counterfactual Conditional

**Symbol**: `\\boxright` (□→)
**Name**: Counterfactual Conditional
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "If A were the case, then B would be the case"

**Truth Conditions**: A counterfactual conditional A □→ B is true at an evaluation point w when:

```
For all x,u: (x verifies A and u is alternative to x relative to w) implies B is true at u
```

**Usage Examples**:

```python
# Basic counterfactual reasoning
"(p \\boxright q)"  # If p were the case, q would be the case

# With negation
"(\\neg p \\boxright r)"  # If not-p were the case, r would be the case

# Complex antecedents
"((p \\wedge q) \\boxright r)"  # If both p and q were the case, r would be the case
```

**Key Properties**:

- **Identity**: `(A \\boxright A)` is always valid
- **Modus Ponens**: From `A` and `(A \\boxright B)`, infer `B`
- **Transitivity**: Generally invalid (see countermodel CF_CM_10)
- **Antecedent Strengthening**: Generally invalid (see countermodel CF_CM_1)

### Might Counterfactual

**Symbol**: `\\diamondright` (◇→)
**Name**: Might Counterfactual
**Arity**: 2 (binary)
**Type**: Defined operator

**Meaning**: "If A were the case, then B might be the case"

**Definition**: `\\neg(A \\boxright \\neg B)` - Defined as the negation of the counterfactual conditional with negated consequent.

**Usage Examples**:

```python
# Expressing possibility under counterfactual assumption
"(p \\diamondright q)"  # If p were the case, q might be the case

# Relationship to would-counterfactuals
"(A \\boxright B) \\rightarrow (A \\diamondright B)"  # Would implies might
```

**Key Properties**:

- **Factivity**: From `A` and `B`, infer `(A \\diamondright B)` (see theorem CF_TH_10)
- **Weaker than Would**: `(A \\boxright B)` implies `(A \\diamondright B)`
- **Non-factivity for Would**: `A` and `B` do not imply `(A \\boxright B)` (see countermodel CF_CM_18)

## Examples

### Example Categories

The counterfactual subtheory includes **33 comprehensive examples** organized into two main categories:

#### Countermodels (CF*CM*\*): 21 Examples

Tests for **invalid** counterfactual arguments, demonstrating where counterfactual principles fail:

- **CF_CM_1**: Counterfactual Antecedent Strengthening
- **CF_CM_2**: Might Counterfactual Antecedent Strengthening
- **CF_CM_7**: Counterfactual Contraposition
- **CF_CM_10**: Transitivity
- **CF_CM_13**: Sobel Sequence (complex)
- **CF_CM_15**: Counterfactual Excluded Middle
- **CF_CM_18**: Must Factivity
- **CF_CM_19**: Counterfactual Exportation

#### Theorems (CF*TH*\*): 12 Examples

Tests for **valid** counterfactual arguments, confirming valid principles:

- **CF_TH_1**: Counterfactual Identity
- **CF_TH_2**: Counterfactual Modus Ponens
- **CF_TH_3**: Weakened Transitivity
- **CF_TH_5**: Simplification of Disjunctive Antecedent
- **CF_TH_9**: Counterfactual Conjunction Introduction
- **CF_TH_10**: Might Factivity
- **CF_TH_11**: Definition of Necessity
- **CF_TH_12**: Contradiction to Impossibility

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

#### Running Tests

The counterfactual subtheory includes **33 comprehensive test examples** covering all four operators through both countermodel and theorem examples. Tests validate hypothetical reasoning principles and demonstrate where counterfactual inferences fail.

```bash
# Run all counterfactual tests
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py -k "CF_CM_1"

# Run via project test runner
python test_theories.py --theories logos --counterfactual --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

#### Programmatic Access

```python
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import (
    counterfactual_cm_examples,    # All countermodel examples
    counterfactual_th_examples,    # All theorem examples
    counterfactual_examples        # Combined collection
)

# Access specific example
cf_cm_1 = counterfactual_cm_examples['CF_CM_1']
premises, conclusions, settings = cf_cm_1

# Run example with custom theory
from model_checker import BuildExample
from model_checker.theory_lib import logos

theory = logos.get_theory(['counterfactual'])
model = BuildExample("cf_test", theory)
result = model.check_validity(premises, conclusions, settings)
```

### Example Structure

Each example follows the standard format:

```python
# CF_TH_2: COUNTERFACTUAL MODUS PONENS
CF_TH_2_premises = ['A','(A \\boxright B)']      # What must be true
CF_TH_2_conclusions = ['B']                       # What we're testing
CF_TH_2_settings = {                             # Model constraints
    'N' : 4,                                     # Number of atomic states
    'contingent' : False,                        # Non-contingent propositions
    'non_empty' : False,                         # Allow empty verifier/falsifier sets
    'non_null' : False,                          # Allow null state participation
    'max_time' : 1,                              # Solver timeout (seconds)
    'iterate' : 1,                               # Number of models to find
    'expectation' : False,                       # Expected result (False = valid)
}
CF_TH_2_example = [CF_TH_2_premises, CF_TH_2_conclusions, CF_TH_2_settings]
```

**Settings Explanation**:

- `N`: Controls state space size (larger N allows more complex models)
- `contingent`: Whether atomic propositions must be contingent
- `non_empty`: Whether propositions must have non-empty truth sets
- `non_null`: Whether null state can participate in verification/falsification
- `expectation`: Expected model-finding result (False for valid arguments, True for invalid)

## Semantic Theory

### Theoretical Background

The counterfactual subtheory implements the semantic theory developed in Brast-McKie (2025), which provides a hyperintensional approach to counterfactual reasoning based on truthmaker semantics.

**Key Innovations**:

1. **Hyperintensional Semantics**: Propositions individuated by verifier and falsifier sets
2. **Alternative Worlds**: Semantic relation determining counterfactual evaluation points
3. **Verification-based Truth**: Truth conditions defined in terms of state verification
4. **Bilateral Semantics**: Both positive (verifiers) and negative (falsifiers) truth conditions

### Truth Conditions

#### Counterfactual Conditional (A �� B)

**True at evaluation point w** when:

```
 x,u: (x verifies A ' u is alternative to x relative to w) � B is true at u
```

**False at evaluation point w** when:

```
x,u: (x verifies A ' u is alternative to x relative to w) ' B is false at u
```

#### Imposition (A imposition B)

**True at evaluation point w** when:

```
 u,v: (u verifies A ' v verifies B) � (u  v) verifies B
```

Where `` represents the fusion operation on states.

### Verification Semantics

The counterfactual operators follow the **null-state verification pattern**:

- **Verifiers**: Only the null state verifies true counterfactuals/impositions
- **Falsifiers**: Only the null state falsifies false counterfactuals/impositions
- **Evaluation**: Truth value determined by world-relative evaluation, not state verification

This ensures counterfactuals behave as **world-sensitive** rather than **state-sensitive** operators.

## Testing and Validation

### Theorem Examples

**Valid Principles** (should always find models for premises but not conclusions):

1. **CF_TH_1 - Counterfactual Identity**:

   - `[] � (A \\boxright A)`
   - Counterfactuals are reflexive

2. **CF_TH_2 - Counterfactual Modus Ponens**:

   - `[A, (A \\boxright B)] � B`
   - Basic inference rule for counterfactuals

3. **CF_TH_3 - Weakened Transitivity**:

   - `[(A \\boxright B), ((A \\wedge B) \\boxright C)] � (A \\boxright C)`
   - Restricted form of transitivity that remains valid

4. **CF_TH_10 - Might Factivity**:
   - `[A, B] � (A \\diamondright B)`
   - If both antecedent and consequent are true, might counterfactual holds

### Countermodel Examples

**Invalid Principles** (should find countermodels where premises are true but conclusions false):

1. **CF_CM_1 - Counterfactual Antecedent Strengthening**:

   - `[\\neg A, (A \\boxright C)] � ((A \\wedge B) \\boxright C)`
   - Strengthening antecedent can change truth value

2. **CF_CM_7 - Counterfactual Contraposition**:

   - `[(A \\boxright B)] � (\\neg B \\boxright \\neg A)`
   - Contraposition fails for counterfactuals

3. **CF_CM_10 - Transitivity**:

   - `[(A \\boxright B), (B \\boxright C)] � (A \\boxright C)`
   - Transitivity is generally invalid

4. **CF_CM_18 - Must Factivity**:
   - `[A, B] � (A \\boxright B)`
   - Truth of antecedent and consequent doesn't guarantee counterfactual

### Logical Properties

**Properties that HOLD**:

- Reflexivity: `(A \\boxright A)`
- Modus Ponens: `A, (A \\boxright B) � B`
- Weakened Transitivity: `(A \\boxright B), ((A ' B) \\boxright C) � (A \\boxright C)`
- Would-to-Might: `(A \\boxright B) � (A \\diamondright B)`
- Might Factivity: `A, B � (A \\diamondright B)`

**Properties that FAIL**:

- Antecedent Strengthening: `(A \\boxright C) � ((A ' B) \\boxright C)`
- Contraposition: `(A \\boxright B) � (�B \\boxright �A)`
- Transitivity: `(A \\boxright B), (B \\boxright C) � (A \\boxright C)`
- Must Factivity: `A, B � (A \\boxright B)`
- Exportation: `((A ' B) \\boxright C) � (A \\boxright (B \\boxright C))`

## Integration

### Dependencies

The counterfactual subtheory depends on the **extensional subtheory** for:

- `NegationOperator`: Required for defining might counterfactual and might imposition
- Basic logical operators used in complex examples

```python
# Automatic dependency loading
theory = logos.get_theory(['counterfactual'])  # Also loads extensional
```

### Usage with Other Subtheories

```python
# Combined with modal logic
theory = logos.get_theory(['counterfactual', 'modal'])

# Mixed reasoning examples
premises = ["\\Box p", "(p \\boxright q)"]
conclusion = "\\Diamond q"
result = model.check_validity(premises, [conclusion])

# Combined with constitutive operators
theory = logos.get_theory(['counterfactual', 'constitutive'])

# Ground and counterfactual interaction
premises = ["(p \\leq q)", "(p \\boxright r)"]
conclusion = "(q \\boxright r)"
result = model.check_validity(premises, [conclusion])
```

### API Reference

#### Core Functions

```python
from model_checker.theory_lib.logos.subtheories.counterfactual import get_operators

# Get all counterfactual operators
operators = get_operators()
# Returns: {
#     "\\boxright": CounterfactualOperator,
#     "\\diamondright": MightCounterfactualOperator,
#     "\\imposition": ImpositionOperator,
#     "\\could": MightImpositionOperator
# }
```

#### Example Collections

```python
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import (
    counterfactual_cm_examples,     # 21 countermodel examples
    counterfactual_th_examples,     # 12 theorem examples
    counterfactual_examples,        # Combined 33 examples
    example_range                   # Selected examples for execution
)
```

#### Direct Operator Usage

```python
from model_checker.theory_lib.logos.subtheories.counterfactual.operators import (
    CounterfactualOperator,
    MightCounterfactualOperator,
    ImpositionOperator,
    MightImpositionOperator
)
```

## Advanced Topics

### Sobel Sequences

**Sobel sequences** test the limit behavior of counterfactuals with increasingly specific antecedents:

```python
# CF_CM_13: SOBEL SEQUENCE
premises = [
    '(A \\boxright X)',                                    # A would lead to X
    '\\neg ((A \\wedge B) \\boxright X)',                 # A'B would not lead to X
    '(((A \\wedge B) \\wedge C) \\boxright X)',          # A'B'C would lead to X
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',  # But A'B'C'D would not
    # ... continues with more specific antecedents
]
```

Sobel sequences demonstrate the **non-monotonic** nature of counterfactual reasoning, where adding more specific information can flip truth values.

### Antecedent Strengthening

**Antecedent strengthening** is the principle that if `(A \\boxright C)` is true, then `((A \\wedge B) \\boxright C)` should also be true. This principle **fails** in the counterfactual subtheory:

```python
# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING (INVALID)
premises = ['\\neg A', '(A \\boxright C)']
conclusions = ['((A \\wedge B) \\boxright C)']  # Does not follow
```

This failure reflects the **context-sensitive** nature of counterfactual reasoning, where additional information in the antecedent can change the relevant alternatives.

### Factivity Properties

The subtheory distinguishes between **must factivity** and **might factivity**:

**Might Factivity (VALID)**:

```python
# CF_TH_10: If A and B are both true, then "if A were the case, B might be the case"
premises = ['A', 'B']
conclusions = ['(A \\diamondright B)']  # Valid
```

**Must Factivity (INVALID)**:

```python
# CF_CM_18: A and B being true doesn't guarantee "if A were the case, B would be the case"
premises = ['A', 'B']
conclusions = ['(A \\boxright B)']  # Invalid - countermodel exists
```

This distinction captures the intuition that actual truth guarantees counterfactual possibility but not counterfactual necessity.

## Dependencies

The counterfactual subtheory depends on the **extensional subtheory** for:

- `NegationOperator`: Required for defining might counterfactual as negation of counterfactual with negated consequent
- Basic logical operators used in complex counterfactual formulas

```python
# Automatic dependency loading
theory = logos.get_theory(['counterfactual'])  # Also loads extensional
```

## Testing

The counterfactual subtheory includes **33 comprehensive test examples** covering both counterfactual operators through countermodel examples (invalid principles) and theorem examples (valid counterfactual reasoning).

```bash
# Run all counterfactual tests
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py -k "CF_CM_1"

# Run via project test runner
python test_theories.py --theories logos --counterfactual --examples
```

## References

### Primary Sources

- Brast-McKie (2025) ["Counterfactual Worlds"](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf), Journal of Philosophical Logic
- Lewis (1973) ["Counterfactuals"](https://www.hup.harvard.edu/books/9780674127241), Harvard University Press
- Fine (2012) ["Counterfactuals without Possible Worlds"](https://doi.org/10.5840/jphil2012109312), Journal of Philosophy

### Related Resources

- **[Extensional Subtheory](../extensional/)** - Truth-functional foundation for counterfactual operators
- **[Modal Subtheory](../modal/)** - Integration with necessity and possibility
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)
