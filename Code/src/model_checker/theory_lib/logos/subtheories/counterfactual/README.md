# Counterfactual Subtheory: Hypothetical Reasoning Operators

[← Back to Subtheories](../README.md) | [Citation →](CITATION.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure

```
counterfactual/
├── README.md               # This file - counterfactual subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (37 examples)
├── operators.py           # Counterfactual operator definitions (2 operators)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_counterfactual_examples.py  # Integration tests with 37 examples
```

## Overview

The **Counterfactual Subtheory** implements hyperintensional semantics for counterfactual conditional (□→) and might counterfactual (◇→) operators. All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond extensional equivalence or necessary equivalence.

Within the Logos framework, the counterfactual subtheory implements alternative worlds semantics developed in Brast-McKie (2025), which defines an alternative worlds relation using a primitive space of states closed under parthood together with a semantic primitive for possibility. The two operators (one primitive, one defined) integrate seamlessly with modal, constitutive, and relevance operators while providing much more computationally efficient reasoning than frameworks requiring primitive three-place imposition relations.

## Subdirectories

### [tests/](tests/)

Comprehensive test suite with 37 integration examples covering both counterfactual operators. Includes countermodel examples (invalid classical principles like antecedent strengthening, contraposition, transitivity) and theorem examples (valid counterfactual principles like identity, modus ponens, weakened transitivity). Tests demonstrate the non-monotonic nature of counterfactual reasoning and validate alternative worlds semantics. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users

- **[Examples](examples.py)** - Complete collection of validated examples
- **[Operator Reference](#operator-reference)** - Complete guide to both counterfactual operators
- **[Testing Guide](tests/README.md)** - How to run and understand counterfactual tests

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Alternative worlds semantics and theoretical background
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid counterfactual patterns
- **[Academic References](#references)** - Primary sources and theoretical foundations

### For Developers

- **[Implementation Details](operators.py)** - Counterfactual operator definitions and semantics
- **[Examples Module](examples.py)** - Test cases and example formulas (37 examples)
- **[Integration Testing](tests/test_counterfactual_examples.py)** - Complete test implementation

## Operator Reference

The counterfactual subtheory provides two operators: one primitive operator that directly implements alternative worlds semantics, and one defined operator constructed from the primitive.

**Primitive Operator:**

- Counterfactual Conditional (□→) - Would counterfactual

**Defined Operator:**

- Might Counterfactual (◇→) - Defined as ¬(A □→ ¬B)

### Counterfactual Conditional

**Symbol**: `\\boxright` (displayed as □→)
**Name**: Counterfactual Conditional
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "If A were the case, then B would be the case"

**Alternative Worlds**: Given a world w and a state s that verifies A, an s-alternative to w is any world that contains both s and a maximal part of w that is compatible with s. This captures the idea of minimally changing w to accommodate A.

**Truth Conditions**: A □→ B is true at a world w when B is true at all alternative worlds where A holds. Specifically, for every verifier s of A and every s-alternative world u to w, B must be true at u.

**Usage Examples**:

```python
# Basic counterfactual reasoning
"(p \\boxright q)"  # If p were the case, q would be the case

# With negation
"(\\neg p \\boxright r)"  # If it were not the case that p, r would be the case

# Complex antecedents and consequents
"((p \\wedge q) \\boxright r)"  # If both p and q were the case, r would be the case
"(p \\boxright (q \\vee r))"  # If p were the case, either q or r would be the case

# Nested counterfactuals
"(p \\boxright (q \\boxright r))"  # If p were the case, then if q were the case, r would be the case
```

**Key Properties**:

- **Identity**: `(A □→ A)` is always valid
- **Modus Ponens**: From `A, (A □→ B) ⊢ B`
- **Non-monotonic**: Antecedent strengthening fails
- **Non-transitive**: Transitivity generally fails
- **Variably Strict**: Alternative worlds depend on antecedent content

### Might Counterfactual

**Symbol**: `\\diamondright` (displayed as ◇→)
**Name**: Might Counterfactual
**Arity**: 2 (binary)
**Type**: Defined operator

**Meaning**: "If A were the case, then B might be the case"

**Definition**: `(A \\diamondright B) := \\neg (A \\boxright \\neg B)` - Defined as the negation of the counterfactual conditional with negated consequent.

**Usage Examples**:

```python
# Basic might counterfactual
"(p \\diamondright q)"  # If p were the case, q might be the case

# With complex formulas
"((p \\wedge q) \\diamondright r)"  # If p and q were the case, r might be the case

# Relationship to would-counterfactuals
"(A \\boxright B) \\rightarrow (A \\diamondright B)"  # Would implies might (always valid)

# Expressing contingency
"(p \\diamondright q) \\wedge (p \\diamondright \\neg q)"  # If p were the case, q might or might not be
```

**Key Properties**:

- **Dual of Would**: `(A ◇→ B) ↔ ¬(A □→ ¬B)`
- **Might Factivity**: From `A, B ⊢ (A ◇→ B)`
- **Weaker than Would**: `(A □→ B) ⊢ (A ◇→ B)`
- **Non-monotonic**: Like would-counterfactuals, fails antecedent strengthening

## Examples

### Example Categories

The counterfactual subtheory includes **37 comprehensive examples** organized into two main categories:

#### Countermodels (CF_CM): 21 Examples

Tests for **invalid** counterfactual arguments, demonstrating where counterfactual principles fail:

- **CF_CM_1**: Counterfactual Antecedent Strengthening
- **CF_CM_2**: Might Counterfactual Antecedent Strengthening
- **CF_CM_7**: Counterfactual Contraposition
- **CF_CM_10**: Transitivity
- **CF_CM_13**: Sobel Sequence (complex)
- **CF_CM_15**: Counterfactual Excluded Middle
- **CF_CM_18**: Must Factivity
- **CF_CM_19**: Counterfactual Exportation

#### Theorems (CF_TH): 12 Examples

Tests for **valid** counterfactual arguments, confirming valid principles:

- **CF_TH_1**: Counterfactual Identity
- **CF_TH_2**: Counterfactual Modus Ponens
- **CF_TH_3**: Weakened Transitivity
- **CF_TH_5**: Simplification of Disjunctive Antecedent
- **CF_TH_9**: Counterfactual Conjunction Introduction
- **CF_TH_10**: Might Factivity
- **CF_TH_11**: Definition of Necessity
- **CF_TH_12**: Contradiction to Impossibility

### Example Structure

Each example follows the standard format:

```python
# CF_TH_2: COUNTERFACTUAL MODUS PONENS
CF_TH_2_premises = ['A','(A \\boxright B)']
CF_TH_2_conclusions = ['B']
CF_TH_2_settings = {
    'N' : 4,                    # Number of atomic states
    'contingent' : False,       # Non-contingent propositions
    'non_empty' : False,        # Allow empty verifier/falsifier sets
    'non_null' : False,         # Allow null state participation
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models to find
    'expectation' : False,      # Expected result (False = valid)
}
CF_TH_2_example = [
    CF_TH_2_premises,
    CF_TH_2_conclusions,
    CF_TH_2_settings,
]
```

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

#### Running Tests

The counterfactual subtheory includes **37 comprehensive test examples** covering both operators through countermodel and theorem examples. Tests validate hypothetical reasoning principles and demonstrate where counterfactual inferences fail.

```bash
# Run all counterfactual tests
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py -k "CF_CM_1"

# Run via project test runner
python test_theories.py --theories logos --counterfactual --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

## Semantic Theory

### Theoretical Background

The counterfactual subtheory implements the semantic theory developed in Brast-McKie (2025), which provides a hyperintensional approach to counterfactual reasoning based on truthmaker semantics.

**Key Innovations**:

1. **Hyperintensional Semantics**: Propositions individuated by verifier and falsifier sets
2. **Alternative Worlds**: Defined semantic relation determining counterfactual evaluation points
3. **Bilateral Semantics**: Both positive (verifiers) and negative (falsifiers) truth conditions

### Truth Conditions

#### Counterfactual Conditional (A □→ B)

**Informal Description**: A □→ B is true at a world w when B is true at all alternative worlds where A holds. An alternative world is a minimal change to the current world that accommodates the antecedent A - it contains both a verifier of A and as much of the original world as is compatible with that verifier.

**Alternative Worlds in Z3**: The semantics uses `is_alternative(u, x, w)` predicate where:

- `u` is a candidate alternative world
- `x` is a verifier state of the antecedent
- `w` is the evaluation world

The alternative relation ensures that `u` contains both the verifier `x` and a maximal compatible part of `w`.

**Z3 Implementation** (from operators.py):

```python
# Truth conditions
def true_at(self, leftarg, rightarg, eval_point):
    """Defines truth conditions for counterfactual conditional at an evaluation point."""
    semantics = self.semantics
    N = semantics.N
    x = z3.BitVec("t_cf_x", N)
    u = z3.BitVec("t_cf_u", N)
    return ForAll(
        [x, u],
        z3.Implies(
            z3.And(
                semantics.extended_verify(x, leftarg, eval_point),
                semantics.is_alternative(u, x, eval_point["world"])
            ),
            semantics.true_at(rightarg, {"world": u}),
        ),
    )

def false_at(self, leftarg, rightarg, eval_point):
    """Defines falsity conditions for counterfactual conditional at an evaluation point."""
    semantics = self.semantics
    N = semantics.N
    x = z3.BitVec("f_cf_x", N)
    u = z3.BitVec("f_cf_u", N)
    return Exists(
        [x, u],
        z3.And(
            semantics.extended_verify(x, leftarg, eval_point),
            semantics.is_alternative(u, x, eval_point["world"]),
            semantics.false_at(rightarg, {"world": u})
        )
    )
```

#### Might Counterfactual (A ◇→ B)

**Informal Description**: A ◇→ B is true when it is not the case that if A were true, B would be false. This captures the idea that B might be true if A were the case.

**Definition**: `(A ◇→ B) := ¬(A □→ ¬B)` - Defined as the negation of the counterfactual conditional with negated consequent.

### Verification Semantics

The counterfactual operators follow the **null-state verification pattern**:

- **Verifiers**: Only the null state verifies true counterfactuals
- **Falsifiers**: Only the null state falsifies false counterfactuals
- **Evaluation**: Truth value determined by world-relative evaluation, not state verification

This ensures counterfactuals behave as **world-sensitive** rather than **state-sensitive** operators.

**Z3 Implementation** (from operators.py):

```python
# Verifier/falsifier conditions (hyperintensional)
def extended_verify(self, state, leftarg, rightarg, eval_point):
    """Defines verification conditions for counterfactual conditional in the extended semantics."""
    return z3.And(
        state == self.semantics.null_state,
        self.true_at(leftarg, rightarg, eval_point)
    )

def extended_falsify(self, state, leftarg, rightarg, eval_point):
    """Defines falsification conditions for counterfactual conditional in the extended semantics."""
    return z3.And(
        state == self.semantics.null_state,
        self.false_at(leftarg, rightarg, eval_point)
    )
```

## Testing and Validation

### Theorem Examples

**Valid Principles** (should always find models for premises but not conclusions):

1. **CF_TH_1 - Counterfactual Identity**:
   - `⊢ (A □→ A)`
   - Counterfactuals are reflexive

2. **CF_TH_2 - Counterfactual Modus Ponens**:
   - `A, (A □→ B) ⊢ B`
   - Basic inference rule for counterfactuals

3. **CF_TH_3 - Weakened Transitivity**:
   - `(A □→ B), ((A ∧ B) □→ C) ⊢ (A □→ C)`
   - Restricted form of transitivity that remains valid

4. **CF_TH_10 - Might Factivity**:
   - `A, B ⊢ (A ◇→ B)`
   - If both antecedent and consequent are true, might counterfactual holds

### Countermodel Examples

**Invalid Principles** (should find countermodels where premises are true but conclusions false):

1. **CF_CM_1 - Counterfactual Antecedent Strengthening**:
   - `¬A, (A □→ C) ⊬ (A ∧ B) □→ C`
   - Strengthening antecedent can change truth value

2. **CF_CM_7 - Counterfactual Contraposition**:
   - `(A □→ B) ⊬ ¬B □→ ¬A`
   - Contraposition fails for counterfactuals

3. **CF_CM_10 - Transitivity**:
   - `(A □→ B), (B □→ C) ⊬ A □→ C`
   - Transitivity is generally invalid

4. **CF_CM_18 - Must Factivity**:
   - `A, B ⊬ A □→ B`
   - Truth of antecedent and consequent doesn't guarantee counterfactual

### Logical Properties

**Properties that HOLD**:

- Reflexivity: `(A \\boxright A)`
- Modus Ponens: `A, (A \\boxright B) ⊢ B`
- Weakened Transitivity: `(A \\boxright B), ((A ∧ B) \\boxright C) ⊢ (A \\boxright C)`
- Would-to-Might: `(A \\boxright B) ⊢ (A \\diamondright B)`
- Might Factivity: `A, B ⊢ (A \\diamondright B)`

**Properties that FAIL**:

- Antecedent Strengthening: `(A \\boxright C) ⊬ ((A ∧ B) \\boxright C)`
- Contraposition: `(A \\boxright B) ⊬ (¬B \\boxright ¬A)`
- Transitivity: `(A \\boxright B), (B \\boxright C) ⊬ (A \\boxright C)`
- Must Factivity: `A, B ⊬ (A \\boxright B)`
- Exportation: `((A ∧ B) \\boxright C) ⊬ (A \\boxright (B \\boxright C))`

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

# Mixed reasoning example
MIXED_MOD_premises = ["\\Box P", "(P \\boxright Q)"]
MIXED_MOD_conclusions = ["\\Diamond Q"]
MIXED_MOD_settings = {'N': 3, 'expectation': False}  # Expecting validity
MIXED_MOD_example = [MIXED_MOD_premises, MIXED_MOD_conclusions, MIXED_MOD_settings]

# Combined with constitutive operators
theory = logos.get_theory(['counterfactual', 'constitutive'])

# Ground and counterfactual interaction example
MIXED_CON_premises = ["(P \\leq Q)", "(P \\boxright R)"]
MIXED_CON_conclusions = ["(Q \\boxright R)"]
MIXED_CON_settings = {'N': 3, 'expectation': True}  # May be invalid
MIXED_CON_example = [MIXED_CON_premises, MIXED_CON_conclusions, MIXED_CON_settings]
```

### API Reference

#### Core Functions

```python
from model_checker.theory_lib.logos.subtheories.counterfactual import get_operators

# Get all counterfactual operators
operators = get_operators()
# Returns: {
#     "\\boxright": CounterfactualOperator,
#     "\\diamondright": MightCounterfactualOperator
# }
```

#### Example Collections

```python
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import (
    counterfactual_cm_examples,     # 21 countermodel examples
    counterfactual_th_examples,     # 12 theorem examples
    counterfactual_examples,        # Combined 37 examples
    example_range                   # Selected examples for execution
)
```

#### Direct Operator Usage

```python
from model_checker.theory_lib.logos.subtheories.counterfactual.operators import (
    CounterfactualOperator,
    MightCounterfactualOperator
)
```

## Advanced Topics

### Sobel Sequences

**Sobel sequences** test the limit behavior of counterfactuals with increasingly specific antecedents:

```python
# CF_CM_13: SOBEL SEQUENCE
premises = [
    '(A \\boxright X)',                                    # A would lead to X
    '\\neg ((A \\wedge B) \\boxright X)',                 # A∧B would not lead to X
    '(((A \\wedge B) \\wedge C) \\boxright X)',          # A∧B∧C would lead to X
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',  # But A∧B∧C∧D would not
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
- `ConjunctionOperator`: Required for compound counterfactual antecedents and consequents
- `DisjunctionOperator`: Required for disjunctive counterfactual formulas
- `ConditionalOperator`: Required for conditional formulas within counterfactual contexts
- `BiconditionalOperator`: Required for biconditional formulas within counterfactual contexts
- `TopOperator`: Required for tautologies in counterfactual contexts
- `BottomOperator`: Required for contradictions in counterfactual contexts

```python
# Automatic dependency loading
theory = logos.get_theory(['counterfactual'])  # Also loads extensional
```

## Testing

The counterfactual subtheory includes **37 comprehensive test examples** covering both counterfactual operators through countermodel examples (invalid principles) and theorem examples (valid counterfactual reasoning)

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
- Fine (2012) ["Counterfactuals without Possible Worlds"](https://doi.org/10.5840/jphil2012109312), Journal of Philosophy

### Related Resources

- **[Extensional Subtheory](../extensional/)** - Extensional foundation for counterfactual operators
- **[Modal Subtheory](../modal/)** - Integration with necessity and possibility
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)
