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

The **Relevance Subtheory** implements hyperintensional semantics for the relevance operator (⪯). All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond extensional equivalence or necessary equivalence.

Within the Logos framework, the relevance subtheory provides specialized exploration of relevance logic through the relevance operator, which is imported from the constitutive subtheory where it is defined alongside other content relationship operators. The relevance relation captures content relationships between propositions through fusion closure conditions on verifiers and falsifiers, enabling formal analysis of when propositions are appropriately connected by content. This subtheory's 20 examples demonstrate valid and invalid relevance principles while maintaining integration with all other hyperintensional operators.

## Subdirectories

### [tests/](tests/)

Comprehensive test suite with 20 integration examples focusing exclusively on the relevance operator. Includes countermodel examples (invalid relevance principles like antecedent strengthening, transitivity failure) and theorem examples (valid relevance principles like connections to grounding and essence). Tests demonstrate the hyperintensional nature of relevance logic and validate fusion closure conditions. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users

- **[Quick Start](#quick-start)** - Basic relevance logic examples
- **[Operator Reference](#operator-reference)** - Complete guide to the relevance operator
- **[Testing Guide](tests/README.md)** - How to run and understand relevance tests

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Fusion closure conditions and theoretical background
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid relevance patterns
- **[Academic References](#references)** - Primary sources and theoretical foundations

### For Developers

- **[Implementation Details](#implementation-note)** - Relevance operator import structure
- **[Examples Module](examples.py)** - Test cases and example formulas (20 examples)
- **[Integration Testing](tests/test_relevance_examples.py)** - Complete test implementation

## Operator Reference

The relevance subtheory provides one operator imported from the constitutive subtheory:

**Imported Operator:**
- Relevance (⪯) - Content relevance relation

### Relevance

**Symbol**: `\\preceq` (displayed as ⪯)
**Name**: Relevance
**Arity**: 2 (binary)
**Type**: Primitive operator (defined in constitutive subtheory)

**Meaning**: "A is relevant to B"

**Truth Conditions**: A ⪯ B is true when both fusion closure conditions hold: 

1. if x verifies A and y verifies B, then the fusion of x and y verifies B;
2. if x falsifies A and y falsifies B, then the fusion of x and y falsifies B.

**Usage Examples**:

```python
# Basic relevance
"(A \\preceq B)"  # A is relevant to B

# Self-relevance
"(A \\preceq A)"  # A is relevant to itself (always valid)

# Relevance chains
"((A \\preceq B) \\wedge (B \\preceq C))"  # Relevance chain (transitivity may fail)

# Relevance with logical operators
"((A \\wedge B) \\preceq A)"  # Conjunction relevant to conjunct (invalid)
"(A \\preceq (A \\vee B))"  # Proposition relevant to its disjunction (valid)
```

**Key Properties**:

- **Reflexivity**: `(A \\preceq A)` is always valid
- **Weaker than Ground**: `(A \\leq B) \\rightarrow (A \\preceq B)` is valid
- **Weaker than Essence**: `(A \\sqsubseteq B) \\rightarrow (A \\preceq B)` is valid
- **Non-transitive**: Transitivity generally fails
- **Fusion Closure**: Based on verifier and falsifier fusion conditions

## Examples

### Example Categories

The relevance subtheory includes **20 comprehensive examples** organized into two main categories:

#### Countermodels (REL_CM_*): 11 Examples

Tests for **invalid** relevance arguments, demonstrating where relevance principles fail:

- **REL_CM_1**: Antecedent Strengthening
- **REL_CM_2**: Antecedent Weakening
- **REL_CM_3**: Relevance Transitivity
- **REL_CM_4**: Relevant Implication: Ground
- **REL_CM_5**: Relevant Implication: Essence
- **REL_CM_6**: Relevant Implication: Identity
- **REL_CM_7**: Strict Implication
- **REL_CM_8**: Reverse Distribution: Disjunction over Conjunction
- **REL_CM_9**: Reverse Distribution: Conjunction over Disjunction
- **REL_CM_10**: Conjunction Introduction
- **REL_CM_11**: Disjunction Introduction

#### Theorems (REL_TH_*): 9 Examples

Tests for **valid** relevance arguments, confirming valid principles:

- **REL_TH_1**: Relevance to Conjunction
- **REL_TH_2**: Relevance to Disjunction
- **REL_TH_3**: Conjunction to Relevance
- **REL_TH_4**: Disjunction to Relevance
- **REL_TH_5**: Conjunction Introduction
- **REL_TH_6**: Disjunction Introduction
- **REL_TH_7**: Grounding Relevance
- **REL_TH_8**: Essence Relevance
- **REL_TH_9**: Identity Relevance

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/relevance/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/relevance/examples.py
```

#### Running Tests

The relevance subtheory includes **20 comprehensive test examples** focusing exclusively on relevance logic principles through countermodel and theorem examples. Tests validate content-based reasoning and demonstrate where classical logic fails in relevance-sensitive contexts.

```bash
# Run all relevance tests
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_CM_1"

# Run via project test runner
python test_theories.py --theories logos --relevance --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

### Example Structure

Each example follows the standard format:

```python
# REL_CM_1: ANTECEDENT STRENGTHENING
REL_CM_1_premises = []
REL_CM_1_conclusions = ["((A \\wedge B) \\preceq A)"]
REL_CM_1_settings = {
    'N' : 4,                    # Number of atomic states
    'contingent' : True,        # Contingent propositions allowed
    'non_null' : True,          # Exclude null state from verifiers
    'non_empty' : True,         # Non-empty verifier/falsifier sets
    'disjoint' : False,         # Allow overlapping content
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models to find
    'expectation' : True,       # Expected result (True = countermodel found)
}
REL_CM_1_example = [
    REL_CM_1_premises,
    REL_CM_1_conclusions,
    REL_CM_1_settings,
]
```


## Semantic Theory

### Theoretical Background

The relevance subtheory implements relevance logic within the hyperintensional truthmaker semantic framework. The relevance relation captures content connections between propositions through fusion closure conditions.

**Key Features**:

1. **Fusion Closure**: Central to relevance semantics
2. **Bilateral Conditions**: Both verifier and falsifier constraints
3. **Content Sensitivity**: Goes beyond extensional connections
4. **Weaker than Constitutive Relations**: More permissive than ground or essence

### Truth Conditions

#### Relevance (A ⪯ B)

**Informal Description**: A ⪯ B is true when A's content is relevant to B's content. This requires that fusing verifiers (falsifiers) of A with verifiers (falsifiers) of B produces verifiers (falsifiers) of B.

**Z3 Implementation** (from constitutive/operators.py):

```python
# Truth conditions
def true_at(self, leftarg, rightarg, eval_point):
    """Defines truth conditions for relevance relation at an evaluation point."""
    N = self.semantics.N
    sem = self.semantics
    x = z3.BitVec("t_peq_x", N)
    y = z3.BitVec("t_peq_y", N)
    return z3.And(
        ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point)
                ),
                sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
            ),
        ),
        ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point)
                ),
                sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point)
            ),
        ),
    )

def false_at(self, leftarg, rightarg, eval_point):
    """Defines falsity conditions for relevance relation at an evaluation point."""
    sem = self.semantics
    N = self.semantics.N
    x = z3.BitVec("f_seq_x", N)
    y = z3.BitVec("f_seq_y", N)
    return z3.Or(
        Exists(
            [x, y],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.extended_verify(y, rightarg, eval_point),
                z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
            ),
        ),
        Exists(
            [x, y],
            z3.And(
                sem.extended_falsify(x, leftarg, eval_point),
                sem.extended_falsify(y, rightarg, eval_point),
                z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point))
            ),
        ),
    )
```

### Verification Semantics

The relevance operator follows the **null-state verification pattern**:

- **Verifiers**: Only the null state verifies true relevance relations
- **Falsifiers**: Only the null state falsifies false relevance relations
- **Evaluation**: Truth value determined by fusion closure conditions

**Z3 Implementation** (from constitutive/operators.py):

```python
# Verifier/falsifier conditions (hyperintensional)
def extended_verify(self, state, leftarg, rightarg, eval_point):
    """Defines verification conditions for relevance relation in the extended semantics."""
    return z3.And(
        state == self.semantics.null_state,
        self.true_at(leftarg, rightarg, eval_point)
    )

def extended_falsify(self, state, leftarg, rightarg, eval_point):
    """Defines falsification conditions for relevance relation in the extended semantics."""
    return z3.And(
        state == self.semantics.null_state,
        self.false_at(leftarg, rightarg, eval_point)
    )
```

## Testing and Validation

### Theorem Examples

**Valid Principles** (should find no countermodels):

1. **REL_TH_1 - Relevance to Conjunction**:
   - `A, B ⊢ A ≺ (A ∧ B)`
   - A proposition is relevant to any conjunction containing it

2. **REL_TH_2 - Relevance to Disjunction**:
   - `⊢ A ≺ (A ∨ B)`
   - A proposition is relevant to any disjunction containing it

3. **REL_TH_7 - Grounding Relevance**:
   - `A ≤ B ⊢ A ≺ B`
   - If A grounds B, then A is relevant to B

4. **REL_TH_9 - Identity Relevance**:
   - `A ≡ B ⊢ A ≺ B`
   - If A is identical to B, then A is relevant to B

### Countermodel Examples

**Invalid Principles** (should find countermodels):

1. **REL_CM_1 - Antecedent Strengthening**:
   - `⊬ (A ∧ B) ≺ A`
   - A conjunction is not necessarily relevant to its conjunct

2. **REL_CM_3 - Relevance Transitivity**:
   - `A ≺ B, B ≺ C ⊬ A ≺ C`
   - Relevance is not transitive

3. **REL_CM_7 - Strict Implication**:
   - `□(A → B) ⊬ A ≺ B`
   - Necessary implication doesn't guarantee relevance

4. **REL_CM_10 - Conjunction Introduction**:
   - `A ≺ B ⊬ A ≺ (B ∧ C)`
   - Relevance to B doesn't imply relevance to B∧C

### Logical Properties

**Properties that HOLD**:

- Reflexivity: `(A \\preceq A)`
- Ground implies Relevance: `(A \\leq B) ⊢ (A \\preceq B)`
- Essence implies Relevance: `(A \\sqsubseteq B) ⊢ (A \\preceq B)`
- Identity implies Relevance: `(A \\equiv B) ⊢ (A \\preceq B)`
- Relevance to Disjunction: `(A \\preceq (A \\vee B))`

**Properties that FAIL**:

- Transitivity: `(A \\preceq B), (B \\preceq C) ⊬ (A \\preceq C)`
- Antecedent Strengthening: `((A \\wedge B) \\preceq A)` is invalid
- Strict Implication: `\\Box (A \\rightarrow B) ⊬ (A \\preceq B)`
- Distribution over Conjunction: Various distribution principles fail

## Integration

### Dependencies

The relevance subtheory depends on:
- **Constitutive subtheory**: Imports the `RelevanceOperator` from constitutive operators
- **Extensional subtheory**: Required by constitutive for basic logical operators

```python
# Automatic dependency loading
theory = logos.get_theory(['relevance'])  # Loads constitutive and extensional
```

### Usage with Other Subtheories

```python
# Combined with modal logic
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['relevance', 'modal'])

# REL_MOD_1: RELEVANCE IN MODAL CONTEXTS
REL_MOD_1_premises = ["\\Box (A \\rightarrow B)"]
REL_MOD_1_conclusions = ["(A \\preceq B)"]
REL_MOD_1_settings = {
    'N' : 3,                    # Number of atomic states
    'contingent' : False,       # Allow non-contingent propositions
    'non_null' : False,         # Allow null state
    'non_empty' : False,        # Allow empty verifier/falsifier sets
    'disjoint' : False,         # Allow overlapping verifier/falsifier sets
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models to find
    'expectation' : True,       # Expected result (True = countermodel found)
}
REL_MOD_1_example = [
    REL_MOD_1_premises,
    REL_MOD_1_conclusions,
    REL_MOD_1_settings,
]

# Combined with counterfactual logic
logos_registry2 = LogosOperatorRegistry()
logos_registry2.load_subtheories(['relevance', 'counterfactual'])

# REL_CF_1: RELEVANCE AND COUNTERFACTUALS
REL_CF_1_premises = ["(A \\preceq B)", "(B \\boxright C)"]
REL_CF_1_conclusions = ["(A \\preceq C)"]
REL_CF_1_settings = {
    'N' : 3,                    # Number of atomic states
    'contingent' : False,       # Allow non-contingent propositions
    'non_null' : False,         # Allow null state
    'non_empty' : False,        # Allow empty verifier/falsifier sets
    'disjoint' : False,         # Allow overlapping verifier/falsifier sets
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 1,              # Number of models to find
    'expectation' : True,       # Expected result (True = countermodel may be found)
}
REL_CF_1_example = [
    REL_CF_1_premises,
    REL_CF_1_conclusions,
    REL_CF_1_settings,
]
```

### API Reference

#### Core Functions

```python
from model_checker.theory_lib.logos.subtheories.relevance import get_operators

# Get all relevance operators
operators = get_operators()
# Returns: {
#     "\\preceq": RelevanceOperator
# }
```

#### Example Collections

```python
from model_checker.theory_lib.logos.subtheories.relevance.examples import (
    relevance_cm_examples,     # 11 countermodel examples
    relevance_th_examples,     # 9 theorem examples
    relevance_examples,        # Combined 20 examples
    example_range             # Selected examples for execution
)
```

#### Direct Operator Usage

```python
from model_checker.theory_lib.logos.subtheories.relevance.operators import (
    RelevanceOperator
)
```

## Advanced Topics

### Implementation Note

The relevance operator is implemented in the constitutive subtheory alongside other content relationship operators (ground, essence, identity). The relevance subtheory imports this operator to provide focused exploration of relevance logic principles.

This design choice reflects the theoretical connections between relevance and other hyperintensional relations while allowing specialized study of relevance logic through dedicated examples and tests.

### Fusion Closure Conditions

The relevance relation is defined by two fusion closure conditions:

**Verifier Fusion Closure**: If x verifies A and y verifies B, then x⊕y verifies B
**Falsifier Fusion Closure**: If x falsifies A and y falsifies B, then x⊕y falsifies B

These conditions capture the intuition that A is relevant to B when A's content can be "combined" with B's content in a meaningful way.

### Relevance Logic Applications

The relevance subtheory is particularly useful for:

- Analyzing relationships between hyperintensional propositions
- Testing logical principles in relevance logic
- Exploring connections between relevance and other hyperintensional operators
- Developing formal models of subject-matter sensitive reasoning

## Dependencies

The relevance subtheory depends on the **constitutive subtheory** for:

- `RelevanceOperator`: The core relevance operator implementation
- Indirect dependency on extensional operators through constitutive

```python
# Automatic dependency loading
theory = logos.get_theory(['relevance'])  # Also loads constitutive and extensional
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

- Brast-McKie, B. (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic

### Related Resources

- **[Constitutive Subtheory](../constitutive/)** - Where the relevance operator is defined
- **[Extensional Subtheory](../extensional/)** - Extensional foundation
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)
