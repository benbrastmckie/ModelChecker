# Counterfactual Subtheory: Hypothetical Reasoning in Logos Theory

The **Counterfactual Subtheory** implements operators for hypothetical reasoning within the Logos theory framework. This subtheory provides four specialized operators for evaluating counterfactual conditionals and imposition relations, enabling sophisticated analysis of "what if" scenarios and alternative possibilities.

## Overview

The Counterfactual Subtheory implements **4 logical operators** for hypothetical reasoning:

- **Counterfactual Conditional** (`\\boxright`): "If A were the case, B would be the case"
- **Might Counterfactual** (`\\diamondright`): "If A were the case, B might be the case"  
- **Imposition** (`\\imposition`): "A imposes B" (Fine's semantics for counterfactuals)
- **Might Imposition** (`\\could`): "A could impose B"

This implementation follows the semantic theory developed in:
- Brast-McKie (2025) ["Counterfactual Worlds"](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf), Journal of Philosophical Logic

For details about the underlying semantic framework, see the [Logos Theory README](../../README.md).

## Table of Contents

- [Quick Start](#quick-start)
- [Operator Reference](#operator-reference)
  - [Counterfactual Conditional](#counterfactual-conditional)
  - [Might Counterfactual](#might-counterfactual)
  - [Imposition](#imposition)
  - [Might Imposition](#might-imposition)
- [Examples](#examples)
  - [Example Categories](#example-categories)
  - [Running Examples](#running-examples)
  - [Example Structure](#example-structure)
- [Semantic Theory](#semantic-theory)
  - [Theoretical Background](#theoretical-background)
  - [Truth Conditions](#truth-conditions)
  - [Verification Semantics](#verification-semantics)
- [Testing and Validation](#testing-and-validation)
  - [Theorem Examples](#theorem-examples)
  - [Countermodel Examples](#countermodel-examples)
  - [Logical Properties](#logical-properties)
- [Integration](#integration)
  - [Dependencies](#dependencies)
  - [Usage with Other Subtheories](#usage-with-other-subtheories)
  - [API Reference](#api-reference)
- [Advanced Topics](#advanced-topics)
  - [Sobel Sequences](#sobel-sequences)
  - [Antecedent Strengthening](#antecedent-strengthening)
  - [Factivity Properties](#factivity-properties)

## Quick Start

### Basic Usage

```python
from model_checker.theory_lib import logos

# Load counterfactual subtheory (automatically loads extensional dependency)
theory = logos.get_theory(['counterfactual'])

# Check a simple counterfactual
from model_checker import BuildExample
model = BuildExample("cf_example", theory)

# Counterfactual modus ponens: If A and (A �� B), then B
result = model.check_validity(["A", "(A \\boxright B)"], ["B"])
print(f"Counterfactual Modus Ponens: {'Valid' if result else 'Invalid'}")
```

### Running Examples

```bash
# Run all counterfactual examples
model-checker src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Run in development mode
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Run with constraints printed
./dev_cli.py -p src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

### Project Generation

```bash
# Generate a project focused on counterfactual logic
./dev_cli.py -l logos  # Select counterfactual subtheory during setup
```

## Operator Reference

### Counterfactual Conditional

**Symbol**: `\\boxright` (��)  
**Name**: Counterfactual Conditional  
**Arity**: 2 (binary)  
**Type**: Primitive operator

**Meaning**: "If A were the case, then B would be the case"

**Truth Conditions**: A counterfactual conditional A �� B is true at an evaluation point when, for all states x that verify A and all alternative worlds u to x, B is true at u.

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

**Symbol**: `\\diamondright` (ǒ)  
**Name**: Might Counterfactual  
**Arity**: 2 (binary)  
**Type**: Defined operator

**Meaning**: "If A were the case, then B might be the case"

**Definition**: `�(A �� �B)` - Defined as the negation of the counterfactual conditional with negated consequent.

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

### Imposition

**Symbol**: `\\imposition`  
**Name**: Imposition  
**Arity**: 2 (binary)  
**Type**: Primitive operator

**Meaning**: "A imposes B" - Fine's semantics for counterfactuals

**Truth Conditions**: A imposes B when for all verifiers u of A and v of B, the fusion of u and v verifies B.

**Usage Examples**:
```python
# Basic imposition relation
"(p \\imposition q)"  # p imposes q

# Comparison with counterfactual conditional
# Imposition and counterfactual conditional may differ in truth conditions
```

**Key Properties**:
- **Alternative Semantics**: Provides Fine's approach to counterfactual reasoning
- **Verifier-based**: Truth conditions defined in terms of verifier fusion
- **Comparison Point**: Allows testing differences between semantic approaches

### Might Imposition

**Symbol**: `\\could`  
**Name**: Might Imposition  
**Arity**: 2 (binary)  
**Type**: Defined operator

**Meaning**: "A could impose B"

**Definition**: `�(A imposition �B)` - Defined as the negation of imposition with negated consequent.

**Usage Examples**:
```python
# Expressing possibility under imposition
"(p \\could q)"  # p could impose q

# Relationship to imposition
"(A \\imposition B) \\rightarrow (A \\could B)"  # Imposition implies might imposition
```

## Examples

### Example Categories

The counterfactual subtheory includes **33 comprehensive examples** organized into two main categories:

#### Countermodels (CF_CM_*): 21 Examples
Tests for **invalid** counterfactual arguments, demonstrating where counterfactual principles fail:

- **CF_CM_1**: Counterfactual Antecedent Strengthening  
- **CF_CM_2**: Might Counterfactual Antecedent Strengthening  
- **CF_CM_7**: Counterfactual Contraposition  
- **CF_CM_10**: Transitivity  
- **CF_CM_13**: Sobel Sequence (complex)  
- **CF_CM_15**: Counterfactual Excluded Middle  
- **CF_CM_18**: Must Factivity  
- **CF_CM_19**: Counterfactual Exportation  

#### Theorems (CF_TH_*): 12 Examples  
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

---

## References

- Brast-McKie (2025) ["Counterfactual Worlds"](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf), Journal of Philosophical Logic
- Fine (2012) ["Counterfactuals without Possible Worlds"](https://link.springer.com/article/10.1007/BF00248737), Journal of Philosophy  
- Lewis (1973) "Counterfactuals", Harvard University Press
- For semantic framework details, see [Logos Theory README](../../README.md)

## License

The counterfactual subtheory is part of the ModelChecker package and follows the same licensing terms. See `LICENSE.md` for details.