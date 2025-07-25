# Modal Subtheory: Necessity and Possibility Operators

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure
```
modal/
├── README.md               # This file - modal subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (23 examples)
├── operators.py           # Modal operator definitions (4 operators)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_modal_examples.py  # Integration tests with 23 examples
```

## Overview

The **Modal Subtheory** implements hyperintensional semantics for modal operators (necessity, possibility, counterfactual necessity, counterfactual possibility). All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond truth-functional equivalence or necessary equivalence.

Within the Logos framework, the modal subtheory provides essential operators for reasoning about necessity and possibility. The four operators integrate seamlessly with other hyperintensional operators while maintaining classical modal logic principles including S5 modal axioms and modal duality relationships. This enables sophisticated analysis of modal claims alongside counterfactual, constitutive, and relevance reasoning within a unified semantic framework.

## Quick Start

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load modal subtheory (automatically loads extensional dependency)
theory = logos.get_theory(['modal'])
model = BuildExample("modal_example", theory)

# Test basic modal principles
result1 = model.check_validity(["\\Box A"], ["A"])  # Necessity implies truth (T axiom)
result2 = model.check_validity(["\\Box (A \\rightarrow B)", "\\Box A"], ["\\Box B"])  # K axiom
result3 = model.check_validity(["\\Diamond A"], ["\\Box A"])  # Invalid: possibility ≠ necessity

print(f"T axiom: {result1}")  # False (valid argument)
print(f"K axiom: {result2}")  # False (valid argument)  
print(f"Possibility to necessity: {result3}")  # True (invalid argument)
```

## Subdirectories

### [tests/](tests/)
Comprehensive test suite with 23 integration examples covering all four modal operators. Includes countermodel examples (invalid arguments), theorem examples (valid modal principles), and definitional examples (operator relationships). Tests validate S5 modal logic principles including K, T, 4, and 5 axioms. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users
- **[Quick Start](#quick-start)** - Basic modal reasoning examples with necessity and possibility
- **[Operator Reference](#operator-reference)** - Complete guide to all four modal operators
- **[Testing Guide](tests/README.md)** - How to run and understand modal logic tests

### For Researchers
- **[Modal Logic Theory](#modal-logic-theory)** - S5 modal logic principles and axioms
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid modal reasoning patterns
- **[Dependencies](#dependencies)** - Integration with extensional foundation

### For Developers
- **[Implementation Details](operators.py)** - Modal operator definitions and semantics
- **[Examples Module](examples.py)** - Test cases and example formulas (23 examples)
- **[Integration Testing](tests/test_modal_examples.py)** - Complete test implementation

## Operator Reference

### Necessity

**Symbol**: `\\Box` (Box)  
**Name**: Necessity  
**Arity**: 1 (unary)  
**Type**: Primitive operator

**Meaning**: "It is necessarily the case that A"

**Truth Conditions**: Box A is true at a world when A is true in all possible worlds.

**Usage Examples**:
```python
# Basic necessity
"\\Box p"  # It is necessarily the case that p

# Necessity with complex formulas
"\\Box (p \\rightarrow q)"  # It is necessarily the case that if p then q

# Necessity of tautologies
"\\Box (p \\vee \\neg p)"  # It is necessarily the case that p or not p
```

**Key Properties**:
- **Truth implies Necessity**: If A is necessarily true, then A is true
- **Distribution over Conjunction**: Box(A and B) implies (Box A and Box B)
- **K Axiom**: Box(A implies B) and Box A together imply Box B
- **Necessitation**: If A is a theorem, then Box A is a theorem

### Possibility

**Symbol**: `\\Diamond` (Diamond)  
**Name**: Possibility  
**Arity**: 1 (unary)  
**Type**: Defined operator

**Meaning**: "It is possibly the case that A"

**Definition**: `\\neg \\Box \\neg A` - Defined as the negation of the necessity of the negation.

**Usage Examples**:
```python
# Basic possibility
"\\Diamond p"  # It is possibly the case that p

# Possibility with complex formulas
"\\Diamond (p \\wedge q)"  # It is possibly the case that p and q

# Possibility of contingent statements
"\\Diamond A"  # A is possibly true
```

**Key Properties**:
- **Dual of Necessity**: Diamond A is equivalent to not Box not A
- **Distribution over Disjunction**: (Diamond A or Diamond B) implies Diamond(A or B)
- **Weaker than Truth**: Diamond A does not imply A
- **Consistency**: Diamond A means A is consistent

### Counterfactual Necessity

**Symbol**: `\\CFBox`  
**Name**: Counterfactual Necessity  
**Arity**: 1 (unary)  
**Type**: Defined operator

**Meaning**: "Under counterfactual evaluation, it is necessarily the case that A"

**Definition**: `\\Box A` - Currently defined as equivalent to standard necessity.

**Usage Examples**:
```python
# Counterfactual necessity
"\\CFBox p"  # Under counterfactual evaluation, necessarily p

# Relationship to standard necessity
"\\Box A \\rightarrow \\CFBox A"  # Standard necessity implies counterfactual necessity

# Integration with counterfactuals
"\\CFBox (p \\rightarrow q)"  # Under counterfactual evaluation, necessarily if p then q
```

**Key Properties**:
- **Currently Equivalent**: CFBox A is currently equivalent to Box A
- **Future Extension**: Designed for future counterfactual-specific semantics
- **Integration Point**: Connects modal and counterfactual reasoning

### Counterfactual Possibility

**Symbol**: `\\CFDiamond`  
**Name**: Counterfactual Possibility  
**Arity**: 1 (unary)  
**Type**: Defined operator

**Meaning**: "Under counterfactual evaluation, it is possibly the case that A"

**Definition**: `\\Diamond A` - Currently defined as equivalent to standard possibility.

**Usage Examples**:
```python
# Counterfactual possibility
"\\CFDiamond p"  # Under counterfactual evaluation, possibly p

# Relationship to standard possibility
"\\Diamond A \\rightarrow \\CFDiamond A"  # Standard possibility implies counterfactual possibility

# Modal duality in counterfactual context
"\\CFDiamond A \\equiv \\neg \\CFBox \\neg A"  # Counterfactual modal duality
```

**Key Properties**:
- **Currently Equivalent**: CFDiamond A is currently equivalent to Diamond A
- **Future Extension**: Designed for future counterfactual-specific semantics
- **Dual Structure**: Maintains duality with counterfactual necessity

## Examples

### Example Categories

The modal subtheory includes **23 comprehensive examples** organized into three main categories:

#### Countermodels (MOD_CM_*): 3 Examples
Tests for **invalid** modal arguments, demonstrating where modal principles fail:

- **MOD_CM_1**: Possibility Does Not Entail Necessity (invalid)
- **MOD_CM_2**: Possibility to Actuality (invalid)
- **MOD_CM_3**: Counterfactual to Strict Implication (invalid)

#### Theorems (MOD_TH_*): 14 Examples
Tests for **valid** modal arguments, confirming standard modal logic principles:

- **MOD_TH_1**: Necessity Distribution over Conjunction
- **MOD_TH_2**: Possibility Distribution over Disjunction
- **MOD_TH_3**: Modal Duality (Box to Diamond)
- **MOD_TH_4**: Modal Duality (Diamond and Box)
- **MOD_TH_5**: Modal K Axiom
- **MOD_TH_6**: Necessitation Rule
- **MOD_TH_7**: Counterfactual Necessity Implies Necessity
- **MOD_TH_8**: Possibility Implies Counterfactual Possibility
- **MOD_TH_9**: Counterfactual Modal Duality
- **MOD_TH_10**: Double Necessity (Idempotence)
- **MOD_TH_11**: 5 Axiom (Euclidean Property)
- **MOD_TH_12**: Box-to-Top Equivalence
- **MOD_TH_13**: Top-to-Box Equivalence
- **MOD_TH_14**: Necessary Equivalence of Tautologies

#### Definitional Examples (MOD_DEF_*): 6 Examples
Tests for **definitional relationships** between primitive and defined modal operators:

- **MOD_DEF_1**: Primitive vs Defined Necessity
- **MOD_DEF_2**: Defined vs Primitive Necessity  
- **MOD_DEF_3**: Primitive vs Defined Possibility
- **MOD_DEF_4**: Defined vs Primitive Possibility
- **MOD_DEF_5**: Necessity and Negated Possibility
- **MOD_DEF_6**: Possibility and Negated Necessity

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/modal/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/modal/examples.py
```

#### Programmatic Access

```python
from model_checker.theory_lib.logos.subtheories.modal.examples import (
    modal_cm_examples,     # All countermodel examples
    modal_th_examples,     # All theorem examples
    modal_def_examples,    # All definitional examples
    modal_examples         # Combined collection
)

# Access specific example
mod_th_5 = modal_th_examples['MOD_TH_5']
premises, conclusions, settings = mod_th_5

# Run example with custom theory
from model_checker import BuildExample
from model_checker.theory_lib import logos

theory = logos.get_theory(['modal'])
model = BuildExample("modal_test", theory)
result = model.check_validity(premises, conclusions, settings)
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

**Settings Explanation**:
- `N`: Controls state space size (moderate N suitable for modal logic)
- `contingent`: Whether atomic propositions must be contingent
- `non_null`: Whether to exclude the null state from consideration
- `non_empty`: Whether propositions must have non-empty truth sets
- `expectation`: Expected model-finding result (False for valid arguments, True for invalid)

## Modal Logic Theory

### Classical Modal Logic

The modal subtheory implements core principles of classical modal logic:

**Basic Principles**:
1. **Necessity implies Truth**: If something is necessarily true, then it is true
2. **Possibility from Truth**: If something is true, it could be possibly true (though not required)
3. **Modal Duality**: Necessity and possibility are dual notions
4. **Distribution Properties**: Modal operators interact systematically with logical connectives

**Truth Conditions**:
- **Box A**: True when A is true in all possible worlds
- **Diamond A**: True when A is true in at least one possible world

### Modal Axioms

The subtheory validates key modal axioms:

**K Axiom (Distribution)**:
```python
# Box(A implies B) and Box A together imply Box B
premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
conclusion = "\\Box B"  # Valid
```

**T Axiom (Reflexivity)**:
```python
# Box A implies A
premises = ["\\Box A"]  
conclusion = "A"  # Valid
```

**5 Axiom (Euclidean)**:
```python
# Diamond A implies Box Diamond A
premises = ["\\Diamond A"]
conclusion = "\\Box \\Diamond A"  # Valid
```

**4 Axiom (Transitivity)**:
```python
# Box A implies Box Box A
premises = ["\\Box A"]
conclusion = "\\Box \\Box A"  # Valid (via double necessity)
```

### Modal Duality

Modal operators exhibit systematic duality relationships:

**Standard Duality**:
```python
# Box A equivalent to not Diamond not A
"\\Box A \\equiv \\neg \\Diamond \\neg A"  # Valid

# Diamond A equivalent to not Box not A  
"\\Diamond A \\equiv \\neg \\Box \\neg A"  # Valid
```

**Counterfactual Duality**:
```python
# CFBox A equivalent to not CFDiamond not A
"\\CFBox A \\equiv \\neg \\CFDiamond \\neg A"  # Valid
```

## Testing and Validation

### Theorem Examples

**Valid Principles** (should always find models for premises but not conclusions):

1. **MOD_TH_5 - Modal K Axiom**:
   - `[Box(A implies B), Box A] entails Box B`
   - Basic modal inference rule

2. **MOD_TH_1 - Necessity Distribution over Conjunction**:
   - `[Box(A and B)] entails (Box A and Box B)`
   - Necessity distributes over conjunction

3. **MOD_TH_11 - 5 Axiom**:
   - `[Diamond A] entails Box Diamond A`
   - Euclidean property of modal accessibility

4. **MOD_TH_14 - Necessary Equivalence of Tautologies**:
   - `[] entails Box((A or not A) iff (B or not B))`
   - All tautologies are necessarily equivalent

### Countermodel Examples

**Invalid Principles** (should find countermodels where premises are true but conclusions false):

1. **MOD_CM_1 - Possibility Does Not Entail Necessity**:
   - `[Diamond A] does-not-entail Box A`
   - Being possibly true does not make something necessarily true

2. **MOD_CM_2 - Possibility to Actuality**:
   - `[Diamond A] does-not-entail A`
   - Being possibly true does not make something actually true

3. **MOD_CM_3 - Counterfactual to Strict Implication**:
   - `[(A boxright B)] does-not-entail Box(A implies B)`
   - Counterfactual conditionals do not imply necessary implications

### Definitional Examples

**Definitional Equivalences** (testing relationships between primitive and defined operators):

1. **MOD_DEF_1/DEF_2 - Necessity Equivalences**:
   - `Box A entails CFBox A` and `CFBox A entails Box A`
   - Current equivalence of standard and counterfactual necessity

2. **MOD_DEF_5/DEF_6 - Modal Duality**:
   - `Box A entails not Diamond not A` and `Diamond A entails not Box not A`
   - Standard modal duality relationships

## Integration

### Dependencies

The modal subtheory depends on the **extensional subtheory** for:
- `NegationOperator`: Required for defining possibility as negation of necessity of negation
- Basic logical operators used in complex modal formulas

```python
# Automatic dependency loading
theory = logos.get_theory(['modal'])  # Also loads extensional
```

### Usage with Other Subtheories

```python
# Combined with counterfactual logic
theory = logos.get_theory(['modal', 'counterfactual'])

# Modal and counterfactual interaction
premises = ["\\Box p", "(p \\boxright q)"]
conclusion = "\\Box q"
result = model.check_validity(premises, [conclusion])

# Combined with constitutive operators
theory = logos.get_theory(['modal', 'constitutive'])

# Necessity and identity interaction
premises = ["\\Box p", "(p \\equiv q)"]
conclusion = "\\Box q"
result = model.check_validity(premises, [conclusion])
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
    modal_cm_examples,      # 3 countermodel examples
    modal_th_examples,      # 14 theorem examples
    modal_def_examples,     # 6 definitional examples
    modal_examples,         # Combined 23 examples
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

### Modal Systems

The modal subtheory currently implements a system similar to **S5 modal logic**:

**S5 Characteristics**:
- **Reflexive**: Box A implies A (T axiom)
- **Symmetric**: Diamond A implies Box Diamond A (5 axiom)  
- **Transitive**: Box A implies Box Box A (4 axiom)
- **Euclidean**: Diamond A implies Box Diamond A (5 axiom)

**Other Systems**: The framework can be adapted to implement other modal systems (K, T, S4, etc.) by modifying the semantic constraints.

### Counterfactual Modal Operators

The CFBox and CFDiamond operators provide integration points for counterfactual reasoning:

**Current Implementation**:
- CFBox A is equivalent to Box A
- CFDiamond A is equivalent to Diamond A

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
"(\\top \\boxright \\Box A) \\equiv \\CFBox A"  # Future equivalence
```

### Truth-functional vs Modal

The modal subtheory reveals the distinction between truth-functional and modal operators:

**Truth-functional Operators** (extensional):
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
# Truth-functional: A or not A is always true
"(A \\vee \\neg A)"  # Tautology

# Modal: Necessarily A or not A
"\\Box (A \\vee \\neg A)"  # Necessary tautology

# Mixed: Possibly A and necessarily not A
"(\\Diamond A \\wedge \\Box \\neg A)"  # Inconsistent
```

## Dependencies

The modal subtheory depends on the **extensional subtheory** for:
- `NegationOperator`: Required for defining possibility as negation of necessity of negation
- Basic logical operators used in complex modal formulas

```python
# Automatic dependency loading
theory = logos.get_theory(['modal'])  # Also loads extensional
```

## Testing

The modal subtheory includes **23 comprehensive test examples** covering all four modal operators through countermodel, theorem, and definitional examples. Tests validate S5 modal logic principles including K, T, 4, and 5 axioms.

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
- Lewis (1973) ["Counterfactuals"](https://press.princeton.edu/books/paperback/9780631224259/counterfactuals), Harvard University Press
- Kripke (1963) ["Semantical Analysis of Modal Logic"](https://doi.org/10.1007/BF01028024), Zeitschrift für mathematische Logik
- Hughes & Cresswell (1996) ["A New Introduction to Modal Logic"](https://www.routledge.com/A-New-Introduction-to-Modal-Logic/Hughes-Cresswell/p/book/9780415125994), Routledge

### Related Resources
- **[Extensional Subtheory](../extensional/)** - Truth-functional foundation for modal operators
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation
- **[Counterfactual Subtheory](../counterfactual/)** - Integration with counterfactual reasoning

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)