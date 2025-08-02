# Constitutive Subtheory: Propositional Content Relationships

[← Back to Subtheories](../README.md) | [Citation →](CITATION.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure

```
constitutive/
├── README.md               # This file - constitutive subtheory overview
├── __init__.py            # Module initialization and public API
├── examples.py            # Example formulas and test cases (33 examples)
├── operators.py           # Content relationship operator definitions (5 operators)
└── tests/                 # Test suite (see tests/README.md)
    ├── README.md          # Test documentation and methodology
    ├── __init__.py        # Test module initialization
    └── test_constitutive_examples.py  # Integration tests with 33 examples
```

## Overview

The **Constitutive Subtheory** implements hyperintensional semantics for identity (≡), ground (≤), essence (⊑), and relevance (⪯) as primitive operators, with reduction (⟹) as a defined operator. All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond extensional equivalence or necessary equivalence.

This subtheory serves as the foundation for hyperintensional reasoning within the Logos framework, implementing the semantic theory developed in Brast-McKie (2021) and providing essential operators for expressing content relationships while maintaining integration with modal, extensional, and counterfactual reasoning which are also included in the Logos.

## Subdirectories

### [tests/](tests/)

Comprehensive test suite with 33 integration examples covering all five content operators. Includes countermodel examples (invalid intensional principles), theorem examples (valid hyperintensional principles), and exploration of reasoning that is sensitive to differences in subject-matter. Tests validate hyperintensional distinctions that intensional logic cannot capture. See [tests/README.md](tests/README.md) for complete testing methodology.

## Documentation

### For New Users

- **[Examples](examples.py)** - Complete collection of validated examples
- **[Operator Reference](#operator-reference)** - Complete guide to all five content operators
- **[Testing Guide](tests/README.md)** - How to run and understand hyperintensional tests

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Hyperintensional truthmaker semantics and theoretical background
- **[Test Examples](tests/README.md#test-categories)** - Valid and invalid content reasoning patterns
- **[Academic References](#references)** - Primary sources and theoretical foundations

### For Developers

- **[Implementation Details](operators.py)** - Content operator definitions and truthmaker semantics
- **[Examples Module](examples.py)** - Test cases and example formulas (33 examples)
- **[Integration Testing](tests/test_constitutive_examples.py)** - Complete test implementation

## Operator Reference

The constitutive subtheory provides five operators: four primitive operators that directly implement truthmaker semantics, and one defined operator constructed from the primitives.

**Primitive Operators:**
- Identity (≡) - Content identity relation
- Ground (≤) - Disjunctive-part/grounding relation  
- Essence (⊑) - Conjunctive-part/essence relation
- Relevance (⪯) - Subject-matter overlap relation

**Defined Operator:**
- Reduction (⟹) - Defined as conjunction of ground and essence: (A ⟹ B) ≡ (A ≤ B) ∧ (A ⊑ B)

### Identity

**Symbol**: `\\equiv` (displayed as ≡)
**Name**: Identity
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "A has exactly the same content as B"

**Truth Conditions**: Two propositions A and B are identical when they have exactly the same verifiers and exactly the same falsifiers.

**Usage Examples**:

```python
# Basic identity
"(p \\equiv q)"  # p is identical to q

# Identity with complex formulas
"((p \\wedge q) \\equiv (q \\wedge p))"  # Conjunction commutativity

# Self-identity
"(A \\equiv A)"  # Always valid (reflexivity)
```

**Key Properties**:

- **Reflexivity**: `(A \\equiv A)` is always valid
- **Symmetry**: `(A \\equiv B)` implies `(B \\equiv A)`
- **Transitivity**: `(A \\equiv B)` and `(B \\equiv C)` imply `(A \\equiv C)`
- **Negation Transparency**: `(A \\equiv B)` implies `(\\neg A \\equiv \\neg B)`

### Ground

**Symbol**: `\\leq` (displayed as ≤)
**Name**: Ground (Disjunctive-Part)
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "A grounds B" or "A is a disjunctive-part of B"

**Truth Conditions**: A grounds B when:

1. Every verifier of A is a verifier of B
2. For any A-falsifier and B-falsifier, their fusion falsifies B
3. Every falsifier of B contains some falsifier of A as a part

**Usage Examples**:

```python
# Basic grounding
"(p \\leq q)"  # p grounds q

# Grounding with conjunction
"(p \\leq (p \\vee q))"  # p grounds p or q (valid)

# Invalid grounding
"((p \\wedge q) \\leq p)"  # p and q does not ground p (invalid)
```

**Key Properties**:

- **Reflexivity**: `(A \\leq A)` is always valid
- **Transitivity**: `(A \\leq B)` and `(B \\leq C)` imply `(A \\leq C)`
- **Anti-symmetry**: `(A \\leq B)` and `(B \\leq A)` imply `(A \\equiv B)`
- **Strict Implication**: `(A \\leq B)` implies `Box(A \\rightarrow B)`

### Essence

**Symbol**: `\\sqsubseteq` (displayed as ⊑)
**Name**: Essence (Conjunctive-Part)
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "A is essential to B" or "A is a conjunctive-part of B"

**Truth Conditions**: A is essential to B when:

1. For any A-verifier and B-verifier, their fusion verifies B
2. Every verifier of B contains some verifier of A as a part
3. Every falsifier of A is a falsifier of B

**Usage Examples**:

```python
# Basic essence
"(p \\sqsubseteq q)"  # p is essential to q

# Essence with conjunction
"(p \\sqsubseteq (p \\wedge q))"  # p is essential to p and q (valid)

# Invalid essence
"(p \\sqsubseteq (p \\vee q))"  # p is not essential to p or q (invalid)
```

**Key Properties**:

- **Reflexivity**: `(A \\sqsubseteq A)` is always valid
- **Transitivity**: `(A \\sqsubseteq B)` and `(B \\sqsubseteq C)` imply `(A \\sqsubseteq C)`
- **Anti-symmetry**: `(A \\sqsubseteq B)` and `(B \\sqsubseteq A)` imply `(A \\equiv B)`
- **Converse Strict Implication**: `(A \\sqsubseteq B)` implies `Box(B \\rightarrow A)`

### Relevance

**Symbol**: `\\preceq` (displayed as ⪯)
**Name**: Relevance
**Arity**: 2 (binary)
**Type**: Primitive operator

**Meaning**: "A is relevant to B"

**Truth Conditions**: A is relevant to B when:

1. The fusion of any A-verifier with any B-verifier verifies B
2. The fusion of any A-falsifier with any B-falsifier falsifies B

**Usage Examples**:

```python
# Basic relevance
"(p \\preceq q)"  # p is relevant to q

# Self-relevance
"(A \\preceq A)"  # Always valid

# Relevance with complex formulas
"((p \\wedge q) \\preceq p)"  # p and q is relevant to p
```

**Key Properties**:

- **Reflexivity**: `(A \\preceq A)` is always valid
- **Weakest Relation**: Implied by both ground and essence
- **Transitivity**: Generally valid
- **Content Interaction**: Captures subject-matter inclusion

### Reduction

**Symbol**: `\\Rightarrow` (displayed as ⟹)
**Name**: Reduction
**Arity**: 2 (binary)
**Type**: Defined operator

**Meaning**: "A reduces to B" (A both grounds and is essential to B)

**Definition**: `(A \\leq B) \\wedge (A \\sqsubseteq B)` - Defined as the conjunction of ground and essence.

**Usage Examples**:

```python
# Basic reduction
"(p \\Rightarrow q)"  # p reduces to q

# Reduction with absorption laws
"(A \\Rightarrow (A \\wedge (A \\vee B)))"  # Valid absorption reduction

# Reduction with distribution
"((A \\vee (A \\wedge B)) \\Rightarrow (A \\wedge (A \\vee B)))"  # Valid distribution reduction
```

**Key Properties**:

- **Strongest Relation**: Combines both ground and essence
- **Absorption Laws**: Valid for absorption formulas
- **Distribution Laws**: Valid for certain distribution patterns
- **Content Equivalence**: Strongest content relationship short of identity

## Examples

### Example Categories

The constitutive subtheory includes **33 comprehensive examples** organized into two main categories, testing both primitive operators (identity, ground, essence, relevance) and the defined reduction operator:

#### Countermodels (CL_CM_*): 14 Examples

Tests for **invalid** constitutive arguments, demonstrating where intensional principles fail in hyperintensional logic:

- **CL_CM_1**: Equivalence of Tautologies (tautologies are not identical)
- **CL_CM_2**: Equivalence of Contradictions (contradictions are not identical)
- **CL_CM_3**: Ground Conjunction Supplementation (invalid)
- **CL_CM_4**: Essence Disjunction Supplementation (invalid)
- **CL_CM_5**: Identity Absorption: Disjunction over Conjunction (invalid)
- **CL_CM_6**: Identity Absorption: Conjunction over Disjunction (invalid)
- **CL_CM_7**: Identity Distribution: Conjunction over Disjunction (invalid)
- **CL_CM_8**: Identity Distribution: Disjunction over Conjunction (invalid)
- **CL_CM_9**: Strict Implication to Ground (invalid)
- **CL_CM_10**: Strict Implication to Essence (invalid)
- **CL_CM_11**: Essence Distribution (invalid)
- **CL_CM_12**: Ground Distribution (invalid)
- **CL_CM_13**: Shannon Expansion (invalid)
- **CL_CM_14**: Dual Shannon Expansion (invalid)

#### Theorems (CL_TH_*): 19 Examples

Tests for **valid** constitutive arguments, confirming valid hyperintensional principles:

- **CL_TH_1**: Ground to Essence (interconversion)
- **CL_TH_2**: Essence to Ground (interconversion)
- **CL_TH_3**: Essence to Identity (interaction)
- **CL_TH_4**: Identity to Essence (interaction)
- **CL_TH_5**: Ground to Identity (interaction)
- **CL_TH_6**: Identity to Ground (interaction)
- **CL_TH_7**: Negation Transparency (identity preserved under negation)
- **CL_TH_8**: Reverse Negation Transparency
- **CL_TH_9**: Absorption Identity
- **CL_TH_10-13**: Absorption and Distribution Reductions
- **CL_TH_14**: Ground to Strict Implication
- **CL_TH_15**: Essence to Converse Strict Implication
- **CL_TH_16-17**: Anti-symmetry principles
- **CL_TH_18-19**: Transitivity principles

### Running Examples

#### Command Line Execution

```bash
# Run all examples
model-checker src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py

# Run with debugging output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py
```

#### Running Tests

The constitutive subtheory includes **33 comprehensive test examples** covering all five operators through both countermodel and theorem examples. Tests validate hyperintensional content relationships and demonstrate where intensional principles fail.

```bash
# Run all constitutive tests
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_CM_1"

# Run via project test runner
python test_theories.py --theories logos --constitutive --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

### Example Structure

Each example follows the standard format:

```python
# CL_TH_16: GROUNDING ANTI-SYMMETRY
CL_TH_16_premises = ['(A \\leq B)', '(B \\leq A)']
CL_TH_16_conclusions = ['(A \\equiv B)']
CL_TH_16_settings = {
    'N' : 2,
    'contingent' : False,
    'non_null' : False,
    'non_empty' : False,
    'disjoint' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : False,
}
CL_TH_16_example = [
    CL_TH_16_premises,
    CL_TH_16_conclusions,
    CL_TH_16_settings,
]
```

## Semantic Theory

### Theoretical Background

The constitutive subtheory implements the semantic theory developed in Brast-McKie (2021), which provides a hyperintensional approach to content relationships based on truthmaker semantics.

**Key Innovations**:

1. **Hyperintensional Propositions**: Propositions individuated by verifier and falsifier sets
2. **Content-Based Relations**: Operators defined in terms of content overlap and containment
3. **Bilateral Semantics**: Both positive (verifiers) and negative (falsifiers) conditions
4. **Fine-Grained Distinctions**: Distinguishes necessarily equivalent but content-distinct propositions

### Truth Conditions

#### Identity (A ≡ B)

**Z3 Implementation** (simplified from operators.py):

```python
# Identity requires exact same verifiers and falsifiers
ForAll([x], 
    z3.And(
        # Same verifiers
        semantics.extended_verify(x, leftarg, eval_point) == 
        semantics.extended_verify(x, rightarg, eval_point),
        # Same falsifiers
        semantics.extended_falsify(x, leftarg, eval_point) == 
        semantics.extended_falsify(x, rightarg, eval_point)
    )
)
```

#### Ground (A ≤ B)

**Z3 Implementation** (from operators.py):

```python
# Ground has three conditions
conditions = [
    # 1. All A-verifiers are B-verifiers
    ForAll([x], z3.Implies(
        semantics.extended_verify(x, leftarg, eval_point),
        semantics.extended_verify(x, rightarg, eval_point)
    )),
    # 2. Fusion condition for falsifiers
    ForAll([x, y], z3.Implies(
        z3.And(
            semantics.extended_falsify(x, leftarg, eval_point),
            semantics.extended_falsify(y, rightarg, eval_point)
        ),
        semantics.extended_falsify(semantics.fusion(x, y), rightarg, eval_point)
    )),
    # 3. Every B-falsifier contains an A-falsifier
    ForAll([x], z3.Implies(
        semantics.extended_falsify(x, rightarg, eval_point),
        z3.Exists([y], z3.And(
            semantics.extended_falsify(y, leftarg, eval_point),
            semantics.part_of(y, x)
        ))
    ))
]
```

#### Essence (A ⊑ B)

**Z3 Implementation** (from operators.py):

```python
# Essence has three conditions
conditions = [
    # 1. Fusion condition for verifiers
    ForAll([x, y], z3.Implies(
        z3.And(
            semantics.extended_verify(x, leftarg, eval_point),
            semantics.extended_verify(y, rightarg, eval_point)
        ),
        semantics.extended_verify(semantics.fusion(x, y), rightarg, eval_point)
    )),
    # 2. Every B-verifier contains an A-verifier
    ForAll([x], z3.Implies(
        semantics.extended_verify(x, rightarg, eval_point),
        z3.Exists([y], z3.And(
            semantics.extended_verify(y, leftarg, eval_point),
            semantics.part_of(y, x)
        ))
    )),
    # 3. All A-falsifiers are B-falsifiers
    ForAll([x], z3.Implies(
        semantics.extended_falsify(x, leftarg, eval_point),
        semantics.extended_falsify(x, rightarg, eval_point)
    ))
]
```

#### Relevance (A ⪯ B)

**Z3 Implementation** (from operators.py):

```python
# Relevance has two fusion conditions
conditions = [
    # 1. Fusion of verifiers verifies B
    ForAll([x, y], z3.Implies(
        z3.And(
            semantics.extended_verify(x, leftarg, eval_point),
            semantics.extended_verify(y, rightarg, eval_point)
        ),
        semantics.extended_verify(semantics.fusion(x, y), rightarg, eval_point)
    )),
    # 2. Fusion of falsifiers falsifies B
    ForAll([x, y], z3.Implies(
        z3.And(
            semantics.extended_falsify(x, leftarg, eval_point),
            semantics.extended_falsify(y, rightarg, eval_point)
        ),
        semantics.extended_falsify(semantics.fusion(x, y), rightarg, eval_point)
    ))
]
```

### Hyperintensional Content

The constitutive operators are **hyperintensional**, meaning they distinguish between necessarily equivalent propositions with distinct subject-matter:

**Intensional Logic**: (A ∨ ¬A) ↔ (B ∨ ¬B) (all tautologies equivalent)
**Hyperintensional Logic**: (A ∨ ¬A) ≢ (B ∨ ¬B) (different tautologies not identical)

This allows for fine-grained analysis of:

- **Subject-Matter Sensitivity**: Tracks what a proposition is about
- **Constitutive Relations**: Captures constitutive dependence needed to track explanatory relationships

## Testing and Validation

### Theorem Examples

**Valid Principles** (should always find models for premises but not conclusions):

1. **CL_TH_16 - Grounding Anti-symmetry**:

   - `[(A \\leq B), (B \\leq A)] entails (A \\equiv B)`
   - If A grounds B and B grounds A, then A is identical to B

2. **CL_TH_7 - Negation Transparency**:

   - `[(A \\equiv B)] entails (\\neg A \\equiv \\neg B)`
   - If A is identical to B, then it not being the case that A is identical to it not being the case that B

3. **CL_TH_3 - Essence to Identity**:

   - `[(A \\sqsubseteq B)] entails ((A \\wedge B) \\equiv B)`
   - If A is essential for B, then A and B is identical to B

4. **CL_TH_14 - Ground to Strict Implication**:
   - `[(A \\leq B)] entails Box(A -> B)`
   - If A grounds B, then necessarily if A then B

### Countermodel Examples

**Invalid Principles** (should find countermodels where premises are true but conclusions false):

1. **CL_CM_1 - Equivalence of Tautologies**:

   - `[] does-not-entail ((A \\vee \\neg A) \\equiv (B \\vee \\neg B))`
   - A or it not being the case that A is not necessarily identical to B or it not being the case that B

2. **CL_CM_7 - Identity Distribution**:

   - `[] does-not-entail ((A \\wedge (B \\vee C)) \\equiv ((A \\wedge B) \\vee (A \\wedge C)))`
   - Distribution law fails for identity

3. **CL_CM_9 - Strict Implication to Ground**:

   - `[Box(A -> B)] does-not-entail (A \\leq B)`
   - Necessarily if A then B does not imply that A grounds B

4. **CL_CM_13 - Shannon Expansion**:
   - `[] does-not-entail (A \\equiv ((A \\wedge B) \\vee (A \\wedge \\neg B)))`
   - A is not necessarily identical to A and B or A and it not being the case that B

### Logical Properties

**Properties that HOLD**:

- Reflexivity: All operators are reflexive
- Transitivity: Ground, essence, and relevance are transitive
- Anti-symmetry: Ground and essence satisfy anti-symmetry
- Negation Transparency: Identity preserved under negation
- Interconversion: Ground and essence convert through negation

**Properties that FAIL**:

- Hyperintensional Equivalence: More fine-grained than either extensional equivalence and necessary equivalence
- Absorption Laws: Only hold in one direction
- Distribution Laws: Only hold in one direction
- Essence Supplementation: Essence only satisfies conjunction supplementation
- Ground Supplementation: Ground only satisfies disjunction supplementation

## Integration

### Dependencies

The constitutive subtheory depends on the **extensional subtheory** for:

- `NegationOperator` (¬): Used in operator interdefinability
- `AndOperator` (∧): Required for defining reduction operator
- `OrOperator` (∨): Used in example formulas
- `ImplicationOperator` (→): Used in test examples
- `BiconditionalOperator` (↔): Used in equivalence tests
- `TopOperator` (⊤): Truth constant
- `BottomOperator` (⊥): Falsity constant

```python
# Automatic dependency loading
theory = logos.get_theory(['constitutive'])  # Also loads extensional
```

### Usage with Other Subtheories

```python
# Combined with modal logic
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['constitutive', 'modal'])

# CON_MOD_1: GROUND AND NECESSITY INTERACTION
CON_MOD_1_premises = ['(A \\leq B)', '\\Box A']
CON_MOD_1_conclusions = ['\\Box B']
CON_MOD_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : False,
    'non_empty' : False,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
CON_MOD_1_example = [
    CON_MOD_1_premises,
    CON_MOD_1_conclusions,
    CON_MOD_1_settings,
]

# Combined with counterfactual operators
logos_registry2 = LogosOperatorRegistry()
logos_registry2.load_subtheories(['constitutive', 'counterfactual'])

# CON_CF_1: IDENTITY AND COUNTERFACTUAL INTERACTION
CON_CF_1_premises = ['(A \\equiv B)', '(A \\boxright C)']
CON_CF_1_conclusions = ['(B \\boxright C)']
CON_CF_1_settings = {
    'N' : 3,
    'contingent' : False,
    'non_null' : False,
    'non_empty' : False,
    'disjoint' : False,
    'max_time' : 1,
    'iterate' : 1,
    'expectation' : False,
}
CON_CF_1_example = [
    CON_CF_1_premises,
    CON_CF_1_conclusions,
    CON_CF_1_settings,
]
```

### API Reference

#### Core Functions

```python
from model_checker.theory_lib.logos.subtheories.constitutive import get_operators

# Get all constitutive operators
operators = get_operators()
# Returns: {
#     "\\equiv": IdentityOperator,
#     "\\leq": GroundOperator,
#     "\\sqsubseteq": EssenceOperator,
#     "\\preceq": RelevanceOperator,
#     "\\Rightarrow": ReductionOperator
# }
```

#### Example Collections

```python
from model_checker.theory_lib.logos.subtheories.constitutive.examples import (
    constitutive_cm_examples,     # 14 countermodel examples
    constitutive_th_examples,     # 19 theorem examples
    constitutive_examples,        # Combined 33 examples
)
```

#### Direct Operator Usage

```python
from model_checker.theory_lib.logos.subtheories.constitutive.operators import (
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
    ReductionOperator
)
```

## Advanced Topics

### Intensional vs Hyperintensional Logic

The constitutive subtheory reveals key differences between intensional and hyperintensional logic:

**Intensional Logic** (possible worlds):

- All tautologies are equivalent: (A ∨ ¬A) ↔ (B ∨ ¬B)
- Distribution laws: A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C)
- Absorption laws: A ↔ A ∧ (A ∨ B)

**Hyperintensional Logic** (states):

- Tautologies differ in subject-matter: (A ∨ ¬A) ≢ (B ∨ ¬B)
- Distribution fails: A ∧ (B ∨ C) ≢ (A ∧ B) ∨ (A ∧ C)
- Absorption fails: A ≢ A ∧ (A ∨ B)

### Operator Interdefinability

The constitutive operators exhibit interesting interdefinability patterns:

**Ground-Essence Duality**:

```python
# A grounds B iff it not being the case that A is essential for it not being the case that B
"(A \\leq B) \\equiv (\\neg A \\sqsubseteq \\neg B)"  # Valid

# A is essential for B iff it not being the case that A grounds it not being the case that B
"(A \\sqsubseteq B) \\equiv (\\neg A \\leq \\neg B)"  # Valid
```

**Identity Characterizations**:

```python
# A is identical to B iff A grounds B and B grounds A
"(A \\equiv B) \\equiv ((A \\leq B) \\wedge (B \\leq A))"  # Valid

# A is identical to B iff A is essential for B and B is essential for A
"(A \\equiv B) \\equiv ((A \\sqsubseteq B) \\wedge (B \\sqsubseteq A))"  # Valid
```

**Reduction Decomposition**:

```python
# A reduces to B iff A grounds B and A is essential for B
"(A \\Rightarrow B) \\equiv ((A \\leq B) \\wedge (A \\sqsubseteq B))"  # By definition
```

### Subject-Matter Sensitivity

The constitutive operators enable analysis of **subject-matter sensitivity**:

**Subject-Matter Individuation**:

- What makes propositions about the same subject-matter?
- How do we individuate propositional subject-matter?
- When do propositions share subject-matter?

**Dependence Analysis**:

- What does it mean for one proposition to depend on another?
- How do ground and essence capture different dependency relations?
- When is subject-matter overlap sufficient for logical connection?

**Hyperintensional Reasoning**:

- Moving beyond extensional logic
- Analyzing subject-matter relationships
- Understanding aboutness and topicality

## Dependencies

The constitutive subtheory depends on the **extensional subtheory** for:

- `NegationOperator` (¬): Used in operator interdefinability (ground-essence duality)
- `AndOperator` (∧): Required for defining reduction operator as conjunction of ground and essence
- `OrOperator` (∨): Used in complex example formulas
- `ImplicationOperator` (→): Used in test examples and logical principles
- `BiconditionalOperator` (↔): Used in equivalence tests and definitions
- `TopOperator` (⊤): Truth constant for semantic testing
- `BottomOperator` (⊥): Falsity constant for semantic testing

```python
# Automatic dependency loading
theory = logos.get_theory(['constitutive'])  # Also loads extensional
```

## Testing

The constitutive subtheory includes **33 comprehensive test examples** covering all five content operators through countermodel examples (invalid intensional principles) and theorem examples (valid hyperintensional principles).

```bash
# Run all constitutive tests
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_CM_1"

# Run via project test runner
python test_theories.py --theories logos --constitutive --examples
```

## References

### Primary Sources

- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content I"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content II"](https://doi.org/10.1007/s10992-016-9419-5), Journal of Philosophical Logic

### Related Resources

- **[Extensional Subtheory](../extensional/)** - Extensional foundation for constitutive operators
- **[Modal Subtheory](../modal/)** - Integration with necessity and possibility
- **[Logos Theory](../../README.md)** - Complete hyperintensional framework documentation

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)
