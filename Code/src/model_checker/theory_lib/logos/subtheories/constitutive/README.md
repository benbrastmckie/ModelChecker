# Constitutive Subtheory: Propositional Content Relationships in Logos Theory

The **Constitutive Subtheory** implements operators for analyzing relationships between propositional content within the Logos theory framework. This subtheory provides five specialized operators for evaluating identity, grounding, essence, relevance, and reduction relations between propositions, enabling sophisticated analysis of hyperintensional content relationships.

## Overview

The Constitutive Subtheory implements **5 logical operators** for content relationships:

- **Identity** (`\\equiv`): "A has exactly the same content as B"
- **Ground** (`\\leq`): "A grounds B" or "A is a disjunctive-part of B"
- **Essence** (`\\sqsubseteq`): "A is essential to B" or "A is a conjunctive-part of B"
- **Relevance** (`\\preceq`): "A is relevant to B"
- **Reduction** (`\\Rightarrow`): "A reduces to B" (ground + essence)

This implementation follows the semantic theory developed in:
- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic

For details about the underlying semantic framework, see the [Logos Theory README](../../README.md).

## Table of Contents

- [Quick Start](#quick-start)
- [Operator Reference](#operator-reference)
  - [Identity](#identity)
  - [Ground](#ground)
  - [Essence](#essence)
  - [Relevance](#relevance)
  - [Reduction](#reduction)
- [Examples](#examples)
  - [Example Categories](#example-categories)
  - [Running Examples](#running-examples)
  - [Example Structure](#example-structure)
- [Semantic Theory](#semantic-theory)
  - [Theoretical Background](#theoretical-background)
  - [Truth Conditions](#truth-conditions)
  - [Hyperintensional Content](#hyperintensional-content)
- [Testing and Validation](#testing-and-validation)
  - [Theorem Examples](#theorem-examples)
  - [Countermodel Examples](#countermodel-examples)
  - [Logical Properties](#logical-properties)
- [Integration](#integration)
  - [Dependencies](#dependencies)
  - [Usage with Other Subtheories](#usage-with-other-subtheories)
  - [API Reference](#api-reference)
- [Advanced Topics](#advanced-topics)
  - [Classical vs Hyperintensional Logic](#classical-vs-hyperintensional-logic)
  - [Operator Interdefinability](#operator-interdefinability)
  - [Content Sensitivity](#content-sensitivity)

## Quick Start

### Basic Usage

```python
from model_checker.theory_lib import logos

# Load constitutive subtheory (automatically loads extensional dependency)
theory = logos.get_theory(['constitutive'])

# Check identity relationship
from model_checker import BuildExample
model = BuildExample("constitutive_example", theory)

# Identity is reflexive: A equiv A is always valid
result = model.check_validity([], ["(A \\equiv A)"])
print(f"Identity Reflexivity: {'Valid' if result else 'Invalid'}")
```

### Running Examples

```bash
# Run all constitutive examples
model-checker src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py

# Run in development mode
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py

# Run with constraints printed
./dev_cli.py -p src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py
```

### Project Generation

```bash
# Generate a project focused on constitutive logic
./dev_cli.py -l logos  # Select constitutive subtheory during setup
```

## Operator Reference

### Identity

**Symbol**: `\\equiv`  
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

**Symbol**: `\\leq`  
**Name**: Ground (Disjunctive-Part)  
**Arity**: 2 (binary)  
**Type**: Primitive operator

**Meaning**: "A grounds B" or "A is a disjunctive-part of B"

**Truth Conditions**: A grounds B when:
1. Every verifier of A is a verifier of B
2. The falsifiers interact appropriately (fusion conditions)
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
- **Strict Implication**: `(A \\leq B)` implies `Box(A -> B)`

### Essence

**Symbol**: `\\sqsubseteq`  
**Name**: Essence (Conjunctive-Part)  
**Arity**: 2 (binary)  
**Type**: Primitive operator

**Meaning**: "A is essential to B" or "A is a conjunctive-part of B"

**Truth Conditions**: A is essential to B when:
1. Verifiers interact appropriately (fusion conditions)  
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
- **Converse Strict Implication**: `(A \\sqsubseteq B)` implies `Box(B -> A)`

### Relevance

**Symbol**: `\\preceq`  
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
- **Transitivity**: Generally valid
- **Weakest Relation**: Implied by both ground and essence
- **Content Interaction**: Captures content overlap without direction

### Reduction

**Symbol**: `\\Rightarrow`  
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

The constitutive subtheory includes **33 comprehensive examples** organized into two main categories:

#### Countermodels (CL_CM_*): 14 Examples
Tests for **invalid** constitutive arguments, demonstrating where classical principles fail in hyperintensional logic:

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

The constitutive subtheory includes **33 comprehensive test examples** covering all five operators through both countermodel and theorem examples. Tests validate hyperintensional content relationships and demonstrate where classical principles fail.

```bash
# Run all constitutive tests
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_CM_1"

# Run via project test runner
python test_theories.py --theories logos --constitutive --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**

#### Programmatic Access

```python
from model_checker.theory_lib.logos.subtheories.constitutive.examples import (
    constitutive_cm_examples,    # All countermodel examples
    constitutive_th_examples,    # All theorem examples  
    constitutive_examples        # Combined collection
)

# Access specific example
cl_cm_1 = constitutive_cm_examples['CL_CM_1']
premises, conclusions, settings = cl_cm_1

# Run example with custom theory
from model_checker import BuildExample
from model_checker.theory_lib import logos

theory = logos.get_theory(['constitutive'])
model = BuildExample("constitutive_test", theory)
result = model.check_validity(premises, conclusions, settings)
```

### Example Structure

Each example follows the standard format:

```python
# CL_TH_16: GROUNDING ANTI-SYMMETRY
CL_TH_16_premises = ['(A \\leq B)', '(B \\leq A)']     # What must be true
CL_TH_16_conclusions = ['(A \\equiv B)']                # What we're testing
CL_TH_16_settings = {                                   # Model constraints
    'N' : 2,                                           # Number of atomic states
    'M' : 2,                                           # Additional constraint
    'contingent' : False,                              # Non-contingent propositions
    'disjoint' : False,                                # Allow overlapping content
    'max_time' : 2,                                    # Solver timeout (seconds)
    'expectation' : False,                             # Expected result (False = valid)
}
CL_TH_16_example = [CL_TH_16_premises, CL_TH_16_conclusions, CL_TH_16_settings]
```

**Settings Explanation**:
- `N`: Controls state space size (smaller N often sufficient for constitutive logic)
- `M`: Additional parameter for complex constraints
- `contingent`: Whether atomic propositions must be contingent  
- `disjoint`: Whether propositions must have disjoint subject matters
- `expectation`: Expected model-finding result (False for valid arguments, True for invalid)

## Semantic Theory

### Theoretical Background

The constitutive subtheory implements the semantic theory developed in Brast-McKie (2021), which provides a hyperintensional approach to content relationships based on truthmaker semantics.

**Key Innovations**:
1. **Hyperintensional Propositions**: Propositions individuated by verifier and falsifier sets
2. **Content-Based Relations**: Operators defined in terms of content overlap and containment
3. **Bilateral Semantics**: Both positive (verifiers) and negative (falsifiers) conditions
4. **Fine-Grained Distinctions**: Distinguishes logically equivalent but content-distinct propositions

### Truth Conditions

#### Identity (A equiv B)

**True** when A and B have identical content:
```
For all x: (x verifies A iff x verifies B) and (x falsifies A iff x falsifies B)
```

#### Ground (A leq B)

**True** when A is a disjunctive-part of B:
```
1. For all x: x verifies A implies x verifies B
2. For all x,y: (x falsifies A and y falsifies B) implies (x fusion y) falsifies B  
3. For all x: x falsifies B implies exists y: (y falsifies A and y part-of x)
```

#### Essence (A sqsubseteq B)

**True** when A is a conjunctive-part of B:
```
1. For all x,y: (x verifies A and y verifies B) implies (x fusion y) verifies B
2. For all x: x verifies B implies exists y: (y verifies A and y part-of x)
3. For all x: x falsifies A implies x falsifies B
```

#### Relevance (A preceq B)

**True** when A is relevant to B:
```
1. For all x,y: (x verifies A and y verifies B) implies (x fusion y) verifies B
2. For all x,y: (x falsifies A and y falsifies B) implies (x fusion y) falsifies B
```

### Hyperintensional Content

The constitutive operators are **hyperintensional**, meaning they distinguish between logically equivalent but content-distinct propositions:

**Classical Logic**: `(A or neg A) iff (B or neg B)` (all tautologies equivalent)  
**Hyperintensional Logic**: `(A or neg A) not-equiv (B or neg B)` (different tautologies not identical)

This allows for fine-grained analysis of:
- **Topic sensitivity**: What a proposition is about
- **Content overlap**: How propositions share subject matter  
- **Dependence relations**: How propositions depend on each other

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
- Classical Distribution: Identity doesn't satisfy classical distribution laws
- Tautology Equivalence: All tautologies are not identical
- Modal Conversion: Strict implication doesn't convert to content relations
- Supplementation: Content relations don't satisfy classical supplementation

## Integration

### Dependencies

The constitutive subtheory depends on the **extensional subtheory** for:
- `AndOperator`: Required for defining reduction operator
- Basic logical operators used in complex examples

```python
# Automatic dependency loading
theory = logos.get_theory(['constitutive'])  # Also loads extensional
```

### Usage with Other Subtheories

```python
# Combined with modal logic
theory = logos.get_theory(['constitutive', 'modal'])

# Ground and necessity interaction
premises = ["(p \\leq q)", "\\Box p"]
conclusion = "\\Box q"
result = model.check_validity(premises, [conclusion])

# Combined with counterfactual operators  
theory = logos.get_theory(['constitutive', 'counterfactual'])

# Identity and counterfactual interaction
premises = ["(p \\equiv q)", "(p \\boxright r)"]
conclusion = "(q \\boxright r)"
result = model.check_validity(premises, [conclusion])
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

### Classical vs Hyperintensional Logic

The constitutive subtheory reveals key differences between classical and hyperintensional logic:

**Classical Logic** (extensional):
- All tautologies are equivalent: `(A or neg A) iff (B or neg B)`
- Distribution laws: `A and (B or C) iff (A and B) or (A and C)`
- Absorption laws: `A iff A and (A or B)`

**Hyperintensional Logic** (content-sensitive):
- Tautologies differ in content: `(A or neg A) not-equiv (B or neg B)`
- Distribution fails: `A not-equiv A and (A or B)` (generally)
- Content matters: Same truth conditions not-equal same content

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

### Content Sensitivity

The constitutive operators enable analysis of **content sensitivity**:

**Topic Individuation**:
- What makes propositions about the same topic?
- How do we individuate propositional content?
- When do propositions share subject matter?

**Dependence Analysis**:
- What does it mean for one proposition to depend on another?
- How do ground and essence capture different dependency relations?
- When is content overlap sufficient for logical connection?

**Hyperintensional Reasoning**:
- Moving beyond truth-functional logic
- Analyzing content relationships
- Understanding aboutness and topicality

---

## References

- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content I"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content II"](https://doi.org/10.1007/s10992-016-9419-5), Journal of Philosophical Logic

## License

The constitutive subtheory is part of the ModelChecker package and follows the same licensing terms. See `LICENSE.md` for details.
