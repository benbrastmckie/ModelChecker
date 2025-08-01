# Logos Theory User Guide

A practical guide to using the Logos semantic theory for hyperintensional logic and truthmaker semantics.

## Table of Contents

- [Introduction](#introduction)
- [Getting Started](#getting-started)
- [Basic Usage](#basic-usage)
- [Working with Operators](#working-with-operators)
- [Finding Models and Countermodels](#finding-models-and-countermodels)
- [Advanced Features](#advanced-features)
- [Common Patterns](#common-patterns)
- [Troubleshooting](#troubleshooting)
- [Examples Gallery](#examples-gallery)

## Introduction

The Logos theory provides a powerful framework for working with hyperintensional logic, where even necessarily equivalent formulas can have different content. This guide will help you:

- Understand the basic concepts
- Write and check logical formulas
- Find countermodels to invalid arguments
- Explore advanced features like model iteration
- Integrate Logos into your research or teaching

### What Makes Logos Special?

Unlike classical logic where all tautologies are identical, Logos distinguishes between:
- "A ∨ ¬A" (law of excluded middle)
- "B → B" (reflexivity of implication)

Both are tautologies, but they have different content—they're "about" different things.

## Getting Started

### Installation Check

First, ensure ModelChecker is properly installed:

```python
# Test basic import
from model_checker.theory_lib import logos

# Load the theory
theory = logos.get_theory()
print(f"Loaded {len(theory['operators'].operator_dictionary)} operators")
```

### Your First Example

Let's understand the T axiom - that necessity implies truth:

```python
# EXT_TH_5: T AXIOM
EXT_TH_5_premises = []
EXT_TH_5_conclusions = ["\\Box A \\rightarrow A"]
EXT_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
EXT_TH_5_example = [
    EXT_TH_5_premises,
    EXT_TH_5_conclusions,
    EXT_TH_5_settings,
]

# See [examples.py](../subtheories/extensional/examples.py) for complete implementation.
```

To run this example:

```bash
# Navigate to the logos directory
cd src/model_checker/theory_lib/logos

# Run the extensional examples
model-checker subtheories/extensional/examples.py
```

### Understanding the Output

When you run an example, you'll see output like:

```
========================================
EXAMPLE t_axiom: no countermodel found.

Atomic States: 16
Semantic Theory: Logos Semantics

Formula:
1. (□ p → p)

Z3 Run Time: 0.234 seconds

The formula is valid!
========================================
```

## Basic Usage

### Writing Formulas

Logos uses LaTeX-style notation for operators:

| Symbol | LaTeX | Meaning | Example |
|--------|--------|---------|---------|
| ¬ | `\neg` | Negation | `\neg p` |
| ∧ | `\wedge` | Conjunction | `p \wedge q` |
| ∨ | `\vee` | Disjunction | `p \vee q` |
| → | `\rightarrow` | Implication | `p \rightarrow q` |
| □ | `\Box` | Necessity | `\Box p` |
| ◇ | `\Diamond` | Possibility | `\Diamond p` |

**Important**: Always use the LaTeX notation (e.g., `\Box`) not Unicode (□) in formulas.

### Understanding Validity

Here's how transitivity of implication works:

```python
# EXT_TH_6: TRANSITIVITY OF IMPLICATION
EXT_TH_6_premises = ["A \\rightarrow B", "B \\rightarrow C"]
EXT_TH_6_conclusions = ["A \\rightarrow C"]
EXT_TH_6_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
EXT_TH_6_example = [
    EXT_TH_6_premises,
    EXT_TH_6_conclusions,
    EXT_TH_6_settings,
]

# See [examples.py](../subtheories/extensional/examples.py) for complete implementation.
```

To explore validity:
1. Look at the examples in the subtheory directories
2. Run them with the model-checker command
3. Examine the output to understand countermodels

### Understanding Countermodels

Some modal principles fail in hyperintensional logic:

```python
# MOD_TH_9: DISTRIBUTION FAILURE
MOD_TH_9_premises = ["\\Box (A \\rightarrow B)"]
MOD_TH_9_conclusions = ["\\Box A \\rightarrow \\Box B"]
MOD_TH_9_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_TH_9_example = [
    MOD_TH_9_premises,
    MOD_TH_9_conclusions,
    MOD_TH_9_settings,
]

# Distribution of necessity over implication (FAILS)
# Status: Invalid - countermodel demonstrates hyperintensional sensitivity
# See [examples.py](../subtheories/modal/examples.py) for complete implementation.
```

When you run invalid examples, the output shows:
1. The countermodel structure
2. Which states make premises true but conclusions false
3. Why the argument fails semantically

## Working with Operators

### Loading Specific Subtheories

You don't always need all 20 operators. Load only what you need:

```python
# Just modal logic
modal_theory = logos.get_theory(['extensional', 'modal'])

# Constitutive logic
constitutive_theory = logos.get_theory(['extensional', 'constitutive'])

# Everything except relevance
most_theory = logos.get_theory(['extensional', 'modal', 
                                'constitutive', 'counterfactual'])
```

### Operator Categories

#### Extensional Operators
Basic extensional logic principles:

```python
# EXT_TH_1: MODUS PONENS
EXT_TH_1_premises = ["A", "A \\rightarrow B"]
EXT_TH_1_conclusions = ["B"]
EXT_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]

# EXT_TH_7: DEMORGAN'S LAW
EXT_TH_7_premises = []
EXT_TH_7_conclusions = ["\\neg (A \\wedge B) \\leftrightarrow (\\neg A \\vee \\neg B)"]
EXT_TH_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
EXT_TH_7_example = [
    EXT_TH_7_premises,
    EXT_TH_7_conclusions,
    EXT_TH_7_settings,
]

# See [examples.py](../subtheories/extensional/examples.py) for complete implementations.
```

#### Modal Operators
Necessity and possibility relationships:

```python
# MOD_TH_1: T AXIOM
MOD_TH_1_premises = []
MOD_TH_1_conclusions = ["\\Box A \\rightarrow A"]
MOD_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_1_example = [
    MOD_TH_1_premises,
    MOD_TH_1_conclusions,
    MOD_TH_1_settings,
]

# MOD_TH_2: MODAL DUALITY
MOD_TH_2_premises = []
MOD_TH_2_conclusions = ["\\Diamond A \\leftrightarrow \\neg \\Box \\neg A"]
MOD_TH_2_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_2_example = [
    MOD_TH_2_premises,
    MOD_TH_2_conclusions,
    MOD_TH_2_settings,
]

# See [examples.py](../subtheories/modal/examples.py) for complete implementations.
```

#### Constitutive Operators
Content and grounding relationships:

```python
# CON_TH_1: IDENTITY REFLEXIVITY
CON_TH_1_premises = []
CON_TH_1_conclusions = ["A \\equiv A"]
CON_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CON_TH_1_example = [
    CON_TH_1_premises,
    CON_TH_1_conclusions,
    CON_TH_1_settings,
]

# CON_TH_2: GROUND MODUS PONENS
CON_TH_2_premises = ["A \\leq B", "A"]
CON_TH_2_conclusions = ["B"]
CON_TH_2_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CON_TH_2_example = [
    CON_TH_2_premises,
    CON_TH_2_conclusions,
    CON_TH_2_settings,
]

# See [examples.py](../subtheories/constitutive/examples.py) for complete implementations.
```

#### Counterfactual Operators
Counterfactual reasoning patterns:

```python
# COU_TH_1: COUNTERFACTUAL MODUS PONENS
COU_TH_1_premises = ["A", "A \\boxright B"]
COU_TH_1_conclusions = ["B"]
COU_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
COU_TH_1_example = [
    COU_TH_1_premises,
    COU_TH_1_conclusions,
    COU_TH_1_settings,
]

# COU_TH_8: SOBEL SEQUENCE FAILURE
COU_TH_8_premises = ["\\neg A", "\\neg B", "A \\boxright B"]
COU_TH_8_conclusions = ["(A \\wedge C) \\boxright B"]
COU_TH_8_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
COU_TH_8_example = [
    COU_TH_8_premises,
    COU_TH_8_conclusions,
    COU_TH_8_settings,
]

# Antecedent strengthening (FAILS)
# See [examples.py](../subtheories/counterfactual/examples.py) for complete implementations.
```

## Finding Models and Countermodels

### Understanding Model Structure

Logos models show possibility and contingency:

```python
# MOD_TH_4: CONTINGENCY EXAMPLE
MOD_TH_4_premises = ["\\Diamond A", "\\Diamond \\neg A"]
MOD_TH_4_conclusions = ["\\Box (A \\vee \\neg A)"]
MOD_TH_4_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_4_example = [
    MOD_TH_4_premises,
    MOD_TH_4_conclusions,
    MOD_TH_4_settings,
]

# Contingent propositions and necessary tautologies
# Status: Valid - demonstrates modal structure
# See [examples.py](../subtheories/modal/examples.py) for complete implementation.
```

### Multiple Model Exploration

Some formulas have multiple distinct models:

```bash
# Run examples with iteration enabled
model-checker subtheories/modal/examples.py --iterate 5

# This explores different ways modal formulas can be satisfied
```

For interactive exploration, see the [iteration guide](ITERATE.md) and [Jupyter notebooks](../notebooks/).

### Understanding Model Output

Models show several components:

```
State Space:
  000 = ∅                    # Empty state
  001 = a                    # Atomic state
  010 = b                    # Atomic state  
  011 = a.b (world)         # Fusion (possible world)
  100 = c (impossible)      # Impossible state
  ...

Evaluation world: a.b.c

INTERPRETED PREMISES:
1. |□(p → q)| = < {a.b.c}, {} >  (True in a.b.c)

INTERPRETED CONCLUSIONS:
2. |□p → □q| = < {a.c}, {a.b.c} >  (False in a.b.c)
```

Key elements:
- **States**: All possible combinations of atoms
- **Worlds**: Maximal possible states
- **Impossible**: States that cannot exist
- **Verifiers/Falsifiers**: States that make formulas true/false

## Advanced Features

### Custom Settings

Control model generation through settings in examples:

```python
# In your example file (e.g., my_examples.py)
my_example = [
    ["\\Diamond A"],           # Premises
    ["A"],                    # Conclusions
    {
        'N': 8,               # More atomic states
        'contingent': True,    # Force contingent propositions
        'non_empty': True,     # No empty verifier/falsifier sets
        'max_time': 30,        # Longer timeout
        'iterate': 10,         # Find multiple models
        'expectation': True,   # Expect countermodel
    }
]
```

See [SETTINGS.md](SETTINGS.md) for complete documentation of available options.

### Interactive Exploration

Use Jupyter notebooks for hands-on learning:

```bash
# Launch Jupyter environment
./run_jupyter.sh

# Navigate to logos notebooks
# Open: src/model_checker/theory_lib/logos/notebooks/
```

The notebooks provide:
- Interactive formula testing
- Visual model exploration
- Step-by-step tutorials
- Debugging tools

### Debugging Complex Formulas

When formulas don't behave as expected:

```bash
# Run with constraint printing enabled
model-checker -p -z my_example.py

# This shows the Z3 constraints and solving process
# Helpful for understanding why certain models exist
```

Debugging strategies:
1. Start with smaller state spaces (N=3)
2. Use the `-p` flag to see constraints
3. Check examples in subtheory directories
4. Use Jupyter notebooks for step-by-step analysis

### Theory Comparison

Compare how different theories handle the same formulas:

```bash
# Test in logos theory
model-checker src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Test in imposition theory  
model-checker src/model_checker/theory_lib/imposition/examples.py

# Compare results for similar principles
```

The frameworks show different behaviors for:
- Counterfactual transitivity
- Modal distribution principles
- Relevance constraints
- Grounding relationships

## Common Patterns

### Testing Logical Principles

Explore how modal axioms behave in hyperintensional logic:

```python
# MOD_TH_5: K AXIOM (DISTRIBUTION)
MOD_TH_5_premises = []
MOD_TH_5_conclusions = ["\\Box (A \\rightarrow B) \\rightarrow (\\Box A \\rightarrow \\Box B)"]
MOD_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_TH_5_example = [
    MOD_TH_5_premises,
    MOD_TH_5_conclusions,
    MOD_TH_5_settings,
]

# MOD_TH_6: 4 AXIOM
MOD_TH_6_premises = []
MOD_TH_6_conclusions = ["\\Box A \\rightarrow \\Box \\Box A"]
MOD_TH_6_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_6_example = [
    MOD_TH_6_premises,
    MOD_TH_6_conclusions,
    MOD_TH_6_settings,
]

# MOD_TH_7: 5 AXIOM
MOD_TH_7_premises = []
MOD_TH_7_conclusions = ["\\Diamond A \\rightarrow \\Box \\Diamond A"]
MOD_TH_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_TH_7_example = [
    MOD_TH_7_premises,
    MOD_TH_7_conclusions,
    MOD_TH_7_settings,
]

# Distribution of necessity over implication (FAILS)
# Necessity implies truth (VALID)
# Necessity of necessity (VALID)
# Necessity of possibility (FAILS)
# See [examples.py](../subtheories/modal/examples.py) for complete implementations.
```

### Building Complex Arguments

Examine sophisticated logical patterns:

```python
# COU_TH_5: HYPOTHETICAL SYLLOGISM
COU_TH_5_premises = ["A \\boxright B", "B \\boxright C"]
COU_TH_5_conclusions = ["A \\boxright C"]
COU_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
COU_TH_5_example = [
    COU_TH_5_premises,
    COU_TH_5_conclusions,
    COU_TH_5_settings,
]

# COU_TH_3: CONTRAPOSITION
COU_TH_3_premises = ["A \\boxright B"]
COU_TH_3_conclusions = ["\\neg B \\boxright \\neg A"]
COU_TH_3_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
COU_TH_3_example = [
    COU_TH_3_premises,
    COU_TH_3_conclusions,
    COU_TH_3_settings,
]

# Transitivity of counterfactuals (FAILS)
# Reason: Counterfactuals are not generally transitive
# Contraposition for counterfactuals (FAILS)
# Reason: Asymmetry in counterfactual reasoning
# See [examples.py](../subtheories/counterfactual/examples.py) for complete implementations.
```

### Exploring Operator Interactions

Understand how different operators relate:

```python
# INT_TH_1: NECESSITY AND GROUND
INT_TH_1_premises = ["\\Box A"]
INT_TH_1_conclusions = ["A \\leq A"]
INT_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
INT_TH_1_example = [
    INT_TH_1_premises,
    INT_TH_1_conclusions,
    INT_TH_1_settings,
]

# INT_TH_2: GROUND AND NECESSITY
INT_TH_2_premises = ["A \\leq B"]
INT_TH_2_conclusions = ["\\Box A \\rightarrow \\Box B"]
INT_TH_2_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
INT_TH_2_example = [
    INT_TH_2_premises,
    INT_TH_2_conclusions,
    INT_TH_2_settings,
]

# INT_TH_3: COUNTERFACTUAL AND IDENTITY
INT_TH_3_premises = ["A \\boxright B", "A \\equiv B"]
INT_TH_3_conclusions = ["A \\rightarrow B"]
INT_TH_3_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
INT_TH_3_example = [
    INT_TH_3_premises,
    INT_TH_3_conclusions,
    INT_TH_3_settings,
]

# Necessary truths ground themselves (VALID)
# Grounding preserves necessity (FAILS)
# Reason: Ground relationships are hyperintensional
# Identity strengthens counterfactals (VALID)
# See examples across subtheory directories for operator interactions.
```

## Troubleshooting

### Common Issues and Solutions

#### "Operator not found" Error
```bash
# Problem: Using operators not in loaded subtheories
# Solution: Load required subtheories
# Example: For ground operator (\leq), need constitutive subtheory
```

#### Z3 Timeout
```python
# Problem: Formula too complex for Z3 solver
# Solution: Adjust settings in your example
my_example = [
    [premises],
    [conclusions], 
    {
        'N': 3,           # Reduce state space
        'max_time': 60,   # Increase timeout
    }
]
```

#### Unexpected Invalid Result
```bash
# Problem: Formula seems valid but shows countermodel
# Solution: Run with detailed output
model-checker -v my_example.py

# The output shows:
# - State space structure
# - Which world makes premises true but conclusion false
# - Why the argument fails semantically
```

#### Memory Issues
```python
# Problem: Large state spaces consume memory
# Solution: Start small and increase gradually
my_example = [
    [premises],
    [conclusions],
    {'N': 3}  # Start with minimal state space
]

# Load only needed subtheories:
# theory = logos.get_theory(['extensional', 'modal'])
```

### Getting Help

1. **Check Documentation**: Review this guide and other docs
2. **Examine Examples**: Look at test cases in subtheories
3. **Use Notebooks**: Interactive exploration often reveals issues
4. **Enable Debugging**: Use `-p` and `-z` flags for details

## Examples Gallery

### Modal Logic Examples

S5 principles in hyperintensional setting:

```python
# MOD_TH_1: T AXIOM
MOD_TH_1_premises = []
MOD_TH_1_conclusions = ["\\Box A \\rightarrow A"]
MOD_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_1_example = [
    MOD_TH_1_premises,
    MOD_TH_1_conclusions,
    MOD_TH_1_settings,
]

# MOD_TH_5: K AXIOM (Distribution)
MOD_TH_5_premises = []
MOD_TH_5_conclusions = ["\\Box (A \\rightarrow B) \\rightarrow (\\Box A \\rightarrow \\Box B)"]
MOD_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_TH_5_example = [
    MOD_TH_5_premises,
    MOD_TH_5_conclusions,
    MOD_TH_5_settings,
]

# MOD_TH_6: 4 AXIOM
MOD_TH_6_premises = []
MOD_TH_6_conclusions = ["\\Box A \\rightarrow \\Box \\Box A"]
MOD_TH_6_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_6_example = [
    MOD_TH_6_premises,
    MOD_TH_6_conclusions,
    MOD_TH_6_settings,
]

# MOD_TH_7: 5 AXIOM
MOD_TH_7_premises = []
MOD_TH_7_conclusions = ["\\Diamond A \\rightarrow \\Box \\Diamond A"]
MOD_TH_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_TH_7_example = [
    MOD_TH_7_premises,
    MOD_TH_7_conclusions,
    MOD_TH_7_settings,
]

# MOD_TH_8: B AXIOM
MOD_TH_8_premises = []
MOD_TH_8_conclusions = ["A \\rightarrow \\Box \\Diamond A"]
MOD_TH_8_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_TH_8_example = [
    MOD_TH_8_premises,
    MOD_TH_8_conclusions,
    MOD_TH_8_settings,
]

# Status: VALID ✓ Necessity implies truth
# Status: INVALID ✗ Hyperintensional sensitivity blocks distribution
# Status: VALID ✓ Necessity of necessity
# Status: INVALID ✗ Possibility doesn't necessitate possibility
# Status: INVALID ✗ Truth doesn't necessitate possibility
# See [examples.py](../subtheories/modal/examples.py) for complete implementations.
```

### Constitutive Logic Examples

Ground and essence relationships:

```python
# CON_TH_7: GROUND DISTRIBUTION FAILURE
CON_TH_7_premises = ["(A \\wedge B) \\leq C"]
CON_TH_7_conclusions = ["A \\leq C"]
CON_TH_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CON_TH_7_example = [
    CON_TH_7_premises,
    CON_TH_7_conclusions,
    CON_TH_7_settings,
]

# CON_TH_5: ESSENCE TRANSITIVITY
CON_TH_5_premises = ["A \\sqsubseteq B", "B \\sqsubseteq C"]
CON_TH_5_conclusions = ["A \\sqsubseteq C"]
CON_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CON_TH_5_example = [
    CON_TH_5_premises,
    CON_TH_5_conclusions,
    CON_TH_5_settings,
]

# CON_TH_3: IDENTITY REDUCTION
CON_TH_3_premises = ["A \\equiv B"]
CON_TH_3_conclusions = ["(A \\leq B) \\wedge (B \\leq A)"]
CON_TH_3_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CON_TH_3_example = [
    CON_TH_3_premises,
    CON_TH_3_conclusions,
    CON_TH_3_settings,
]

# Status: INVALID ✗ Conjunction grounding doesn't distribute to conjuncts
# Status: VALID ✓ Essence relationships are transitive
# Status: VALID ✓ Identity reduces to mutual grounding
# See [examples.py](../subtheories/constitutive/examples.py) for complete implementations.
```

### Counterfactual Examples

Classic counterfactual patterns:

```python
# COU_TH_7: ANTECEDENT STRENGTHENING FAILURE
COU_TH_7_premises = ["A \\boxright C"]
COU_TH_7_conclusions = ["(A \\wedge B) \\boxright C"]
COU_TH_7_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
COU_TH_7_example = [
    COU_TH_7_premises,
    COU_TH_7_conclusions,
    COU_TH_7_settings,
]

# COU_TH_5: TRANSITIVITY FAILURE
COU_TH_5_premises = ["A \\boxright B", "B \\boxright C"]
COU_TH_5_conclusions = ["A \\boxright C"]
COU_TH_5_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
COU_TH_5_example = [
    COU_TH_5_premises,
    COU_TH_5_conclusions,
    COU_TH_5_settings,
]

# COU_TH_1: COUNTERFACTUAL MODUS PONENS
COU_TH_1_premises = ["A", "A \\boxright B"]
COU_TH_1_conclusions = ["B"]
COU_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
COU_TH_1_example = [
    COU_TH_1_premises,
    COU_TH_1_conclusions,
    COU_TH_1_settings,
]

# Status: INVALID ✗ Adding conditions can change counterfactual truth
# Status: INVALID ✗ Counterfactual chains can break
# Status: VALID ✓ Actual antecedents support counterfactual inference
# See [examples.py](../subtheories/counterfactual/examples.py) for complete implementations.
```

### Hyperintensional Phenomena

Content sensitivity in logical equivalents:

```python
# CON_TH_8: DISTRIBUTIVE IDENTITY FAILURE
CON_TH_8_premises = []
CON_TH_8_conclusions = ["(A \\wedge (B \\vee C)) \\equiv ((A \\wedge B) \\vee (A \\wedge C))"]
CON_TH_8_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
CON_TH_8_example = [
    CON_TH_8_premises,
    CON_TH_8_conclusions,
    CON_TH_8_settings,
]

# CON_TH_9: MUTUAL GROUNDING OF EQUIVALENTS
CON_TH_9_premises = []
CON_TH_9_conclusions = ["((A \\wedge (B \\vee C)) \\leq ((A \\wedge B) \\vee (A \\wedge C))) \\wedge (((A \\wedge B) \\vee (A \\wedge C)) \\leq (A \\wedge (B \\vee C)))"]
CON_TH_9_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
CON_TH_9_example = [
    CON_TH_9_premises,
    CON_TH_9_conclusions,
    CON_TH_9_settings,
]

# Status: INVALID ✗ Logically equivalent formulas have different content
# Status: VALID ✓ Equivalent formulas ground each other despite different content
# See [examples.py](../subtheories/constitutive/examples.py) for complete implementations.
```

This demonstrates the key insight: necessary equivalence ≠ identity in hyperintensional logic.

## Next Steps

Now that you understand the basics:

1. **Explore Notebooks**: Try the [interactive demos](../notebooks/)
2. **Read Subtheory Docs**: Deep dive into specific [operator categories](../subtheories/)
3. **Study Examples**: Review the [test cases](../tests/)
4. **Contribute**: Add new examples or improve documentation

Remember: Logos is a powerful tool for exploring hyperintensional logic. The more you experiment, the more intuitive it becomes!

---

**Navigation**: [README](README.md) | [Architecture](ARCHITECTURE.md) | [Settings](SETTINGS.md) | [Iteration](ITERATE.md) | [Main README](../README.md)
