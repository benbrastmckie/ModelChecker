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

### Your First Formula Check

Let's check if necessity implies truth (the T axiom):

```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

# Load the theory
theory = logos.get_theory()

# Create a model checker
model = BuildExample("t_axiom", theory)

# Check the formula
result = model.check_formula("\\Box p \\rightarrow p")
print(f"□p → p is {'valid' if result else 'invalid'}")
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

### Checking Validity

To check if an argument is valid:

```python
# Set up premises and conclusions
premises = ["p \rightarrow q", "q \rightarrow r"]
conclusions = ["p \rightarrow r"]

# Create model with the argument
model = BuildExample("transitivity", theory,
    premises=premises,
    conclusions=conclusions,
    settings={'N': 4}
)

# Check validity
result = model.check_validity(premises, conclusions)
print(f"The argument is {'valid' if result else 'invalid'}")
```

### Finding Countermodels

When an argument is invalid, you can examine the countermodel:

```python
# Invalid argument: □(p → q) ⊢ □p → □q
premises = ["\\Box (p \\rightarrow q)"]
conclusions = ["\\Box p \\rightarrow \\Box q"]

model = BuildExample("distribution_failure", theory,
    premises=premises,
    conclusions=conclusions,
    settings={'N': 4}
)

# This will show the countermodel
# demonstrating why distribution fails
```

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
Basic extensional logic:
```python
# Modus ponens
model.check_validity(["p", "p \\rightarrow q"], ["q"])

# DeMorgan's law
model.check_formula("\\neg (p \\wedge q) \\leftrightarrow (\\neg p \\vee \\neg q)")
```

#### Modal Operators
Necessity and possibility:
```python
# T axiom: □p → p
model.check_formula("\\Box p \\rightarrow p")

# Duality: ◇p ↔ ¬□¬p
model.check_formula("\\Diamond p \\leftrightarrow \\neg \\Box \\neg p")
```

#### Constitutive Operators
Content relationships:
```python
# Identity is reflexive
model.check_formula("p \\equiv p")

# Ground implies truth
model.check_validity(["p \\leq q", "p"], ["q"])
```

#### Counterfactual Operators
Counterfactual reasoning:
```python
# Counterfactual modus ponens
model.check_validity(["p", "p \\boxright q"], ["q"])

# Testing Sobel sequences
premises = ["\\neg p", "\\neg q", "p \\boxright q"]
conclusions = ["(p \\wedge r) \\boxright q"]
model.check_validity(premises, conclusions)
```

## Finding Models and Countermodels

### Single Model Finding

The basic approach finds one model:

```python
model = BuildExample("example", theory,
    premises=["\\Diamond p", "\\Diamond \\neg p"],
    conclusions=["\\Box (p \\vee \\neg p)"],
    settings={'N': 4, 'max_time': 5}
)
```

### Multiple Model Iteration

Find multiple distinct models:

```python
# Using settings
model = BuildExample("multiple", theory,
    premises=["\\Diamond p"],
    conclusions=[],
    settings={
        'N': 4,
        'iterate': 5,  # Find up to 5 models
        'iteration_timeout': 2.0
    }
)

# Using the iterator directly
from model_checker.theory_lib.logos.iterate import iterate_example
models = iterate_example(model, max_iterations=5)
```

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

Fine-tune model generation:

```python
settings = {
    'N': 8,               # More atomic states
    'contingent': True,   # Force contingent propositions
    'non_empty': True,    # No empty verifier/falsifier sets
    'non_null': True,     # Null state can't verify/falsify
    'disjoint': True,     # Atomic propositions are disjoint
    'max_time': 30,       # Longer timeout for complex formulas
    'iterate': 10,        # Find multiple models
}

model = BuildExample("complex", theory, 
                    premises=premises,
                    conclusions=conclusions,
                    settings=settings)
```

### Interactive Exploration

Use Jupyter notebooks for interactive work:

```python
from model_checker.jupyter import ModelExplorer

# Interactive model exploration
explorer = ModelExplorer(theory='logos')
explorer.display()
```

### Debugging Complex Formulas

When formulas don't behave as expected:

```python
# Enable constraint printing
model = BuildExample("debug", theory,
    premises=["(p \\leq q) \\wedge (q \\leq r)"],
    conclusions=["p \\leq r"],
    settings={'N': 3}
)

# Run with debugging
from model_checker import cli
cli.main(["-p", "-z", "debug_example.py"])
```

### Theory Comparison

Compare how different theories handle the same formula:

```python
from model_checker.theory_lib import logos, imposition

# Same formula, different theories
formula = "p \\boxright (q \\boxright p)"

logos_model = BuildExample("logos_test", logos.get_theory())
logos_result = logos_model.check_formula(formula)

imposition_model = BuildExample("imposition_test", imposition_theory)
imposition_result = imposition_model.check_formula(formula)

print(f"Logos: {logos_result}, Imposition: {imposition_result}")
```

## Common Patterns

### Testing Logical Principles

```python
def test_principle(name, formula, theory=None):
    """Test if a logical principle holds."""
    if theory is None:
        theory = logos.get_theory()
    
    model = BuildExample(name, theory)
    result = model.check_formula(formula)
    
    print(f"{name}: {'✓ Valid' if result else '✗ Invalid'}")
    return result

# Test some principles
test_principle("K axiom", "\\Box (p \\rightarrow q) \\rightarrow (\\Box p \\rightarrow \\Box q)")
test_principle("T axiom", "\\Box p \\rightarrow p")
test_principle("4 axiom", "\\Box p \\rightarrow \\Box \\Box p")
test_principle("5 axiom", "\\Diamond p \\rightarrow \\Box \\Diamond p")
```

### Building Complex Arguments

```python
def check_argument(name, premises, conclusions, settings=None):
    """Check a complex argument."""
    if settings is None:
        settings = {'N': 4, 'max_time': 10}
    
    theory = logos.get_theory()
    model = BuildExample(name, theory,
                        premises=premises,
                        conclusions=conclusions,
                        settings=settings)
    
    result = model.check_validity(premises, conclusions)
    
    if result:
        print(f"✓ {name}: Valid argument")
    else:
        print(f"✗ {name}: Invalid - countermodel found")
        print(f"  Premises true but conclusion false in world {model.model_structure.main_world}")
    
    return result

# Example: Testing hypothetical syllogism for counterfactuals
check_argument("Hypothetical Syllogism",
    premises=["p \\boxright q", "q \\boxright r"],
    conclusions=["p \\boxright r"])
```

### Exploring Operator Interactions

```python
def explore_interaction(op1, op2, prop="p"):
    """Explore how two operators interact."""
    theory = logos.get_theory()
    
    formulas = [
        f"{op1} {op2} {prop}",
        f"{op2} {op1} {prop}",
        f"{op1} {prop} \\rightarrow {op2} {prop}",
        f"{op2} {prop} \\rightarrow {op1} {prop}",
    ]
    
    for formula in formulas:
        model = BuildExample(f"test_{formula}", theory)
        result = model.check_formula(formula)
        print(f"{formula}: {'Valid' if result else 'Invalid'}")

# Explore modal and ground interaction
explore_interaction("\\Box", "\\leq")
```

## Troubleshooting

### Common Issues and Solutions

#### "Operator not found" Error
```python
# Problem: Operator not loaded
# Solution: Ensure subtheory is loaded
theory = logos.get_theory(['extensional', 'modal'])  # Must include both
```

#### Z3 Timeout
```python
# Problem: Formula too complex
# Solution: Adjust settings
settings = {
    'N': 3,           # Reduce state space
    'max_time': 60,   # Increase timeout
}
```

#### Unexpected Invalid Result
```python
# Problem: Formula seems valid but isn't
# Solution: Examine the countermodel
model = BuildExample("debug", theory,
    premises=premises,
    conclusions=conclusions,
    settings={'N': 3})

# Check what makes premises true but conclusion false
print("Countermodel found:")
print(f"World: {model.model_structure.main_world}")
print(f"Premise values: {[p.truth_value_at(model.model_structure.main_world) for p in model.premises]}")
print(f"Conclusion value: {model.conclusions[0].truth_value_at(model.model_structure.main_world)}")
```

#### Memory Issues
```python
# Problem: Large models consume too much memory
# Solution: Use smaller N or load fewer subtheories
theory = logos.get_theory(['extensional', 'modal'])  # Minimal
settings = {'N': 3}  # Smallest useful size
```

### Getting Help

1. **Check Documentation**: Review this guide and other docs
2. **Examine Examples**: Look at test cases in subtheories
3. **Use Notebooks**: Interactive exploration often reveals issues
4. **Enable Debugging**: Use `-p` and `-z` flags for details

## Examples Gallery

### Modal Logic Examples

```python
# S5 principles in hyperintensional setting
examples = {
    "T": "\\Box p \\rightarrow p",
    "K": "\\Box (p \\rightarrow q) \\rightarrow (\\Box p \\rightarrow \\Box q)",
    "4": "\\Box p \\rightarrow \\Box \\Box p", 
    "5": "\\Diamond p \\rightarrow \\Box \\Diamond p",
    "B": "p \\rightarrow \\Box \\Diamond p",
}

for name, formula in examples.items():
    model = BuildExample(f"axiom_{name}", theory)
    result = model.check_formula(formula)
    print(f"{name}: {'✓' if result else '✗'}")
```

### Constitutive Logic Examples

```python
# Ground and essence relationships
check_argument("Ground Distribution",
    premises=["(p \\wedge q) \\leq r"],
    conclusions=["p \\leq r"])

check_argument("Essence Transitivity",
    premises=["p \\sqsubseteq q", "q \\sqsubseteq r"],
    conclusions=["p \\sqsubseteq r"])

check_argument("Identity Reduction",
    premises=["p \\equiv q"],
    conclusions=["(p \\leq q) \\wedge (q \\leq p)"])
```

### Counterfactual Examples

```python
# Classic counterfactual patterns
check_argument("Antecedent Strengthening",
    premises=["p \\boxright r"],
    conclusions=["(p \\wedge q) \\boxright r"])  # Invalid!

check_argument("Transitivity", 
    premises=["p \\boxright q", "q \\boxright r"],
    conclusions=["p \\boxright r"])  # Invalid!

check_argument("Modus Ponens",
    premises=["p", "p \\boxright q"],
    conclusions=["q"])  # Valid
```

### Hyperintensional Phenomena

```python
# Content sensitivity examples
model = BuildExample("content_difference", theory)

# These are necessarily equivalent but have different content
f1 = "(p \\wedge (q \\vee r))"
f2 = "((p \\wedge q) \\vee (p \\wedge r))"

# Check if they're identical (they shouldn't be)
result = model.check_formula(f"{f1} \\equiv {f2}")
print(f"Distributive formulas are identical: {result}")  # False

# But they ground each other
result1 = model.check_formula(f"{f1} \\leq {f2}")
result2 = model.check_formula(f"{f2} \\leq {f1}")
print(f"They ground each other: {result1 and result2}")  # True
```

## Next Steps

Now that you understand the basics:

1. **Explore Notebooks**: Try the [interactive demos](../notebooks/)
2. **Read Subtheory Docs**: Deep dive into specific [operator categories](../subtheories/)
3. **Study Examples**: Review the [test cases](../tests/)
4. **Contribute**: Add new examples or improve documentation

Remember: Logos is a powerful tool for exploring hyperintensional logic. The more you experiment, the more intuitive it becomes!

---

**Navigation**: [README](README.md) | [Architecture](ARCHITECTURE.md) | [Settings](SETTINGS.md) | [Iteration](ITERATE.md) | [Main README](../README.md)
