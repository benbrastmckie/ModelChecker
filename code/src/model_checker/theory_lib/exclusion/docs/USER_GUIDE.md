# User Guide: Tutorial for Exclusion Theory

[← Back to Documentation](README.md) | [Settings →](SETTINGS.md) | [Exclusion Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # Architectural patterns and design
├── DATA.md            # Test data analysis
├── ITERATE.md         # Model iteration guide
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration parameters
└── USER_GUIDE.md      # This file - user tutorial
```

## Overview

The **User Guide** provides an accessible tutorial for using Bernard and Champollion's unilateral semantics in the ModelChecker framework. This guide explains how unilateral logic differs from classical logic and demonstrates practical usage through examples.

Within the exclusion theory framework, this guide serves as the primary entry point for new users. Unlike classical bilateral logic where negation simply swaps truth and falsity, unilateral semantics uses an exclusion relation between states to define negation, leading to surprising logical behaviors like the failure of double negation elimination.

This tutorial serves researchers and students exploring non-classical logics, providing hands-on examples demonstrating how witness predicates enable computational investigation of unilateral semantics.

## Getting Started

Test classical principles in unilateral semantics:

```python
# Test a classical principle in unilateral semantics
from model_checker import BuildExample, get_theory

# Load exclusion theory
theory = get_theory("exclusion")

# Test double negation elimination: ¬¬A ⊢ A
model = BuildExample("double_neg", theory,
    premises=['\\neg \\neg A'],  # ¬¬A
    conclusions=['A'],                           # A
    settings={'N': 3}
)

result = model.check_validity()
print(f"¬¬A ⊨ A: {result}")  # False - countermodel found!

# Classical logic would say True, but unilateral finds countermodel
```

## What is Unilateral Semantics?

### Classical vs. Unilateral Logic

In **classical (bilateral) logic**, propositions have both verifiers and falsifiers:
- States that make A true (verifiers)
- States that make A false (falsifiers)
- Negation ¬A simply swaps verifiers and falsifiers

In **unilateral logic**, propositions have only verifiers:
- States that make A true (verifiers)
- No primitive notion of falsification
- Negation ¬A emerges through an **exclusion relation** between states

### The Exclusion Relation

The key innovation is the **exclusion relation** between states. Some states exclude others:
- State `a` might exclude state `b`
- This is not necessarily symmetric: `b` might not exclude `a`
- Exclusion captures the idea that certain states are incompatible

### How Unilateral Negation Works

A state `s` verifies ¬A when:
1. For every state that verifies A, there exist **witness functions** h and y
2. The witness y finds a part of each A-verifier that is excluded by h applied to that verifier
3. All the h-values are parts of s
4. s is minimal with these properties

This complex definition requires **existential quantification over functions**, which creates the computational challenge that the exclusion theory solves.

## Basic Usage

### Loading the Theory

```python
from model_checker import BuildExample, get_theory

# Load the exclusion theory
theory = get_theory("exclusion")

# Or import components directly
from model_checker.theory_lib.exclusion import (
    WitnessSemantics,
    WitnessProposition,
    WitnessStructure,
    witness_operators
)
```

### Simple Examples

#### Example 1: Testing Classical Negation Properties

Classical logic says ¬¬A should be equivalent to A. Let's test this:

```python
# Create a model to test double negation elimination
model = BuildExample("double_negation_test", theory,
    premises=['\\neg \\neg A'],  # ¬¬A
    conclusions=['A'],                           # A
    settings={'N': 3}
)

result = model.check_formula()
print(f"¬¬A ⊨ A: {result}")  # False - finds countermodel!
```

The exclusion theory correctly finds that **double negation elimination fails** in unilateral semantics.

#### Example 2: Testing DeMorgan's Laws

Classical logic says ¬(A ∧ B) should be equivalent to (¬A ∨ ¬B). Let's test:

```python
# Test DeMorgan's law
model = BuildExample("demorgans_test", theory,
    premises=['\\neg (A \\wedge B)'],     # ¬(A ∧ B)
    conclusions=['\\neg A \\vee \\neg B'],  # ¬A ∨ ¬B
    settings={'N': 3}
)

result = model.check_formula()
print(f"¬(A ∧ B) ⊨ (¬A ∨ ¬B): {result}")  # False - DeMorgan's law fails!
```

#### Example 3: What Does Work?

Some logical principles still hold in unilateral semantics:

```python
# Test reflexivity - this should be valid
model = BuildExample("reflexivity_test", theory,
    premises=['A'],
    conclusions=['A'],
    settings={'N': 3}
)

result = model.check_formula()
print(f"A ⊨ A: {result}")  # True - reflexivity still works
```

### Available Operators

The exclusion theory provides these logical operators:

| Operator | Symbol | Syntax | Description |
|----------|---------|---------|-------------|
| **Unilateral Negation** | ¬ | `\\neg` | Exclusion-based negation |
| **Conjunction** | ∧ | `\\wedge` | Standard conjunction |
| **Disjunction** | ∨ | `\\vee` | Standard disjunction |
| **Identity** | ≡ | `\\equiv` | Verifier set equality |

### Model Settings

Common settings for exclusion theory models:

```python
settings = {
    'N': 3,                    # State space size (2^3 = 8 states)
    'contingent': True,        # Allow contingent propositions
    'non_empty': True,         # Require non-empty verifier sets
    'possible': True,          # Require possible states exist
    'max_time': 10,            # Solver timeout in seconds
    'iterate': 1               # Number of distinct models to find
}
```

## Understanding the Results

### Valid Inferences

When a formula is **valid**, the system reports no countermodel found:

```
Checking: A ⊨ A
Result: No countermodel found - inference is valid
```

### Invalid Inferences (Countermodels)

When a formula is **invalid**, the system finds a countermodel:

```
Checking: ¬¬A ⊨ A
Result: Countermodel found
State Space: {∅, a, b, c, a∧b, a∧c, b∧c, a∧b∧c}
Evaluation Point: ∅ (empty state)
Premise ¬¬A: TRUE at ∅
Conclusion A: FALSE at ∅
```

This shows that the empty state ∅ verifies ¬¬A but not A, violating double negation elimination.

### Witness Function Information

The exclusion theory can show you the witness functions that make negation work:

```python
# After finding a countermodel, inspect witness functions
model_structure = model.get_model()
if hasattr(model_structure, 'get_h_witness'):
    h_value = model_structure.get_h_witness("\\neg A", 1)
    y_value = model_structure.get_y_witness("\\neg A", 1)
    print(f"For ¬A at state 1: h(1) = {h_value}, y(1) = {y_value}")
```

## Common Use Cases

### 1. Testing Classical Logic Principles

Use the exclusion theory to discover which classical principles fail in unilateral semantics:

```python
classical_principles = [
    # Double negation
    (['\\neg \\neg A'], ['A']),
    # DeMorgan's laws  
    (['\\neg (A \\wedge B)'], ['\\neg A \\vee \\neg B']),
    # Explosion
    (['A', '\\neg A'], ['B'])
]

for premises, conclusions in classical_principles:
    model = BuildExample("classical_test", theory, premises, conclusions, {'N': 3})
    result = model.check_formula()
    print(f"{' & '.join(premises)} ⊨ {' & '.join(conclusions)}: {result}")
```

### 2. Exploring Unilateral Consequences

Find what logical principles do hold in unilateral semantics:

```python
unilateral_candidates = [
    # Reflexivity
    (['A'], ['A']),
    # Conjunction introduction
    (['A', 'B'], ['A \\wedge B']),
    # Disjunction elimination  
    (['A \\vee B', '\\neg A'], ['B'])
]
```

### 3. Comparing with Other Theories

Load multiple theories to compare their behavior:

```python
from model_checker.theory_lib.logos import logos_theory
from model_checker.theory_lib.exclusion import exclusion_theory

# Test the same formula in both theories
formula_premises = ['\\neg \\neg A']
formula_conclusions = ['A']

# Test in logos (bilateral) theory
logos_model = BuildExample("logos_test", logos_theory, 
    formula_premises, formula_conclusions, {'N': 3})
logos_result = logos_model.check_formula()

# Test in exclusion (unilateral) theory  
exclusion_model = BuildExample("exclusion_test", exclusion_theory,
    formula_premises, formula_conclusions, {'N': 3})
exclusion_result = exclusion_model.check_formula()

print(f"Double negation in logos: {logos_result}")
print(f"Double negation in exclusion: {exclusion_result}")
```

## Performance Tips

### Model Size Selection

The `N` parameter determines state space size (2^N states). Larger values give more expressive models but take longer to solve:

- **N=2**: 4 states, very fast, limited expressiveness
- **N=3**: 8 states, good balance for most examples  
- **N=4**: 16 states, slower but more complex countermodels
- **N=5+**: 32+ states, use only for complex investigations

### Timeout Management

Set reasonable timeouts for complex formulas:

```python
settings = {
    'N': 3,
    'max_time': 30,  # 30 second timeout
    'iterate': 1
}
```

### Finding Multiple Models

Use iteration to find multiple distinct countermodels:

```python
settings = {
    'N': 3,
    'iterate': 3  # Find up to 3 different countermodels
}
```

## Common Errors and Troubleshooting

### Error: "No module named 'witness_model'"

Make sure you're importing from the correct module:

```python
# Correct
from model_checker.theory_lib.exclusion import WitnessSemantics

# Incorrect  
from model_checker.theory_lib.exclusion.witness_model import WitnessSemantics
```

### Error: "Solver timeout"

Try reducing model complexity or increasing timeout:

```python
settings = {
    'N': 2,           # Smaller state space
    'max_time': 60    # Longer timeout
}
```

### Error: "Unknown operator"

Use the correct syntax for exclusion operators:

```python
# Correct
'\\neg A'      # Unilateral negation

# Incorrect
'\\neg A'              # Classical negation (not available)
'¬ A'                  # Unicode (not parsed)
```

## Advanced Features

### Custom State Space Constraints

Control the structure of generated models:

```python
settings = {
    'N': 3,
    'possible': True,        # Require some states to be possible
    'contingent': True,      # Allow contingent propositions  
    'non_empty': True,       # Propositions must have verifiers
    'disjoint': False,       # Allow overlapping verifier sets
    'fusion_closure': True   # Require fusion closure
}
```

### Debugging Formula Structure

Use the development CLI with debug flags:

```bash
# Show constraints generated for your formula
./dev_cli.py -p examples/my_exclusion_test.py

# Show Z3 solver output
./dev_cli.py -z examples/my_exclusion_test.py  

# Show both
./dev_cli.py -p -z examples/my_exclusion_test.py
```

## Documentation

### For New Users

- **[What is Unilateral Semantics?](#what-is-unilateral-semantics)** - Core concepts explained
- **[Basic Usage](#basic-usage)** - Loading the theory and running examples
- **[Understanding Results](#understanding-the-results)** - Interpreting countermodels

### For Researchers

- **[Available Operators](#available-operators)** - Logical operators reference
- **[Common Use Cases](#common-use-cases)** - Testing logical principles
- **[Theory Comparison](#3-comparing-with-other-theories)** - Cross-theory validation

### For Advanced Users

- **[Performance Tips](#performance-tips)** - Optimization strategies
- **[Advanced Features](#advanced-features)** - Custom constraints and debugging
- **[Troubleshooting](#common-errors-and-troubleshooting)** - Common issues

## Key Concepts

1. **Unilateral vs Bilateral**: Only verifiers, no primitive falsifiers
2. **Exclusion Relation**: States can exclude other states (asymmetrically)
3. **Witness Functions**: Negation requires existentially quantified h, y functions
4. **Classical Failures**: Double negation, DeMorgan's laws fail
5. **Computational Solution**: Witness predicates solve the False Premise Problem

## References

### Example Files

- **[Examples Module](../examples.py)** - Complete 38-example test suite
- **[Notebooks](../notebooks/)** - Interactive Jupyter tutorials
- **[Tests](../tests/)** - Comprehensive test coverage

### Related Documentation

- **[API Reference](API_REFERENCE.md)** - Technical details
- **[Architecture](ARCHITECTURE.md)** - Witness predicate design
- **[Implementation Story](../history/IMPLEMENTATION_STORY.md)** - Development journey

---

[← Back to Documentation](README.md) | [Settings →](SETTINGS.md) | [Exclusion Theory →](../README.md)
