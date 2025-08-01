# Notebooks: Interactive Examples for Imposition Theory

[← Back to Theory](../README.md) | [Documentation →](../docs/README.md) | [Examples →](../examples.py)

## Directory Structure

```
notebooks/
├── README.md        # This file - notebook overview
└── examples.ipynb   # Interactive counterfactual examples
```

## Overview

The **Notebooks** directory provides interactive Jupyter notebooks demonstrating Kit Fine's imposition theory for counterfactual reasoning. These notebooks enable hands-on exploration of counterfactual semantics through executable examples and visual model representations.

Within the imposition theory framework, these notebooks illustrate how counterfactuals are evaluated through state imposition rather than possible worlds. The examples showcase both valid theorems and invalid principles with countermodels, providing deep insights into Fine's innovative semantic approach.

This collection serves researchers and students learning counterfactual logic, offering interactive tools to explore the differences between various semantic theories and understand the formal structure of counterfactual reasoning.

## Getting Started

```bash
# Launch Jupyter environment
./run_jupyter.sh

# Navigate to notebooks
cd src/model_checker/theory_lib/imposition/notebooks/

# Open examples notebook
# Select 'examples.ipynb' in Jupyter interface
```

## Available Notebooks

### examples.ipynb

**32 Interactive Examples** demonstrating counterfactual reasoning:

**Structure**:
1. Setup and imports
2. Helper function for running examples
3. Countermodels (21 examples) - Invalid counterfactual principles
4. Theorems (11 examples) - Valid counterfactual principles

**Key Examples**:
- Antecedent strengthening (invalid)
- Contraposition (valid) 
- Sobel sequences
- Exportation principles
- Transitivity tests

## Notebook Features

### Output Format

Each example produces detailed semantic output:

```
========================================
EXAMPLE Antecedent Strengthening: there is a countermodel.

Atomic States: 3
Semantic Theory: Imposition Semantics

Premise:
1. (A \boxright C)

Conclusion:
2. ((A \wedge B) \boxright C)

Z3 Run Time: 0.004 seconds
========================================
State Space:
  #b000 = □
  #b001 = a
  #b010 = b
  #b011 = a.b (world)
  ...

The evaluation world is: a.b

INTERPRETED PREMISE:
1. |(A \boxright C)| = < {□}, ∅ >  (True in a.b)
   |A| = < {a.b}, {b.c} >
   |A|-alternatives to a.b = {a.b}
     |C| = < {c}, {a.c} >  (True in a.b)

INTERPRETED CONCLUSION:
2. |((A \wedge B) \boxright C)| = < ∅, {□} >  (False in a.b)
   |(A \wedge B)| = < {a.b.c}, {a, b} >
   |(A \wedge B)|-alternatives to a.b = {b.c}
     |C| = < {c}, {a.c} >  (False in b.c)
========================================
```

### Interactive Features

1. **Execute cells individually** to explore specific examples
2. **Modify formulas** to test variations
3. **Adjust settings** (N, max_time, constraints)
4. **Compare theories** by changing semantic theory

### Visualization Elements

- **State space** representation with world markers
- **Verification/falsification sets** for each formula
- **Alternative world calculations** for counterfactuals
- **Truth value indicators** at evaluation world

## Usage Patterns

### Running All Examples

```python
# In notebook cell
for example_name, example_case in get_test_examples().items():
    print(f"\n{'='*60}")
    print(f"Running: {example_name}")
    run_example(example_name, example_case)
```

### Exploring Specific Principles

```python
# Test antecedent strengthening
example = BuildExample("ant_str", theory,
    premises=['A \\boxright C'],
    conclusions=['(A \\wedge B) \\boxright C'],
    settings={'N': 3, 'expectation': False}
)
example.print_model()
```

### Comparing Semantic Theories

```python
# Compare imposition with other theories
theories = {
    "Imposition": imposition_theory,
    "Logos": logos_theory
}

for name, theory in theories.items():
    example = BuildExample(f"{name}_test", theory, example_case)
    print(f"{name}: {example.check_validity()}")
```

## Learning Objectives

### Understanding Countermodels

The notebook demonstrates why certain counterfactual principles fail:

1. **Antecedent Strengthening**: Adding conjuncts can change outcomes
2. **Transitivity**: Chains of counterfactuals may not compose
3. **Monotonicity**: Imposition doesn't preserve subset relations

### Understanding Theorems

Valid principles illustrated include:

1. **Modus Ponens**: If A and A→B, then B
2. **Contraposition**: Preserving logical relationships
3. **Identity**: A counterfactually implies itself

### Semantic Insights

- How imposition differs from material conditionals
- Role of alternative worlds in evaluation
- Bilateral verification/falsification conditions
- State-based vs world-based semantics

## Documentation

### For Students

- **[Output Format](#output-format)** - Understanding model displays
- **[Usage Patterns](#usage-patterns)** - Common interaction patterns
- **[Learning Objectives](#learning-objectives)** - Key concepts to master

### For Researchers

- **[Interactive Features](#interactive-features)** - Advanced exploration tools
- **[Comparing Theories](#comparing-semantic-theories)** - Cross-theory analysis
- **[Example Module](../examples.py)** - Source definitions

### For Developers

- **[Notebook Structure](#examplesipynb)** - Implementation details
- **[Helper Functions](#usage-patterns)** - Code patterns
- **[API Reference](../docs/API_REFERENCE.md)** - Technical documentation

## Key Insights

1. **32 Examples Total**: 21 countermodels, 11 theorems
2. **Interactive Exploration**: Modify and test variations
3. **Visual Understanding**: See semantic structures directly
4. **Theory Comparison**: Test same formulas across theories
5. **Fine's Innovation**: State imposition vs possible worlds

## References

### Implementation Files

- **[Examples Module](../examples.py)** - Source for all examples
- **[Semantic Module](../semantic.py)** - ImpositionSemantics
- **[Operators Module](../operators.py)** - Counterfactual operators

### Related Resources

- **[User Guide](../docs/USER_GUIDE.md)** - Tutorial introduction
- **[Theory Documentation](../README.md)** - Comprehensive overview
- **Fine (2012)** - "Counterfactuals without Possible Worlds"

---

[← Back to Theory](../README.md) | [Documentation →](../docs/README.md) | [Examples →](../examples.py)