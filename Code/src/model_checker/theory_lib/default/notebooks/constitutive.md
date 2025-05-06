---
jupyter:
  jupytext:
    text_representation:
      extension: .md
      format_name: markdown
      format_version: '1.3'
      jupytext_version: 1.16.4
  kernelspec:
    display_name: Python 3 (ipykernel)
    language: python
    name: python3
---

# Constitutive Theory Demo Notebook

This notebook demonstrates constitutive logic examples from the default theory. It includes various countermodels showing invalid arguments and theorems showing valid arguments in constitutive logic.

```python
# Add parent directory to Python path to ensure module imports work
import sys
import os

# Add parent directories to path for proper imports
current_dir = os.path.dirname(os.path.abspath('.'))
parent_dir = os.path.dirname(current_dir)
parent_parent_dir = os.path.dirname(parent_dir)
parent_parent_parent_dir = os.path.dirname(parent_parent_dir)
parent_parent_parent_parent_dir = os.path.dirname(parent_parent_parent_dir)

# Add all possible parent paths to ensure the module is found
for path in [current_dir, parent_dir, parent_parent_dir, parent_parent_parent_dir, parent_parent_parent_parent_dir]:
    if path not in sys.path:
        sys.path.insert(0, path)

# Print current path to help with debugging
print(f"Current directory: {os.getcwd()}")
print(f"Python path: {sys.path}")
```

```python
import model_checker
from model_checker.theory_lib import default
from model_checker.theory_lib.default.examples import constitutive
```

## Setup

First, let's set up the basic components we need for model checking.

```python
# Import operators
operators = default.default_operators

# Get default settings
default_settings = default.Semantics.DEFAULT_EXAMPLE_SETTINGS

# Define general settings for display
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Update default settings with general settings
default_settings.update(general_settings)
```

## Helper Function

Let's create a helper function to run our examples.

```python
def run_example(example, name):
    """Run a specific example and display the results.
    
    Args:
        example: The example to run (list containing premises, conclusions, settings)
        name: The name of the example
    """
    premises, conclusions, settings = example
    
    # Create syntax object
    syntax = model_checker.syntactic.Syntax(premises, conclusions, operators)
    
    # Update default settings with example-specific settings and general settings
    example_settings = default_settings.copy()
    example_settings.update(settings)
    
    # Ensure print_impossible is set
    if 'print_impossible' not in example_settings:
        example_settings['print_impossible'] = True
    
    # Create semantics
    semantics = default.Semantics(example_settings)
    proposition_class = default.Proposition
    
    # Create model constraints
    model_constraints = model_checker.model.ModelConstraints(example_settings, syntax, semantics, proposition_class)
    
    # Create model structure
    model_structure = default.ModelStructure(model_constraints, example_settings)
    
    # Interpret sentences before printing
    sentences = model_structure.premises + model_structure.conclusions
    model_structure.interpret(sentences)
    
    # Print results
    model_structure.print_all(example_settings, name, "Default Semantics")
```

## Countermodels

Let's examine some key countermodels from constitutive logic.


### CL_CM_1: Equivalence of Tautologies

```python
run_example(constitutive.CL_CM_1_example, "Equivalence of Tautologies")
```

### CL_CM_2: Equivalence of Contradictions

```python
run_example(constitutive.CL_CM_2_example, "Equivalence of Contradictions")
```

### CL_CM_3: Ground Conjunction Supplementation

```python
run_example(constitutive.CL_CM_3_example, "Ground Conjunction Supplementation")
```

### CL_CM_4: Essence Disjunction Supplementation

```python
run_example(constitutive.CL_CM_4_example, "Essence Disjunction Supplementation")
```

### CL_CM_5: Identity Absorption: Disjunction over Conjunction

```python
run_example(constitutive.CL_CM_5_example, "Identity Absorption: Disjunction over Conjunction")
```

### CL_CM_6: Identity Absorption: Conjunction over Disjunction

```python
run_example(constitutive.CL_CM_6_example, "Identity Absorption: Conjunction over Disjunction")
```

### CL_CM_7: Identity Distribution: Conjunction over Disjunction

```python
run_example(constitutive.CL_CM_7_example, "Identity Distribution: Conjunction over Disjunction")
```

### CL_CM_8: Identity Distribution: Disjunction over Conjunction

```python
run_example(constitutive.CL_CM_8_example, "Identity Distribution: Disjunction over Conjunction")
```

### CL_CM_9: Strict Implication to Ground

```python
run_example(constitutive.CL_CM_9_example, "Strict Implication to Ground")
```

### CL_CM_10: Strict Implication to Essence

```python
run_example(constitutive.CL_CM_10_example, "Strict Implication to Essence")
```

### CL_CM_11: Essence Distribution

```python
run_example(constitutive.CL_CM_11_example, "Essence Distribution")
```

### CL_CM_12: Ground Distribution

```python
run_example(constitutive.CL_CM_12_example, "Ground Distribution")
```

### CL_CM_13: Shannon Expansion

```python
run_example(constitutive.CL_CM_13_example, "Shannon Expansion")
```

### CL_CM_14: Dual Shannon Expansion

```python
run_example(constitutive.CL_CM_14_example, "Dual Shannon Expansion")
```

## Theorems

Now let's examine some key theorems from constitutive logic.


### CL_TH_1: Ground to Essence

```python
run_example(constitutive.CL_TH_1_example, "Ground to Essence")
```

### CL_TH_2: Essence to Ground

```python
run_example(constitutive.CL_TH_2_example, "Essence to Ground")
```

### CL_TH_3: Essence to Identity

```python
run_example(constitutive.CL_TH_3_example, "Essence to Identity")
```

### CL_TH_4: Identity to Essence

```python
run_example(constitutive.CL_TH_4_example, "Identity to Essence")
```

### CL_TH_5: Ground to Identity

```python
run_example(constitutive.CL_TH_5_example, "Ground to Identity")
```

### CL_TH_6: Identity to Ground

```python
run_example(constitutive.CL_TH_6_example, "Identity to Ground")
```

### CL_TH_7: Negation Transparency

```python
run_example(constitutive.CL_TH_7_example, "Negation Transparency")
```

### CL_TH_8: Reverse Negation Transparency

```python
run_example(constitutive.CL_TH_8_example, "Reverse Negation Transparency")
```

### CL_TH_9: Absorption Identity

```python
run_example(constitutive.CL_TH_9_example, "Absorption Identity")
```

### CL_TH_10: Absorption Reduction: Conjunction over Disjunction

```python
run_example(constitutive.CL_TH_10_example, "Absorption Reduction: Conjunction over Disjunction")
```

### CL_TH_11: Absorption Reduction: Disjunction over Conjunction

```python
run_example(constitutive.CL_TH_11_example, "Absorption Reduction: Disjunction over Conjunction")
```

### CL_TH_12: Distribution Reduction: Disjunction over Conjunction

```python
run_example(constitutive.CL_TH_12_example, "Distribution Reduction: Disjunction over Conjunction")
```

### CL_TH_13: Distribution Reduction: Conjunction over Disjunction

```python
run_example(constitutive.CL_TH_13_example, "Distribution Reduction: Conjunction over Disjunction")
```

### CL_TH_14: Ground to Strict Implication

```python
run_example(constitutive.CL_TH_14_example, "Ground to Strict Implication")
```

### CL_TH_15: Essence to Converse Strict Implication

```python
run_example(constitutive.CL_TH_15_example, "Essence to Converse Strict Implication")
```

### CL_TH_16: Grounding Anti-Symmetry

```python
run_example(constitutive.CL_TH_16_example, "Grounding Anti-Symmetry")
```

### CL_TH_17: Essence Anti-Symmetry

```python
run_example(constitutive.CL_TH_17_example, "Essence Anti-Symmetry")
```

### CL_TH_18: Grounding Transitivity

```python
run_example(constitutive.CL_TH_18_example, "Grounding Transitivity")
```

### CL_TH_19: Essence Transitivity

```python
run_example(constitutive.CL_TH_19_example, "Essence Transitivity")
```

## Summary

This notebook demonstrates the key countermodels and theorems in constitutive logic using the default theory of the ModelChecker framework. The examples showcase various properties of ground (\leq), essence (\sqsubseteq), and identity (\equiv) operators, including their relationships with strict implication.
# %%

