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

# Logos Theory Demo

Welcome to the Logos Theory demonstration notebook! This notebook provides an interactive introduction to the Logos Theory implementation in ModelChecker.

## Overview

The Logos Theory provides a unified hyperintensional semantic framework for counterfactuals, constitutive operators, and modal logic. It implements a comprehensive approach to hyperintensional reasoning with over 20 operators organized across 5 subtheories.

### Key Features:
- **Hyperintensional bilateral propositions**: More fine-grained than possible world semantics
- **Truthmaker semantics**: For extensional connectives
- **Counterfactual conditionals**: Via alternative world-states
- **Constitutive operators**: For essence, ground, and propositional identity
- **Modular architecture**: 5 subtheories with selective loading

### Author:
- **Theory Author**: Benjamin Brast-McKie
- **Implementation Author**: Benjamin Brast-McKie
- **Contributors**: Miguel Buitrago
- **Key Papers**:
  - Brast-McKie (2021) "Identity and Aboutness", Journal of Philosophical Logic
  - Brast-McKie (2025) "Counterfactual Worlds", Journal of Philosophical Logic


## Setup and Imports

Let's start by importing the necessary modules and exploring the modular structure of logos theory:

```python
# Import the model checker and logos theory
from model_checker.theory_lib import logos
from model_checker.jupyter.interactive import check_formula, find_countermodel, ModelExplorer
from model_checker import BuildExample

# Explore available subtheories
print("Logos Theory Subtheories:")
subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual', 'conditional']
for sub in subtheories:
    print(f"  - {sub}")

print("\nLoading logos theory with all subtheories...")
logos_theory = logos.get_theory(subtheories)
print(f"Available operators: {len(logos_theory['operators'].operator_dictionary)} total")
```

## 1. Theory Introduction

### Logos Semantics Fundamentals

The Logos Theory is built on several key semantic innovations:

#### Core Concepts:

1. **Hyperintensional Propositions**: Go beyond possible world semantics
2. **Bilateral Truth Conditions**: Separate verifiers and falsifiers
3. **Alternative World-States**: For counterfactual reasoning
4. **Constitutive Relations**: Essence, ground, and identity
5. **Truthmaker Semantics**: For extensional operators

Let's explore the modular structure:

```python
# Load specific subtheories to see their operators
extensional_theory = logos.get_theory(['extensional'])
modal_theory = logos.get_theory(['modal'])

print("Extensional operators:")
ext_ops = list(extensional_theory['operators'].operator_dictionary.keys())
for op in sorted(ext_ops):
    print(f"  {op}")

print("\nModal operators:")
modal_ops = list(modal_theory['operators'].operator_dictionary.keys())
modal_only = [op for op in modal_ops if op not in ext_ops]
for op in sorted(modal_only):
    print(f"  {op}")
```

## 2. Basic Examples

Let's start with basic examples using different subtheories:


### Example 1: Extensional Logic

First, let's explore basic extensional reasoning in the logos framework:

```python
# Test basic extensional logic
result1 = check_formula("p → (q → p)", theory_name="logos")
display(result1)
```

```python
# Test conjunction and disjunction
result2 = check_formula("(p ∧ q) → (p ∨ q)", theory_name="logos")
display(result2)
```

### Example 2: Modal Logic

Now let's explore modal operators:

```python
# Test basic modal logic
result3 = check_formula("□p → p", theory_name="logos")
display(result3)
```

```python
# Test modal interdefinability
result4 = find_countermodel("□p ↔ ¬◇¬p", theory_name="logos")
display(result4)
```

### Example 3: Hyperintensional Reasoning

Let's explore what makes logos truly hyperintensional:

```python
# Test hyperintensional distinctions
# In classical logic, equivalent formulas are substitutable
# In hyperintensional logic, this may fail

result5 = find_countermodel("□(p ∨ ¬p) → □(q ∨ ¬q)", theory_name="logos")
display(result5)
```

## 3. Advanced Features

Now let's explore the advanced features that make logos theory unique:


### Constitutive Operators

Logos theory includes operators for constitutive relations like essence and ground:

```python
# Load constitutive operators
constitutive_theory = logos.get_theory(['extensional', 'modal', 'constitutive'])

print("Constitutive operators available:")
const_ops = list(constitutive_theory['operators'].operator_dictionary.keys())
base_ops = list(modal_theory['operators'].operator_dictionary.keys())
const_only = [op for op in const_ops if op not in base_ops]
for op in sorted(const_only):
    print(f"  {op}")
```

### Counterfactual Reasoning

Let's explore counterfactual conditionals in the logos framework:

```python
# Load counterfactual operators
counterfactual_theory = logos.get_theory(['extensional', 'modal', 'counterfactual'])

# Test basic counterfactual reasoning
# Note: Specific counterfactual operators depend on implementation
example_cf = [
    ["p"],  # premises
    ["◇p"],  # conclusions - if p then possibly p
    {'N': 3, 'max_time': 5, 'expectation': False}
]

cf_model = BuildExample("counterfactual_test", counterfactual_theory, example_cf)
cf_result = cf_model.check_result()

print(f"Counterfactual example is {'valid' if cf_result else 'invalid'}")
if not cf_result:
    print("\nCountermodel structure:")
    cf_model.model_structure.print_all()
```

### Interactive Model Explorer

Let's use the interactive model explorer with logos theory:

```python
# Create an interactive explorer for logos theory
explorer = ModelExplorer(theory_name="logos")

# Set up a complex modal example
explorer.set_formula("□(p → q) → (□p → □q)")
explorer.set_premises([])

# Update settings for modal logic
explorer.update_settings({
    'N': 4,
    'max_time': 10,
    'contingent': True
})

# Display the explorer
explorer.display()
```

## 4. Subtheory Comparison

Let's compare how different subtheories handle the same formulas:

```python
# Test formula across different subtheory combinations
test_formula = "□p → ◇p"
subtheory_combinations = [
    ['extensional'],
    ['extensional', 'modal'],
    ['extensional', 'modal', 'constitutive'],
    ['extensional', 'modal', 'counterfactual']
]

print(f"Testing formula: {test_formula}")
print("Across different subtheory combinations:\n")

for subs in subtheory_combinations:
    try:
        theory = logos.get_theory(subs)
        example = [[], [test_formula], {'N': 3, 'max_time': 5, 'expectation': False}]
        model = BuildExample(f"test_{'+'.join(subs)}", theory, example)
        result = model.check_result()
        
        print(f"Subtheories {'+'.join(subs)}: {'Valid' if result else 'Invalid'}")
        
    except Exception as e:
        print(f"Subtheories {'+'.join(subs)}: Error - {str(e)[:50]}...")
```

## 5. Comparison with Other Theories

Let's compare logos theory with classical and other non-classical approaches:


### Logos vs Classical Logic

| Principle | Classical Logic | Logos Theory |
|-----------|----------------|---------------|
| Substitution of Equivalents | Always valid | May fail (hyperintensional) |
| Modal Logic | Standard S5/S4 | Hyperintensional modal logic |
| Truth Conditions | Classical two-valued | Bilateral (verifiers/falsifiers) |
| Counterfactuals | Not primitive | Alternative world-states |

```python
# Test substitution failure in hyperintensional contexts
substitution_tests = [
    "□(2+2=4) → □(3+3=6)",  # Mathematical equivalents
    "□(p ∨ ¬p) → □(q ∨ ¬q)",  # Logical equivalents
    "◇(p ∧ q) → ◇(q ∧ p)",  # Conjunction commutativity
]

print("Testing substitution in hyperintensional contexts:")
for i, formula in enumerate(substitution_tests, 1):
    try:
        result = find_countermodel(formula, theory_name="logos")
        print(f"\n{i}. {formula}")
        display(result)
    except Exception as e:
        print(f"\n{i}. {formula}: Error - {e}")
```

### Comparison with Exclusion Theory

Let's compare how logos and exclusion theories handle similar formulas:

```python
# Compare basic logical principles across theories
comparison_formulas = [
    "p ∨ ¬p",  # Law of excluded middle
    "(p ∧ q) → p",  # Conjunction elimination
    "p → (q → p)",  # Weakening
]

theories_to_compare = ["logos", "exclusion"]

print("Comparing theories on basic principles:\n")
for formula in comparison_formulas:
    print(f"Formula: {formula}")
    for theory in theories_to_compare:
        try:
            result = check_formula(formula, theory_name=theory)
            # Extract validity from HTML result (simplified)
            validity = "Valid" if "Valid" in str(result) else "Invalid"
            print(f"  {theory.capitalize()}: {validity}")
        except Exception as e:
            print(f"  {theory.capitalize()}: Error")
    print()
```

## 6. Interactive Exercises

Try these exercises to explore logos theory:


### Exercise 1: Selective Subtheory Loading

Experiment with different subtheory combinations:

```python
# Exercise 1: Modify the subtheories list and observe available operators
my_subtheories = ['extensional', 'modal']  # Try different combinations

my_theory = logos.get_theory(my_subtheories)
available_ops = list(my_theory['operators'].operator_dictionary.keys())

print(f"Selected subtheories: {my_subtheories}")
print(f"Available operators: {len(available_ops)}")
print("Operators:")
for op in sorted(available_ops):
    print(f"  {op}")
```

### Exercise 2: Modal Logic Exploration

Test different modal logic principles:

```python
# Exercise 2: Test modal logic principles
modal_formulas = [
    "□p → p",  # T axiom
    "□p → □□p",  # 4 axiom
    "◇p → □◇p",  # 5 axiom
    "□(p → q) → (□p → □q)",  # K axiom
]

print("Testing modal logic axioms in logos theory:\n")
for axiom in modal_formulas:
    result = check_formula(axiom, theory_name="logos")
    print(f"Testing: {axiom}")
    display(result)
    print()
```

### Exercise 3: Build Complex Examples

Create sophisticated logical arguments:

```python
# Exercise 3: Build your own complex example
complex_premises = [
    "□(p → q)",  # Necessarily, if p then q
    "◇p",        # Possibly p
    "□¬r"        # Necessarily not r
]

complex_conclusions = [
    "◇q",        # Possibly q
    "¬◇r"        # Not possibly r
]

complex_settings = {
    'N': 4,
    'max_time': 10,
    'contingent': True,
    'expectation': False
}

complex_example = [complex_premises, complex_conclusions, complex_settings]
complex_model = BuildExample("complex_modal", logos_theory, complex_example)

result = complex_model.check_result()
print(f"Complex modal argument is {'valid' if result else 'invalid'}")
print(f"Premises: {complex_premises}")
print(f"Conclusions: {complex_conclusions}")

if not result:
    print("\nCountermodel found:")
    complex_model.model_structure.print_all()
else:
    print("\nNo countermodel found - the argument is valid!")
```

### Exercise 4: Hyperintensional Distinctions

Explore what makes logos theory hyperintensional:

```python
# Exercise 4: Test hyperintensional phenomena
hyperintensional_tests = [
    # Test if necessarily equivalent formulas are substitutable
    ("□(p ↔ p)", "□(q ↔ q)", "Should tautologies be substitutable?"),
    
    # Test fine-grained distinctions
    ("□(p ∧ q)", "□(q ∧ p)", "Are conjunctions commutative in modal contexts?"),
    
    # Test content sensitivity
    ("□((p → q) → p)", "□((r → s) → r)", "Do necessarily equivalent schemas substitute?"),
]

print("Testing hyperintensional distinctions:\n")
for formula1, formula2, question in hyperintensional_tests:
    print(f"Question: {question}")
    equivalence = f"({formula1}) ↔ ({formula2})"
    
    result = find_countermodel(equivalence, theory_name="logos")
    print(f"Testing: {equivalence}")
    display(result)
    print("-" * 50)
```

## 7. Summary and Further Reading

### What We've Learned:

1. **Modular Architecture**: How to selectively load subtheories for specific needs
2. **Hyperintensional Semantics**: Going beyond possible world semantics
3. **Bilateral Truth Conditions**: Separate treatment of verifiers and falsifiers
4. **Rich Operator Set**: 20+ operators across 5 semantic domains
5. **Advanced Modal Logic**: Hyperintensional approach to necessity and possibility

### Key Innovations:

- **Hyperintensional Propositions**: Finer-grained than classical propositions
- **Truthmaker Semantics**: Connects truth to what makes things true
- **Alternative World-States**: Novel approach to counterfactuals
- **Constitutive Relations**: Essence, ground, and identity as primitive
- **Modular Design**: Load only the operators you need

### Subtheory Guide:

- **Extensional**: Basic truth-functional operators
- **Modal**: Necessity, possibility, and related operators
- **Constitutive**: Essence, ground, and identity operators
- **Counterfactual**: Alternative world-state semantics
- **Conditional**: Various conditional operators

### Further Reading:

- Brast-McKie (2021) "Identity and Aboutness", Journal of Philosophical Logic
- Brast-McKie (2025) "Counterfactual Worlds", Journal of Philosophical Logic
- ModelChecker documentation: [Logos Theory README](../README.md)
- Individual subtheory documentation in `logos/subtheories/`

### Next Steps:

1. Explore individual subtheory notebooks (if available)
2. Compare with [Exclusion Theory notebook](../../exclusion/notebooks/exclusion_demo.ipynb)
3. Experiment with constitutive operators for metaphysical reasoning
4. Try counterfactual reasoning with alternative world-states
5. Study the implementation in `logos/` directory for technical details


### Creating Custom Subtheory Combinations

One of the most powerful features of logos theory is its modularity. Here's how to create your own combinations:

```python
# Example: Create a theory with just what you need
def create_custom_logos(subtheories, description=""):
    """Create a custom logos theory with specific subtheories."""
    theory = logos.get_theory(subtheories)
    
    print(f"Custom Logos Theory: {description}")
    print(f"Subtheories: {', '.join(subtheories)}")
    print(f"Total operators: {len(theory['operators'].operator_dictionary)}")
    
    return theory

# Example combinations for different purposes
basic_modal = create_custom_logos(
    ['extensional', 'modal'], 
    "Basic Modal Logic"
)

print()

metaphysics = create_custom_logos(
    ['extensional', 'modal', 'constitutive'], 
    "Metaphysical Reasoning"
)

print()

full_theory = create_custom_logos(
    ['extensional', 'modal', 'constitutive', 'counterfactual', 'conditional'],
    "Complete Hyperintensional Framework"
)
```

---

*This notebook was created as part of the ModelChecker project. The Logos Theory represents a significant advance in computational metaphysics and hyperintensional logic. For questions, contributions, or to cite this work, please visit the [project repository](https://github.com/benbrastmckie/ModelChecker).*
