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

# Logos Modal Operators Demo

This notebook focuses specifically on the modal operators available in the Logos Theory. Modal logic deals with concepts of necessity, possibility, and related notions.

## Overview

The Logos modal subtheory provides a hyperintensional approach to modal logic that goes beyond traditional possible world semantics. This allows for finer-grained distinctions between necessarily equivalent propositions.

### Key Modal Operators:
- **□** (Box): Necessity
- **◇** (Diamond): Possibility  
- **Various accessibility relations**: For different modal systems
- **Hyperintensional distinctions**: Beyond S5 modal logic


## Setup

```python
# Import necessary modules
from model_checker.theory_lib import logos
from model_checker.jupyter.interactive import check_formula, find_countermodel
from model_checker import BuildExample

# Load modal operators specifically
modal_theory = logos.get_theory(['extensional', 'modal'])
print("Modal theory loaded successfully!")

# Show available modal operators
all_ops = list(modal_theory['operators'].operator_dictionary.keys())
ext_only = logos.get_theory(['extensional'])
ext_ops = list(ext_only['operators'].operator_dictionary.keys())
modal_ops = [op for op in all_ops if op not in ext_ops]

print(f"\nModal-specific operators: {len(modal_ops)}")
for op in sorted(modal_ops):
    print(f"  {op}")
```

## 1. Basic Modal Logic

Let's start with fundamental modal logic principles:


### Necessity and Possibility

```python
# Test basic modal interdefinability
print("Testing modal interdefinability:")

# Possibility defined via necessity
result1 = check_formula("◇p ↔ ¬□¬p", theory_name="logos")
print("◇p ↔ ¬□¬p (possibility via necessity):")
display(result1)

# Necessity defined via possibility  
result2 = check_formula("□p ↔ ¬◇¬p", theory_name="logos")
print("\n□p ↔ ¬◇¬p (necessity via possibility):")
display(result2)
```

### Modal System Axioms

Let's test which modal logic axioms hold in the Logos framework:

```python
# Test standard modal logic axioms
modal_axioms = [
    ("K", "□(p → q) → (□p → □q)", "Distribution of necessity over implication"),
    ("T", "□p → p", "What is necessary is actual"),
    ("4", "□p → □□p", "Necessity of necessity"),
    ("5", "◇p → □◇p", "Possibility of possibility"),
    ("B", "p → □◇p", "What is actual is possibly necessary")
]

print("Testing modal logic axioms in Logos theory:\n")

for name, axiom, description in modal_axioms:
    print(f"Axiom {name}: {description}")
    print(f"Formula: {axiom}")
    
    result = check_formula(axiom, theory_name="logos")
    display(result)
    print("-" * 60)
```

## 2. Hyperintensional Modal Logic

Now let's explore what makes Logos modal logic hyperintensional:


### Substitution Failures

In hyperintensional logic, necessarily equivalent formulas may not be substitutable in modal contexts:

```python
# Test substitution of logical equivalents
substitution_tests = [
    ("□(p ∨ ¬p)", "□(q ∨ ¬q)", "Substitution of tautologies"),
    ("□(p ∧ q)", "□(q ∧ p)", "Conjunction commutativity"),
    ("□((p → q) → p)", "□((r → s) → r)", "Schema substitution"),
    ("□(p ↔ p)", "□(q ↔ q)", "Identity substitution")
]

print("Testing hyperintensional substitution failures:\n")

for formula1, formula2, description in substitution_tests:
    print(f"Test: {description}")
    equivalence = f"({formula1}) ↔ ({formula2})"
    print(f"Checking: {equivalence}")
    
    # Look for countermodels to the equivalence
    result = find_countermodel(equivalence, theory_name="logos")
    display(result)
    print("-" * 60)
```

### Content Sensitivity

Hyperintensional logic is sensitive to the content or subject matter of propositions:

```python
# Test content sensitivity
content_tests = [
    # Mathematical vs empirical necessities
    ("□(2+2=4) → □(snow_is_white)", "Mathematical necessity doesn't imply empirical necessity"),
    
    # Logical vs metaphysical necessity
    ("□(p → p) → □(water_is_H2O)", "Logical necessity doesn't imply metaphysical necessity"),
    
    # Subject matter distinctions
    ("□(p ∨ ¬p) → □(q ∨ ¬q)", "Tautologies with different subject matters"),
]

print("Testing content sensitivity in modal contexts:\n")

for formula, description in content_tests:
    print(f"Test: {description}")
    print(f"Formula: {formula}")
    
    result = find_countermodel(formula, theory_name="logos")
    display(result)
    print("-" * 60)
```

## 3. Complex Modal Reasoning

Let's explore more sophisticated modal reasoning patterns:


### Nested Modalities

```python
# Test complex nested modal formulas
nested_examples = [
    {
        'premises': ["□(p → □q)", "◇p"],
        'conclusions': ["◇□q"],
        'description': "From necessary conditional and possibility"
    },
    {
        'premises': ["□◇p", "□(p → q)"],
        'conclusions': ["□◇q"],
        'description': "Necessity of possibility with conditional"
    },
    {
        'premises': ["◇□p", "□(p ↔ q)"],
        'conclusions': ["◇□q"],
        'description': "Possibility of necessity with biconditional"
    }
]

print("Testing complex nested modal reasoning:\n")

for i, example in enumerate(nested_examples, 1):
    print(f"Example {i}: {example['description']}")
    print(f"Premises: {example['premises']}")
    print(f"Conclusions: {example['conclusions']}")
    
    # Build the example
    modal_example = [
        example['premises'],
        example['conclusions'],
        {'N': 4, 'max_time': 10, 'expectation': False}
    ]
    
    model = BuildExample(f"nested_modal_{i}", modal_theory, modal_example)
    result = model.check_result()
    
    print(f"Result: {'Valid' if result else 'Invalid'}")
    
    if not result:
        print("Countermodel found - detailed structure:")
        model.model_structure.print_all()
    
    print("=" * 70)
```

## 4. Interactive Modal Explorer

Use this interactive section to experiment with modal formulas:

```python
# Interactive modal logic explorer
def explore_modal_formula(formula, premises=None, settings=None):
    """Explore a modal formula with detailed analysis."""
    if premises is None:
        premises = []
    if settings is None:
        settings = {'N': 3, 'max_time': 10}
    
    print(f"Exploring modal formula: {formula}")
    if premises:
        print(f"With premises: {premises}")
    
    # Check validity
    if premises:
        example = [premises, [formula], {**settings, 'expectation': False}]
        model = BuildExample("modal_exploration", modal_theory, example)
        result = model.check_result()
        print(f"\nArgument is {'valid' if result else 'invalid'}")
    else:
        result = check_formula(formula, theory_name="logos")
        display(result)
    
    # Also check for countermodels
    print("\nLooking for countermodels:")
    counter_result = find_countermodel(formula, theory_name="logos", premises=premises)
    display(counter_result)

# Try your own modal formulas here!
explore_modal_formula("□(p → q) → (□p → □q)")  # K axiom
```

```python
# Exercise: Modify this cell to test your own modal formulas
my_formula = "◇□p → □◇p"  # Change this formula
my_premises = []  # Add premises if needed

explore_modal_formula(my_formula, my_premises)
```

## 5. Comparative Analysis

Compare modal logic in Logos vs classical systems:

```python
# Compare Logos modal logic with standard systems
def test_modal_system_features():
    """Test which features of standard modal systems hold in Logos."""
    
    systems = {
        'K': ["□(p → q) → (□p → □q)"],
        'T (K + T)': ["□(p → q) → (□p → □q)", "□p → p"],
        'S4 (T + 4)': ["□(p → q) → (□p → □q)", "□p → p", "□p → □□p"],
        'S5 (S4 + 5)': ["□(p → q) → (□p → □q)", "□p → p", "□p → □□p", "◇p → □◇p"]
    }
    
    print("Testing correspondence to standard modal systems:\n")
    
    for system_name, axioms in systems.items():
        print(f"System {system_name}:")
        all_valid = True
        
        for axiom in axioms:
            # Quick test - just check if it's a tautology
            try:
                example = [[], [axiom], {'N': 3, 'max_time': 5, 'expectation': False}]
                model = BuildExample(f"test_{system_name}", modal_theory, example)
                result = model.check_result()
                status = "✓" if result else "✗"
                print(f"  {status} {axiom}")
                if not result:
                    all_valid = False
            except Exception as e:
                print(f"  ? {axiom} (error: {str(e)[:30]}...)")
                all_valid = False
        
        correspondence = "Full" if all_valid else "Partial"
        print(f"  → {correspondence} correspondence to {system_name}")
        print()

test_modal_system_features()
```

## 6. Advanced Exercises

Try these advanced modal logic exercises:


### Exercise 1: Modal Paradoxes

Test how Logos handles classical modal paradoxes:

```python
# Exercise 1: Modal paradoxes
paradoxes = [
    ("□(□p → p) → □p", "Löb's theorem"),
    ("□(□(□p → p) → p) → □p", "Generalized Löb"),
    ("◇□⊥ → ⊥", "Impossibility of necessary contradiction"),
]

print("Testing modal paradoxes and theorems:\n")

for formula, name in paradoxes:
    print(f"Testing {name}:")
    print(f"Formula: {formula}")
    
    try:
        result = find_countermodel(formula, theory_name="logos")
        display(result)
    except Exception as e:
        print(f"Error: {e}")
    
    print("-" * 50)
```

### Exercise 2: Build Your Own Modal Argument

Create and test your own modal logic argument:

```python
# Exercise 2: Design your own modal argument
# Example: Ontological argument structure

my_modal_argument = {
    'name': 'Custom Modal Argument',
    'premises': [
        "◇□p",  # Possibly necessarily p
        "□(□p → q)",  # Necessarily, if necessarily p then q
    ],
    'conclusions': [
        "◇q",  # Possibly q
    ],
    'settings': {
        'N': 4,
        'max_time': 15,
        'contingent': True,
        'expectation': False  # We're testing validity
    }
}

print(f"Testing: {my_modal_argument['name']}")
print(f"Premises: {my_modal_argument['premises']}")
print(f"Conclusions: {my_modal_argument['conclusions']}")

example = [
    my_modal_argument['premises'],
    my_modal_argument['conclusions'],
    my_modal_argument['settings']
]

model = BuildExample("custom_modal", modal_theory, example)
result = model.check_result()

print(f"\nResult: The argument is {'valid' if result else 'invalid'}")

if not result:
    print("\nCountermodel details:")
    model.model_structure.print_all()
else:
    print("\nNo countermodel found - the argument is logically valid!")
```

## Summary

In this notebook, we've explored:

1. **Basic Modal Logic**: Necessity, possibility, and standard axioms
2. **Hyperintensional Features**: How Logos goes beyond classical modal logic
3. **Substitution Failures**: When equivalent formulas aren't substitutable
4. **Complex Reasoning**: Nested modalities and sophisticated arguments
5. **System Comparison**: How Logos relates to K, T, S4, S5
6. **Advanced Applications**: Paradoxes and custom arguments

### Key Takeaways:

- Logos modal logic is **hyperintensional** - it makes distinctions beyond possible world semantics
- **Substitution failures** occur even for necessarily equivalent formulas
- The system may not correspond exactly to classical modal systems
- **Content and subject matter** affect modal reasoning
- The framework enables sophisticated **nested modal reasoning**

### Next Steps:

1. Explore the [main Logos notebook](../logos_demo.ipynb) for the full theory
2. Try the [constitutive operators](./constitutive_operators_demo.ipynb) if available
3. Compare with [Exclusion Theory](../../exclusion/notebooks/exclusion_demo.ipynb)
4. Study the implementation in `logos/subtheories/modal/`
