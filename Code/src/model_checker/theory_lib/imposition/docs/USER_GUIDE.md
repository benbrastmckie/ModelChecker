# User Guide: Tutorial and Introduction to Imposition Theory

[← Back to Documentation](README.md) | [Settings →](SETTINGS.md) | [Imposition Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # Design and implementation
├── ITERATE.md         # Model iteration guide
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration parameters
└── USER_GUIDE.md      # This file - tutorial and introduction
```

## Overview

The **User Guide** provides a comprehensive tutorial and introduction to Kit Fine's imposition theory for counterfactual reasoning within the ModelChecker framework. This guide demonstrates how to use the imposition operation for evaluating counterfactual conditionals without possible worlds semantics.

Within the imposition theory framework, counterfactuals like "if A then must B" are evaluated through state imposition rather than world accessibility. The theory provides operators for must-counterfactuals (↪) and might-counterfactuals (⟂), enabling sophisticated counterfactual reasoning grounded in hyperintensional semantics.

This guide serves researchers and developers learning to use the imposition theory, providing practical examples, common patterns, and troubleshooting tips.

## Getting Started

### Basic Counterfactual Reasoning

```python
# Basic counterfactual reasoning
from model_checker.theory_lib.imposition import get_theory
from model_checker import BuildExample

# Create counterfactual validity test
theory = get_theory()
example = BuildExample("modus_ponens", theory,
    premises=['A', 'A \\boxright B'],  # A is true, if A then must B
    conclusions=['B'],                    # Therefore B
    settings={'N': 3}
)

# Check validity
result = example.check_validity()
print(f"Counterfactual modus ponens valid: {result}")  # True

# Find counterexample to antecedent strengthening
counter = BuildExample("antecedent_str", theory,
    premises=['A \\boxright C'],
    conclusions=['(A \\wedge B) \\boxright C'],
    settings={'N': 3, 'expectation': False}
)

# Display countermodel
if not counter.check_validity():
    counter.print_model()
```

## Basic Concepts

### Imposition Semantics

Fine's imposition semantics evaluates counterfactuals through state imposition:

1. **States**: Partial ways things could be (not complete worlds)
2. **Imposition**: Operation that imposes one state on another
3. **Alternative Worlds**: Outcomes of imposing antecedent states on evaluation world

### Operators

The theory provides 11 operators total:

**Extensional Operators** (7):
- `\\neg` (¬): Negation
- `\\wedge` (∧): Conjunction
- `\\vee` (∨): Disjunction
- `\\to` (→): Material conditional
- `\\leftrightarrow` (↔): Biconditional
- `\\top` (⊤): Truth constant
- `\\bot` (⊥): Falsehood constant

**Modal Operators** (2, inherited):
- `\\Box` (□): Necessity
- `\\Diamond` (◇): Possibility

**Imposition Operators** (2):
- `\\boxright` (▷): Must-counterfactual ("if A then must B")
- `\\diamondright` (◇▷): Might-counterfactual ("if A then might B")

### Truth Conditions

**Must-Counterfactual**: `A \\boxright B`
- Verified when: Some part imposes A-verifiers on world yielding B-verifiers
- Falsified when: Some part imposes A-verifiers on world yielding B-falsifiers

**Might-Counterfactual**: `A \\diamondright B` := `\\neg(A \\boxright \\neg B)`
- Verified when: Not the case that imposing A must yield ¬B
- Falsified when: Imposing A necessarily yields ¬B

## Common Examples

### Testing Validity

```python
# Counterfactual modus ponens (valid)
example = BuildExample("cf_mp", theory,
    premises=['A', 'A \\boxright B'],
    conclusions=['B']
)
assert example.check_validity() == True

# Antecedent strengthening (invalid)
example = BuildExample("ant_str", theory,
    premises=['A \\boxright C'],
    conclusions=['(A \\wedge B) \\boxright C'],
    settings={'expectation': False}
)
assert example.check_validity() == False

# Sobel sequences
example = BuildExample("sobel", theory,
    premises=['A \\boxright X', '\\neg((A \\wedge B) \\boxright X)'],
    conclusions=['(A \\wedge B) \\boxright \\neg X'],
    settings={'N': 4}
)
```

### Exploring Model Space

```python
from model_checker.theory_lib.imposition import iterate_example

# Find multiple counterfactual models
example = BuildExample("explore", theory,
    premises=['\\neg A', 'A \\boxright B'],
    conclusions=['A \\diamondright C']
)

models = iterate_example(example, max_iterations=5)
for i, model in enumerate(models):
    print(f"\nModel {i+1}:")
    model.print_model()
    if hasattr(model, 'print_model_differences'):
        model.print_model_differences()
```

### Theory Comparison

```python
# Compare with logos theory
from model_checker.theory_lib.logos import get_theory as get_logos

logos_theory = get_logos()
imp_theory = get_theory()

# Test exportation principle
for theory_name, theory in [("Logos", logos_theory), ("Imposition", imp_theory)]:
    example = BuildExample(f"{theory_name}_export", theory,
        premises=['A \\boxright (B \\boxright C)'],
        conclusions=['(A \\wedge B) \\boxright C']
    )
    print(f"{theory_name}: {example.check_validity()}")
```

## Tips and Patterns

### Performance

1. **Start Simple**: Begin with N=3 for most examples
2. **Timeout Strategy**: Increase max_time for nested counterfactuals
3. **Constraint Settings**: Use non_empty=True for meaningful models

### Formula Construction

1. **Use LaTeX Notation**: Write `\\boxright` not `↪` in formulas
2. **Parenthesize Carefully**: Counterfactuals have specific precedence
3. **Combine Operators**: Mix classical and counterfactual operators

### Debugging

1. **Enable Diagnostics**:
   ```python
   settings = {
       'print_constraints': True,
       'print_z3': True,
       'N': 2  # Start minimal
   }
   ```

2. **Check Model Structure**:
   ```python
   if not example.check_validity():
       model = example.model_structure
       print(f"Worlds: {model.worlds}")
       print(f"Alternatives: {model.calculate_alternative_worlds(...)}")
   ```

## Advanced Usage

### Custom Settings

```python
# Complex counterfactual exploration
advanced_settings = {
    'N': 5,                # Larger state space
    'contingent': True,    # Realistic scenarios
    'disjoint': True,      # Clear boundaries
    'non_empty': True,     # No trivial states
    'max_time': 30,        # Extended solving
    'iterate': 10,         # Find many models
    'maximize': True       # Diverse models
}
```

### Model Analysis

```python
def analyze_imposition(model):
    """Analyze imposition patterns in a model."""
    print("\nImposition Analysis:")
    
    # Check which states impose on which worlds
    for state in model.states:
        for world in model.worlds:
            # Check imposition outcomes
            outcomes = [w for w in model.worlds 
                       if model.semantics.is_alternative(w, state, {'world': world})]
            if outcomes:
                print(f"  {state} imposed on {world} yields: {outcomes}")
```

### Batch Testing

```python
from model_checker.theory_lib.imposition import get_test_examples

# Run all test examples
test_results = {}
for name, example_case in get_test_examples().items():
    example = BuildExample(name, theory, example_case)
    result = example.check_result()
    test_results[name] = result['model_found']
    
# Summarize results
countermodels = sum(1 for r in test_results.values() if r)
theorems = sum(1 for r in test_results.values() if not r)
print(f"Countermodels: {countermodels}, Theorems: {theorems}")
```

## Documentation

### For Beginners

- **[Basic Concepts](#basic-concepts)** - Core ideas and operators
- **[Common Examples](#common-examples)** - Standard usage patterns
- **[Tips and Patterns](#tips-and-patterns)** - Best practices

### For Advanced Users

- **[Advanced Usage](#advanced-usage)** - Complex scenarios
- **[Model Analysis](#model-analysis)** - Deep inspection
- **[Batch Testing](#batch-testing)** - Systematic exploration

### For Researchers

- **[Truth Conditions](#truth-conditions)** - Formal semantics
- **[Theory Comparison](#theory-comparison)** - Cross-theory analysis
- **[API Reference](API_REFERENCE.md)** - Technical details

## Key Takeaways

1. **State-Based**: Counterfactuals via imposition, not possible worlds
2. **Two Operators**: Must (↪) and might (⟂) counterfactuals
3. **Fine's Semantics**: Bilateral verification/falsification conditions
4. **Model Iteration**: Explore multiple counterfactual scenarios
5. **Theory Integration**: Compare with other semantic frameworks

## References

### Implementation Resources

- **[Examples Module](../examples.py)** - 32 test cases
- **[Iterate Module](../iterate.py)** - Model iteration
- **[Notebooks](../notebooks/)** - Interactive tutorials

### Related Documentation

- **[API Reference](API_REFERENCE.md)** - Complete technical reference
- **[Architecture](ARCHITECTURE.md)** - Design and implementation
- **[Settings](SETTINGS.md)** - Configuration options

---

[← Back to Documentation](README.md) | [Settings →](SETTINGS.md) | [Imposition Theory →](../README.md)