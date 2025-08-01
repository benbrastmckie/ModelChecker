# Bimodal Logic User Guide

## Overview

The Bimodal theory implements temporal-modal logic, combining reasoning about time and possibility. This theory allows you to express and validate formulas that involve both temporal operators (what happens at different times) and modal operators (what is possible or necessary), making it suitable for reasoning about dynamic systems and temporal necessity.

## Key Features

- **Temporal Operators**: Future (⏵) and Past (⏴) for temporal reasoning
- **Modal Operators**: Necessity (□) and Possibility (◇) for modal reasoning
- **Extensional Base**: Full support for classical propositional logic
- **World Histories**: Models represent sequences of states over time
- **Dual Dimensions**: Simultaneous reasoning about time and modality

## Available Operators

The bimodal theory provides operators for both temporal and modal reasoning:

### Extensional Operators
- **¬** (negation): Classical negation
- **∧** (conjunction): Classical conjunction
- **∨** (disjunction): Classical disjunction
- **→** (conditional): Material conditional
- **↔** (biconditional): Material biconditional

### Modal Operators
- **□** (necessity): "It is necessary that..."
- **◇** (possibility): "It is possible that..."

### Temporal Operators
- **⏵** (future): "In the future..."
- **⏴** (past): "In the past..."

### Extremal Operators
- **⊤** (top): Logical truth
- **⊥** (bottom): Logical falsehood

## Understanding Bimodal Models

### Time Points and Worlds

Bimodal models consist of:
- **Time Points**: Discrete moments (0, 1, 2, ...)
- **Worlds**: Alternative possibilities at each time point
- **World Histories**: Sequences of worlds across time

### Model Parameters

- **M**: Number of time points in the model
- **N**: Number of atomic propositions
- **World Structure**: How worlds are connected across time and modality

## Formula Examples

### Pure Temporal Reasoning

```python
# Future necessity
premises = ["□p"]
conclusions = ["⏵□p"]
settings = {"M": 3, "N": 1}

# What is necessary now will be necessary in the future
```

### Pure Modal Reasoning

```python
# Necessity and possibility
premises = ["□p"]
conclusions = ["¬◇¬p"]
settings = {"M": 1, "N": 1}

# What is necessary is not possibly false
```

### Combined Temporal-Modal

```python
# Temporal necessity
premises = ["□⏵p"]
conclusions = ["⏵□p"]
settings = {"M": 3, "N": 1}

# It is necessary that p will be true vs. it will be necessary that p is true
```

### Complex Interactions

```python
# Past and future interaction
premises = ["⏴p", "⏵q"]
conclusions = ["⏴p ∧ ⏵q"]
settings = {"M": 3, "N": 2}

# Combining past and future information
```

## Working with Examples

### Accessing Built-in Examples

```python
from model_checker.theory_lib.bimodal import get_examples, get_test_examples

# Get curated examples for exploration
examples = get_examples()
print(f"Available examples: {list(examples.keys())}")

# Get comprehensive test suite
test_examples = get_test_examples()
print(f"Test examples: {len(test_examples)} total")
```

### Running Specific Examples

```python
from model_checker import BuildExample
from model_checker.theory_lib.bimodal import get_theory, get_examples

theory = get_theory()
examples = get_examples()

# Run a specific example
if "EX_CM_1" in examples:
    example_case = examples["EX_CM_1"]
    example = BuildExample("extensional_test", theory, example_case)
    result = example.check_result()
    
    print(f"Example EX_CM_1 result: {result['model_found']}")
```

## Settings and Configuration

### Essential Settings

```python
settings = {
    "M": 3,                   # Number of time points (crucial for temporal reasoning)
    "N": 2,                   # Number of atomic propositions
    "max_time": 15,          # Solver timeout (bimodal can be complex)
    "contingent": True,      # Often useful for interesting temporal patterns
    "disjoint": False,       # Usually not needed for temporal-modal logic
}
```

### Bimodal-Specific Considerations

- **M (Time Points)**: Critical parameter - determines temporal depth
  - M=1: Pure modal logic (no temporal reasoning)
  - M=2-3: Simple temporal sequences  
  - M=4+: Complex temporal patterns (performance impact)

- **N (Propositions)**: Affects complexity exponentially
  - N=1-2: Good for exploring basic patterns
  - N=3+: Complex interactions between propositions over time

For detailed settings documentation, see [SETTINGS.md](SETTINGS.md).

## Model Iteration

Explore multiple models for bimodal examples:

```python
from model_checker.theory_lib.bimodal import iterate_example

# Create example
example = BuildExample("test", theory, example_case)

# Find multiple models
models = iterate_example(example, max_iterations=3)

print(f"Found {len(models)} different models")
for i, model in enumerate(models):
    print(f"Model {i+1}: {model.z3_model_status}")
```

## Common Use Cases

### 1. Temporal Logic Validation

```python
# Test temporal principles
example_case = [
    [],                       # No premises
    ["⏵⏵p → ⏵p"],           # Future operator transitivity
    {"M": 4, "N": 1, "expectation": True}
]
```

### 2. Modal Logic with Time

```python
# Necessity over time
example_case = [
    ["□p"],                   # p is necessary
    ["⏵□p"],                 # In the future, p will be necessary
    {"M": 3, "N": 1}
]
```

### 3. Temporal-Modal Interactions

```python
# Explore interaction between temporal and modal operators
example_case = [
    ["□⏵p"],                 # It's necessary that p will be true
    ["⏵□p"],                 # In the future, p will be necessary
    {"M": 3, "N": 1, "expectation": False}  # These are different!
]
```

### 4. Dynamic System Modeling

```python
# Model state changes over time
example_case = [
    ["p", "⏵¬p", "⏵⏵p"],   # p oscillates: true, false, true
    ["◇⏵⏵⏵p"],             # Eventually p will be true again
    {"M": 4, "N": 1}
]
```

## Advanced Topics

### World History Semantics

Bimodal models use world histories - sequences of worlds across time:

```
Time:    0    1    2
World A: w₀ → w₁ → w₂
World B: w₀ → w₁' → w₂'
```

Each history represents a possible way the world could evolve over time.

### Accessibility Relations

The theory uses two accessibility relations:
- **Temporal**: Connects time points (t₀ → t₁ → t₂)
- **Modal**: Connects possible worlds at each time point

### Evaluation Points

Formulas are evaluated at specific (world, time) pairs:
- **⏵p** at (w,t): p is true at (w,t+1)
- **□p** at (w,t): p is true at all worlds accessible from w at time t

## Tips and Best Practices

### Performance Optimization
- Start with small M and N values (M=2-3, N=1-2)
- Increase max_time for complex temporal formulas
- Use contingent=True to avoid trivial models

### Formula Construction
- Use ⏵/⏴ for temporal operators, not classical conditionals
- Remember □/◇ work within each time point
- Combine operators carefully - order matters

### Model Interpretation
- Check both temporal progression and modal alternatives
- Use iteration to explore different world histories
- Pay attention to the distinction between □⏵p and ⏵□p

### Debugging
- Start with pure temporal or pure modal formulas
- Use print_constraints=True to understand the model structure
- Compare with simpler theories to isolate temporal-modal effects

## Common Patterns

### Temporal Sequences

```python
# Simple progression
"p ∧ ⏵q ∧ ⏵⏵r"           # p now, q next, r after that

# Temporal loops
"p ∧ ⏵¬p ∧ ⏵⏵p"          # p oscillates

# Eventually patterns
"◇⏵p"                     # Eventually p will be true
```

### Modal Combinations

```python
# Necessary possibility
"□◇p"                     # It's necessary that p is possible

# Possible necessity  
"◇□p"                     # It's possible that p is necessary

# Temporal necessity
"□⏵p"                     # It's necessary that p will be true
```

### Complex Interactions

```python
# Past necessity, future possibility
"⏴□p ∧ ⏵◇q"              # p was necessary, q will be possible

# Temporal modal sequences
"□p ∧ ⏵◇¬p ∧ ⏵⏵□p"      # Necessary, then possibly not, then necessary again
```

## Theoretical Background

The bimodal theory combines:

1. **Temporal Logic**: Linear time with discrete time points
2. **Modal Logic**: Possible worlds at each time point  
3. **Truthmaker Semantics**: States verify/falsify propositions
4. **World Histories**: Branching temporal structures

This creates a rich framework for reasoning about:
- How possibilities change over time
- When necessities persist or change
- Dynamic systems with modal uncertainty

## Troubleshooting

### Common Issues

**Solver Timeouts**:
- Reduce M (time points) or N (propositions)
- Increase max_time setting
- Simplify complex temporal-modal combinations

**Unexpected Results**:
- Check the difference between □⏵p and ⏵□p
- Remember that time is linear but worlds branch
- Use small examples to understand operator interactions

**Performance Issues**:
- Bimodal logic is computationally intensive
- State space grows as O(2^(M×N))
- Consider using simpler theories for initial exploration

### Getting Help

- Review the example files for usage patterns
- Check [ARCHITECTURE.md](ARCHITECTURE.md) for technical details
- Use model iteration to explore different interpretations
- Compare with pure temporal or modal theories

## Integration with Other Theories

Compare bimodal results with other approaches:

```python
# Example comparison with other theories
from model_checker.theory_lib.bimodal.examples import semantic_theories

for theory_name, theory_config in semantic_theories.items():
    example = BuildExample(f"test_{theory_name}", theory_config, example_case)
    result = example.check_result()
    print(f"{theory_name}: {result['model_found']}")
```

## Further Reading

- **Temporal Logic**: Understanding time in logic
- **Modal Logic**: Necessity and possibility
- **Bimodal Logic Theory**: Combining temporal and modal reasoning
- **World History Semantics**: Branching time structures

---

**Navigation**: [README](../README.md) | [Architecture](ARCHITECTURE.md) | [Settings](SETTINGS.md) | [Operators](OPERATORS.md)