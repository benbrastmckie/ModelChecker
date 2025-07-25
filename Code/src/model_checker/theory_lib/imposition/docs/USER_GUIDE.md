# Imposition Theory User Guide

## Overview

The Imposition theory implements Fine's semantics for counterfactuals through the imposition operation. This theory provides a sophisticated framework for reasoning about counterfactual conditionals and possibility claims, grounded in the formal semantics developed by Kit Fine.

## Key Features

- **Imposition Operator (↪)**: Models counterfactual conditionals with Fine's imposition semantics
- **Could Operator (⟂)**: Represents possibility claims within the imposition framework
- **Extensional Base**: Full support for classical propositional logic operators
- **Logos Integration**: Reuses Logos theory components for proposition and model structure

## Quick Start

### Basic Usage

```python
from model_checker.theory_lib.imposition import get_theory

# Load the imposition theory
theory = get_theory()

# Access components
semantics = theory['semantics']
operators = theory['operators']
```

### Using with BuildExample

```python
from model_checker import BuildExample
from model_checker.theory_lib.imposition import get_theory

# Load theory
theory = get_theory()

# Create an example with counterfactual reasoning
example_case = [
    ["A"],                    # Premises
    ["A ↪ B"],               # Conclusions  
    {"N": 3, "max_time": 10} # Settings
]

# Build and check the example
example = BuildExample("counterfactual_test", theory, example_case)
result = example.check_result()

print(f"Valid: {result['model_found']}")
```

## Available Operators

The imposition theory provides a comprehensive set of logical operators:

### Extensional Operators
- **¬** (negation): Classical negation
- **∧** (conjunction): Classical conjunction  
- **∨** (disjunction): Classical disjunction
- **→** (conditional): Material conditional
- **↔** (biconditional): Material biconditional

### Imposition Operators
- **↪** (imposition): Counterfactual conditional with Fine's imposition semantics
- **⟂** (could): Possibility operator for "could" statements

### Extremal Operators  
- **⊤** (top): Logical truth
- **⊥** (bottom): Logical falsehood

## Formula Examples

### Counterfactual Reasoning

```python
# Test counterfactual antecedent strengthening
premises = []
conclusions = ["(A ↪ C) → ((A ∧ B) ↪ C)"]
settings = {"N": 3, "expectation": False}  # Expect countermodel

# This should be invalid - demonstrates failure of antecedent strengthening
```

### Possibility Claims

```python
# Test possibility with imposition
premises = ["A ↪ B"]  
conclusions = ["⟂ B"]
settings = {"N": 2}

# If A counterfactually implies B, then B is possible
```

### Complex Counterfactuals

```python
# Nested counterfactuals
premises = ["A ↪ (B ↪ C)"]
conclusions = ["(A ∧ B) ↪ C"]
settings = {"N": 4, "max_time": 15}

# Test exportation in counterfactual logic
```

## Working with Examples

### Accessing Built-in Examples

```python
from model_checker.theory_lib.imposition import get_examples, get_test_examples

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
from model_checker.theory_lib.imposition import get_theory, get_examples

theory = get_theory()
examples = get_examples()

# Run a specific example
if "IM_CM_1" in examples:
    example_case = examples["IM_CM_1"]
    example = BuildExample("antecedent_strengthening", theory, example_case)
    result = example.check_result()
    
    print(f"Example IM_CM_1 result: {result['model_found']}")
```

## Settings and Configuration

### Common Settings

```python
settings = {
    "N": 3,                    # Number of atomic propositions
    "max_time": 10,           # Solver timeout in seconds
    "contingent": False,      # Require contingent propositions
    "disjoint": False,        # Require disjoint proposition content
    "non_empty": True,        # Require non-empty verifier/falsifier sets
}
```

### Theory-Specific Considerations

The imposition theory works well with:
- **N=3-5**: Good balance of expressiveness and performance
- **max_time=10-30**: Counterfactual reasoning can be complex
- **contingent=False**: Imposition semantics handles non-contingent cases naturally

For detailed settings documentation, see [SETTINGS.md](SETTINGS.md).

## Model Iteration

Find multiple models for imposition examples:

```python
from model_checker.theory_lib.imposition import iterate_example

# Create example
example = BuildExample("test", theory, example_case)

# Find multiple models
models = iterate_example(example, max_iterations=3)

print(f"Found {len(models)} different models")
for i, model in enumerate(models):
    print(f"Model {i+1}: {model.z3_model_status}")
```

## Integration with Other Theories

The imposition theory can be compared with other theories:

```python
# Compare imposition with logos theory
from model_checker.theory_lib.imposition.examples import semantic_theories

theories = semantic_theories
for theory_name, theory_config in theories.items():
    example = BuildExample(f"test_{theory_name}", theory_config, example_case)
    result = example.check_result()
    print(f"{theory_name}: {result['model_found']}")
```

## Common Use Cases

### 1. Testing Counterfactual Validity

```python
# Test if a counterfactual principle is valid
example_case = [
    [],                           # No premises
    ["(A ↪ B) → (¬B ↪ ¬A)"],    # Contraposition for counterfactuals
    {"N": 3, "expectation": True} # Expect validity
]
```

### 2. Finding Counterexamples

```python
# Look for counterexamples to invalid principles
example_case = [
    [],
    ["(A ↪ C) → ((A ∧ B) ↪ C)"],  # Antecedent strengthening (invalid)
    {"N": 3, "expectation": False}  # Expect countermodel
]
```

### 3. Exploring Possibility

```python
# Explore relationship between counterfactuals and possibility
example_case = [
    ["A ↪ B", "¬⟂ B"],          # Counterfactual but not possible
    ["⟂ ¬A"],                   # Therefore A is not necessary
    {"N": 2}
]
```

## Tips and Best Practices

### Performance Optimization
- Start with small N values (2-3) for initial testing
- Increase max_time for complex counterfactual formulas
- Use non_empty=True to avoid degenerate models

### Formula Construction
- Use ↪ for counterfactual conditionals, not →
- Remember that ⟂ represents "could" or possibility
- Combine with classical operators for complex reasoning

### Debugging
- Use print_constraints=True to see Z3 constraints
- Check model_found to distinguish validity from invalidity
- Use iterate functionality to explore multiple models

## Theoretical Background

The imposition theory implements Fine's semantics where:

1. **States**: Represent possible ways things could be
2. **Imposition**: A ↪ B holds when imposing A on a state leads to B
3. **Possibility**: ⟂ A holds when A is possible in some accessible state
4. **Verification**: Propositions are verified/falsified by states according to Fine's rules

For technical details, see:
- [ARCHITECTURE.md](ARCHITECTURE.md) - Implementation details
- [SETTINGS.md](SETTINGS.md) - Configuration options
- Fine, K. (2012). "Counterfactuals without Possible Worlds"

## Troubleshooting

### Common Issues

**Solver Timeouts**:
- Increase max_time setting
- Reduce N (number of propositions)
- Simplify complex nested counterfactuals

**Unexpected Results**:
- Check that you're using ↪ for counterfactuals, not →
- Remember counterfactual logic differs from classical logic
- Use iterate_example to explore alternative models

**Performance Issues**:
- Counterfactual reasoning is computationally intensive
- Start with simple examples and build complexity gradually
- Consider theory comparison to verify results

### Getting Help

- Check the README.md for basic information
- Review example files for usage patterns
- Compare with other theories to understand differences
- Use the iteration functionality to explore model space

---

**Navigation**: [README](../README.md) | [Architecture](ARCHITECTURE.md) | [Settings](SETTINGS.md) | [Operators](OPERATORS.md)