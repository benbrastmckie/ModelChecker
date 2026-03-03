# Theory Library Usage Guide

## Overview

The ModelChecker theory library provides a comprehensive framework for implementing and evaluating hyperintensional logical theories. This guide covers the architecture and usage patterns for the available theories.

## Architecture Overview

The theory library follows a modular architecture:

```
theory_lib/
├── types.py                 # Type definitions and protocols
├── errors.py               # Standardized error hierarchy
├── logos/                  # Base hyperintensional framework
│   ├── semantic.py         # LogosSemantics foundation
│   ├── protocols.py        # Protocol definitions
│   └── subtheories/        # Modular subtheory system
└── bimodal/               # Bimodal semantics for counterfactuals
    └── semantic.py         # BimodalSemantics
```

## Available Theories

### Logos Theory

The primary truthmaker semantics implementation with a modular subtheory system.

**Features:**
- Bilateral truthmaker semantics
- Modular operator architecture through subtheories
- Extensional and intensional logic support

### Bimodal Theory

Experimental bimodal semantics for counterfactuals.

**Features:**
- Two modal dimensions
- Counterfactual reasoning support

## Getting Started

### Basic Setup

All theories share a common settings pattern:

```python
from model_checker.theory_lib.logos import get_theory

# Get logos theory with extensional operators
theory = get_theory(['extensional'])

# Common settings structure
basic_settings = {
    'N': 3,                    # Number of bits for state representation
    'max_time': 10,           # Z3 solver timeout in seconds
    'iterate': 1,             # Number of iterations for model finding
    'contingent': False,      # Enable contingency constraints
    'non_empty': False,       # Require non-empty states
    'non_null': False,        # Require non-null states
    'disjoint': False,        # Require disjoint state constraints
}
```

### Error Handling

The library uses a standardized error hierarchy with contextual information:

```python
from model_checker.theory_lib.errors import (
    TheoryError,
    TheoryLoadError,
    TheoryNotFoundError
)

try:
    # Operations that might fail
    theory = get_theory(['invalid_subtheory'])
except TheoryError as e:
    print(f"Theory error: {e}")
    print(f"Context: {e.context}")
    print(f"Suggestion: {e.suggestion}")
```

## Logos Theory

### Core Concepts

The logos theory implements bilateral truthmaker semantics where propositions have both verification and falsification conditions. States can verify propositions (make them true) or falsify them (make them false).

### Basic Usage

```python
from model_checker.theory_lib.logos import get_theory
from model_checker.theory_lib.logos.semantic import LogosSemantics

# Get theory with specific subtheories
theory = get_theory(['extensional'])

# Initialize semantics with custom settings
settings = {
    'N': 3,
    'max_time': 15,
    'iterate': 2
}

# Create semantics instance
semantics = LogosSemantics(settings)
```

### Subtheory System

Logos uses a modular subtheory system to compose operators:

```python
from model_checker.theory_lib.logos import get_theory

# Available subtheories include:
# - extensional: Basic propositional operators
# - intensional: Modal operators (Box, Diamond)

# Combine subtheories
theory = get_theory(['extensional', 'intensional'])

# Access theory components
semantics_class = theory['semantics']
operators = theory['operators']
proposition_class = theory['proposition']
model_class = theory['model']
```

### Working with States

```python
import z3

# Create semantics
semantics = LogosSemantics({'N': 3})

# State operations
state1 = z3.BitVecVal(1, 3)
state2 = z3.BitVecVal(2, 3)

# Check compatibility
compatibility = semantics.compatible(state1, state2)

# Compute fusion
fusion_result = semantics.fusion(state1, state2)

# Check if state is possible
is_possible = semantics.possible(state1)

# Check if state is a world
is_world = semantics.is_world(state1)
```

## Bimodal Theory

### Core Concepts

The bimodal theory implements semantics with two modal dimensions, supporting counterfactual reasoning.

### Basic Usage

```python
from model_checker.theory_lib.bimodal import get_theory

# Get bimodal theory
theory = get_theory()

# Access components
semantics_class = theory['semantics']
operators = theory['operators']
```

## Performance Optimization

### Best Practices

1. **Reuse semantics instances** - Initialization is expensive
2. **Use appropriate N values** - Smaller N means faster solving
3. **Set reasonable timeouts** - Balance completeness vs. performance

```python
# Good: Reuse semantics
semantics = LogosSemantics(settings)
for formula in formulas:
    # ... process formula with same semantics
    pass
```

### Performance Tips

```python
# Use smaller N for faster solving
settings['N'] = 3  # Instead of 4 or higher

# Set reasonable timeout
settings['max_time'] = 10
```

## Testing and Validation

### Unit Testing

```bash
# Run all theory tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/ -v

# Run specific theory tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v

# Run error handling tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v
```

### Validation Examples

```python
# Validate theory setup
try:
    from model_checker.theory_lib.logos import get_theory
    theory = get_theory(['extensional'])
    print("Logos theory loaded successfully")

except Exception as e:
    print(f"Setup failed: {e}")
```

## Troubleshooting

### Common Issues

1. **Z3 Timeout Errors**
   ```python
   # Increase timeout or reduce problem size
   settings['max_time'] = 30  # Increase timeout
   settings['N'] = 2         # Reduce state space
   ```

2. **Memory Issues with Large N**
   ```python
   # Use smaller N values
   settings['N'] = 3  # Instead of 4 or higher
   ```

3. **Import Errors**
   ```python
   # Use absolute imports
   from model_checker.theory_lib.logos import get_theory
   ```

### Debugging Tips

1. **Enable detailed error context**
   ```python
   try:
       operation()
   except TheoryError as e:
       print(f"Error: {e}")
       print(f"Context: {e.context}")
       print(f"Suggestion: {e.suggestion}")
   ```

2. **Check theory initialization**
   ```python
   # Verify settings are complete
   required_keys = ['N', 'max_time', 'iterate']
   missing = [k for k in required_keys if k not in settings]
   if missing:
       print(f"Missing required settings: {missing}")
   ```

## References

- Truthmaker semantics literature
- Z3 Theorem Prover documentation
- ModelChecker framework documentation
