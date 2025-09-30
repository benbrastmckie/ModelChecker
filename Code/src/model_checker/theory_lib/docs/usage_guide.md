# Theory Library Usage Guide

## Overview

The ModelChecker theory library provides a comprehensive framework for implementing and evaluating hyperintensional logical theories. This guide covers the refactored architecture and usage patterns for all three major theories.

## Architecture Overview

The refactored theory library follows a modular architecture:

```
theory_lib/
├── types.py                 # Type definitions and protocols
├── errors.py               # Standardized error hierarchy
├── exclusion/              # Witness-based negation semantics
│   └── semantic/
│       ├── core.py         # WitnessSemantics main class
│       ├── model.py        # WitnessAwareModel structure
│       ├── registry.py     # WitnessRegistry for predicates
│       └── constraints.py  # WitnessConstraintGenerator
├── imposition/             # Kit Fine's imposition semantics
│   └── semantic/
│       ├── core.py         # ImpositionSemantics main class
│       ├── model.py        # ImpositionModelStructure
│       └── helpers.py      # Utility functions
└── logos/                  # Base hyperintensional framework
    ├── semantic.py         # LogosSemantics foundation
    └── protocols.py        # Protocol definitions
```

## Getting Started

### Basic Setup

All theories share a common settings pattern:

```python
from model_checker.theory_lib.exclusion.semantic import WitnessSemantics
from model_checker.theory_lib.imposition.semantic import ImpositionSemantics

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

# Create semantics instances
witness_sem = WitnessSemantics(basic_settings)
imposition_sem = ImpositionSemantics(basic_settings)
```

### Error Handling

The library uses a standardized error hierarchy with contextual information:

```python
from model_checker.theory_lib.errors import (
    WitnessSemanticError,
    ImpositionSemanticError,
    WitnessRegistryError
)

try:
    # Operations that might fail
    h_pred, y_pred = witness_sem.witness_registry.register_witness_predicates("")
except WitnessRegistryError as e:
    print(f"Registry error: {e}")
    print(f"Context: {e.context}")
    print(f"Suggestion: {e.suggestion}")
```

## Exclusion Theory (Witness Semantics)

### Core Concepts

The exclusion theory implements witness-based negation where ¬φ is true at a state s if:
1. s verifies the negation of φ
2. There exists a witness state w that makes φ true
3. s excludes w

### Basic Usage

```python
from model_checker.theory_lib.exclusion.semantic import WitnessSemantics

# Initialize with custom settings
settings = {
    'N': 3,
    'possible': False,        # Exclusion-specific: possibility constraints
    'fusion_closure': False,  # Closure under fusion operations
    'max_time': 15,
    'iterate': 2
}

semantics = WitnessSemantics(settings)

# Register witness predicates for a formula
formula_name = "p_and_q"
h_pred, y_pred = semantics.witness_registry.register_witness_predicates(formula_name)

# Create evaluation point
eval_point = {"world": semantics.main_world}

# Generate constraints for witness semantics (requires formula AST)
# constraints = semantics.constraint_generator.generate_witness_constraints(
#     formula_name, formula_ast, h_pred, y_pred, eval_point
# )
```

### Advanced Features

```python
# Performance optimization: Cached predicate lookups
# First call registers and caches
h1, y1 = semantics.witness_registry.register_witness_predicates("formula1")

# Subsequent calls use cache for faster access
h1_cached, y1_cached = semantics.witness_registry.get_witness_predicates("formula1")

# Check if predicates are cached
all_preds = semantics.witness_registry.get_all_predicates()
print(f"Registered predicates: {list(all_preds.keys())}")

# Clear registry when needed
semantics.witness_registry.clear()
```

### Integration with Logos Operations

```python
import z3

# Witness semantics inherits all logos operations
state1 = z3.BitVecVal(1, 3)
state2 = z3.BitVecVal(2, 3)

# Use inherited operations
compatibility = semantics.compatible(state1, state2)
fusion_result = semantics.fusion(state1, state2)
is_possible = semantics.possible(state1)
is_world = semantics.is_world(state1)

# Exclusion-specific operations
conflicts = semantics.conflicts(state1, state2)
coheres = semantics.coheres(state1, state2)
compossible = semantics.compossible(state1, state2)
necessary = semantics.necessary(state1)
```

## Imposition Theory (Fine's Semantics)

### Core Concepts

The imposition theory implements Kit Fine's counterfactual semantics where counterfactuals are analyzed through an imposition operation that maps states and worlds to alternative outcome worlds.

### Basic Usage

```python
from model_checker.theory_lib.imposition.semantic import ImpositionSemantics

# Initialize with imposition-specific settings
settings = {
    'N': 3,
    'derive_imposition': False,  # Imposition-specific setting
    'max_time': 20,
    'iterate': 1
}

semantics = ImpositionSemantics(settings)

# Main imposition operation
state_y = z3.BitVecVal(1, 3)     # State being imposed
world_w = z3.BitVecVal(2, 3)     # World being imposed on
outcome_u = z3.BitVecVal(3, 3)   # Potential outcome world

# Check if u is an alternative world resulting from imposing y on w
is_alternative = semantics.alt_imposition(state_y, world_w, outcome_u)
```

### Working with Outcome Worlds

```python
# Calculate outcome worlds for a set of verifiers
verifiers = {1, 2, 4}  # States that verify some condition
eval_point = {"world": semantics.main_world}

# Create a model structure (empty constraints for basic example)
model_structure = semantics.create_model_structure([])
outcomes = semantics.calculate_outcome_worlds(verifiers, eval_point, model_structure)

print(f"Outcome worlds: {outcomes}")
```

### Helper Functions

```python
from model_checker.theory_lib.imposition.semantic.helpers import (
    safe_bitvec_as_long,
    format_imposition_relation,
    group_impositions_by_world
)

# Format relations for display
formatted = format_imposition_relation(state_y, world_w, outcome_u)
print(formatted)  # Output: "s1 ->_2 s3"

# Safe conversion from Z3 bitvectors
state_val = safe_bitvec_as_long(state_y)
print(f"State value: {state_val}")

# Group relations by world
relations = [
    (z3.BitVecVal(0, 3), z3.BitVecVal(1, 3), z3.BitVecVal(2, 3)),
    (z3.BitVecVal(1, 3), z3.BitVecVal(1, 3), z3.BitVecVal(3, 3))
]
grouped = group_impositions_by_world(relations)
for world, state_outcome_pairs in grouped.items():
    print(f"World {safe_bitvec_as_long(world)}: {len(state_outcome_pairs)} relations")
```

## Performance Optimization

### Caching Strategies

Both theories implement performance optimizations:

```python
# Exclusion theory caching
witness_sem = WitnessSemantics(settings)

# Predicate lookups are automatically cached
h1, y1 = witness_sem.witness_registry.register_witness_predicates("formula1")
# Subsequent calls use cache
h1_fast, y1_fast = witness_sem.witness_registry.get_witness_predicates("formula1")

# Imposition theory caching
imposition_sem = ImpositionSemantics(settings)

# Model structure evaluations are cached
# Repeated calls to _evaluate_z3_boolean use cached results
model_constraints = [z3.BoolVal(True)]
model_structure = imposition_sem.create_model_structure(model_constraints)
```

### Performance Best Practices

1. **Reuse semantics instances** - Initialization is expensive
2. **Cache predicate registrations** - Registry lookups are optimized
3. **Use appropriate N values** - Smaller N means faster solving
4. **Set reasonable timeouts** - Balance completeness vs. performance
5. **Clear caches when memory is constrained**

```python
# Good: Reuse semantics
semantics = WitnessSemantics(settings)
for formula in formulas:
    h, y = semantics.witness_registry.register_witness_predicates(formula)
    # ... use predicates

# Clear cache if needed
semantics.witness_registry.clear()
```

## Integration Patterns

### Cross-Theory Compatibility

All theories inherit from `LogosSemantics` and can be used together:

```python
from model_checker.theory_lib.exclusion.semantic import WitnessSemantics
from model_checker.theory_lib.imposition.semantic import ImpositionSemantics

# Both theories share the same base operations
witness_sem = WitnessSemantics(settings)
imposition_sem = ImpositionSemantics(settings)

# Common operations work on both
state = z3.BitVecVal(1, 3)
witness_possible = witness_sem.possible(state)
imposition_possible = imposition_sem.possible(state)

# Theory-specific operations
h_pred, y_pred = witness_sem.witness_registry.register_witness_predicates("p")
alt_world = imposition_sem.alt_imposition(state, state, state)
```

### Type Safety

The library provides comprehensive type annotations:

```python
from model_checker.theory_lib.types import (
    WitnessSemantics as WitnessSemanticsProtocol,
    ImpositionSemantics as ImpositionSemanticsProtocol,
    StateId,
    OperatorDict
)

def process_witness_semantics(sem: WitnessSemanticsProtocol) -> StateId:
    """Function that works with any witness semantics implementation."""
    # Type checker ensures sem has required methods
    return sem.witness_registry.register_witness_predicates("test")

def process_imposition_semantics(sem: ImpositionSemanticsProtocol) -> z3.BoolRef:
    """Function that works with any imposition semantics implementation."""
    state = z3.BitVecVal(1, sem.N)
    return sem.alt_imposition(state, state, state)
```

## Testing and Validation

### Unit Testing

The library includes comprehensive unit tests:

```bash
# Run all theory tests
pytest Code/src/model_checker/theory_lib/tests/ -v

# Run specific theory tests
pytest Code/src/model_checker/theory_lib/tests/unit/exclusion/ -v
pytest Code/src/model_checker/theory_lib/tests/unit/imposition/ -v

# Run error handling tests
pytest Code/src/model_checker/theory_lib/tests/unit/test_error_handling.py -v

# Run integration tests
pytest Code/src/model_checker/theory_lib/tests/integration/ -v
```

### Validation Examples

```python
# Validate theory setup
try:
    semantics = WitnessSemantics(settings)
    # Test basic operations
    state = z3.BitVecVal(0, semantics.N)
    result = semantics.possible(state)
    print("WitnessSemantics initialized successfully")

except Exception as e:
    print(f"Setup failed: {e}")

# Validate cross-theory compatibility
witness_sem = WitnessSemantics(settings)
imposition_sem = ImpositionSemantics(settings)

# Both should have compatible state representations
assert witness_sem.N == imposition_sem.N
print("Cross-theory compatibility validated")
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
   # Clear caches regularly
   semantics.witness_registry.clear()

   # Use smaller N values
   settings['N'] = 3  # Instead of 4 or higher
   ```

3. **Import Errors**
   ```python
   # Use absolute imports
   from model_checker.theory_lib.exclusion.semantic.core import WitnessSemantics

   # Or use wrapper imports for backward compatibility
   from model_checker.theory_lib.exclusion.semantic import WitnessSemantics
   ```

4. **Type Checking Issues**
   ```python
   # Ensure all type annotations are imported
   from typing import Dict, Any, List, Optional
   from model_checker.theory_lib.types import StateId
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

3. **Validate Z3 expressions**
   ```python
   import z3

   # Check if expression is valid
   expr = semantics.possible(z3.BitVecVal(1, 3))
   print(f"Expression type: {type(expr)}")
   print(f"Expression: {expr}")
   ```

## Advanced Topics

### Custom Theory Development

To create a new theory following the established patterns:

1. **Inherit from LogosSemantics**
2. **Define theory-specific operations**
3. **Add comprehensive type annotations**
4. **Implement error handling with custom exceptions**
5. **Create performance optimizations**
6. **Add comprehensive documentation and examples**

### Integration with External Tools

The theory library can be integrated with:

- **Custom Z3 solvers** - All theories use standard Z3 expressions
- **External logical frameworks** - Through the protocol-based type system
- **Analysis tools** - Via the standardized model structure API
- **Testing frameworks** - Through the comprehensive test suite

## References

- Kit Fine. "The Logic of Essence" - Foundation for imposition semantics
- Brast-McKie. "Witness-based Negation" - Foundation for exclusion semantics
- Z3 Theorem Prover documentation
- ModelChecker framework documentation