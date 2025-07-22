# Model Iteration System

The ModelChecker's iteration system provides a framework for systematically finding multiple semantically distinct models for logical examples. This documentation covers the architecture, usage, and extension points of the iteration system.

## Overview

The iteration system allows you to:

1. Find multiple semantically distinct models for a logical formula
2. Generate constraints that ensure each new model differs from previous ones
3. Check for model isomorphism to avoid structural duplicates
4. Handle edge cases where no more distinct models exist
5. Visualize differences between models for analysis

This functionality is valuable for:

- Exploring the space of possible models for a formula
- Analyzing the semantic range of a theory
- Testing the robustness of logical principles
- Demonstrating semantic diversity in countermodels
- Understanding the limits of model variation

## Architecture

The iteration system follows a modular architecture with clear separation between theory-agnostic and theory-specific components:

```
BaseModelIterator (in iterate/core.py)
├── DefaultModelIterator (in theory_lib/default/iterate.py)
├── BimodalModelIterator (in theory_lib/bimodal/iterate.py)
├── ExclusionModelIterator (in theory_lib/exclusion/iterate.py)
├── ImpositionModelIterator (in theory_lib/imposition/iterate.py)
└── LogosModelIterator (in theory_lib/logos/iterate.py)
```

### Key Components

1. **BaseModelIterator** (`iterate/core.py`)
   - Abstract base class providing the theory-agnostic iteration framework
   - Handles solver management, model building, and iteration control
   - Manages invalid model detection and consecutive failure limits
   - Provides isomorphism detection using NetworkX when available
   - Collects and stores debug messages for later display

2. **Theory-Specific Iterators** (`theory_lib/<theory>/iterate.py`)
   - Extend BaseModelIterator with theory-specific implementations
   - Implement constraint generation based on theory's semantic primitives
   - Provide theory-specific model comparison and difference detection
   - Define visualization methods for model differences

3. **Supporting Infrastructure**
   - `iterate/graph_utils.py`: Graph-based model representation for isomorphism checking
   - Theory-specific `iterate_example` functions for simplified usage
   - Integration with the builder system for seamless iteration support

## Usage

### Basic Usage in Examples

When defining examples in a theory's `examples.py` file, enable iteration by setting the `iterate` parameter:

```python
# In theory_lib/logos/subtheories/counterfactual/examples.py

CF_CM_1_settings = {
    'N': 4,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 3,  # Request 3 models
    'expectation': True,
}

CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]
```

### Programmatic Usage

Each theory provides its own `iterate_example` function:

```python
from model_checker.theory_lib.logos import iterate_example
from model_checker import BuildExample, get_theory

# Create an example with a valid model
theory = get_theory(['extensional'])
example = BuildExample("example_name", theory)

# Find multiple models (up to 5)
model_structures = iterate_example(example, max_iterations=5)

# Process the results
for i, structure in enumerate(model_structures, start=1):
    print(f"=== Model {i} ===")
    structure.print_model()
```

### Iteration Process

When iteration is enabled, the following process occurs:

1. The first model is found and displayed normally
2. An iterator is created using the theory-specific implementation
3. The iterator searches for additional models by:
   - Adding constraints to differ from previous models
   - Checking new models for validity (at least one possible world)
   - Checking for isomorphism with previous models
   - Applying stronger constraints if stuck in isomorphic models
4. Each distinct model is displayed with differences from the previous
5. Debug messages are collected and shown after all models
6. A summary shows how many distinct models were found

### Handling Edge Cases

The iterator handles several edge cases gracefully:

- **Invalid Models**: Models with no possible worlds are automatically excluded
- **Isomorphic Models**: Structurally identical models are detected and skipped
- **Insufficient Models**: If fewer than requested models exist, iteration stops early
- **Consecutive Failures**: After 5 consecutive invalid models, iteration stops
- **Escape Attempts**: After 3 failed attempts to escape isomorphism, iteration stops

## Abstract Methods

Theory-specific iterators must implement these methods from BaseModelIterator:

### 1. _calculate_differences(new_structure, previous_structure)

Calculate semantic differences between models based on theory-specific primitives:

```python
def _calculate_differences(self, new_structure, previous_structure):
    """Calculate differences between two model structures.
    
    For logos theory, this focuses on:
    - Changes in which states are worlds
    - Changes in verification and falsification of sentence letters
    - Changes in part-whole relationships
    - Changes in modal accessibility relations
    
    Returns:
        dict: Structured differences between the models
    """
```

### 2. _create_difference_constraint(previous_models)

Create Z3 constraints ensuring the next model differs from all previous ones:

```python
def _create_difference_constraint(self, previous_models):
    """Create a Z3 constraint requiring difference from all previous models.
    
    For logos theory, we create constraints that require at least one of:
    - Different verification/falsification for some sentence letter
    - Different world structure
    - Different possible states
    
    Returns:
        z3.ExprRef: Z3 constraint expression
    """
```

### 3. _create_non_isomorphic_constraint(z3_model)

Create constraints to avoid isomorphic models:

```python
def _create_non_isomorphic_constraint(self, z3_model):
    """Create a constraint that forces structural differences.
    
    For logos theory, we focus on breaking symmetries in the state space
    by requiring specific structural differences.
    
    Returns:
        z3.ExprRef: Z3 constraint or None if creation fails
    """
```

### 4. _create_stronger_constraint(isomorphic_model)

Create aggressive constraints when stuck in isomorphic models:

```python
def _create_stronger_constraint(self, isomorphic_model):
    """Create stronger constraints after multiple isomorphism failures.
    
    This is called when we've found too many isomorphic models in a row.
    For logos theory, we create more aggressive constraints that force
    significant structural differences.
    
    Returns:
        z3.ExprRef: Z3 constraint or None if creation fails
    """
```

## Implementing a New Theory Iterator

To add iteration support to a new theory:

1. **Create the iterator class** in `theory_lib/<theory>/iterate.py`:

```python
from model_checker.iterate.core import BaseModelIterator
import z3

class MyTheoryModelIterator(BaseModelIterator):
    """Model iterator for my theory."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Initialize differences structure
        differences = {
            "worlds": {"added": [], "removed": []},
            "theory_specific": {}
        }
        
        # Calculate theory-specific differences
        # ...
        
        return differences
    
    def _create_difference_constraint(self, previous_models):
        semantics = self.build_example.model_structure.semantics
        
        # Create constraints for each previous model
        model_constraints = []
        for prev_model in previous_models:
            differences = []
            
            # Add theory-specific difference requirements
            # ...
            
            model_constraints.append(z3.Or(*differences))
        
        return z3.And(*model_constraints)
    
    def _create_non_isomorphic_constraint(self, z3_model):
        try:
            semantics = self.build_example.model_structure.semantics
            constraints = []
            
            # Add structural difference constraints
            # ...
            
            return z3.Or(*constraints) if constraints else None
        except Exception:
            return None
    
    def _create_stronger_constraint(self, isomorphic_model):
        try:
            # Create very strong constraints
            # ...
            
            return constraint
        except Exception:
            return None
```

2. **Add the convenience function**:

```python
def iterate_example(example, max_iterations=None):
    """Iterate a my_theory example to find multiple models."""
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    iterator = MyTheoryModelIterator(example)
    models = iterator.iterate()
    
    # Store iterator for debug message access
    example._iterator = iterator
    
    return models
```

3. **Export from `__init__.py`**:

```python
from .iterate import MyTheoryModelIterator, iterate_example

__all__ = [
    # ... existing exports ...
    "MyTheoryModelIterator",
    "iterate_example"
]
```

## Debug Messages and Progress Tracking

The iteration system collects debug messages during execution:

- Messages are stored in `iterator.debug_messages`
- Only `[ITERATION]` prefixed messages are shown to users
- Messages appear after all models are displayed
- Progress includes:
  - Which model is being searched for
  - Invalid models found and excluded
  - Isomorphic models detected
  - Escape attempts and stronger constraints
  - Final status (success or reason for stopping)

## Configuration Options

Control iteration behavior through settings:

```python
settings = {
    # Basic iteration
    'iterate': 5,                    # Max models to find
    
    # Advanced options
    'max_invalid_attempts': 5,       # Max consecutive invalid models
    'iteration_attempts': 5,         # Max isomorphic models before stronger constraints
    'escape_attempts': 3,            # Max attempts to escape isomorphism
    'iteration_timeout': 1.0,        # Timeout for isomorphism check (seconds)
    'iteration_solver_timeout': 5000 # Solver timeout per iteration (milliseconds)
}
```

## Integration with Process Example

The builder system automatically handles iteration when the `iterate` setting is present:

1. Prints "MODEL 1/N" header for the first model
2. Finds additional models using theory-specific iterator
3. Displays differences between consecutive models
4. Shows debug messages after all models
5. Prints summary "Found X/N distinct models"

## Best Practices

1. **Start Small**: Begin with `iterate: 2` or `3` to test iteration
2. **Reasonable Limits**: Most examples have 1-5 distinct models
3. **Handle Failures**: Expect that requested models may not exist
4. **Theory Specifics**: Focus constraints on theory's key semantic primitives
5. **Performance**: Add timeouts for complex theories
6. **Debug Output**: Use debug messages to understand iteration behavior

## Common Issues and Solutions

### "Too many consecutive invalid models"
- The constraints are generating models with no possible worlds
- Solution: Review constraint generation logic

### "Exhausted escape attempts"
- The iterator is stuck finding isomorphic models
- Solution: Strengthen the non-isomorphic constraints

### Performance Issues
- Large state spaces or complex constraints slow iteration
- Solution: Reduce N, add timeouts, or optimize constraints

### No Additional Models Found
- Only one model may satisfy all constraints
- This is often expected behavior, not an error