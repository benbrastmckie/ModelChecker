# Model Iteration System

The ModelChecker's iteration system provides a framework for systematically finding multiple semantically distinct models for logical examples. This documentation covers the architecture, usage, and extension points of the iteration system.

## Overview

The iteration system allows you to:

1. Find multiple semantically distinct models for a logical formula
2. Generate constraints that ensure model distinctness
3. Check for model isomorphism to avoid structural duplicates
4. Visualize differences between models for analysis

This functionality is valuable for applications such as:

- Exploring the space of possible models for a formula
- Analyzing the semantic range of a theory
- Testing the robustness of logical principles
- Demonstrating semantic diversity in countermodels

## Architecture

The iteration system follows a modular architecture with a clear separation between theory-agnostic and theory-specific components:

```
BaseModelIterator (in iterate/core.py)
├── DefaultModelIterator (in theory_lib/default/iterate.py)
├── BimodalModelIterator (in theory_lib/bimodal/iterate.py)
├── ExclusionModelIterator (in theory_lib/exclusion/iterate.py)
└── ImpositionModelIterator (in theory_lib/imposition/iterate.py)
```

### Key Components

1. **BaseModelIterator** (`iterate/core.py`)
   - Abstract base class that provides the theory-agnostic iteration framework
   - Defines abstract methods that theory-specific implementations must override
   - Handles common functionality like model building, solver management, and iteration control
   - Provides methods for diagnostic tracking and history management

2. **Theory-Specific Iterators** (`theory_lib/<theory>/iterate.py`)
   - Extend BaseModelIterator with theory-specific implementations
   - Implement concrete methods for constraint generation and difference detection
   - Provide theory-specific model comparison and visualization
   - Define which semantic primitives are worth comparing when generating different models

3. **Core Utilities**
   - `iterate/graph_utils.py`: Graph-based model representation for isomorphism checking
   - Theory-specific `iterate_example` functions for simplified usage

## Usage

### Basic Usage in Examples

Each theory provides its own `iterate_example` function in its module that simplifies the iteration process:

```python
from model_checker.theory_lib.default import iterate_example
from model_checker import BuildExample, get_theory

# Create an example with a valid model
theory = get_theory("default")
example = BuildExample("example_name", theory)
example.check_formula("p | ~p")  # Ensure a model has been found

# Find multiple models (up to 5)
model_structures = iterate_example(example, max_iterations=5)

# Print found models
for i, structure in enumerate(model_structures, start=1):
    print(f"=== Model {i} ===")
    structure.print_model()
    print()
```

### Usage in Theory Examples

When setting up theory examples in `examples.py`, you can enable iteration by setting the `iterate` parameter:

```python
# In theory_lib/default/examples.py

example_settings = {
    'N': 3,
    'max_time': 1,
    'iterate': 5,  # Find up to 5 distinct models
}

my_example = [
    ['premise1', 'premise2'],  # Premises
    ['conclusion'],           # Conclusions
    example_settings           # Settings including iteration
]
```

### Internal Process

When `iterate_example` is called, the following process occurs:

1. An appropriate theory-specific iterator is created for the example
2. The initial model is used as the starting point
3. A solver is set up with the original constraints
4. Additional constraints are added to ensure difference from previous models
5. New models are found and checked for isomorphism
6. Differences between models are calculated and stored
7. The process continues until max_iterations is reached or no more models can be found

## Abstract Methods

When implementing a theory-specific iterator, you must override the following abstract methods from BaseModelIterator:

### 1. _calculate_differences(new_structure, previous_structure)

Calculate differences between two models, focusing on theory-specific semantics.

```python
def _calculate_differences(self, new_structure, previous_structure):
    """Calculate differences between two theory-specific model structures.
    
    Args:
        new_structure: The new model structure
        previous_structure: The previous model structure
        
    Returns:
        dict: Structured differences between the models
    """
    # Implement theory-specific difference detection
    differences = {
        "worlds": {"added": [], "removed": []},
        "possible_states": {"added": [], "removed": []},
        # Add theory-specific difference categories
    }
    
    # Detect differences in theory-specific semantic primitives
    
    return differences
```

### 2. _create_difference_constraint(previous_models)

Create constraints that force the next model to differ from previous ones.

```python
def _create_difference_constraint(self, previous_models):
    """Create theory-specific constraints to differentiate models.
    
    Args:
        previous_models: List of Z3 models to differ from
        
    Returns:
        z3.ExprRef: Z3 constraint requiring difference from previous models
    """
    # Get key structures
    model_structure = self.build_example.model_structure
    semantics = model_structure.semantics
    
    # Create constraints focusing on theory-specific semantic primitives
    diff_components = []
    
    # Add constraints for semantic functions
    
    # Return a combined constraint
    return z3.And([z3.Or(components) for components in diff_components])
```

### 3. _create_non_isomorphic_constraint(z3_model)

Create constraints that force structural differences to avoid isomorphism.

```python
def _create_non_isomorphic_constraint(self, z3_model):
    """Create constraints that force structural differences for this theory.
    
    Args:
        z3_model: The Z3 model to differ from
    
    Returns:
        z3.ExprRef: Z3 constraint expression or None if creation fails
    """
    # Create theory-specific structural constraints
    constraints = []
    
    # Force different world counts, letter valuations, etc.
    
    # Return combined constraints
    return z3.Or(constraints) if constraints else None
```

### 4. _create_stronger_constraint(isomorphic_model)

Create more aggressive constraints when multiple isomorphic models are found.

```python
def _create_stronger_constraint(self, isomorphic_model):
    """Create stronger constraints to escape isomorphic models.
    
    Args:
        isomorphic_model: The Z3 model that was isomorphic
    
    Returns:
        z3.ExprRef: Stronger constraint or None if creation fails
    """
    # Create more dramatic constraints for when we're stuck in isomorphic models
    constraints = []
    
    # Force extreme values, dramatically different structures, etc.
    
    # Return combined constraints
    return z3.Or(constraints) if constraints else None
```

## Implementing a Theory-Specific Iterator

To implement an iterator for a new theory, follow these steps:

1. Create `theory_lib/<your_theory>/iterate.py` with a class that extends `BaseModelIterator`
2. Implement all the required abstract methods
3. Add an `iterate_example` function that uses your iterator class
4. Update `theory_lib/<your_theory>/__init__.py` to export your iterator and function

Example implementation:

```python
# theory_lib/my_theory/iterate.py
from model_checker.iterate.core import BaseModelIterator

class MyTheoryModelIterator(BaseModelIterator):
    """Model iterator for my theory."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        # Implementation
        
    def _create_difference_constraint(self, previous_models):
        # Implementation
        
    def _create_non_isomorphic_constraint(self, z3_model):
        # Implementation
        
    def _create_stronger_constraint(self, isomorphic_model):
        # Implementation

# Convenience function for use in examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for an example using my theory.
    
    Args:
        example: A BuildExample instance
        max_iterations: Maximum number of models to find
        
    Returns:
        list: List of distinct model structures
    """
    # Create the iterator
    iterator = MyTheoryModelIterator(example)
    
    # Set max iterations if provided
    if max_iterations is not None:
        iterator.max_iterations = max_iterations
    
    # Perform iteration
    return iterator.iterate()
```

Then update your theory's `__init__.py`:

```python
# In theory_lib/my_theory/__init__.py
from .iterate import MyTheoryModelIterator, iterate_example

__all__ = [
    # Existing exports
    "MyTheoryModelIterator",
    "iterate_example"
]
```

## Design Considerations

The iteration system follows these design principles:

1. **Theory Agnostic Core**: The base iterator class contains no theory-specific logic
2. **Explicit Theory Selection**: Each theory must provide its own iterate_example function
3. **Abstract Method Pattern**: Required methods must be implemented by theory-specific subclasses
4. **No Default Values**: Each theory must explicitly implement all required methods
5. **Clear Interfaces**: Well-defined methods with consistent signatures
6. **Diagnostic Tracking**: Iteration history and diagnostics are maintained for debugging

## Diagnostic Information

All iterator implementations collect diagnostic information during execution:

- `debug_messages`: List of debug messages from the iteration process
- `checked_model_count`: Total number of models checked (including isomorphic ones)
- `distinct_models_found`: Number of distinct models found
- `escape_attempts`: Number of times stronger constraints were applied
- Model differences for each found model

## Difference Output Format

The difference detection system records changes in a structured format:

```python
{
    "worlds": {
        "added": [world1, world2, ...],
        "removed": [world3, world4, ...]
    },
    "possible_states": {
        "added": [state1, state2, ...],
        "removed": [state3, state4, ...]
    },
    "sentence_letters": {
        "A": {
            "old": old_value,
            "new": new_value
        },
        # Additional letters
    },
    # Theory-specific categories
}
```

Theory-specific categories might include:
- "parthood" for default theory
- "temporal_relations" for bimodal theory
- "accessibility" for modal logics
- "exclusion_relations" for exclusion theory

## Integration with Builder System

The model iteration system is integrated with the BuildModule class in the builder system, which provides a high-level interface for running examples with iteration:

```python
from model_checker.builder.module import BuildModule

# Create a module and run examples with iteration
module = BuildModule("examples")
module.add_example("example1")
module.process_example("example1")  # Will use iteration if enabled in settings
```

The BuildModule handles:
- Detecting the `iterate` setting in examples
- Calling the appropriate theory-specific `iterate_example` function
- Displaying model differences between iterations
- Formatting and presenting the results

## Isomorphism Detection

The iteration system includes graph-based isomorphism detection to avoid returning models that are structurally identical despite having different Z3 representations:

1. Each model is converted to a graph representation
2. Graphs are compared using NetworkX's isomorphism algorithms
3. If models are isomorphic, constraints are added to force structural differences
4. After multiple isomorphic models, stronger constraints are applied

This approach ensures that the iteration system returns genuinely different models rather than superficial variations of the same structure.

## Advanced Configuration

Advanced users can configure iteration behavior using settings:

```python
example_settings = {
    # Basic settings
    'iterate': 5,              # Maximum number of models to find
    
    # Advanced iteration settings
    'iteration_attempts': 10,  # Max consecutive isomorphic models before applying stronger constraints
    'escape_attempts': 3,      # Max attempts to escape isomorphic models
    'iteration_timeout': 2.0,  # Timeout for isomorphism checking (seconds)
    'iterate_timeout': 60.0,   # Overall timeout for iteration process
}
```

These settings provide fine-grained control over the iteration process for complex theories where finding distinct models may be computationally intensive.