# Model Iteration System

The ModelChecker's iteration system provides a framework for systematically finding multiple semantically distinct models for logical examples. This documentation covers the architecture, usage, and extension points of the iteration system.

## Overview

The iteration system allows you to:

1. **Find Multiple Models**: Generate multiple semantically distinct models for a logical formula
2. **Ensure Distinctness**: Create constraints that ensure each new model differs from previous ones
3. **Avoid Duplicates**: Check for structural isomorphism to avoid equivalent models
4. **Handle Edge Cases**: Gracefully manage cases where no more distinct models exist
5. **Track Progress**: Provide real-time progress updates with timing information
6. **Analyze Differences**: Visualize semantic differences between models

This functionality is valuable for:

- **Semantic Exploration**: Understanding the full space of possible models for a formula
- **Theory Analysis**: Examining how different theories handle the same logical principles
- **Countermodel Discovery**: Finding diverse counterexamples to logical arguments
- **Robustness Testing**: Verifying that logical principles hold across model variations
- **Educational Purposes**: Demonstrating the semantic diversity within logical theories

## Architecture

The iteration system follows a modular architecture with clear separation between theory-agnostic core functionality and theory-specific implementations:

```
iterate/
├── core.py                  # BaseModelIterator abstract class
├── progress.py             # Progress bar and timing utilities
├── stats.py               # Model statistics collection
├── parallel.py            # Parallel constraint generation utilities
└── graph_utils.py         # Graph-based isomorphism checking

theory_lib/<theory>/iterate.py  # Theory-specific implementations:
├── logos/iterate.py           # LogosModelIterator
├── exclusion/iterate.py       # ExclusionModelIterator (extends LogosModelIterator)
├── default/iterate.py         # DefaultModelIterator
├── bimodal/iterate.py         # BimodalModelIterator
└── imposition/iterate.py      # ImpositionModelIterator
```

### Key Components

#### 1. BaseModelIterator (`iterate/core.py`)
The abstract base class providing the theory-agnostic iteration framework:

- **Solver Management**: Handles Z3 solver lifecycle and constraint application
- **Model Building**: Orchestrates the process of finding and validating new models
- **Iteration Control**: Manages retry logic, failure limits, and termination conditions
- **Invalid Model Detection**: Automatically excludes models with no possible worlds
- **Isomorphism Detection**: Uses graph-based comparison to identify structurally identical models
- **Progress Tracking**: Integrates with progress reporting and timing systems
- **Debug Collection**: Gathers detailed iteration information for analysis

**Key Features**:
- Automatic retry with stronger constraints when stuck on isomorphic models
- Configurable limits for consecutive failures and escape attempts
- Smart constraint ordering for improved performance
- Comprehensive error handling and recovery

#### 2. Theory-Specific Iterators
Each theory extends BaseModelIterator with specialized implementations:

- **Constraint Generation**: Creates difference constraints using theory's semantic primitives
- **Model Comparison**: Detects meaningful differences based on theory's concepts
- **Isomorphism Handling**: Defines structural similarity for the theory's models
- **Visualization**: Provides theory-appropriate display of model differences

**Current Implementations**:
- **LogosModelIterator**: Handles hyperintensional semantics with verification/falsification
- **ExclusionModelIterator**: Extends LogosModelIterator for witness-aware exclusion semantics
- **DefaultModelIterator**: Basic classical logic implementation
- **BimodalModelIterator**: Supports temporal and modal operators
- **ImpositionModelIterator**: Handles imposition theory semantics

#### 3. Supporting Infrastructure

**Progress System** (`iterate/progress.py`):
- Real-time progress bars with timing information
- Configurable display options for different environments
- Integration with model counting and iteration statistics

**Statistics Collection** (`iterate/stats.py`):
- Model diversity analysis and difference categorization
- Performance metrics and timing breakdowns
- Summary reports for iteration sessions

**Performance Optimizations**:
- Parallel constraint generation for complex theories
- Isomorphism caching to avoid repeated comparisons
- Smart constraint ordering based on constraint priority

## Usage

### Basic Usage in Examples

Enable iteration by adding the `iterate` parameter to your example settings:

```python
# In theory_lib/exclusion/examples.py

EX_CM_21_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 2,        # Request 2 distinct models
    'expectation': True,
}
```

When you run this example, the system will:
1. Find and display the first model normally
2. Search for a second model that differs semantically from the first
3. Display differences between the models
4. Show progress with timing information

### Advanced Configuration

Control iteration behavior with additional settings:

```python
settings = {
    # Basic iteration
    'iterate': 5,                    # Maximum models to find
    
    # Failure handling
    'max_invalid_attempts': 5,       # Max consecutive invalid models before stopping
    'iteration_attempts': 5,         # Max isomorphic models before using stronger constraints
    'escape_attempts': 3,            # Max attempts to escape isomorphism loops
    
    # Performance tuning
    'iteration_timeout': 1.0,        # Timeout for isomorphism check (seconds)
    'iteration_solver_timeout': 5000,# Z3 solver timeout per iteration (milliseconds)
    
    # Theory-specific options (varies by theory)
    'max_time': 5,                   # Overall timeout for model finding
    'contingent': True,              # Enable contingent valuations
    'non_empty': True,               # Require non-empty state spaces
}
```

### Programmatic Usage

Each theory provides its own `iterate_example` function for direct use:

```python
# Logos theory example
from model_checker.theory_lib.logos import iterate_example
from model_checker import BuildExample, get_theory

# Create example with logos theory
theory = get_theory('logos')
example = BuildExample("counterfactual_example", theory, 
                      premises=['(A □→ B)'], 
                      conclusions=['(A → B)'])

# Find up to 5 distinct models
model_structures = iterate_example(example, max_iterations=5)

# Process results
print(f"Found {len(model_structures)} distinct models")
for i, structure in enumerate(model_structures, 1):
    print(f"\n=== Model {i} ===")
    structure.print_model()

# Access iteration debug information
if hasattr(example, '_iterator'):
    iterator = example._iterator
    print("\nIteration Summary:")
    for message in iterator.debug_messages:
        if message.startswith('[ITERATION]'):
            print(message)
```

```python
# Exclusion theory example
from model_checker.theory_lib.exclusion import iterate_example

# Example with exclusion theory
example = BuildExample("exclusion_example", exclusion_theory,
                      premises=['A'], 
                      conclusions=['B'])

# Find multiple models showing different exclusion patterns
models = iterate_example(example, max_iterations=3)

# Models will differ in their exclusion relations and witness structures
for structure in models:
    structure.print_model()  # Shows exclusion relations and coherence patterns
```

### Integration with Dev CLI

The iteration system integrates seamlessly with the development CLI:

```bash
# Run exclusion examples with iteration enabled
./dev_cli.py /path/to/exclusion/examples.py

# The system automatically detects 'iterate' settings and:
# 1. Shows "MODEL 1/N" headers
# 2. Displays progress bars during iteration
# 3. Shows differences between consecutive models
# 4. Provides iteration summary at the end
```

## Theory-Specific Behavior

### Logos Theory
The LogosModelIterator focuses on hyperintensional differences:

- **Verification Changes**: Different truth values for sentence letters at specific states
- **World Structure**: Changes in which states count as possible worlds
- **Part-Whole Relations**: Modifications to the mereological structure
- **Modal Relations**: Different accessibility relations for modal operators
- **Constitutive Relations**: Changes in grounding and essence relationships

**Example Output**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===
Verification Changes:
  □ verifies A: False → True
  a.b falsifies B: True → False

Structural Properties:
  Worlds: 2 → 3
  Possible States: {□, a, b, a.b} → {□, a, c, a.c}
```

### Exclusion Theory
The ExclusionModelIterator extends LogosModelIterator with exclusion-specific features:

- **Exclusion Relations**: Changes in which states exclude each other
- **Witness Structures**: Modifications to witness predicate assignments
- **Coherence Patterns**: Different coherence relationships between states
- **Verification Differences**: Similar to Logos but with unilateral negation semantics

**Example Output**:
```
=== DIFFERENCES FROM PREVIOUS MODEL ===
Exclusion Changes:
  a.b excludes a.b: False → True

Verification Changes:
  □ verifies A: True → False
  
Structural Properties:
  Worlds: 1 → 2
  Conflicts: Added conflict between a.b and a.b.c
```

## Abstract Methods for New Theories

When implementing iteration for a new theory, you must provide these methods:

### 1. _calculate_differences(new_structure, previous_structure)

Calculate theory-specific semantic differences between models:

```python
def _calculate_differences(self, new_structure, previous_structure):
    """Calculate semantic differences between models.
    
    Args:
        new_structure: The new model structure
        previous_structure: The previous model structure
        
    Returns:
        dict: Structured differences categorized by type
    """
    differences = {
        "theory_specific_category1": {},
        "theory_specific_category2": {},
        "structural": {}
    }
    
    # Implementation varies by theory
    # Compare semantic primitives (verify, falsify, modal relations, etc.)
    # Focus on differences that matter for the theory's semantics
    
    return differences
```

### 2. _create_difference_constraint(previous_models)

Generate Z3 constraints ensuring new models differ from all previous ones:

```python
def _create_difference_constraint(self, previous_models):
    """Create constraints requiring difference from all previous models.
    
    Args:
        previous_models: List of Z3 models to differ from
        
    Returns:
        z3.ExprRef: Constraint ensuring semantic difference
    """
    semantics = self.build_example.model_structure.semantics
    all_states = self.build_example.model_structure.all_states
    
    model_constraints = []
    
    for prev_model in previous_models:
        differences = []
        
        # Add constraints based on theory's semantic primitives
        for state in all_states:
            for atom in sentence_letters:
                # Example: require different verification
                prev_verifies = prev_model.eval(semantics.verify(state, atom))
                differences.append(semantics.verify(state, atom) != prev_verifies)
        
        # Combine all possible differences with OR
        if differences:
            model_constraints.append(z3.Or(*differences))
    
    # Must differ from ALL previous models
    return z3.And(*model_constraints) if model_constraints else z3.BoolVal(True)
```

### 3. _create_non_isomorphic_constraint(z3_model)

Generate constraints to break structural symmetries:

```python
def _create_non_isomorphic_constraint(self, z3_model):
    """Create constraints to avoid structurally identical models.
    
    Args:
        z3_model: Z3 model to differ from structurally
        
    Returns:
        z3.ExprRef or None: Constraint to break isomorphism
    """
    try:
        semantics = self.build_example.model_structure.semantics
        constraints = []
        
        # Force specific structural differences
        # Example: require different world count or different state properties
        
        return z3.Or(*constraints) if constraints else None
        
    except Exception as e:
        # Return None if constraint generation fails
        return None
```

### 4. _create_stronger_constraint(isomorphic_model)

Create aggressive constraints when stuck in isomorphic loops:

```python
def _create_stronger_constraint(self, isomorphic_model):
    """Create stronger constraints after repeated isomorphism.
    
    Args:
        isomorphic_model: Z3 model we're stuck being isomorphic to
        
    Returns:
        z3.ExprRef or None: Strong constraint to escape isomorphism
    """
    try:
        # Create very restrictive constraints
        # Often involves forcing specific values for key predicates
        
        return strong_constraint
        
    except Exception:
        return None
```

## Performance Considerations

### Optimization Strategies

1. **Smart Constraint Ordering**: Prioritize constraints most likely to produce distinct models
2. **Isomorphism Caching**: Cache graph representations to avoid repeated isomorphism checks
3. **Parallel Processing**: Generate constraints in parallel for complex theories
4. **Early Termination**: Stop iteration early when patterns indicate no more distinct models exist

### Common Performance Issues

**Large State Spaces**: 
- **Problem**: Theories with high N values create exponentially large state spaces
- **Solution**: Use focused constraints, reduce N for iteration testing, add timeouts

**Complex Semantic Relations**: 
- **Problem**: Theories with many semantic primitives generate complex constraints
- **Solution**: Prioritize key differences, use parallel constraint generation

**Isomorphism Detection**: 
- **Problem**: Graph isomorphism checking can be expensive for large models
- **Solution**: Use heuristics, caching, and timeouts

### Configuration for Performance

```python
# For large models or complex theories
settings = {
    'iterate': 3,                     # Start with fewer models
    'iteration_solver_timeout': 10000,# Increase solver timeout
    'iteration_timeout': 2.0,         # Increase isomorphism timeout
    'max_invalid_attempts': 3,        # Reduce failure tolerance
}
```

## Debug Information and Diagnostics

The iteration system provides comprehensive debugging information:

### Debug Message Categories

```
[ITERATION] Searching for model 2/3...
[ITERATION] Found isomorphic model #2 - will try different constraints  
[ITERATION] Found invalid model (no possible worlds) - attempt 1/5
[ITERATION] Using stronger constraints after 3 isomorphic failures
[ITERATION] Successfully found distinct model 2/3
```

### Accessing Debug Information

```python
# After iteration completes
iterator = example._iterator
debug_messages = iterator.debug_messages

# Filter for user-facing messages
iteration_messages = [msg for msg in debug_messages if msg.startswith('[ITERATION]')]

# Get performance statistics if available
if hasattr(iterator, 'statistics'):
    stats = iterator.statistics.get_summary()
    print(f"Total time: {stats['total_time']:.2f}s")
    print(f"Models checked: {stats['models_checked']}")
```

## Best Practices

### For Theory Implementers

1. **Focus on Semantic Primitives**: Base difference detection on your theory's core semantic concepts
2. **Handle Edge Cases**: Provide graceful fallbacks when constraint generation fails
3. **Test Thoroughly**: Verify iteration works with various example types
4. **Document Theory-Specific Behavior**: Explain what makes models "different" in your theory

### For Users

1. **Start Small**: Begin with `iterate: 2` or `3` to understand your examples
2. **Expect Variation**: Not all examples will have multiple distinct models
3. **Use Timeouts**: Add reasonable time limits for complex examples
4. **Monitor Progress**: Pay attention to progress messages for stuck iterations
5. **Analyze Differences**: Study the difference output to understand your theory better

### For Performance

1. **Optimize Constraints**: Make difference constraints as specific as possible
2. **Use Appropriate N Values**: Smaller state spaces iterate faster
3. **Configure Timeouts**: Balance thoroughness with performance needs
4. **Profile Complex Cases**: Use debug output to identify bottlenecks

This iteration system provides a powerful foundation for exploring the semantic space of logical theories while maintaining flexibility for theory-specific requirements and optimizations.