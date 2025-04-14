# ModelIterator Implementation Plan

## Current Situation

The ModelChecker currently processes examples one at a time, finding a single model for each example if one exists. When analyzing logical formulas, it's often valuable to find multiple distinct models to better understand the semantic space and verify that observed patterns are not artifacts of a particular model structure.

The `BuildModule.process_iterations` method in `module.py` contains partial support for iterations, but:

1. It lacks a structured approach to model differentiation
2. It doesn't consistently handle theory-specific model components
3. It's not factored into a separate reusable component
4. The constraint generation for alternative models is limited

## Design Goals

The new `iterate.py` module will:

1. Follow the project's "fail fast" design philosophy with clear error messages
2. Use explicit parameter passing without implicit conversions
3. Maintain clear data flow between components
4. Provide deterministic model iteration behavior
5. Generate constraints that ensure semantically meaningful model differences
6. Integrate seamlessly with the existing BuildExample and BuildModule architecture
7. Support all theory types without requiring theory-specific code modifications

## Component Architecture

### 1. Core Classes

#### `ModelIterator` Class

```python
class ModelIterator:
    """Handles systematic discovery of multiple distinct models for a logical example.
    
    This class manages the process of finding semantically distinct models by:
    1. Building on an initial model from a BuildExample instance
    2. Adding constraints that require differences from previously found models
    3. Iteratively solving for new models up to the specified limit
    
    Attributes:
        build_example: The BuildExample instance with the initial model
        max_iterations: Maximum number of models to find (from settings)
        found_models: List of Z3 models found so far
        current_iteration: Current iteration count
    """
    
    def __init__(self, build_example):
        """Initialize with a BuildExample that already has a valid model.
        
        Args:
            build_example: BuildExample instance with a valid model
            
        Raises:
            ValueError: If the build_example has no valid model
            TypeError: If build_example is not a BuildExample instance
        """
        # Attribute initialization with validation
```

### 2. Core Methods

#### 2.1. Public API

```python
def iterate(self):
    """Find multiple distinct models up to max_iterations.
    
    Systematic process:
    1. Start with the initial model from build_example
    2. For each iteration:
       a. Create constraints requiring difference from all previous models
       b. Add these constraints to the solver
       c. Attempt to find a new model
       d. If successful, add to found_models and continue
       e. If unsuccessful, stop iteration
    
    Returns:
        list: All found model structures (including the initial one)
        
    Raises:
        RuntimeError: If iteration fails for unexpected reasons
    """
    # Implementation
```

```python
def reset_iterator(self):
    """Reset the iterator to its initial state.
    
    Clears:
    - All found models except the initial one
    - Any added differentiation constraints
    - Iteration counters
    
    Useful when wanting to start iteration process over with 
    different parameters.
    
    Returns:
        self: For method chaining
    """
    # Implementation
```

#### 2.2. Constraint Generation

```python
def _create_difference_constraint(self, previous_models):
    """Create a Z3 constraint requiring difference from all previous models.
    
    The constraint ensures the new model differs in at least one of:
    - Sentence letter valuations
    - Semantic function interpretations
    - Model structure components
    
    Args:
        previous_models: List of Z3 models to differ from
        
    Returns:
        z3.ExprRef: Z3 constraint expression
        
    Raises:
        RuntimeError: If constraint generation fails
    """
    # Implementation
```

```python
def _extract_model_components(self, z3_model):
    """Extract all relevant components from a Z3 model for differentiation.
    
    Systematically extracts:
    1. All sentence letter valuations
    2. All semantic function interpretations for relevant inputs
    3. Theory-specific structure components
    
    Args:
        z3_model: Z3 model to extract from
        
    Returns:
        dict: Structured representation of model components
        
    Raises:
        RuntimeError: If extraction fails
    """
    # Implementation
```

#### 2.3. Model Updating

```python
def _solve_with_constraints(self, diff_constraint):
    """Attempt to solve the model with added differentiation constraints.
    
    Args:
        diff_constraint: Z3 constraint requiring difference
        
    Returns:
        tuple: (success, new_model) where:
            - success: True if new model found, False otherwise
            - new_model: New model structure if successful, None otherwise
    """
    # Implementation
```

```python
def _update_build_example(self, new_model):
    """Update the BuildExample with a new model.
    
    Updates:
    - Z3 model reference
    - Model structure
    - All derived properties
    
    Args:
        new_model: New Z3 model
        
    Returns:
        bool: True if update successful, False otherwise
        
    Raises:
        RuntimeError: If update fails
    """
    # Implementation
```

### 3. Settings Integration

```python
def _get_iteration_settings(self):
    """Extract and validate iteration settings from BuildExample.
    
    Settings:
    - iterate: Maximum number of models to find (int > 0)
    - iterate_timeout: Maximum time to spend on all iterations (optional)
    - iterate_variables: Which variables to consider for differences (optional)
    
    Returns:
        dict: Validated iteration settings
        
    Raises:
        ValueError: If settings are invalid
    """
    # Implementation
```

## Detailed Implementation Plan

### 1. Model Difference Specification

To ensure models are meaningfully different, we'll implement a comprehensive strategy:

```python
def _create_difference_constraint(self, previous_models):
    """Create a constraint requiring the new model to differ from all previous ones."""
    import z3
    
    # Get key structures from build_example
    model_structure = self.build_example.model_structure
    model_constraints = self.build_example.model_constraints
    semantics = model_constraints.semantics
    
    # For each previous model, create a constraint requiring at least one difference
    model_diff_constraints = []
    
    for prev_model in previous_models:
        # Components that could differ
        diff_components = []
        
        # 1. Sentence letter valuations
        for letter in model_constraints.sentence_letters:
            prev_value = prev_model.eval(letter, model_completion=True)
            diff_components.append(letter != prev_value)
        
        # 2. Semantic function interpretations
        for attr_name in dir(semantics):
            if attr_name.startswith('_'):
                continue
                
            attr = getattr(semantics, attr_name)
            if isinstance(attr, z3.FuncDeclRef):
                # Get domain size
                arity = attr.arity()
                if arity == 0:
                    continue
                
                # For unary and binary functions, check specific values
                if arity <= 2:
                    # Get the domain size (number of worlds)
                    n_worlds = model_structure.num_worlds
                    
                    # Create constraints for all relevant inputs
                    for inputs in self._generate_input_combinations(arity, n_worlds):
                        try:
                            # Check what this function returns in the previous model
                            args = [z3.IntVal(i) for i in inputs]
                            prev_value = prev_model.eval(attr(*args), model_completion=True)
                            
                            # Add constraint requiring it to be different
                            diff_components.append(attr(*args) != prev_value)
                        except z3.Z3Exception:
                            pass
        
        # 3. Theory-specific model components (if available)
        if hasattr(model_structure, 'get_differentiable_components'):
            for component, args, prev_value in model_structure.get_differentiable_components(prev_model):
                diff_components.append(component(*args) != prev_value)
        
        # Create a single constraint for this model requiring at least one difference
        if diff_components:
            model_diff_constraints.append(z3.Or(diff_components))
    
    # The new model must be different from ALL previous models
    if model_diff_constraints:
        return z3.And(model_diff_constraints)
    else:
        raise RuntimeError("Could not create any difference constraints")
```

### 2. Integration with BuildModule

```python
def process_iterations(self, example_name, example_case, theory_name, semantic_theory):
    """Process multiple iterations of model checking for a given example.
    
    Uses ModelIterator to find multiple distinct models for the example.
    
    Args:
        example_name: Name of the example being processed
        example_case: The example case containing [premises, conclusions, settings]
        theory_name: Name of the semantic theory being used
        semantic_theory: Dictionary containing the semantic theory implementation
    
    Returns:
        BuildExample: The final example after all iterations
    """
    from model_checker.builder.iterate import ModelIterator
    from model_checker.builder.example import BuildExample
    
    # Create initial spinner for user feedback
    spinner = Spinner(message=f"Running {example_name} with {theory_name}")
    spinner.start()
    
    try:
        # Create initial example and find first model
        example = BuildExample(self, semantic_theory, example_case)
    finally:
        spinner.stop()
    
    # Check if first model was found
    if not example.model_structure.z3_model_status:
        # No initial model found, handle as usual
        example.print_model(example_name, theory_name)
        return example
        
    # Print the initial model
    example.print_model(example_name, theory_name)
    
    # Get iteration count from settings
    iterations = example.settings.get('iterate', 1)
    if iterations <= 1:
        # No additional iterations requested
        return example
        
    # Create iterator and find additional models
    try:
        iterator = ModelIterator(example)
        model_count = 1  # Already found first model
        
        # Start iteration process
        while model_count < iterations:
            # Show progress
            spinner.start(message=f"Finding model {model_count+1} of {iterations}")
            
            try:
                # Find next model
                success, _ = iterator._solve_with_constraints(
                    iterator._create_difference_constraint(iterator.found_models)
                )
                
                if not success:
                    print(f"\nFound {model_count} models. No more models exist.")
                    break
                    
                # Update model count
                model_count += 1
                
                # Print the new model
                example.print_model(f"{example_name} (Model {model_count})", theory_name)
                
            finally:
                spinner.stop()
                
    except Exception as e:
        print(f"\nError during iteration: {str(e)}")
        
    return example
```

### 3. Helper Functions

```python
def _generate_input_combinations(self, arity, domain_size):
    """Generate all relevant input combinations for a function of given arity.
    
    Args:
        arity: Number of arguments the function takes
        domain_size: Size of the domain (typically number of worlds)
        
    Returns:
        list: All relevant input combinations
    """
    import itertools
    
    # For n-ary functions, generate all combinations of inputs
    # from the domain, which is typically the world indices
    domain = range(domain_size)
    return itertools.product(domain, repeat=arity)
```

```python
def _clone_solver_with_assertions(self, solver):
    """Clone a Z3 solver with all its assertions.
    
    Args:
        solver: Original Z3 solver
        
    Returns:
        z3.Solver: New solver with same assertions
    """
    import z3
    
    new_solver = z3.Solver()
    for assertion in solver.assertions():
        new_solver.add(assertion)
    return new_solver
```

### 4. Public Module Functions

```python
def iterate_example(build_example, max_iterations=None):
    """Convenience function to iterate an example and find multiple models.
    
    Args:
        build_example: BuildExample instance with a solved model
        max_iterations: Override for maximum iterations (optional)
        
    Returns:
        list: All found model structures
        
    Raises:
        ValueError: If iteration is not possible with this example
    """
    iterator = ModelIterator(build_example)
    
    # Override max_iterations if provided
    if max_iterations is not None:
        if not isinstance(max_iterations, int) or max_iterations < 1:
            raise ValueError(f"max_iterations must be a positive integer, got {max_iterations}")
        iterator.max_iterations = max_iterations
        
    return iterator.iterate()
```

## Error Handling Strategy

Following the project's "fail fast" philosophy:

1. Each method will validate its inputs and raise appropriate exceptions with clear messages
2. No silent failures or default fallbacks
3. Errors will propagate naturally to provide accurate debugging information
4. Exception messages will include specific details about the failure context

## Performance Considerations

1. Z3 constraint solving can be computationally expensive
2. For complex models or large iteration counts, performance may become an issue
3. Implementation will include:
   - Progressive constraint building to avoid reevaluating unchanged constraints
   - Caching of extracted model components
   - Optional timeout settings for iteration process

## Testing Strategy

1. **Unit Tests**:
   - Test `ModelIterator` initialization with valid and invalid inputs
   - Test constraint generation with different model components
   - Test model updating mechanisms
   - Test edge cases like models with no differentiable components

2. **Integration Tests**:
   - Test with different theory types (default, exclusion, imposition, bimodal)
   - Verify iteration works with theory-specific components
   - Test interaction with BuildModule's process_iterations

3. **Validation Tests**:
   - Verify that found models are genuinely different in meaningful ways
   - Check that iteration correctly halts when no more models exist
   - Validate integration with settings system

## Implementation Phases

1. **Phase 1: Core Implementation**
   - Create ModelIterator class with basic functionality
   - Implement constraint generation for sentence letters
   - Integrate with BuildModule.process_iterations

2. **Phase 2: Enhanced Differentiation**
   - Add support for semantic function differentiation
   - Add theory-specific extension points
   - Implement proper caching and performance optimizations

3. **Phase 3: Settings Integration**
   - Add support for specialized iteration settings
   - Implement timeout handling
   - Add progress reporting

4. **Phase 4: Testing and Documentation**
   - Implement comprehensive test suite
   - Document public API and usage examples
   - Create integration guide for theory implementers

## Conclusion

The `iterate.py` module will enhance the ModelChecker by enabling systematic discovery of multiple distinct models for logical examples. It will seamlessly integrate with the existing architecture while following the project's design philosophy of explicit parameters, clear data flow, and letting errors occur naturally with detailed error messages.

This implementation will provide users with a more comprehensive understanding of the semantic space of logical theories and formulas.