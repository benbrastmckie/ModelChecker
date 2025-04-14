# Iteration Settings and Model Presentation Refactoring Plan

## Overview

This document outlines a plan to refactor the current model iteration and presentation workflow. The key goal is to consolidate the three settings (`iterate`, `print_differences`, and `check_isomorphism`) into a single `iterate` setting that automatically ensures subsequent models are non-isomorphic to all previous models. Each new model will be presented with its differences from the previous model shown first.

## Current Situation Analysis

After analyzing the code in `builder/iterate.py`, several issues need to be addressed:

1. **Solver Cloning for Each Iteration**:
   - The `_solve_with_constraints` method clones the original solver for each iteration
   - Constraints do not accumulate between iterations
   - Each model may not differ from all previous models

2. **Model Structure Rebuilding Issues**:
   - When a new Z3 model is found, the model structure is rebuilt
   - The differences between consecutive models are not systematically tracked
   - Differences are not consistently shown before the new model presentation

3. **Print Order Problems**:
   - The differences between models are not always shown before the new model
   - The workflow lacks a consistent presentation order

## Design Goals

1. **Accumulate Constraints**: Ensure each new model differs from *all* previous models using a single persistent solver
2. **Unified Setting**: Use a single `iterate` setting that automatically enables required features
3. **Systematic Difference Tracking**: Track and store differences between consecutive models
4. **Consistent Print Order**: Show differences *before* showing each new model
5. **Non-Isomorphic Models**: Ensure all models are structurally distinct from each other

## Implementation Plan

### 1. Update Model Structure Class to Track Differences

```python
class ModelStructure:
    """Concrete implementation of the model structure with difference tracking."""
    
    # Add a new attribute for storing model differences
    def __init__(self, model_constraints, settings):
        # Existing initialization code
        self.model_differences = None  # Will store differences with previous model
        self.previous_model = None     # Reference to previous model for comparison
    
    def _update_model_structure(self, new_model, previous_structure=None):
        """Update the model structure with a new Z3 model and compute differences.
        
        Args:
            new_model: The new Z3 model to use
            previous_structure: The previous model structure to compare with (optional)
        """
        # Update core model references
        self.z3_model = new_model
        self.z3_model_status = True
        
        # Update derived properties based on the new model
        # (existing code to update world states, etc.)
        
        # Calculate and store differences if we have a previous structure
        if previous_structure is not None:
            self.model_differences = self._compute_model_differences(previous_structure)
            self.previous_model = previous_structure
    
    def _compute_model_differences(self, previous_structure):
        """Compute differences between this model structure and the previous one.
        
        Args:
            previous_structure: The previous model structure to compare with
            
        Returns:
            dict: Structured differences between the models
        """
        differences = {
            'sentence_letters': {},
            'semantic_functions': {},
            'model_structure': {}
        }
        
        # Compare sentence letter valuations
        # (implementation details)
        
        # Compare semantic function interpretations
        # (implementation details)
        
        # Compare model structure components
        # (implementation details)
        
        return differences if any(differences.values()) else None
```

### 2. Restructure ModelIterator to Use a Single Persistent Solver

```python
class ModelIterator:
    """Handles systematic discovery of multiple distinct models."""
    
    def __init__(self, build_example):
        """Initialize with a BuildExample that already has a valid model."""
        # Validation and basic initialization
        self.build_example = build_example
        self.max_iterations = build_example.settings.get('iterate', 1)
        self.current_iteration = 1  # First model is already found
        
        # Store the initial model
        self.found_models = [build_example.model_structure.z3_model]
        self.model_structures = [build_example.model_structure]
        
        # Create a SINGLE persistent solver that will accumulate constraints
        self.solver = self._create_persistent_solver()
        
        # Initialize isomorphism checking
        self.model_graphs = []
        if HAS_NETWORKX:
            try:
                initial_graph = ModelGraph(
                    self.build_example.model_structure,
                    self.found_models[0]
                )
                self.model_graphs.append(initial_graph)
            except Exception as e:
                print(f"Warning: Could not create graph for initial model: {str(e)}")
    
    def _create_persistent_solver(self):
        """Create a persistent solver with the initial model's constraints."""
        original_solver = self.build_example.model_structure.solver
        persistent_solver = z3.Solver()
        for assertion in original_solver.assertions():
            persistent_solver.add(assertion)
        return persistent_solver
```

### 3. Update the Iteration Method to Accumulate Constraints and Track Differences

```python
def iterate(self):
    """Find multiple distinct models up to max_iterations.
    
    Each new model will:
    1. Differ from ALL previous models (through accumulated constraints)
    2. Be non-isomorphic to all previous models
    3. Have its differences from the previous model tracked
    4. Present differences before showing the model itself
    
    Returns:
        list: All found model structures (including the initial one)
    """
    # Proceed only if first model was successful
    if not self.build_example.model_structure.z3_model_status:
        raise RuntimeError("Cannot iterate when no initial model was found")
    
    # Set up timeout for the entire process
    max_time = self.build_example.settings.get('max_time', 1.0)
    iteration_timeout = max(max_time * 10, 30.0)
    start_time = time.time()
    
    # Start iteration from second model
    while self.current_iteration < self.max_iterations:
        try:
            # Check timeout
            if time.time() - start_time > iteration_timeout:
                print(f"Iteration process exceeded timeout of {iteration_timeout} seconds")
                break
            
            # Create a difference constraint for the latest model
            try:
                latest_model = self.found_models[-1]
                diff_constraint = self._create_difference_constraint([latest_model])
            except RuntimeError as e:
                print(f"No more difference constraints can be created: {str(e)}")
                break
            
            # Add the constraint to our persistent solver
            self.solver.add(diff_constraint)
            
            # Try to find a new model with all accumulated constraints
            result = self.solver.check()
            if result != z3.sat:
                print("No more models satisfy the accumulated constraints")
                break
            
            # Get the new model and update our records
            new_model = self.solver.model()
            self.found_models.append(new_model)
            
            # Create a new model structure from the new model
            # CRITICAL: Pass the previous model structure for difference tracking
            previous_structure = self.model_structures[-1]
            new_structure = self._create_new_model_structure(new_model, previous_structure)
            
            if not new_structure:
                print("Could not create new model structure, stopping iteration")
                break
            
            # Check for isomorphism if NetworkX is available
            is_isomorphic = False
            if HAS_NETWORKX:
                is_isomorphic = self._check_isomorphism(new_structure, new_model)
            
            if is_isomorphic:
                print("Found an isomorphic model despite syntactic differences")
                
                # Add a non-isomorphism constraint and try again
                iso_constraint = self._create_non_isomorphic_constraint(new_model)
                if iso_constraint:
                    self.solver.add(iso_constraint)
                    continue  # Skip to next attempt without incrementing
                else:
                    print("Could not create non-isomorphism constraint, stopping")
                    break
            
            # This is a genuine new model
            self.model_structures.append(new_structure)
            self.current_iteration += 1
            
        except Exception as e:
            print(f"Error during iteration: {str(e)}")
            import traceback
            print(traceback.format_exc())
            break
    
    return self.model_structures
```

### 4. Update the Model Structure Creation Method to Track Differences

```python
def _create_new_model_structure(self, new_model, previous_structure):
    """Create a new model structure based on a Z3 model, tracking differences.
    
    Args:
        new_model: Z3 model to use for the structure
        previous_structure: The previous model structure to compare with
        
    Returns:
        The updated model structure object with difference tracking
    """
    try:
        # Get the original model structure type
        original = self.build_example.model_structure
        
        # Create a new instance of the same class
        import copy
        new_structure = copy.copy(original)
        
        # Update with the new model
        # CRITICAL: Pass the previous structure for difference tracking
        new_structure.z3_model = new_model
        new_structure.z3_model_status = True
        
        # Call the structure's update method with previous structure reference
        if hasattr(new_structure, '_update_model_structure'):
            new_structure._update_model_structure(new_model, previous_structure)
        
        return new_structure
        
    except Exception as e:
        print(f"Error creating new model structure: {str(e)}")
        return None
```

### 5. Implement the BuildModule.process_example Method

```python
def process_example(self, example_name, example_case, theory_name, semantic_theory):
    """Process a single model checking example."""
    from model_checker.builder.iterate import ModelIterator
    
    # Create and solve the example
    example = BuildExample(self, semantic_theory, example_case)
    
    # Check if a model was found
    if not example.model_structure.z3_model_status:
        example.print_model(example_name, theory_name)
        return example
    
    # Print the first model
    example.print_model(example_name, theory_name)
    
    # Check if we need to iterate (find more models)
    iterate_count = example.settings.get('iterate', 1)
    if iterate_count <= 1:
        return example
    
    try:
        # Create iterator and find additional models
        iterator = ModelIterator(example)
        model_structures = iterator.iterate()
        
        # Skip the first model which is already printed
        for i, structure in enumerate(model_structures[1:], start=2):
            # CRITICAL: First print the differences, then print the model
            
            # 1. Print differences if they exist
            if hasattr(structure, 'model_differences') and structure.model_differences:
                print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n")
                structure.print_model_differences(sys.__stdout__)
                print("")  # Add spacing
            
            # 2. Then print the new model
            example.model_structure = structure
            example.print_model(f"{example_name} (Model {i}/{iterate_count})", theory_name)
    
    except Exception as e:
        print(f"Error during iteration: {str(e)}")
    
    return example
```

## Implementation Details and Special Considerations

### 1. Z3 Solver State Management

The persistent solver approach is crucial for ensuring each new model differs from all previous ones:

```python
# Adding constraints cumulatively to a single solver
def iterate(self):
    # ...
    while self.current_iteration < self.max_iterations:
        # Create new constraint for difference from latest model
        diff_constraint = self._create_difference_constraint([latest_model])
        
        # Add to the persistent solver (accumulating constraints)
        self.solver.add(diff_constraint)
        
        # Check if a model exists that satisfies ALL constraints
        result = self.solver.check()
        # ...
```

### 2. Difference Tracking in ModelStructure

The key enhancement is systematic difference tracking between consecutive models:

```python
def _update_model_structure(self, new_model, previous_structure=None):
    # Update internal state with new model
    self.z3_model = new_model
    # ...
    
    # Track differences with previous model
    if previous_structure is not None:
        self.model_differences = self._compute_model_differences(previous_structure)
```

### 3. Print Order Enforcement

The process_example method must always print differences before the model:

```python
# Print order: first differences, then model
if hasattr(structure, 'model_differences') and structure.model_differences:
    print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n")
    structure.print_model_differences(sys.__stdout__)
    print("")  # Add spacing

# Then print the model itself
example.model_structure = structure
example.print_model(f"{example_name} (Model {i}/{iterate_count})", theory_name)
```

### 4. Isomorphism Handling

When an isomorphic model is found, we add non-isomorphism constraints and continue iteration without incrementing:

```python
if is_isomorphic:
    print("Found an isomorphic model despite syntactic differences")
    
    # Add a non-isomorphism constraint and try again
    iso_constraint = self._create_non_isomorphic_constraint(new_model)
    if iso_constraint:
        self.solver.add(iso_constraint)
        continue  # Skip to next attempt without incrementing
```

## Benefits of This Approach

1. **Reliable Difference Finding**: Using a persistent solver ensures each new model differs from all previous ones
2. **Systematic Difference Tracking**: Each model structure explicitly tracks differences with its predecessor
3. **Consistent Print Order**: Differences are always shown before the new model
4. **Structural Distinctness**: Non-isomorphism constraints ensure models are meaningfully different

## Example Workflow

```
1. Find first model
2. Print first model
3. Set accumulated constraints = original constraints
4. While more models needed:
   a. Add difference constraints to accumulated constraints
   b. Find new model satisfying all accumulated constraints
   c. Create new model structure with reference to previous
   d. Check if model is isomorphic to any previous model
      i. If yes, add non-isomorphism constraint and try again
      ii. If no, continue
   e. Print differences from previous model 
   f. Print the new model
   g. Increment counter
```

## Conclusion

This implementation plan focuses on ensuring each new model differs from all previous models through accumulated constraints, systematically tracking differences between consecutive models, and enforcing a consistent print order where differences are always shown before the new model. By using a single persistent solver and proper difference tracking in the model structure, we can provide a more coherent and informative model exploration experience.