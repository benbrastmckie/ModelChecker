# Model Difference Tracking Implementation Plan

## Current Situation

The ModelIterator in `iterate.py` efficiently finds multiple distinct models for a logical example, but it doesn't currently provide a way to visualize the specific differences between successive models. When examining multiple models, users have to manually compare model outputs to identify what changed, which can be error-prone and time-consuming, especially for complex models with many components.

## Addressing Model Isomorphism

Currently, the ModelIterator finds models that are syntactically different but may still be isomorphic in structure. For example, it might generate models that differ only in the specific interpretation assignments but maintain the same structural relationships. To find genuinely different models (non-isomorphic), several strategies could be implemented:

### 1. Structural Difference Constraints

Instead of requiring differences in variable assignments, we can require structural differences:

```python
def _create_structural_difference_constraint(self, previous_models):
    """Create a constraint requiring structural differences from previous models."""
    # Examples of structural properties:
    # - Number of states with specific properties
    # - Connectivity patterns between states
    # - Distribution of truth values across worlds
    
    constraints = []
    for prev_model in previous_models:
        # Extract structural metrics
        prev_metrics = self._extract_structural_metrics(prev_model)
        
        # Create constraint requiring at least one metric to differ
        metric_differences = []
        for name, metric_func in self.structure_metrics.items():
            metric_differences.append(metric_func() != prev_metrics[name])
            
        constraints.append(z3.Or(metric_differences))
    
    return z3.And(constraints)
```

### 2. Graph-Based Difference Detection

For more sophisticated difference detection, treat models as graphs and detect isomorphism:

```python
def _models_are_isomorphic(self, model1, model2):
    """Check if two models are isomorphic by comparing their graph representations."""
    g1 = self._model_to_graph(model1)
    g2 = self._model_to_graph(model2)
    
    # Use standard graph isomorphism algorithms (e.g., VF2)
    return is_isomorphic(g1, g2)
    
def _model_to_graph(self, model):
    """Convert a model to a labeled graph representation."""
    graph = nx.DiGraph()
    
    # Add nodes for worlds with labels for properties
    for world_idx in range(self.build_example.model_structure.num_worlds):
        properties = {}
        # Add truth values of atomic propositions
        for p in self.build_example.model_constraints.sentence_letters:
            properties[str(p)] = model.eval(p(world_idx), model_completion=True)
        graph.add_node(world_idx, **properties)
    
    # Add edges for accessibility relations
    for w1 in range(self.build_example.model_structure.num_worlds):
        for w2 in range(self.build_example.model_structure.num_worlds):
            if model.eval(self.build_example.model_constraints.semantics.R(w1, w2), model_completion=True):
                graph.add_edge(w1, w2)
    
    return graph
```

### 3. Canonical Form Comparison

Another approach is to normalize models to a canonical form before comparison:

```python
def _get_canonical_model(self, model):
    """Convert a model to its canonical form for isomorphism-invariant comparison."""
    # 1. Identify all worlds and their properties
    worlds = []
    for i in range(self.build_example.model_structure.num_worlds):
        world_props = {}
        for p in self.build_example.model_constraints.sentence_letters:
            world_props[str(p)] = model.eval(p(i), model_completion=True)
        worlds.append((i, world_props))
    
    # 2. Sort worlds by properties to create a canonical ordering
    sorted_worlds = sorted(worlds, key=lambda w: tuple(sorted(w[1].items())))
    world_mapping = {old_idx: new_idx for new_idx, (old_idx, _) in enumerate(sorted_worlds)}
    
    # 3. Create a canonical representation of the model structure
    canonical_repr = {
        'worlds': [props for _, props in sorted_worlds],
        'relations': []
    }
    
    # 4. Add relations in canonical form
    for w1 in range(self.build_example.model_structure.num_worlds):
        for w2 in range(self.build_example.model_structure.num_worlds):
            if model.eval(self.build_example.model_constraints.semantics.R(w1, w2), model_completion=True):
                canonical_repr['relations'].append((world_mapping[w1], world_mapping[w2]))
    
    canonical_repr['relations'].sort()
    return canonical_repr

def _create_non_isomorphic_constraint(self, previous_models):
    """Create a constraint requiring the new model to be non-isomorphic to previous ones."""
    # Cache canonical forms for previous models
    if not hasattr(self, 'canonical_models'):
        self.canonical_models = [self._get_canonical_model(model) for model in previous_models]
    
    # Define constraints based on structural metrics that would make this model different
    constraints = []
    for canonical in self.canonical_models:
        # Number of worlds with specific property combinations
        for prop_pattern, count in self._count_property_patterns(canonical):
            # Require different counts for this pattern
            constraints.append(self._property_pattern_count(prop_pattern) != count)
        
        # Connectivity metrics
        edge_counts = len(canonical['relations'])
        constraints.append(self._count_relation_edges() != edge_counts)
        
        # Add more structural metrics as needed
    
    return z3.Or(constraints)
```

### 4. Theory-Specific Semantic Invariants

For specific logical theories, we can define semantic invariants that have meaningful differences:

```python
def _add_theory_specific_constraints(self, solver, previous_models):
    """Add theory-specific constraints for non-isomorphic models."""
    theory_name = getattr(self.build_example.model_structure, 'theory_name', 'default')
    
    if theory_name == 'default':
        # For default theory, require different verification behavior
        verification_diffs = []
        for formula in self.build_example.model_structure.premises + self.build_example.model_structure.conclusions:
            # Get previous valuations for this formula
            prev_values = [self._formula_value(model, formula) for model in previous_models]
            # Require different valuation
            verification_diffs.append(self._formula_value_constraint(formula) not in prev_values)
        
        if verification_diffs:
            solver.add(z3.Or(verification_diffs))
            
    elif theory_name == 'bimodal':
        # For bimodal logic, require different temporal structure
        for prev_model in previous_models:
            temporal_diff = self._create_temporal_difference_constraint(prev_model)
            solver.add(temporal_diff)
```

### 5. Integration with User Requirements

The model difference approach could let users specify what kinds of differences they care about:

```python
def _get_iteration_settings(self):
    """Extract and validate iteration settings from BuildExample."""
    # Existing settings code...
    
    # Extract difference type settings
    validated_settings['difference_type'] = settings.get('difference_type', 'syntactic')
    allowed_types = ['syntactic', 'structural', 'non_isomorphic', 'semantic']
    if validated_settings['difference_type'] not in allowed_types:
        validated_settings['difference_type'] = 'syntactic'
        
    return validated_settings

def _create_difference_constraint(self, previous_models):
    """Create appropriate difference constraint based on settings."""
    diff_type = self.settings.get('difference_type', 'syntactic')
    
    if diff_type == 'syntactic':
        return self._create_syntactic_difference_constraint(previous_models)
    elif diff_type == 'structural':
        return self._create_structural_difference_constraint(previous_models)
    elif diff_type == 'non_isomorphic':
        return self._create_non_isomorphic_constraint(previous_models)
    elif diff_type == 'semantic':
        return self._create_semantic_difference_constraint(previous_models)
    else:
        return self._create_syntactic_difference_constraint(previous_models)
```

### 6. Performance Considerations

Non-isomorphism checking can be computationally expensive:

- For small models, direct graph isomorphism checks are feasible
- For larger models, approximation using structural invariants is more practical
- Some properties to compute:
  - Distribution of atomic proposition truth values
  - World connectivity patterns (in/out degree distributions)
  - Path lengths between worlds
  - Cycle structure

These structural metrics can be used both for creating constraints and for the display of model differences.

## Design Goals

1. Implement a feature that tracks and displays the differences between successive models
2. Maintain the project's "fail fast" design philosophy with explicit error handling
3. Integrate seamlessly with existing ModelIterator and model printing functionality
4. Support all theory types without requiring theory-specific modifications
5. Provide clear, concise, and meaningful difference reporting
6. Make the feature optional and configurable through settings

## Implementation Details

### 1. Model Structure Modifications

#### 1.1 Add a tracking reference to the previous model

We need to store a reference to the previous model to enable comparison:

```python
class ModelIterator:
    # Existing initialization...
    
    def __init__(self, build_example):
        # Existing code...
        self.previous_model_components = None  # Will store the previous model's extracted components
```

#### 1.2 Capture components in structured format

Enhance the existing `_extract_model_components` method to ensure it captures all relevant model aspects:

```python
def _extract_model_components(self, z3_model):
    """Extract all relevant components from a Z3 model for differentiation."""
    # Existing extraction code...
    
    # Ensure we're capturing components in a standardized format for comparison
    extracted = {
        'sentence_letters': {},
        'semantic_functions': {},
        'model_structure': {}
    }
    
    # Extract sentence letter values, semantic functions, model structure...
    
    return extracted
```

### 2. Difference Detection Implementation

#### 2.1 Add a method to compute differences between models

```python
def _compute_model_differences(self, current_components, previous_components):
    """Compute differences between current and previous model components.
    
    Args:
        current_components (dict): Components from the current model
        previous_components (dict): Components from the previous model
        
    Returns:
        dict: Structured differences between the models
    """
    if previous_components is None:
        return None  # No differences to compute for the first model
    
    differences = {
        'sentence_letters': {},
        'semantic_functions': {},
        'model_structure': {}
    }
    
    # Compare sentence letter values
    for letter, current_value in current_components['sentence_letters'].items():
        letter_str = str(letter)
        if letter_str in previous_components['sentence_letters']:
            prev_value = previous_components['sentence_letters'][letter_str]
            if current_value != prev_value:
                differences['sentence_letters'][letter_str] = {
                    'old': prev_value,
                    'new': current_value
                }
    
    # Compare semantic function values
    for func_name, current_values in current_components['semantic_functions'].items():
        if func_name in previous_components['semantic_functions']:
            func_diffs = {}
            for inputs, current_value in current_values.items():
                input_str = str(inputs)
                if input_str in previous_components['semantic_functions'][func_name]:
                    prev_value = previous_components['semantic_functions'][func_name][input_str]
                    if current_value != prev_value:
                        func_diffs[input_str] = {
                            'old': prev_value,
                            'new': current_value
                        }
            if func_diffs:
                differences['semantic_functions'][func_name] = func_diffs
    
    # Compare model structure components
    for component, current_value in current_components['model_structure'].items():
        if component in previous_components['model_structure']:
            prev_value = previous_components['model_structure'][component]
            if current_value != prev_value:
                differences['model_structure'][component] = {
                    'old': prev_value,
                    'new': current_value
                }
    
    return differences
```

### 3. Model Printing Integration

#### 3.1 Update the `_create_new_model_structure` method to track differences

```python
def _create_new_model_structure(self, new_model):
    """Create a new model structure based on a Z3 model."""
    try:
        # Existing code to create a new model structure...
        
        # Extract components for the new model
        current_components = self._extract_model_components(new_model)
        
        # Compute differences from previous model
        differences = self._compute_model_differences(
            current_components, 
            self.previous_model_components
        )
        
        # Store the differences on the model structure
        if differences:
            new_structure.model_differences = differences
            
        # Update previous components for next iteration
        self.previous_model_components = current_components
        
        return new_structure
        
    except Exception as e:
        # Existing error handling...
```

#### 3.2 Add a model difference printing method

Create a new method in the ModelStructure class (to be added to appropriate theory implementations):

```python
def print_model_differences(self, output=sys.__stdout__):
    """Print the differences between this model and the previous one.
    
    Args:
        output (file, optional): Output stream to write to. Defaults to sys.stdout.
    """
    if not hasattr(self, 'model_differences') or not self.model_differences:
        print("No previous model to compare with.", file=output)
        return
    
    print("\n=== MODEL DIFFERENCES ===\n", file=output)
    
    # Print changed sentence letter values
    letter_diffs = self.model_differences.get('sentence_letters', {})
    if letter_diffs:
        print("Changed Sentence Letter Values:", file=output)
        for letter, values in letter_diffs.items():
            print(f"  {letter}: {values['old']} → {values['new']}", file=output)
    
    # Print changed semantic function values
    func_diffs = self.model_differences.get('semantic_functions', {})
    if func_diffs:
        print("\nChanged Semantic Function Values:", file=output)
        for func_name, input_diffs in func_diffs.items():
            print(f"  {func_name}:", file=output)
            for inputs, values in input_diffs.items():
                print(f"    {inputs}: {values['old']} → {values['new']}", file=output)
    
    # Print changed model structure components
    struct_diffs = self.model_differences.get('model_structure', {})
    if struct_diffs:
        print("\nChanged Model Structure Components:", file=output)
        for component, values in struct_diffs.items():
            print(f"  {component}: {values['old']} → {values['new']}", file=output)
    
    print("\n", file=output)
```

#### 3.3 Update the primary print_to method to include differences

Modify the `print_to` method in theory implementations:

```python
def print_to(self, default_settings, example_name, theory_name, print_constraints=None, save_constraints=False, output=sys.__stdout__):
    """Print the model details to the specified output stream."""
    # Existing printing code...
    
    # Print differences if this is not the first model and differences exist
    if hasattr(self, 'model_differences') and self.model_differences:
        self.print_model_differences(output)
    
    # Continue with existing printing...
```

### 4. Settings Integration

#### 4.1 Add a setting to control difference display

```python
def _get_iteration_settings(self):
    """Extract and validate iteration settings from BuildExample."""
    # Existing settings code...
    
    # Add support for print_differences setting
    validated_settings['print_differences'] = settings.get('print_differences', True)
    
    return validated_settings
```

#### 4.2 Update the iteration logic to respect the setting

```python
def iterate(self):
    """Find multiple distinct models up to max_iterations."""
    # Existing iteration code...
    
    # Consider print_differences setting when creating model structures
    print_differences = self.settings.get('print_differences', True)
    
    while self.current_iteration < self.max_iterations:
        # Existing iteration logic...
        
        # Only compute and store differences if enabled
        if print_differences:
            current_components = self._extract_model_components(new_model)
            differences = self._compute_model_differences(
                current_components, 
                self.previous_model_components
            )
            new_structure.model_differences = differences
            self.previous_model_components = current_components
        
        # Continue with existing logic...
```

## Implementation Plan

### Phase 1: Core Difference Tracking

1. Update ModelIterator to track previous model components
2. Implement _compute_model_differences method
3. Modify _create_new_model_structure to store differences

### Phase 2: Model Structure Integration

1. Add print_model_differences method to ModelStructure classes
2. Update print_to methods to include difference display
3. Ensure differences are properly serialized/deserialized

### Phase 3: Settings and Configuration

1. Add print_differences setting to control the feature
2. Add documentation for the new settings
3. Implement proper error handling for difference tracking

### Phase 4: Testing

1. Create test cases that verify difference detection
2. Test with various theory implementations
3. Verify formatting and display across different output targets

## Testing Approach

1. **Unit Tests**:
   - Test difference detection with synthetic model components
   - Verify correct identification of added, changed, and removed values
   - Test edge cases like empty models or models with different component sets

2. **Integration Tests**:
   - Test with real models from different theories
   - Verify difference tracking through multiple iterations
   - Test interaction with settings system

3. **Validation Tests**:
   - Verify readability and usefulness of difference displays
   - Check that differences are meaningful for model understanding

## Error Handling

Following the project's philosophy:

1. Difference tracking will be non-essential - errors won't prevent model finding
2. Clear error messages will be provided if difference computation fails
3. Defaults will show all model information if difference tracking is unavailable

## Backward Compatibility

The implementation will:

1. Make difference display optional and default to enabled
2. Preserve existing model iteration behavior for clients not using the feature
3. Keep the same method signatures for public API functions

## Conclusion

This implementation plan outlines a structured approach to enhancing the ModelIterator with difference tracking capabilities. When implemented, it will provide users with clear insights into how each model differs from the previous one, making it easier to understand the semantic space of logical theories and formulas.