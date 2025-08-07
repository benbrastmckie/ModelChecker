# Implementation Plan 009: Fresh ModelConstraints for Iterator

## Overview

This plan details the implementation of Approach 1 from the iterator fix research: creating fresh ModelConstraints for each iterated model. This ensures that constraints always match the model being evaluated, guaranteeing that premises remain true and conclusions remain false across all iterations.

## Objectives

1. **Primary**: Fix iterator constraint preservation issue where MODEL 2+ violate countermodel requirements
2. **Maintain**: Backward compatibility with existing theory implementations
3. **Preserve**: Iterator performance and capability to find diverse models
4. **Ensure**: Clean architecture with clear separation of concerns

## Technical Design

### Core Changes

#### 1. Extend ModelStructure Interface

Add methods to ModelStructure to support constraint regeneration:

```python
class ModelStructure:
    def get_verify_falsify_state(self):
        """Extract current verify/falsify function values for all sentence letters.
        
        Returns:
            dict: Mapping of (state, letter) -> (verify_value, falsify_value)
        """
        state_map = {}
        for letter in self.sentence_letters:
            for state in range(2**self.N):
                verify_val = self.z3_model.eval(
                    self.semantics.verify(state, letter.sentence_letter),
                    model_completion=True
                )
                falsify_val = self.z3_model.eval(
                    self.semantics.falsify(state, letter.sentence_letter),
                    model_completion=True
                )
                state_map[(state, letter.sentence_letter)] = (verify_val, falsify_val)
        return state_map
    
    def create_constrained_semantics(self, verify_falsify_state):
        """Create semantics instance with specific verify/falsify values.
        
        Args:
            verify_falsify_state: Dict from get_verify_falsify_state()
            
        Returns:
            Semantics instance with constrained functions
        """
        semantics = self.semantics.__class__(self.settings)
        # Initialize with specific verify/falsify values
        semantics.initialize_from_state(verify_falsify_state)
        return semantics
```

#### 2. Modify Iterator's _build_new_model_structure

Replace the current method with one that creates fresh constraints:

```python
def _build_new_model_structure(self, z3_model):
    """Build a new model structure with fresh constraints.
    
    This creates new ModelConstraints using the current model's verify/falsify
    functions, ensuring constraint consistency.
    """
    try:
        # Extract settings and theory components
        original_build = self.build_example
        settings = original_build.settings
        
        # Create fresh syntax (reuses sentence parsing)
        syntax = Syntax(
            list(original_build.syntax.premises_list),
            list(original_build.syntax.conclusions_list),
            original_build.semantic_theory.get("operators")
        )
        
        # Create new semantics with current model's functions
        semantics_class = original_build.semantic_theory["semantics"]
        semantics = semantics_class(settings)
        
        # CRITICAL: Initialize semantics with current model's verify/falsify
        if hasattr(original_build.model_structure, 'get_verify_falsify_state'):
            # For MODEL 2+, constrain to current model's functions
            verify_falsify_state = self._extract_verify_falsify_from_z3(z3_model)
            semantics.initialize_from_state(verify_falsify_state)
        
        # Create fresh ModelConstraints with current context
        proposition_class = original_build.semantic_theory["proposition"]
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            proposition_class
        )
        
        # Create new model structure
        model_class = original_build.semantic_theory["model"]
        new_structure = model_class(model_constraints, settings)
        
        # Set the Z3 model
        new_structure.z3_model = z3_model
        new_structure.z3_model_status = True
        new_structure.satisfiable = True
        new_structure.solved = True
        
        # Initialize Z3-dependent attributes
        self._initialize_z3_dependent_attributes(new_structure, z3_model)
        
        # Interpret sentences with fresh constraints
        new_structure.interpret(new_structure.premises + new_structure.conclusions)
        
        return new_structure
        
    except Exception as e:
        logger.error(f"Error building new model structure: {str(e)}")
        import traceback
        logger.error(f"Full traceback:\n{traceback.format_exc()}")
        return None

def _extract_verify_falsify_from_z3(self, z3_model):
    """Extract verify/falsify values from Z3 model.
    
    Returns:
        dict: Mapping of (state, letter) -> (verify_value, falsify_value)
    """
    state_map = {}
    original_constraints = self.build_example.model_constraints
    
    for letter in original_constraints.sentence_letters:
        for state in range(2**original_constraints.semantics.N):
            verify_val = z3_model.eval(
                original_constraints.semantics.verify(state, letter),
                model_completion=True
            )
            falsify_val = z3_model.eval(
                original_constraints.semantics.falsify(state, letter),
                model_completion=True
            )
            state_map[(state, letter)] = (
                z3.is_true(verify_val),
                z3.is_true(falsify_val)
            )
    
    return state_map
```

#### 3. Update Semantics Base Class

Add initialization method to SemanticDefaults:

```python
class SemanticDefaults:
    def initialize_from_state(self, verify_falsify_state):
        """Initialize verify/falsify functions from a saved state.
        
        This is used by the iterator to ensure MODEL 2+ use
        their own verify/falsify functions when building constraints.
        
        Args:
            verify_falsify_state: Dict mapping (state, letter) -> (verify, falsify)
        """
        # Store state for use in constraint generation
        self._verify_falsify_state = verify_falsify_state
        
        # Override verify/falsify to use stored values
        self._original_verify = self.verify
        self._original_falsify = self.falsify
        
        def constrained_verify(state, letter):
            key = (state, letter)
            if key in self._verify_falsify_state:
                return self._verify_falsify_state[key][0]
            return self._original_verify(state, letter)
        
        def constrained_falsify(state, letter):
            key = (state, letter)
            if key in self._verify_falsify_state:
                return self._verify_falsify_state[key][1]
            return self._original_falsify(state, letter)
        
        # Replace methods
        self.verify = constrained_verify
        self.falsify = constrained_falsify
```

#### 4. Modify Iterator Initialization

Update the iterator to track necessary components:

```python
def __init__(self, build_example, max_iterations=3):
    # ... existing initialization ...
    
    # Store theory components for model building
    self.semantic_theory = build_example.semantic_theory
    self.premises_list = list(build_example.syntax.premises_list)
    self.conclusions_list = list(build_example.syntax.conclusions_list)
    
    # Track whether we need fresh constraints
    self.use_fresh_constraints = build_example.settings.get(
        'iterator_fresh_constraints', True
    )
```

### Implementation Phases

#### Phase 1: Core Infrastructure (2 days)

1. **Add helper methods to ModelStructure base class**
   - `get_verify_falsify_state()`
   - `create_constrained_semantics()`
   - Update all theory-specific ModelStructure classes if needed

2. **Extend SemanticDefaults**
   - Add `initialize_from_state()` method
   - Ensure all semantics classes inherit properly
   - Add unit tests for state initialization

3. **Add configuration option**
   - Add `iterator_fresh_constraints` setting (default True)
   - Allow fallback to old behavior for testing

#### Phase 2: Iterator Refactoring (3 days)

1. **Refactor `_build_new_model_structure`**
   - Implement fresh constraint generation
   - Add `_extract_verify_falsify_from_z3` helper
   - Ensure proper error handling

2. **Update iterator initialization**
   - Store necessary theory components
   - Track configuration preferences
   - Preserve backward compatibility

3. **Optimize performance**
   - Cache operator instances where possible
   - Minimize redundant parsing
   - Profile constraint generation time

#### Phase 3: Testing & Validation (2 days)

1. **Unit tests**
   - Test verify/falsify extraction
   - Test semantics initialization from state
   - Test fresh constraint generation

2. **Integration tests**
   - Verify MODEL 2+ have true premises
   - Verify MODEL 2+ have false conclusions
   - Test with all theories (logos, exclusion, imposition)
   - Check performance impact

3. **Edge case tests**
   - Empty premises/conclusions
   - Single atomic sentences
   - Complex nested formulas
   - Maximum iteration counts

#### Phase 4: Documentation & Cleanup (1 day)

1. **Update documentation**
   - Update iterate/README.md with new behavior
   - Document the fresh constraints approach
   - Add configuration options to docs

2. **Add migration notes**
   - Document change in findings/
   - Update any affected examples
   - Note performance considerations

## Testing Strategy

### Test Cases

1. **Minimal Atomic Test**
   ```python
   premises = ['A']
   conclusions = []
   settings = {'iterate': 3, 'N': 2}
   # Verify all 3 models have A true at evaluation world
   ```

2. **Complex Formula Test**
   ```python
   premises = ['(A \\wedge B)', '\\neg C']
   conclusions = ['(A \\rightarrow C)']
   settings = {'iterate': 5, 'N': 3}
   # Verify all models maintain truth values
   ```

3. **Theory Comparison Test**
   ```python
   # Run same test across logos, exclusion, imposition
   # Verify consistent behavior
   ```

### Performance Benchmarks

- Measure time for 10 iterations before/after
- Track memory usage growth
- Profile constraint generation hotspots

### Validation Criteria

1. **Correctness**: All MODEL 2+ must have:
   - All premises true at evaluation world
   - All conclusions false at evaluation world
   - Valid model structure

2. **Performance**: 
   - No more than 2x slowdown for typical cases
   - Memory usage growth should be linear

3. **Compatibility**:
   - All existing tests must pass
   - Theory-specific features preserved

## Risk Mitigation

### Identified Risks

1. **Performance Degradation**
   - Mitigation: Add caching for operator instances
   - Fallback: Configuration to use old behavior

2. **Memory Usage**
   - Mitigation: Careful cleanup of old constraints
   - Monitor: Add memory profiling to tests

3. **Theory Compatibility**
   - Mitigation: Extensive testing with all theories
   - Gradual rollout with feature flag

### Rollback Plan

1. Keep `iterator_fresh_constraints` setting
2. Default to True but allow False for old behavior
3. Document how to revert if issues found

## Success Metrics

1. **Bug Fix**: No MODEL 2+ with false premises or true conclusions
2. **Performance**: Iterator completes within 2x original time
3. **Compatibility**: All existing tests pass
4. **Code Quality**: Clean, documented implementation

## Timeline

- **Days 1-2**: Core infrastructure
- **Days 3-5**: Iterator refactoring
- **Days 6-7**: Testing and validation
- **Day 8**: Documentation and cleanup

Total estimated time: 8 days

## Future Enhancements

1. **Lazy Constraint Generation**: Build constraints only when needed
2. **Constraint Caching**: Reuse structural constraints across iterations
3. **Parallel Model Generation**: Use multiple Z3 instances
4. **Smart Function Detection**: Only regenerate affected constraints

## Conclusion

This implementation plan provides a systematic approach to fixing the iterator constraint preservation issue by creating fresh ModelConstraints for each iteration. The solution maintains theoretical correctness while minimizing performance impact through careful design and optimization.