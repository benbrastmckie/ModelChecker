# Plan 040: Revised Iterator Generator Implementation

## Overview

This plan revises Plan 038 based on comprehensive research and analysis of the current iterator architecture. After studying the codebase, we've identified that the iterator's fundamental design requires maintaining complete model history for constraint generation and isomorphism detection. This plan proposes a **hybrid approach** that provides generator-like behavior while maintaining necessary state internally.

**Key Insight**: The iterator MUST maintain complete history regardless of interface due to:
- Constraint generation requiring all previous models
- Isomorphism checking against all previous models  
- Progress tracking needing total count
- Difference calculation requiring previous model access

## Selected Approach: Hybrid Generator with Internal State

Instead of a pure generator that discards state, we'll implement a hybrid approach:
1. Maintain internal model history (required for correctness)
2. Provide generator interface for incremental model delivery
3. Allow BuildModule to display models as they're found
4. Keep backward compatibility with list-based interface

This approach balances the benefits of real-time display with the architectural requirements.

## Research and Design Phase

### Current Architecture Analysis

1. **Batch Collection Flow**:
   ```
   iterate() → finds all models → returns List[ModelStructure]
   BuildModule → receives list → displays each model
   ```

2. **Critical Dependencies**:
   - Constraint generation: Needs ALL previous models
   - Isomorphism detection: Compares against ALL previous models
   - Progress tracking: Shows total models found
   - Difference calculation: Accesses previous model by index

3. **Theory Integration Points**:
   - Each theory provides `iterate_example(example, max_iterations)`
   - Returns complete list of ModelStructure objects
   - BuildModule calls theory-specific function directly

### Design Decisions

1. **Internal State Preservation**: Keep `model_structures` list internally
2. **Dual Interface**: Support both generator and list return
3. **Progress Integration**: Update progress as models are yielded
4. **Minimal Breaking Changes**: Preserve existing functionality

## Implementation Plan

### Phase 1: Core Iterator Generator Support (Priority: Critical) ✓ COMPLETE

**Completion Date**: 2025-08-14  
**Commit**: 3d08c40d

**Objective**: Add generator interface to BaseModelIterator while maintaining internal state

**Tests to Write First**:

1. Create `src/model_checker/iterate/tests/test_generator_interface.py`:
```python
import pytest
from model_checker.iterate.core import BaseModelIterator

class TestGeneratorInterface:
    """Test hybrid generator interface."""
    
    def test_iterate_generator_yields_incrementally(self):
        """Test that iterate_generator yields models one at a time."""
        iterator = self._create_test_iterator(max_iterations=3)
        gen = iterator.iterate_generator()
        
        # First model should be yielded immediately
        model1 = next(gen)
        assert model1 is not None
        # Internal state should have exactly one model
        assert len(iterator.model_structures) == 1
        
        # Second model
        model2 = next(gen)
        assert model2 is not None
        assert len(iterator.model_structures) == 2
        
    def test_generator_maintains_history(self):
        """Test that generator maintains complete history internally."""
        iterator = self._create_test_iterator(max_iterations=3)
        models = list(iterator.iterate_generator())
        
        # Should have complete history for constraint generation
        assert len(iterator.found_models) == 3
        assert len(iterator.model_structures) == 3
        
    def test_backward_compatibility(self):
        """Test that iterate() still returns complete list."""
        iterator = self._create_test_iterator(max_iterations=3)
        models = iterator.iterate()
        
        assert isinstance(models, list)
        assert len(models) == 3
```

2. Create baseline captures:
```bash
# Capture current behavior before changes
./dev_cli.py src/model_checker/theory_lib/logos/examples.py > docs/specs/baselines/iterator_batch_baseline.txt 2>&1
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py > docs/specs/baselines/iterator_batch_iterate3.txt 2>&1
```

**Implementation Tasks**:

1. **Add iterate_generator method** to `BaseModelIterator`:
```python
def iterate_generator(self):
    """Generator version of iterate that yields models incrementally.
    
    Yields:
        ModelStructure: Each model as it's found
        
    Note:
        Internal state (model_structures, found_models) is still maintained
        for constraint generation and isomorphism checking.
    """
    try:
        # Same iteration logic as iterate()
        while len(self.model_structures) < self.max_iterations:
            # ... existing iteration logic ...
            
            if not is_isomorphic:
                self.found_models.append(new_model)
                self.model_structures.append(new_structure)
                
                # YIELD instead of just collecting
                yield new_structure
                
                # Update progress after yield
                if self.search_progress:
                    self.search_progress.complete_search(model_number, found=True)
                    
    finally:
        self.progress.finish()
```

2. **Update iterate() to use generator internally**:
```python
def iterate(self):
    """Find multiple distinct models up to max_iterations.
    
    Returns:
        list: All found ModelStructure objects
    """
    # Consume generator to build list for backward compatibility
    return list(self.iterate_generator())
```

**Success Criteria**:
- [x] Generator yields models incrementally
- [x] Internal state properly maintained
- [x] Backward compatibility preserved
- [x] All existing tests pass

**Validation Protocol**:
```bash
# Method 1: Test runner
./run_tests.py --package --components iterate -v

# Method 2: CLI validation
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
diff docs/specs/baselines/iterator_batch_baseline.txt current_output.txt
```

### Phase 2: BuildModule Generator Integration (Priority: Critical) ✓ COMPLETE

**Completion Date**: 2025-08-14  
**Commit**: 3d08c40d

**Objective**: Update BuildModule to consume generator for real-time display

**Tests to Write First**:

1. Add to `src/model_checker/builder/tests/test_iteration_display.py`:
```python
def test_displays_models_incrementally(self):
    """Test that models are displayed as they're found."""
    # Mock stdout to capture output timing
    # Verify MODEL headers appear with proper timing
    pass
    
def test_progress_synchronized_with_display(self):
    """Test progress completes before each model display."""
    # Verify progress bar shows before MODEL header
    pass
```

**Implementation Tasks**:

1. **Update _run_batch_mode** in `builder/module.py`:
```python
# After line ~750 where iterate_example is called
if hasattr(theory_iterate_example, '__wrapped__'):
    # New generator interface
    model_generator = theory_iterate_example(example, max_iterations=iterate_count)
    
    # Process first model (already displayed)
    try:
        first_model = next(model_generator)
    except StopIteration:
        # No additional models found
        return
    
    # Process remaining models as they're yielded
    distinct_count = 1
    for i, structure in enumerate(model_generator, start=2):
        if not hasattr(structure, '_is_isomorphic') or not structure._is_isomorphic:
            distinct_count += 1
            
            # Calculate differences immediately
            # ... existing difference calculation ...
            
            # Print differences
            # ... existing difference printing ...
            
            # Print model header
            print(f"\nMODEL {distinct_count}/{iterate_count}")
            
            # Display model immediately
            example.model_structure = structure
            self._capture_and_save_output(example, example_name, theory_name, model_num=distinct_count)
else:
    # Fallback to list-based processing
    # ... existing code ...
```

2. **Add generator detection**:
```python
def _is_generator_interface(self, iterate_func):
    """Check if iterate function supports generator interface."""
    # Check for generator return type hint or attribute
    return hasattr(iterate_func, '__wrapped__') and \
           hasattr(iterate_func.__wrapped__, 'returns_generator')
```

**Success Criteria**:
- [x] Models display as found (not batched)
- [x] Progress bars show before each model
- [x] Differences calculated and shown correctly (header shown, content needs fix)
- [x] Summary statistics still accurate

### Phase 3: Theory Migration - Logos (Priority: High) ✓ COMPLETE

**Completion Date**: 2025-08-14  
**Commit**: 3d08c40d

**Objective**: Add generator support to logos theory

**Tests to Write First**:

1. Create `src/model_checker/theory_lib/logos/tests/test_iterate_generator.py`:
```python
def test_logos_generator_interface():
    """Test logos supports generator iteration."""
    example = create_test_example()
    gen = iterate_example_generator(example, max_iterations=3)
    
    models = []
    for model in gen:
        models.append(model)
        # Verify incremental yielding
        print(f"Yielded model {len(models)}")
```

**Implementation Tasks**:

1. **Create generator wrapper** in `logos/iterate.py`:
```python
def iterate_example_generator(example, max_iterations=None):
    """Generator version of iterate_example.
    
    Yields:
        ModelStructure: Each model as found
    """
    if max_iterations is not None:
        example.settings['iterate'] = max_iterations
    
    iterator = LogosModelIterator(example)
    yield from iterator.iterate_generator()

# Mark as generator interface
iterate_example_generator.returns_generator = True
```

2. **Update __init__.py exports**:
```python
__all__ = [
    'iterate_example',
    'iterate_example_generator',  # New export
    # ... other exports
]
```

**Success Criteria**:
- [x] Generator interface available
- [x] Backward compatibility maintained
- [x] Theory-specific features preserved

### Phase 4: Progress System Updates (Priority: Medium - DEFERRED)

**Note**: After research, we've decided to defer the unified progress system to a future enhancement. The current dual-system approach (spinner for initial, progress bar for iteration) works adequately.

**Objective**: Future unified progress system (not immediate priority)

**Tests to Write First**:

1. Update `src/model_checker/output/progress/tests/test_generator_progress.py`:
```python
def test_progress_updates_per_yield():
    """Test progress updates as models are yielded."""
    # Mock progress system
    # Verify start_search/complete_search called at right times
```

**Implementation Tasks**:

1. **Update progress calls in iterate_generator**:
```python
# In BaseModelIterator.iterate_generator()
if self.search_progress:
    self.search_progress.start_search(model_number)

# ... model finding logic ...

if not is_isomorphic:
    # Complete search BEFORE yielding
    if self.search_progress:
        self.search_progress.complete_search(model_number, found=True)
    
    yield new_structure
```

2. **Suppress duplicate progress** in BuildModule:
```python
# Set flag to prevent iterator from showing progress
if iterate_count > 1 and use_generator:
    example._suppress_iterator_progress = True
```

**Success Criteria**:
- [ ] Progress bars appear before models
- [ ] No duplicate progress displays
- [ ] Timing accurate for each model

### Phase 5: Theory Migration - Remaining (Priority: Medium)

**Objective**: Add generator support to bimodal, exclusion, imposition theories

**Implementation Pattern** (for each theory):

1. Create `iterate_example_generator` function
2. Mark with `returns_generator = True`
3. Update `__init__.py` exports
4. Test generator behavior

**Validation Protocol**:
```bash
# Test each theory
for theory in bimodal exclusion imposition; do
    echo "=== Testing $theory ==="
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
done
```

### Phase 6: Comprehensive Testing (Priority: High)

**Test Categories**:

1. **Performance Comparison**:
```python
def test_generator_performance():
    """Ensure generator doesn't degrade performance."""
    # Time batch vs generator approaches
    # Should be within 5% of each other
```

2. **Memory Usage**:
```python
def test_memory_efficiency():
    """Verify memory usage is reasonable."""
    # Even though we maintain history, verify no leaks
```

3. **Edge Cases**:
   - No models found
   - Single model only
   - Timeout during iteration
   - Isomorphic models only

**Success Criteria**:
- [ ] All tests pass
- [ ] Performance within 5% of baseline
- [ ] No memory leaks
- [ ] Edge cases handled correctly

### Phase 7: Documentation and Cleanup (Priority: Low)

**Documentation Updates**:

1. Update `iterate/README.md` with generator interface
2. Add examples of using generator interface
3. Document hybrid approach rationale

**Cleanup Tasks**:
- Remove any debug code
- Ensure consistent naming
- Update type hints

## Risk Analysis

### Identified Risks

1. **Backward Compatibility**:
   - **Risk**: Breaking existing code expecting lists
   - **Mitigation**: Dual interface approach
   - **Validation**: Comprehensive backward compatibility tests

2. **Performance Impact**:
   - **Risk**: Generator overhead affects performance
   - **Mitigation**: Benchmark before/after
   - **Validation**: Performance tests with large examples

3. **Progress Synchronization**:
   - **Risk**: Progress and model display out of sync
   - **Mitigation**: Careful ordering of operations
   - **Validation**: Visual inspection during testing

### Testing Strategy

1. **Baseline Comparison**: Save current output before changes
2. **Incremental Testing**: Test each phase independently
3. **Integration Testing**: Full system test after each phase
4. **Visual Validation**: Manual inspection of progress behavior

## Implementation Timeline

- Phase 1: ✓ COMPLETE (core generator support)
- Phase 2: ✓ COMPLETE (BuildModule integration)
- Phase 3: ✓ COMPLETE (Logos theory)
- Phase 3.5: ✓ COMPLETE (model differences fix)
- Phase 4: DEFERRED (Progress updates - will be addressed in unified progress system)
- Phase 5: PENDING (remaining theories)
- Phase 6: PENDING (comprehensive testing)
- Phase 7: PENDING (documentation)

**Completed: ~12 hours**
**Remaining: ~10 hours**

## Phase 3.5: Model Differences Fix (Priority: High) ✓ COMPLETE

**Completion Date**: 2025-08-14  
**Commit**: (pending)

**Objective**: Fix empty model differences display by properly storing differences on yielded models

**Root Cause**: Research revealed that differences ARE calculated before yielding, but they're stored on the model after it's added to the collection. The yielded model needs the differences stored on it before yielding.

**Implementation**:

1. **Update core.py iterate_generator** to store differences on the yielded model:
```python
# After calculating differences (line 293)
if len(self.model_structures) >= 2:
    differences = self.difference_calculator.calculate_differences(
        new_structure, self.model_structures[-2]
    )
else:
    differences = {}

# Store differences on the model structure for access
new_structure.model_differences = differences

# Add to statistics
self.stats.add_model(new_structure, differences)

logger.info(f"Found distinct model #{len(self.model_structures)}")

# YIELD the model with differences already attached
yield new_structure
```

2. **Fixed key mismatch in LogosModelStructure.print_model_differences**:
- DifferenceCalculator was using 'world_changes' and 'possible_changes'
- LogosModelStructure was expecting 'worlds' and 'possible_states'
- Updated print_model_differences to use the correct keys
- Also updated to handle 'atomic_changes' structure correctly

**Success Criteria**:
- [x] Model differences are stored on structure before yielding
- [x] Differences display with content (not just header)
- [x] Differences show what changed from previous model

## Known Issues

1. **Model Differences Display**: ✓ FIXED - Key mismatch resolved, differences now display correctly
2. **Initial Model Numbering**: ✓ FIXED - Initial model no longer shows numbering in batch mode
3. **Progress Bar Inconsistency**: DEFERRED - Will be addressed in unified progress system

## Implementation Notes

- Generator interface successfully implemented and working
- Models are displayed incrementally as found
- Progress bars work correctly (though visually inconsistent)
- All unit tests passing after fixes to import paths
- Model numbering now correct (2/4, 3/4, 4/4 instead of 1/4, 2/4, 3/4)
- Model differences properly displayed between iterations

## Alternative Approach Considered

**Pure Streaming Generator**: 
- Would require complete architectural redesign
- Loss of constraint generation capabilities
- Not feasible given current requirements

**Selected Hybrid Approach**:
- Maintains correctness
- Provides desired UX improvements
- Minimal breaking changes
- Achievable timeline

## Conclusion

This revised plan provides a pragmatic approach to achieving real-time model display while respecting the architectural constraints of the ModelChecker system. The hybrid generator approach maintains the necessary state for correct operation while providing the improved user experience of seeing models as they're discovered.

The implementation follows IMPLEMENT.md standards with:
- Clear phase breakdown
- Test-first development
- Dual validation methodology
- Comprehensive success criteria
- Risk mitigation strategies