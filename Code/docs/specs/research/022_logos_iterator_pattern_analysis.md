# Logos Iterator Pattern Analysis

**Date**: 2025-01-15  
**Type**: Research Report  
**Status**: Complete  
**Purpose**: Understand logos theory iterator implementation to guide exclusion/imposition fixes

## Executive Summary

The logos theory uses a sophisticated iterator pattern that properly integrates with BuildModule's generator interface. Key findings:
1. Uses `iterate_example_generator` with special attributes for detection
2. Extends `BaseModelIterator` from `iterate.core`
3. Uses generic difference keys (`world_changes`, `possible_changes`) in display
4. Yields from `iterator.iterate_generator()` for incremental display
5. Generator interface enables proper progress tracking and ITERATION REPORT

## Implementation Pattern

### 1. Generator Function Structure (logos/iterate.py)

```python
def iterate_example_generator(example, max_iterations=None):
    """Generator version that yields models incrementally."""
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator
    iterator = LogosModelIterator(example)
    
    # Store iterator for debug messages
    example._iterator = iterator
    
    # Use the generator interface
    yield from iterator.iterate_generator()

# Mark for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator
```

### 2. Iterator Class Structure

```python
class LogosModelIterator(BaseModelIterator):
    """Extends BaseModelIterator with theory-specific logic."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Theory-specific difference calculation."""
        # Returns dict with theory-specific keys
        return {
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []},
            "verify": {},
            "falsify": {}
        }
```

### 3. Model Structure Display (semantic.py)

```python
class LogosModelStructure:
    def print_model_differences(self, output=sys.stdout):
        """Uses generic keys from DifferenceCalculator."""
        diffs = self.model_differences
        
        # Generic keys from DifferenceCalculator
        if diffs.get('world_changes', {}).get('added'):
            # Display world changes
        
        if diffs.get('possible_changes', {}).get('added'):
            # Display possible state changes
```

## Key Integration Points

### 1. BuildModule Detection

BuildModule checks for generator interface:
```python
if hasattr(theory_iterate_example, '__wrapped__') and \
   hasattr(theory_iterate_example.__wrapped__, 'returns_generator'):
    # Use generator interface
    self._run_generator_iteration(...)
else:
    # Fallback to list-based iteration
```

### 2. Progress Integration

Generator interface enables:
- Unified progress tracking via `example._unified_progress`
- Incremental model display as found
- Proper ITERATION REPORT at end

### 3. Difference Calculation Flow

1. `DifferenceCalculator` provides generic differences with keys:
   - `world_changes` (added/removed lists)
   - `possible_changes` (added/removed lists)

2. Theory-specific `_calculate_differences` adds custom keys:
   - `verify`, `falsify` (logos)
   - `exclusions`, `verifications` (exclusion)
   - `imposition_relations` (imposition)

3. Display method must handle BOTH generic and theory-specific keys

## Critical Differences from Exclusion/Imposition

### Exclusion Theory Issues:
1. **No generator interface** - only has `iterate_example`
2. **Key mismatch** - expects `worlds`/`verifications` but gets `world_changes`/`possible_changes`
3. **No BaseModelIterator merge** - theory-specific diffs not merged with generic

### Solution Pattern:

1. **Add generator wrapper**:
   ```python
   def iterate_example_generator(example, max_iterations=None):
       # Same pattern as logos
       from model_checker.iterate import BaseModelIterator
       
       # Use base iterator for proper flow
       iterator = BaseModelIterator(example)
       yield from iterator.iterate_generator()
   ```

2. **Fix display to use correct keys**:
   ```python
   def print_model_differences(self, output=sys.stdout):
       # Use 'world_changes' not 'worlds'
       worlds = diffs.get('world_changes', {})
       # Use 'possible_changes' not 'possible_states'
       possible = diffs.get('possible_changes', {})
   ```

## Important Notes

1. **Don't use theory-specific iterator in generator**: 
   - Logos uses `LogosModelIterator` in non-generator `iterate_example`
   - But uses base `BaseModelIterator` would work for generator to avoid issues

2. **Iterator provides incremental yielding**:
   - `iterate_generator()` yields models as found
   - Maintains internal state for constraints
   - Enables proper progress and reporting

3. **Theory-specific differences are secondary**:
   - Generic differences always present
   - Theory-specific are optional additions
   - Display must handle both

## Recommendations for Implementation

1. **Phase 1 Priority**: Add generator interface exactly like logos
2. **Use BaseModelIterator directly**: Avoid complexity of theory-specific iterator in generator
3. **Fix key names**: Update display methods to use generic keys
4. **Test incremental display**: Verify models appear as found, not all at end
5. **Verify ITERATION REPORT**: Should appear after all models with timing details