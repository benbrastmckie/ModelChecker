# Exclusion Theory-Specific Differences Not Displayed

**Date**: 2025-01-15  
**Type**: Research Report  
**Status**: Complete  
**Component**: Exclusion theory iterator difference calculation

## Executive Summary

The exclusion theory iterator (`ExclusionModelIterator`) correctly calculates theory-specific differences (verification changes, witness changes, exclusion relation changes) but these are never displayed because:

1. `BaseModelIterator` uses `DifferenceCalculator` which only provides generic differences
2. The theory-specific `_calculate_differences` method is defined but never called
3. The display method (`print_model_differences`) only shows generic keys, not theory-specific ones

## Current Architecture

### 1. Difference Calculation Flow

```
BaseModelIterator.iterate_generator()
  └─> DifferenceCalculator.calculate_differences()
       ├─> _calculate_basic_differences() → world_changes, possible_changes
       ├─> _calculate_semantic_differences() → (not implemented)
       └─> _calculate_state_differences() → (basic state info)
```

The theory-specific `ExclusionModelIterator._calculate_differences()` is never called.

### 2. ExclusionModelIterator Implementation

```python
class ExclusionModelIterator(LogosModelIterator):
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences including witness-specific changes."""
        differences = {
            "verifications": {},      # State verification changes
            "witnesses": {},          # Witness function changes
            "exclusions": {}          # Exclusion relation changes
        }
        # ... calculates theory-specific differences ...
        return differences
```

### 3. Display Method Limitations

In `WitnessStructure.print_model_differences()`:
```python
# Note: Verification, witness, and exclusion relation differences are tracked
# in the theory-specific iterator but not available through the generic calculator.
# For now, we display the basic structural differences.
```

## Root Cause Analysis

The BaseModelIterator architecture doesn't provide a hook for theory-specific iterators to contribute their differences. The flow is:

1. BaseModelIterator calls DifferenceCalculator (generic)
2. Stores result in model_structure.model_differences
3. Display method only sees generic differences

The theory-specific `_calculate_differences` exists but is orphaned code.

## Solution Options

### Option 1: Override iterate_generator in ExclusionModelIterator
Override the generator to merge theory-specific differences:

```python
def iterate_generator(self):
    """Override to add theory-specific differences."""
    for model in super().iterate_generator():
        # Calculate theory-specific differences
        if len(self.model_structures) >= 2:
            theory_diffs = self._calculate_differences(
                model, self.model_structures[-2]
            )
            # Merge with existing differences
            if hasattr(model, 'model_differences'):
                model.model_differences.update(theory_diffs)
        yield model
```

### Option 2: Extend BaseModelIterator with Hook
Add a method in BaseModelIterator that subclasses can override:

```python
# In BaseModelIterator
def _calculate_theory_specific_differences(self, new_structure, previous_structure):
    """Hook for theory-specific difference calculation."""
    if hasattr(self, '_calculate_differences'):
        return self._calculate_differences(new_structure, previous_structure)
    return {}

# Then merge in iterate_generator:
theory_diffs = self._calculate_theory_specific_differences(new_structure, previous_structure)
differences.update(theory_diffs)
```

### Option 3: Update Display to Show Theory-Specific Keys
Enhance `print_model_differences` to check for and display theory-specific keys:

```python
# After displaying generic differences
if 'exclusions' in diffs:
    # Display exclusion changes
if 'verifications' in diffs:
    # Display verification changes
if 'witnesses' in diffs:
    # Display witness changes
```

## Recommendation

Implement **Option 1** (Override iterate_generator) because:
1. Minimal changes required
2. Follows existing patterns (logos does similar overrides)
3. Preserves BaseModelIterator architecture
4. Theory keeps control of its specific logic

Combined with updating the display method to show the additional keys when present.

## Impact on Witness Functions

The witness function display is particularly affected because:
1. `_calculate_witness_differences` currently returns empty results
2. Witness predicates are stored in the registry, not easily accessible
3. Need to extract witness function mappings from the Z3 model

To display witness function changes, need to:
1. Access witness predicates from the registry
2. Evaluate them in both old and new models
3. Format the function mappings for display

## Testing Implications

Need to verify:
1. Theory-specific differences are calculated
2. They're merged with generic differences
3. Display shows all difference types
4. No impact on other theories (logos, imposition)