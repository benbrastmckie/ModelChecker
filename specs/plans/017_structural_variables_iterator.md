# Implementation Plan: Structural Variables for Model Iteration

## Overview

This plan details the implementation of Pure Z3 Structural Variables (Option 1 from research/010) to enable clean generation of structurally distinct models without referencing model objects or previous models directly in constraints.

**CRITICAL CLARIFICATION**: The structural variables are primarily for the ITERATOR's use in generating difference constraints. The changes should be concentrated in the `iterate/` directory, NOT in the core `models/` components.

## Goals

1. Enable iterator to track structural patterns of found models
2. Generate difference constraints using only Z3 variables (no model references)
3. Keep implementation isolated to iterator code
4. Ensure theory-agnostic implementation in `iterate/core.py`
5. NO BACKWARDS COMPATIBILITY - break compatibility freely for cleaner architecture

## Design Principles

- **Iterator-Focused**: Changes concentrated in `iterate/` directory
- **Minimal Core Changes**: Avoid modifying ModelConstraints if possible
- **Clean Separation**: Iterator tracks patterns independently
- **No Model References**: Constraints operate purely on Z3 variables
- **Fail Fast**: Let errors occur naturally, no masking with defaults
- **Test-Driven Development**: Write tests first to define behavior

## Implementation Approach Clarification

### Why Iterator-Focused?

The iterator needs to:
1. Extract structural patterns from found Z3 models
2. Generate constraints that exclude those patterns
3. Pass these constraints to Z3 for finding new models

This can be done entirely within the iterator by:
- Extracting patterns from the Z3 model directly
- Creating difference constraints based on semantic functions
- Adding these constraints to the solver

### What We're NOT Doing

We are NOT:
- Making ModelConstraints aware of iteration
- Adding permanent structural variables to all models
- Modifying core model checking logic
- Changing how models are built or interpreted

## Implementation Phases

### Phase 1: Create Pattern Extraction Utilities in Iterator

**Files to Create**:
- `src/model_checker/iterate/patterns.py`

**Implementation**:

```python
"""Utilities for extracting and comparing structural patterns from Z3 models."""

import z3
from typing import Dict, Any, List, Optional


class StructuralPattern:
    """Represents a structural pattern extracted from a Z3 model."""
    
    def __init__(self, model_constraints, z3_model):
        """Extract pattern from a Z3 model using model constraints."""
        self.pattern = self._extract_pattern(model_constraints, z3_model)
    
    def _extract_pattern(self, model_constraints, z3_model):
        """Extract structural information from Z3 model."""
        semantics = model_constraints.semantics
        pattern = {}
        
        # Count worlds and possible states
        all_states = list(range(2**semantics.N))
        pattern['num_worlds'] = sum(
            1 for state in all_states
            if z3.is_true(z3_model.eval(semantics.is_world(state), model_completion=True))
        )
        pattern['num_possible'] = sum(
            1 for state in all_states
            if z3.is_true(z3_model.eval(semantics.possible(state), model_completion=True))
        )
        
        # Record which states are worlds
        pattern['world_states'] = [
            state for state in all_states
            if z3.is_true(z3_model.eval(semantics.is_world(state), model_completion=True))
        ]
        
        # Record verify/falsify patterns for each letter
        pattern['verify'] = {}
        pattern['falsify'] = {}
        
        for letter in model_constraints.sentence_letters:
            letter_str = str(letter)
            pattern['verify'][letter_str] = [
                state for state in all_states
                if z3.is_true(z3_model.eval(semantics.verify(state, letter), model_completion=True))
            ]
            pattern['falsify'][letter_str] = [
                state for state in all_states
                if z3.is_true(z3_model.eval(semantics.falsify(state, letter), model_completion=True))
            ]
        
        return pattern
    
    def to_difference_constraint(self, semantics, sentence_letters):
        """Create Z3 constraint that excludes this exact pattern."""
        constraints = []
        all_states = list(range(2**semantics.N))
        
        # At least one world must be different
        world_differences = []
        for state in all_states:
            if state in self.pattern['world_states']:
                # This state is a world in our pattern, so require it not to be
                world_differences.append(z3.Not(semantics.is_world(state)))
            else:
                # This state is not a world in our pattern, so require it to be
                world_differences.append(semantics.is_world(state))
        
        # Or at least one verify/falsify must be different
        verify_differences = []
        for letter in sentence_letters:
            letter_str = str(letter)
            for state in all_states:
                if state in self.pattern['verify'].get(letter_str, []):
                    verify_differences.append(z3.Not(semantics.verify(state, letter)))
                if state in self.pattern['falsify'].get(letter_str, []):
                    verify_differences.append(z3.Not(semantics.falsify(state, letter)))
        
        # Require at least one difference
        return z3.Or(world_differences + verify_differences)


def create_structural_difference_constraint(model_constraints, previous_patterns):
    """Create constraint requiring difference from all previous patterns."""
    if not previous_patterns:
        return z3.BoolVal(True)
    
    # Must be different from ALL previous patterns
    difference_constraints = []
    for pattern in previous_patterns:
        diff_constraint = pattern.to_difference_constraint(
            model_constraints.semantics,
            model_constraints.sentence_letters
        )
        difference_constraints.append(diff_constraint)
    
    return z3.And(*difference_constraints)
```

**Tests**:

1. `src/model_checker/iterate/tests/test_patterns.py`:
```python
def test_extract_pattern_from_model():
    """Pattern extraction must capture structural information."""
    # Create a model with known structure
    # Extract pattern
    # Verify pattern contains expected information
    
def test_pattern_to_difference_constraint():
    """Pattern must generate constraint that excludes it."""
    # Create pattern
    # Generate difference constraint
    # Verify constraint excludes the pattern
    
def test_multiple_pattern_exclusion():
    """Multiple patterns must all be excluded."""
    # Create multiple patterns
    # Generate combined constraint
    # Verify all patterns excluded
```

### Phase 2: Update Iterator to Use Pattern-Based Constraints

**Files to Modify**:
- `src/model_checker/iterate/core.py`

**Changes**:

1. Import pattern utilities:
```python
from model_checker.iterate.patterns import StructuralPattern, create_structural_difference_constraint
```

2. Track patterns in `__init__`:
```python
def __init__(self, build_example):
    # ... existing initialization ...
    
    # Initialize pattern tracking
    self.found_patterns = []
    
    # Extract initial pattern
    initial_pattern = StructuralPattern(
        self.build_example.model_constraints,
        self.found_models[0]
    )
    self.found_patterns.append(initial_pattern)
```

3. Replace `_create_extended_constraints`:
```python
def _create_extended_constraints(self):
    """Create extended constraints using pattern-based differences."""
    # Start with original constraints
    extended_constraints = list(self.original_constraints)
    
    # Add pattern-based difference constraint
    diff_constraint = create_structural_difference_constraint(
        self.build_example.model_constraints,
        self.found_patterns
    )
    extended_constraints.append(diff_constraint)
    
    return extended_constraints
```

4. Track patterns in `iterate` method:
```python
# After finding a new valid model
new_pattern = StructuralPattern(
    self.build_example.model_constraints, 
    new_model
)
self.found_patterns.append(new_pattern)
```

5. Simplify `_build_new_model_structure` (remove verify/falsify extraction):
```python
def _build_new_model_structure(self, z3_model):
    """Build a new model structure for display/interpretation."""
    # Simply create fresh ModelConstraints and structure
    # No need for complex state extraction
    # ... simplified implementation ...
```

**Tests**:

1. `src/model_checker/iterate/tests/test_iterator_patterns.py`:
```python
def test_iterator_uses_pattern_constraints():
    """Iterator must use pattern-based constraints."""
    # Create example with multiple models
    # Run iterator
    # Verify pattern constraints are used
    
def test_iterator_finds_structurally_distinct_models():
    """Iterator must find only structurally distinct models."""
    # Run iterator on example with known distinct models
    # Verify all found models are structurally different
```

### Phase 3: Remove Old Constraint Methods from Theory Iterators

**Files to Modify**:
- `src/model_checker/theory_lib/logos/iterate.py`
- Other theory iterators

**Changes**:

1. Remove these methods (no longer needed):
   - `_create_difference_constraint`
   - `_create_non_isomorphic_constraint`
   - `_create_stronger_constraint`

2. The base iterator now handles everything via patterns

### Phase 3.5: Ensure Each Theory Has iterate.py

**Requirement**: Each theory MUST have `iterate.py` to enable iteration.

**Minimal Implementation**:
```python
"""<Theory> iteration support."""

from model_checker.iterate.core import BaseModelIterator


class <Theory>ModelIterator(BaseModelIterator):
    """Iterator for <theory> theory."""
    pass  # All functionality in base class


def iterate_example(example, max_iterations=None):
    """Entry point for iteration."""
    if max_iterations is not None:
        example.settings['iterate'] = max_iterations
    
    iterator = <Theory>ModelIterator(example)
    return iterator.iterate()
```

### Phase 4: Test with Real Examples

**Use dev_cli.py to validate**:
```bash
# Test iteration works correctly
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

## What This Plan is NOT

This plan does NOT:
- Add structural variables to ModelConstraints
- Modify the core model checking pipeline
- Change how models are built or interpreted
- Add any permanent changes to model structure

This plan ONLY:
- Adds pattern tracking to the iterator
- Changes how the iterator generates difference constraints
- Keeps all changes isolated to the iteration system

## Success Criteria

1. Iterator finds structurally distinct models without model references
2. All changes isolated to `iterate/` directory
3. No modifications to ModelConstraints or core model checking
4. Pattern-based constraints work for all theories
5. Clean, maintainable iterator code

## Timeline

1. **Day 1**: Implement pattern extraction utilities
2. **Day 2**: Update iterator to use patterns
3. **Day 3**: Test with all theories
4. **Day 4**: Documentation and cleanup

This implementation keeps the structural pattern tracking where it belongs - in the iterator that needs it for finding distinct models.