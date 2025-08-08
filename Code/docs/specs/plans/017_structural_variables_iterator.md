# Implementation Plan: Structural Variables for Model Iteration

## Overview

This plan details the implementation of Pure Z3 Structural Variables (Option 1 from research/010) to enable clean generation of structurally distinct models without referencing model objects or previous models directly in constraints.

## Goals

1. Add Z3 structural variables to ModelConstraints that capture model structure
2. Link structural variables to semantic functions via constraints
3. Modify iterator to use structural variables for difference constraints
4. Ensure theory-agnostic implementation outside theory_lib/
5. NO BACKWARDS COMPATIBILITY - break compatibility freely for cleaner architecture

## Design Principles

- **NO BACKWARDS COMPATIBILITY**: Break compatibility for cleaner architecture
- **Separation of Concerns**: Structure and semantics clearly separated
- **Theory Agnostic**: Core implementation works for any theory
- **No Model References**: Constraints operate purely on Z3 variables
- **Fail Fast**: Let errors occur naturally, no masking with defaults
- **Test-Driven Development**: Write tests first to define behavior

## Implementation Phases

### Phase 1: Extend ModelConstraints with Structural Variables

**Files to Modify**:
- `src/model_checker/models/constraints.py`

**Changes**:

1. Update `__init__` to always include structural variables:
```python
def __init__(self, settings, syntax, semantics, proposition_class):
    # ... existing initialization ...
    
    # Always initialize structural variables for clean architecture
    self._initialize_structural_variables()
    self._link_structural_variables()
```

2. Add method to create structural variables:
```python
def _initialize_structural_variables(self):
    """Create Z3 variables to capture structural properties."""
    import z3
    
    self.structural_vars = {
        'num_worlds': z3.Int('num_worlds'),
        'num_possible': z3.Int('num_possible'),
        'world_pattern': z3.BitVec('world_pattern', 2**self.semantics.N),
        'possible_pattern': z3.BitVec('possible_pattern', 2**self.semantics.N),
    }
    
    # Add verify/falsify patterns for each sentence letter
    self.structural_vars['verify_patterns'] = {}
    self.structural_vars['falsify_patterns'] = {}
    
    for letter in self.sentence_letters:
        letter_str = str(letter)
        self.structural_vars['verify_patterns'][letter_str] = \
            z3.BitVec(f'verify_pattern_{letter_str}', 2**self.semantics.N)
        self.structural_vars['falsify_patterns'][letter_str] = \
            z3.BitVec(f'falsify_pattern_{letter_str}', 2**self.semantics.N)
```

3. Add method to link structural variables to semantic functions:
```python
def _link_structural_variables(self):
    """Add constraints linking structural variables to semantic functions."""
    import z3
    
    linking_constraints = []
    all_states = list(range(2**self.semantics.N))
    
    # Link num_worlds to is_world predicate
    linking_constraints.append(
        self.structural_vars['num_worlds'] == 
        z3.Sum([z3.If(self.semantics.is_world(state), 1, 0) for state in all_states])
    )
    
    # Link num_possible to possible predicate
    linking_constraints.append(
        self.structural_vars['num_possible'] == 
        z3.Sum([z3.If(self.semantics.possible(state), 1, 0) for state in all_states])
    )
    
    # Link world_pattern to encode which states are worlds
    for i, state in enumerate(all_states):
        bit = z3.Extract(i, i, self.structural_vars['world_pattern'])
        linking_constraints.append(
            bit == z3.If(self.semantics.is_world(state), 1, 0)
        )
    
    # Link verify/falsify patterns
    for letter in self.sentence_letters:
        letter_str = str(letter)
        verify_var = self.structural_vars['verify_patterns'][letter_str]
        falsify_var = self.structural_vars['falsify_patterns'][letter_str]
        
        for i, state in enumerate(all_states):
            verify_bit = z3.Extract(i, i, verify_var)
            falsify_bit = z3.Extract(i, i, falsify_var)
            
            linking_constraints.append(
                verify_bit == z3.If(self.semantics.verify(state, letter), 1, 0)
            )
            linking_constraints.append(
                falsify_bit == z3.If(self.semantics.falsify(state, letter), 1, 0)
            )
    
    # Add linking constraints to all_constraints
    self.structural_linking_constraints = linking_constraints
    self.all_constraints.extend(linking_constraints)
```

**Tests**:

1. `test_structural_variables_creation.py`:
```python
def test_model_constraints_has_structural_variables():
    """ModelConstraints must create structural variables."""
    # Test that structural_vars exists and contains expected keys
    
def test_linking_constraints_added():
    """Structural variables must be linked to semantic functions."""
    # Test that linking constraints are in all_constraints
    
def test_structural_vars_evaluate_correctly():
    """Structural variables must match semantic function values."""
    # After solving, verify structural vars match actual values
```

### Phase 2: Create Pattern Extraction Module

**Files to Create**:
- `src/model_checker/iterate/patterns.py`

**Implementation**:

```python
"""Utilities for extracting and comparing structural patterns from Z3 models."""

import z3
from typing import Dict, Any, List


class StructuralPattern:
    """Represents a structural pattern extracted from a Z3 model."""
    
    def __init__(self, pattern_dict: Dict[str, Any]):
        self.pattern = pattern_dict
        
    def to_constraint(self, structural_vars: Dict[str, Any]) -> z3.ExprRef:
        """Convert pattern to Z3 constraint for exact match."""
        constraints = []
        
        # Numeric constraints
        for key in ['num_worlds', 'num_possible']:
            if key in self.pattern and key in structural_vars:
                constraints.append(structural_vars[key] == self.pattern[key])
        
        # BitVector constraints
        for key in ['world_pattern', 'possible_pattern']:
            if key in self.pattern and key in structural_vars:
                constraints.append(structural_vars[key] == self.pattern[key])
        
        # Verify/falsify patterns
        for collection in ['verify_patterns', 'falsify_patterns']:
            if collection in self.pattern and collection in structural_vars:
                for letter, pattern in self.pattern[collection].items():
                    if letter in structural_vars[collection]:
                        constraints.append(
                            structural_vars[collection][letter] == pattern
                        )
        
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def to_exclusion_constraint(self, structural_vars: Dict[str, Any]) -> z3.ExprRef:
        """Convert pattern to constraint that excludes this exact pattern."""
        return z3.Not(self.to_constraint(structural_vars))


def extract_structural_pattern(z3_model: z3.ModelRef, 
                              model_constraints) -> StructuralPattern:
    """Extract structural pattern from a Z3 model."""
    if not hasattr(model_constraints, 'structural_vars'):
        raise AttributeError(
            "ModelConstraints does not have structural variables. "
            "Ensure ModelConstraints was properly initialized."
        )
    
    pattern = {}
    structural_vars = model_constraints.structural_vars
    
    # Extract numeric values
    for key in ['num_worlds', 'num_possible']:
        if key in structural_vars:
            pattern[key] = z3_model.eval(structural_vars[key], model_completion=True)
    
    # Extract BitVector patterns
    for key in ['world_pattern', 'possible_pattern']:
        if key in structural_vars:
            pattern[key] = z3_model.eval(structural_vars[key], model_completion=True)
    
    # Extract verify/falsify patterns
    for collection in ['verify_patterns', 'falsify_patterns']:
        if collection in structural_vars:
            pattern[collection] = {}
            for letter, var in structural_vars[collection].items():
                pattern[collection][letter] = z3_model.eval(var, model_completion=True)
    
    return StructuralPattern(pattern)


def create_structural_difference_constraint(current_vars: Dict[str, Any],
                                          previous_patterns: List[StructuralPattern]) -> z3.ExprRef:
    """Create constraint requiring difference from all previous patterns."""
    if not previous_patterns:
        return z3.BoolVal(True)
    
    # Must be different from ALL previous patterns
    exclusions = []
    for pattern in previous_patterns:
        exclusions.append(pattern.to_exclusion_constraint(current_vars))
    
    return z3.And(*exclusions)
```

**Tests**:

1. `test_pattern_extraction.py`:
```python
def test_extract_pattern_from_model():
    """Pattern extraction must capture all structural variables."""
    # Create model with known structure, extract pattern, verify values
    
def test_pattern_to_constraint_conversion():
    """Pattern must convert to exact matching constraint."""
    # Create pattern, convert to constraint, verify it matches original
    
def test_exclusion_constraint_excludes_pattern():
    """Exclusion constraint must prevent exact pattern match."""
    # Create pattern, generate exclusion, verify it excludes pattern
```

### Phase 3: Update Iterator to Use Structural Variables

**Files to Modify**:
- `src/model_checker/iterate/core.py`

**Changes**:

1. Update imports and initialization:
```python
def __init__(self, build_example):
    # ... existing initialization ...
    
    # Initialize pattern tracking
    self.found_patterns = []
    
    # Extract initial pattern - let it fail fast if no structural vars
    from model_checker.iterate.patterns import extract_structural_pattern
    initial_pattern = extract_structural_pattern(
        self.found_models[0], 
        self.build_example.model_constraints
    )
    self.found_patterns.append(initial_pattern)
```

2. Replace `_create_extended_constraints` completely:
```python
def _create_extended_constraints(self):
    """Create extended constraints using structural variables."""
    from model_checker.iterate.patterns import create_structural_difference_constraint
    
    # Start with original constraints
    extended_constraints = list(self.original_constraints)
    
    # Add structural difference constraint
    diff_constraint = create_structural_difference_constraint(
        self.build_example.model_constraints.structural_vars,
        self.found_patterns
    )
    extended_constraints.append(diff_constraint)
    
    return extended_constraints
```

3. Update pattern tracking in `iterate` method:
```python
# After finding a new valid model
from model_checker.iterate.patterns import extract_structural_pattern
new_pattern = extract_structural_pattern(new_model, self.build_example.model_constraints)
self.found_patterns.append(new_pattern)
```

4. Remove `_extract_verify_falsify_from_z3` and simplify `_build_new_model_structure`:
```python
def _build_new_model_structure(self, z3_model):
    """Build a new model structure for display/interpretation."""
    try:
        # Import required modules
        from model_checker.syntactic import Syntax
        from model_checker.models.constraints import ModelConstraints
        
        # Get original build example components
        original_build = self.build_example
        settings = original_build.settings.copy()
        
        # Create fresh syntax
        syntax = Syntax(
            original_build.premises,
            original_build.conclusions,
            original_build.semantic_theory.get("operators")
        )
        
        # Create new semantics
        semantics_class = original_build.semantic_theory["semantics"]
        semantics = semantics_class(settings)
        
        # Create fresh ModelConstraints
        proposition_class = original_build.semantic_theory["proposition"]
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            proposition_class
        )
        
        # Create new model structure
        model_class = original_build.semantic_theory["model"]
        new_structure = model_class(model_constraints)
        
        # Set the Z3 model from iterator
        new_structure.z3_model = z3_model
        new_structure.z3_model_status = True
        new_structure.satisfiable = True
        new_structure.solved = True
        
        # Initialize from Z3 model
        new_structure.initialize_from_z3_model(z3_model)
        
        # Interpret sentences
        new_structure.interpret(new_structure.premises + new_structure.conclusions)
        
        return new_structure
        
    except Exception as e:
        logger.error(f"Error building new model structure: {str(e)}")
        import traceback
        logger.error(f"Full traceback:\n{traceback.format_exc()}")
        raise  # Fail fast
```

5. Update all theory-specific iterators to remove old constraint methods:
```python
# Remove these methods from theory iterators:
# - _create_difference_constraint
# - _create_non_isomorphic_constraint  
# - _create_stronger_constraint
# Base class now handles everything via structural variables
```

### Phase 3.5: Theory Iterator Requirements

**New Requirement**: Each theory must implement an `iterate.py` module to enable iteration support.

**Files to Create/Update**:
- `src/model_checker/theory_lib/<theory_name>/iterate.py` for each theory

**Minimal Theory Iterator Implementation**:

```python
"""<Theory> specific model iteration implementation.

This module is REQUIRED for any theory that wants to support the 'iterate' setting.
Without this module, iteration will not be available for the theory.
"""

from model_checker.iterate.core import BaseModelIterator


class <Theory>ModelIterator(BaseModelIterator):
    """Model iterator for the <theory> theory.
    
    With structural variables, most functionality is handled by the base class.
    Theory-specific iterators only need to exist to enable iteration.
    """
    pass  # All functionality provided by BaseModelIterator with structural vars


# Module-level convenience function REQUIRED
def iterate_example(example, max_iterations=None):
    """Iterate a <theory> example to find multiple models.
    
    This function MUST be present for iteration to work with this theory.
    
    Args:
        example: A BuildExample instance with <theory> theory.
        max_iterations: Maximum number of models to find.
        
    Returns:
        list: List of model structures with distinct models.
    """
    if max_iterations is not None:
        # Update the iterate setting
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator and run
    iterator = <Theory>ModelIterator(example)
    models = iterator.iterate()
    
    # Store the iterator on the example for access to debug messages
    example._iterator = iterator
    
    return models
```

**Theory Iterator Discovery**:

The framework will check for iterate.py when the 'iterate' setting is used:

```python
# In builder/example.py or similar
def _check_iteration_support(self):
    """Check if theory supports iteration."""
    if self.settings.get('iterate', 1) > 1:
        theory_module = self.semantic_theory.get('module_path')
        iterate_module_path = f"{theory_module}.iterate"
        
        try:
            __import__(iterate_module_path)
        except ImportError:
            raise NotImplementedError(
                f"Theory '{self.theory_name}' does not support iteration. "
                f"To enable iteration, create {iterate_module_path}.py with "
                f"a {self.theory_name.title()}ModelIterator class and "
                f"iterate_example function."
            )
```

**Tests**:

1. `test_iterator_with_structural_vars.py`:
```python
def test_iterator_uses_structural_variables():
    """Iterator must use structural variables for differences."""
    # Create example, iterate, verify structural constraints used
    
def test_iterator_finds_all_distinct_models():
    """Iterator must find all structurally distinct models."""
    # Test with known example having N distinct models
    
def test_iterator_fails_fast_without_structural_vars():
    """Iterator must fail immediately if no structural variables."""
    # Test that appropriate error raised
```

### Phase 4: Update All Call Sites

**Files to Update**:
- All theory iterator implementations
- All tests that use iterator
- Any code that expects old iterator behavior

**Changes**:

1. Remove old methods from existing theory iterators
2. Create minimal iterate.py for theories without one
3. Update tests to expect new behavior
4. Remove any backward compatibility checks

**Theory Updates Required**:

1. **Logos** (`theory_lib/logos/iterate.py`): 
   - Remove complex constraint methods
   - Keep minimal iterator class

2. **Exclusion** (`theory_lib/exclusion/iterate.py`):
   - Create if missing
   - Use minimal implementation

3. **Imposition** (`theory_lib/imposition/iterate.py`):
   - Create if missing
   - Use minimal implementation

4. **Bimodal** (`theory_lib/bimodal/iterate.py`):
   - Create if missing
   - Use minimal implementation

**Tests**:
- Run full test suite: `./run_tests.py`
- Verify all tests pass with new implementation

### Phase 5: Performance Testing and Documentation

**Tasks**:

1. Create performance benchmarks:
```python
# Create test_performance_structural_vars.py
def test_performance_vs_baseline():
    """Structural variables must not degrade performance."""
    # Compare solving time with/without structural vars
```

2. Update documentation:
- Update `iterate/README.md` with new approach
- Add examples showing structural variable usage
- Document the pattern extraction process

3. Add debugging output:
```python
# In settings
'debug_structural_vars': False,  # Enable detailed output

# In iterator
if self.settings.get('debug_structural_vars'):
    print(f"Found pattern {len(self.found_patterns)}: {pattern.pattern}")
```

## Testing Strategy

### Unit Tests

1. **test_structural_variables.py**:
   - Test variable creation in ModelConstraints
   - Test linking constraints correctness
   - Test constraint generation

2. **test_patterns.py**:
   - Test pattern extraction
   - Test pattern to constraint conversion
   - Test exclusion constraints

3. **test_iterator_structural.py**:
   - Test iteration with structural vars
   - Test pattern tracking
   - Test model finding

### Integration Tests

1. Test all example files:
```bash
./run_tests.py --examples
```

2. Test specific theories:
```bash
./run_tests.py logos --unit --examples
./run_tests.py exclusion --unit --examples
```

3. Performance comparison:
```bash
# Create benchmark script comparing old vs new
python benchmarks/test_iterator_performance.py
```

## Success Criteria

1. All tests pass without modification
2. Iterator finds exact same models as before
3. No performance degradation
4. Cleaner, more maintainable code
5. No references to model objects in constraints
6. Each theory has iterate.py module for iteration support
7. Clear error messages when theory lacks iteration support

## Risk Mitigation

1. **Breaking Changes**: Update all call sites immediately
2. **Performance**: Profile and optimize BitVector operations
3. **Test Coverage**: Comprehensive tests before implementation
4. **Documentation**: Clear migration guide for theory developers
5. **Missing Theory Support**: Provide template for creating iterate.py
6. **Discovery Mechanism**: Clear error when iterate.py missing

## Timeline

1. **Day 1**: Implement Phase 1-2 (structural vars + patterns)
2. **Day 2**: Implement Phase 3 (iterator updates)
3. **Day 3**: Update all call sites and test
4. **Day 4**: Performance testing and documentation
5. **Day 5**: Final testing and code review

This implementation breaks compatibility for a cleaner architecture that separates structural properties from semantic functions, enabling efficient generation of structurally distinct models.