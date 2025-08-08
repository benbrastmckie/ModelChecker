# Research: Structural Difference Constraints for Model Iteration

## Overview

This document explores alternatives for generating structurally distinct models in the ModelChecker iterator. The goal is to find models that satisfy the original constraints while differing in structure, without referencing the model structure objects or previously found models directly in the constraints.

## Current Implementation Analysis

### How Iterator Currently Works

1. **Initial Model Generation**
   - BuildExample creates ModelConstraints with all Z3 constraints
   - Z3 solver finds MODEL 1 satisfying all constraints
   - ModelStructure built from Z3 model for interpretation/display

2. **Iteration Process**
   - Iterator preserves original constraints in `self.original_constraints`
   - For each new model:
     - Creates difference constraints using `_create_difference_constraint()`
     - Builds new ModelStructure using `_build_new_model_structure()`
     - Checks for isomorphism if NetworkX available
     - Adds to found models if structurally distinct

3. **Key Issues**
   - Difference constraints currently reference model values directly
   - New ModelStructure construction involves complex state extraction
   - Constraints mix semantic values with structural requirements

### Current Difference Constraint Generation (Logos Example)

```python
def _create_difference_constraint(self, previous_models):
    # Creates constraints like:
    # - Different world count
    # - Different verify/falsify for sentence letters
    # - Different possible state structure
    
    # Problem: These reference the actual Z3 model values
    prev_world_count = sum(1 for state in all_states 
                          if bool(prev_model.eval(semantics.is_world(state))))
```

## Alternative Approaches

### Option 1: Pure Z3 Structural Variables

**Concept**: Introduce Z3 variables that explicitly represent structural properties, separate from semantic functions.

**Implementation**:
```python
# In ModelConstraints initialization
self.structure_vars = {
    'num_worlds': z3.Int('num_worlds'),
    'num_possible': z3.Int('num_possible'),
    'world_pattern': z3.BitVec('world_pattern', 2**N),
    'verify_pattern': {letter: z3.BitVec(f'verify_pattern_{letter}', 2**N) 
                       for letter in sentence_letters}
}

# Add constraints linking structure vars to semantic functions
constraints.append(self.structure_vars['num_worlds'] == 
                  z3.Sum([z3.If(semantics.is_world(s), 1, 0) for s in all_states]))
```

**Advantages**:
- Clean separation of structure from semantics
- Easy to create difference constraints: `new_num_worlds != old_num_worlds`
- No need to reference model objects
- Z3 can optimize based on structural variables

**Disadvantages**:
- Requires modifying ModelConstraints class
- Additional variables increase solver complexity
- Need to maintain consistency between vars and functions

### Option 2: Constraint Templates with Parameterization

**Concept**: Create parameterized constraint templates that can be instantiated with different structural requirements.

**Implementation**:
```python
class StructuralConstraintTemplate:
    def __init__(self, semantics, sentence_letters):
        self.semantics = semantics
        self.sentence_letters = sentence_letters
    
    def generate_constraints(self, structural_spec):
        """Generate constraints for a specific structural specification."""
        constraints = []
        
        if 'min_worlds' in structural_spec:
            constraints.append(self._world_count_constraint(structural_spec['min_worlds'], '>='))
        
        if 'verify_differences' in structural_spec:
            for letter, states in structural_spec['verify_differences'].items():
                constraints.append(self._verify_constraint(letter, states))
        
        return z3.And(*constraints)
```

**Advantages**:
- Flexible specification of structural requirements
- No direct model references
- Can generate increasingly specific constraints
- Reusable across different theories

**Disadvantages**:
- Requires careful specification design
- May miss some structural variations
- Need to track what specifications tried

### Option 3: Symmetry Breaking Constraints

**Concept**: Add constraints that break symmetries in the search space, forcing Z3 to explore structurally different regions.

**Implementation**:
```python
def add_symmetry_breaking_constraints(self, iteration_num):
    """Add constraints that force exploration of different structural regions."""
    constraints = []
    
    # Lexicographic ordering on world states
    if iteration_num > 0:
        # Force at least one world to have index > previous max
        constraints.append(z3.Or([semantics.is_world(s) for s in all_states[iteration_num:]]))
    
    # Alternating patterns for verify/falsify
    if iteration_num % 2 == 0:
        # Even iterations: require more verifiers than falsifiers
        for letter in sentence_letters[:1]:  # Just first letter
            verify_count = z3.Sum([z3.If(semantics.verify(s, letter), 1, 0) for s in all_states])
            falsify_count = z3.Sum([z3.If(semantics.falsify(s, letter), 1, 0) for s in all_states])
            constraints.append(verify_count > falsify_count)
```

**Advantages**:
- Simple to implement
- Naturally explores different regions
- No model references needed
- Can be theory-agnostic

**Disadvantages**:
- May not find all possible structures
- Ordering may be artificial
- Could miss interesting models

### Option 4: Incremental Structure Building

**Concept**: Build structural requirements incrementally, adding one structural difference at a time.

**Implementation**:
```python
class IncrementalStructureBuilder:
    def __init__(self, original_constraints):
        self.original_constraints = original_constraints
        self.structural_history = []
    
    def get_next_constraints(self):
        """Get constraints for next structurally different model."""
        new_constraints = list(self.original_constraints)
        
        # Add negation of all previous structural patterns
        for prev_structure in self.structural_history:
            new_constraints.append(z3.Not(self._encode_structure(prev_structure)))
        
        return new_constraints
    
    def record_structure(self, z3_model):
        """Record structural pattern of found model."""
        structure = {
            'world_bits': self._extract_world_pattern(z3_model),
            'verify_bits': self._extract_verify_patterns(z3_model)
        }
        self.structural_history.append(structure)
```

**Advantages**:
- Guarantees all structures explored
- Clean constraint generation
- No forward model references
- Natural progression

**Disadvantages**:
- Requires pattern extraction
- History grows with iterations
- Pattern encoding complexity

### Option 5: Fresh Solver with Exclusion Constraints

**Concept**: For each iteration, create a completely fresh solver with original constraints plus exclusion constraints for previous structural patterns.

**Implementation**:
```python
def iterate_with_fresh_solver(self):
    """Find next model using fresh solver."""
    # Start with original constraints only
    solver = z3.Solver()
    for c in self.original_constraints:
        solver.add(c)
    
    # Add exclusion for each previous structural pattern
    for prev_pattern in self.found_patterns:
        solver.add(self._create_pattern_exclusion(prev_pattern))
    
    if solver.check() == z3.sat:
        model = solver.model()
        pattern = self._extract_pattern(model)
        self.found_patterns.append(pattern)
        return model
```

**Advantages**:
- Complete solver isolation
- No contamination between iterations
- Clean constraint separation
- Easy to parallelize

**Disadvantages**:
- Loses solver learning between iterations
- Pattern extraction/encoding needed
- Potentially slower solving

## Recommended Approach

**Primary Recommendation: Option 1 (Pure Z3 Structural Variables)**

This approach provides the cleanest separation between structure and semantics while maintaining efficiency. Implementation would involve:

1. Extending ModelConstraints to include structural variables
2. Adding constraints linking structural vars to semantic functions
3. Using structural vars for difference constraints in iterator
4. No direct model references in constraints

**Secondary Recommendation: Option 5 (Fresh Solver)**

If modifying ModelConstraints is not desired, the fresh solver approach provides good isolation with minimal changes to existing code.

## Implementation Considerations

### For Option 1 Implementation

1. **Structural Variables to Add**:
   - `num_worlds`: Integer count of worlds
   - `num_possible`: Integer count of possible states
   - `world_pattern`: BitVector encoding which states are worlds
   - `verify_patterns`: Per-letter BitVectors for verification
   - `falsify_patterns`: Per-letter BitVectors for falsification

2. **Constraint Generation**:
   ```python
   # In iterator
   def create_structural_difference(self, prev_patterns):
       return z3.Or([
           self.structure_vars['num_worlds'] != prev['num_worlds'],
           self.structure_vars['world_pattern'] != prev['world_pattern'],
           # ... other structural differences
       ] for prev in prev_patterns)
   ```

3. **Pattern Extraction** (for recording found models):
   ```python
   def extract_structural_pattern(self, z3_model):
       return {
           'num_worlds': z3_model.eval(self.structure_vars['num_worlds']),
           'world_pattern': z3_model.eval(self.structure_vars['world_pattern']),
           # ... other patterns
       }
   ```

### For Option 5 Implementation

1. **Pattern Encoding**:
   ```python
   def encode_pattern(self, semantics, pattern):
       """Create constraint that matches exact pattern."""
       return z3.And(
           z3.Sum([z3.If(semantics.is_world(s), 1, 0) for s in all_states]) == pattern['num_worlds'],
           # ... other pattern matching
       )
   ```

2. **Exclusion Constraints**:
   ```python
   def create_pattern_exclusion(self, semantics, pattern):
       """Create constraint that excludes specific pattern."""
       return z3.Not(self.encode_pattern(semantics, pattern))
   ```

## Benefits of Recommended Approaches

1. **No Model Structure References**: Constraints operate purely on Z3 variables
2. **Clean Separation**: Structure and semantics clearly separated
3. **Efficient Solving**: Z3 can optimize based on structural variables
4. **Theory Agnostic**: Approach works for any theory with similar structure
5. **Parallelizable**: Each iteration independent with fresh solver approach

## Next Steps

1. Prototype Option 1 with minimal changes to ModelConstraints
2. Test performance compared to current implementation
3. Verify all original models still found
4. Extend to other theories beyond Logos
5. Consider hybrid approach if needed

This approach would allow the iterator to find structurally distinct models without referencing model objects, making the constraint generation cleaner and more maintainable.