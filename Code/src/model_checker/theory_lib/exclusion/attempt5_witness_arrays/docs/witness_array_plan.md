# Implementation Plan: Strategy A2 - Witness Arrays

## Overview

This document provides a detailed implementation plan for Strategy A2 (Witness Arrays), which uses Z3 arrays to explicitly store the exclusion function mappings in the model, making them accessible during Phase 2 truth evaluation.

## Core Concept

Instead of using Skolem functions that become inaccessible after Phase 1, we encode the exclusion mappings as Z3 arrays that become part of the model itself:

```python
# Traditional approach (inaccessible):
h_sk = z3.Function(f"h_sk_{id}", BitVecSort(N), BitVecSort(N))

# Witness Array approach (accessible):
h_array = z3.Array(f"h_array_{id}", BitVecSort(N), BitVecSort(N))
y_array = z3.Array(f"y_array_{id}", BitVecSort(N), BitVecSort(N))
```

## Theoretical Foundation

### Why Arrays Work

1. **First-class Model Citizens**: Z3 arrays are part of the model and can be queried after solving
2. **Functional Behavior**: Arrays naturally represent functions (domain → codomain)
3. **Quantifier Support**: Array theory in Z3 supports quantified constraints
4. **Value Extraction**: Can query array[index] for any index after solving

### Semantic Preservation

The three-condition definition remains unchanged:
1. ∀x ∈ Ver(φ): y_array[x] ⊑ x ∧ h_array[x] excludes y_array[x]
2. ∀x ∈ Ver(φ): h_array[x] ⊑ s
3. s is minimal satisfying conditions 1-2

## Implementation Details

### Phase 1: Constraint Generation

#### 1. Array Declaration

```python
def extended_verify(self, state, argument, eval_point):
    """Generate constraints for exclusion using witness arrays."""
    N = self.model.N
    counter = self.model.counter
    
    # Declare witness arrays
    h_array = z3.Array(f"h_array_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
    y_array = z3.Array(f"y_array_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Store array references for Phase 2 access
    self.model.witness_arrays[counter] = {
        'h_array': h_array,
        'y_array': y_array,
        'argument': argument,
        'state': state
    }
    
    self.model.counter += 1
```

#### 2. Constraint Generation

```python
    # Helper for checking if x verifies the argument
    def verifies_arg(x):
        return self.model.verify(x, argument)
    
    # Condition 1: Exclusion property
    x = z3.BitVec(f"x_{counter}", N)
    condition_1 = z3.ForAll([x], 
        z3.Implies(
            verifies_arg(x),
            z3.And(
                self.model.is_part_of(y_array[x], x),
                self.model.excludes(h_array[x], y_array[x])
            )
        )
    )
    
    # Condition 2: Upper bound
    condition_2 = z3.ForAll([x],
        z3.Implies(
            verifies_arg(x),
            self.model.is_part_of(h_array[x], state)
        )
    )
    
    # Condition 3: Minimality (least upper bound)
    z = z3.BitVec(f"z_{counter}", N)
    condition_3 = z3.ForAll([z],
        z3.Implies(
            z3.ForAll([x], 
                z3.Implies(
                    verifies_arg(x),
                    self.model.is_part_of(h_array[x], z)
                )
            ),
            self.model.is_part_of(state, z)
        )
    )
    
    return z3.And(condition_1, condition_2, condition_3)
```

#### 3. Model Storage Structure

```python
class ExclusionSemantics(SemanticDefaults):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # Add storage for witness arrays
        self.witness_arrays = {}
```

### Phase 2: Truth Evaluation

#### 1. Array Value Extraction

```python
def extract_array_values(self, model, array, domain_size):
    """Extract all values from a Z3 array in the model."""
    values = {}
    for i in range(2**domain_size):
        idx = z3.BitVecVal(i, domain_size)
        try:
            val = model.evaluate(array[idx])
            if val is not None:
                values[i] = val.as_long()
        except:
            # Handle cases where array value is undefined
            values[i] = None
    return values
```

#### 2. Verifier Computation

```python
def find_verifiers(self, sentence, model, eval_world=None):
    """Find verifiers using witness array information."""
    
    if sentence.operator.name == 'Exclusion':
        # Find which counter was used for this exclusion
        # This requires tracking sentence → counter mapping
        counter = self.get_counter_for_sentence(sentence)
        
        if counter in self.witness_arrays:
            array_info = self.witness_arrays[counter]
            h_array = array_info['h_array']
            y_array = array_info['y_array']
            argument = array_info['argument']
            
            # Extract array values from model
            h_values = self.extract_array_values(model, h_array, self.N)
            y_values = self.extract_array_values(model, y_array, self.N)
            
            # Compute verifiers of the argument
            arg_verifiers = self.find_verifiers(argument, model, eval_world)
            
            # Find states that verify the exclusion
            verifiers = []
            for state_val in range(2**self.N):
                if self.verify_exclusion_with_arrays(
                    state_val, arg_verifiers, h_values, y_values, model
                ):
                    verifiers.append(state_val)
            
            return verifiers
```

#### 3. Verification Using Arrays

```python
def verify_exclusion_with_arrays(self, state, arg_verifiers, h_values, y_values, model):
    """Check if state verifies exclusion using extracted array values."""
    
    # Check all three conditions using array values
    
    # Condition 1: For all arg verifiers, h excludes some part
    for v in arg_verifiers:
        if v not in h_values or v not in y_values:
            return False
        
        h_v = h_values[v]
        y_v = y_values[v]
        
        # Check y_v is part of v
        if not self.evaluate_part_of(y_v, v, model):
            return False
            
        # Check h_v excludes y_v
        if not self.evaluate_excludes(h_v, y_v, model):
            return False
    
    # Condition 2: All h values are part of state
    for v in arg_verifiers:
        if v in h_values:
            if not self.evaluate_part_of(h_values[v], state, model):
                return False
    
    # Condition 3: Minimality check
    # State should be the fusion of all h values
    h_parts = [h_values[v] for v in arg_verifiers if v in h_values]
    fusion = self.compute_fusion(h_parts, model)
    
    return state == fusion
```

### Key Implementation Challenges

#### 1. Sentence-Counter Mapping

**Challenge**: Need to know which counter/arrays correspond to which sentence.

**Solution**:
```python
class ExclusionSemantics(SemanticDefaults):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.witness_arrays = {}
        self.sentence_to_counter = {}  # New mapping
    
    def extended_verify(self, state, argument, eval_point):
        # ... array creation ...
        
        # Store the mapping
        sentence_id = id(eval_point.get('sentence'))  # Or use sentence hash
        self.sentence_to_counter[sentence_id] = counter
```

#### 2. Array Theory Performance

**Challenge**: Array theory can slow down Z3 solving.

**Mitigation**:
- Use arrays only for exclusion operators
- Consider bit-blasting for small domains
- Add symmetry-breaking constraints

#### 3. Undefined Array Values

**Challenge**: Arrays may have undefined values for some indices.

**Solution**:
```python
def extract_array_values(self, model, array, domain_size):
    values = {}
    for i in range(2**domain_size):
        idx = z3.BitVecVal(i, domain_size)
        val = model.evaluate(array[idx], model_completion=True)
        values[i] = val.as_long() if val is not None else 0  # Default value
    return values
```

## Testing Strategy

### 1. Unit Tests

```python
def test_array_extraction():
    """Test that array values can be extracted from models."""
    # Create simple model with arrays
    # Verify extraction works correctly

def test_witness_array_constraints():
    """Test that array constraints encode exclusion correctly."""
    # Create exclusion constraints
    # Verify three conditions are satisfied

def test_verifier_computation():
    """Test verifier computation using array values."""
    # Create model with known array values
    # Verify correct verifiers are found
```

### 2. Integration Tests

Test on all standard examples:
- Double negation: ¬¬A
- DeMorgan's laws
- Complex nested exclusions

### 3. Performance Tests

Compare with current implementation:
- Solving time
- Model size
- Memory usage

## Migration Path

### Phase 1: Parallel Implementation
1. Implement array-based exclusion alongside current approach
2. Add flag to switch between implementations
3. Compare results on test suite

### Phase 2: Validation
1. Verify identical results on working examples
2. Test on problematic examples (false premises)
3. Analyze any differences in models found

### Phase 3: Integration
1. Replace current exclusion implementation
2. Update documentation
3. Performance optimization

## Expected Outcomes

### Advantages
1. **Accessible Witnesses**: Array values available in Phase 2
2. **Correct Verifier Computation**: Can reconstruct h mapping
3. **Semantic Fidelity**: Preserves original three-condition definition

### Potential Issues
1. **Performance**: Array theory may increase solving time
2. **Model Size**: Arrays add to model complexity
3. **Debugging**: Array constraints harder to debug than functions

### Success Criteria
1. All working examples continue to work
2. False premise examples now evaluate correctly
3. Performance degradation < 2x
4. No new errors introduced

## Alternative Considerations

If array performance is problematic, consider:
1. **Hybrid Approach**: Use arrays only for problematic formulas
2. **Bounded Arrays**: Limit array domain for efficiency
3. **Caching**: Cache array evaluations during Phase 2

## Conclusion

The Witness Array strategy (A2) offers a promising approach to solving the Skolem function accessibility problem while maintaining the two-phase architecture. By encoding witness functions as Z3 arrays, we make the existential witnesses part of the model itself, allowing Phase 2 to access the information needed for correct verifier computation.

The main trade-off is between semantic correctness (which this approach preserves) and potential performance impact from array theory. Implementation should proceed cautiously with thorough testing at each stage.

