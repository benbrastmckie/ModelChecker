# Attempt 7: Explicit Witness Relations Implementation Plan

## Executive Summary

This document outlines a detailed implementation plan for Strategy A1: Explicit Witness Relations, which encodes witness information directly in the model as queryable relations rather than using inaccessible Skolem functions. This approach maintains the two-phase architecture while making witness data accessible during truth evaluation.

## Lessons from Previous Attempts

### From Attempt 6 (Incremental)
1. **Model completion is dangerous**: Z3's incremental SAT checking fills in arbitrary values that can make later constraints unsatisfiable
2. **Quantified formulas need complete context**: Can't evaluate formulas referencing functions that aren't fully constrained
3. **Batch solving works**: Adding all constraints before checking avoids premature decisions
4. **Witness extraction is possible**: Successfully extracted Skolem mappings when they exist in the model

### From Attempts 1-5
1. **Skolem functions are inaccessible**: Two-phase architecture prevents witness retrieval
2. **Simplicity reveals truth**: Complex multi-strategy approaches obscured the real issues
3. **The semantic definition is sound**: Problem is computational, not theoretical

## Strategy A1: Core Concept

Instead of using Skolem functions that become inaccessible after constraint generation:
```python
# Traditional approach (inaccessible):
h_sk = z3.Function("h_sk", BitVecSort(N), BitVecSort(N))
```

We encode the witness mapping as an explicit relation in the model:
```python
# Explicit relation approach (accessible):
H_rel = z3.Function("H_rel", BitVecSort(N), BitVecSort(N), BoolSort())
# Where H_rel(x, y) = True iff h(x) = y
```

## Implementation Architecture

### Phase Structure
1. **Constraint Generation Phase**: Create all constraints including functionality constraints for H_rel
2. **Batch Solving**: Submit all constraints at once (avoiding incremental pitfalls)
3. **Truth Evaluation Phase**: Extract witness mappings from H_rel to compute verifiers

### Key Components

#### 1. ExplicitWitnessSemantics
```python
class ExplicitWitnessSemantics(ExclusionSemantics):
    """
    Exclusion semantics using explicit witness relations.
    """
    
    def __init__(self, settings):
        super().__init__(settings)
        # Create explicit relations for witness mappings
        self.H_rel = z3.Function('H_rel', 
            z3.BitVecSort(self.N), z3.BitVecSort(self.N), z3.BoolSort())
        self.Y_rel = z3.Function('Y_rel', 
            z3.BitVecSort(self.N), z3.BitVecSort(self.N), z3.BoolSort())
    
    def _get_frame_constraints(self):
        constraints = super()._get_frame_constraints()
        # Add functionality constraints for relations
        constraints.extend(self._relation_functionality_constraints())
        return constraints
    
    def _relation_functionality_constraints(self):
        """Ensure H_rel and Y_rel encode functions."""
        x = z3.BitVec('x', self.N)
        y1 = z3.BitVec('y1', self.N)
        y2 = z3.BitVec('y2', self.N)
        
        return [
            # H_rel is functional: if H_rel(x,y1) and H_rel(x,y2) then y1=y2
            ForAll([x, y1, y2],
                z3.Implies(
                    z3.And(self.H_rel(x, y1), self.H_rel(x, y2)),
                    y1 == y2
                )
            ),
            # Y_rel is functional
            ForAll([x, y1, y2],
                z3.Implies(
                    z3.And(self.Y_rel(x, y1), self.Y_rel(x, y2)),
                    y1 == y2
                )
            )
        ]
```

#### 2. ExplicitWitnessOperator
```python
class ExplicitWitnessOperator(ExclusionOperator):
    """
    Exclusion operator using explicit witness relations.
    """
    
    def three_condition_constraint(self, argument, eval_point):
        """
        Generate three-condition constraint using explicit relations.
        """
        sem = self.semantics
        world = eval_point["world"]
        x = z3.BitVec('x', sem.N)
        h_x = z3.BitVec('h_x', sem.N)
        y_x = z3.BitVec('y_x', sem.N)
        
        # Condition 1: For all verifiers, H and Y relations satisfy requirements
        condition1 = ForAll([x],
            z3.Implies(
                sem.extended_verify(x, argument, eval_point),
                z3.Exists([h_x, y_x],
                    z3.And(
                        sem.H_rel(x, h_x),  # h(x) = h_x
                        sem.Y_rel(x, y_x),  # y(x) = y_x
                        sem.is_part_of(y_x, x),
                        sem.excludes(h_x, y_x)
                    )
                )
            )
        )
        
        # Condition 2: All h values are part of world
        condition2 = ForAll([x, h_x],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, argument, eval_point),
                    sem.H_rel(x, h_x)
                ),
                sem.is_part_of(h_x, world)
            )
        )
        
        # Condition 3: World is minimal
        # ... similar pattern using H_rel
        
        return z3.And(condition1, condition2, condition3)
```

#### 3. WitnessExtractor
```python
class WitnessExtractor:
    """
    Extract witness mappings from explicit relations in the model.
    """
    
    def __init__(self, model, semantics):
        self.model = model
        self.sem = semantics
        self.h_mapping = {}
        self.y_mapping = {}
    
    def extract_witness_mappings(self):
        """Extract h and y mappings from H_rel and Y_rel."""
        for i in range(2**self.sem.N):
            for j in range(2**self.sem.N):
                # Check if H_rel(i, j) is true in the model
                if z3.is_true(self.model.eval(self.sem.H_rel(i, j))):
                    self.h_mapping[i] = j
                # Check if Y_rel(i, j) is true in the model
                if z3.is_true(self.model.eval(self.sem.Y_rel(i, j))):
                    self.y_mapping[i] = j
        
        return self.h_mapping, self.y_mapping
    
    def get_h_value(self, x):
        """Get h(x) from extracted mapping."""
        return self.h_mapping.get(x, None)
    
    def get_y_value(self, x):
        """Get y(x) from extracted mapping."""
        return self.y_mapping.get(x, None)
```

#### 4. ExplicitProposition
```python
class ExplicitProposition(UnilateralProposition):
    """
    Proposition class that uses explicit witness relations for verification.
    """
    
    def _compute_verifiers_exclusion(self, sentence, model, eval_point):
        """
        Compute verifiers for exclusion using explicit witness mappings.
        """
        # Extract witness mappings
        extractor = WitnessExtractor(model, self.semantics)
        h_mapping, y_mapping = extractor.extract_witness_mappings()
        
        # Now we can correctly compute verifiers
        verifiers = []
        for state in range(2**self.semantics.N):
            if self._verifies_exclusion_with_witnesses(
                state, sentence, model, eval_point, h_mapping, y_mapping
            ):
                verifiers.append(state)
        
        return verifiers
    
    def _verifies_exclusion_with_witnesses(
        self, state, sentence, model, eval_point, h_mapping, y_mapping
    ):
        """
        Check if state verifies exclusion using extracted witnesses.
        """
        # Get verifiers of the argument
        arg_verifiers = self.extended_compute_verifiers(
            sentence.arguments[0], model, eval_point
        )
        
        # Check three conditions using witness mappings
        # 1. All arg_verifiers have appropriate h and y values
        for v in arg_verifiers:
            if v not in h_mapping or v not in y_mapping:
                return False
            h_v = h_mapping[v]
            y_v = y_mapping[v]
            
            # Check constraints
            if not self.semantics.eval_is_part_of(y_v, v, model):
                return False
            if not self.semantics.eval_excludes(h_v, y_v, model):
                return False
            if not self.semantics.eval_is_part_of(h_v, state, model):
                return False
        
        # 2. Check minimality
        # ... implementation details
        
        return True
```

## Implementation Phases

### Phase 1: Core Infrastructure (2 days)

1. **Create base classes**:
   - `ExplicitWitnessSemantics` extending `ExclusionSemantics`
   - `ExplicitWitnessOperator` extending `ExclusionOperator`
   - `WitnessExtractor` for mapping extraction

2. **Implement relation functionality constraints**:
   - Ensure H_rel and Y_rel encode functions
   - Add domain constraints if needed

3. **Set up testing framework**:
   - Unit tests for relation constraints
   - Integration tests with simple formulas

### Phase 2: Three-Condition Implementation (2 days)

1. **Implement three-condition constraint generation**:
   - Translate existential quantifiers to relation constraints
   - Ensure all three conditions properly encoded

2. **Handle edge cases**:
   - Empty verifier sets
   - Undefined witness values
   - Minimality checking

3. **Verify constraint correctness**:
   - Test on known examples
   - Compare with manual calculations

### Phase 3: Witness Extraction (2 days)

1. **Implement `WitnessExtractor`**:
   - Efficient extraction from model
   - Handle partial functions
   - Cache extracted mappings

2. **Integrate with truth evaluation**:
   - Modify `compute_verifiers` for exclusion
   - Ensure correct verifier computation

3. **Performance optimization**:
   - Lazy extraction
   - Memoization strategies

### Phase 4: Testing and Validation (2 days)

1. **Test suite**:
   - All standard exclusion examples
   - Focus on previously failing cases (NEG_TO_SENT, etc.)
   - Performance benchmarks

2. **Debugging tools**:
   - Witness mapping visualization
   - Constraint analysis utilities
   - Model inspection helpers

3. **Documentation**:
   - API documentation
   - Usage examples
   - Troubleshooting guide

## Key Design Decisions

### 1. Relation Encoding
- Use boolean-valued relations instead of functions
- Allows direct model queries
- Requires functionality constraints

### 2. Batch Constraint Generation
- Generate all constraints before solving
- Avoids incremental model completion issues
- Maintains two-phase architecture

### 3. Lazy Witness Extraction
- Extract only when needed for specific formulas
- Cache results for reuse
- Minimize performance impact

### 4. Fallback Strategy
- If relation approach fails, fall back to conservative approximation
- Log when fallback occurs
- Maintain correctness over completeness

## Success Criteria

1. **Correctness**:
   - NEG_TO_SENT finds valid countermodel
   - All double/triple negation examples work
   - DeMorgan's laws validated

2. **Performance**:
   - No more than 2x slower than current implementation
   - Reasonable memory usage
   - Scales to N=5 or N=6

3. **Maintainability**:
   - Clean separation from standard semantics
   - Well-documented code
   - Comprehensive test coverage

## Risk Assessment

### Technical Risks

1. **Relation constraint complexity**:
   - Risk: Functionality constraints make solving harder
   - Mitigation: Careful constraint formulation, incremental testing

2. **Memory usage**:
   - Risk: Relations require O(2^(2N)) space
   - Mitigation: Sparse representation, domain restrictions

3. **Solver timeout**:
   - Risk: Additional constraints increase solving time
   - Mitigation: Timeout handling, constraint optimization

### Implementation Risks

1. **Integration complexity**:
   - Risk: Changes ripple through codebase
   - Mitigation: Minimal interface changes, adapter pattern

2. **Debugging difficulty**:
   - Risk: Relations harder to debug than functions
   - Mitigation: Comprehensive logging, visualization tools

## Comparison with Incremental Approach

| Aspect | Incremental (Attempt 6) | Explicit Relations (Attempt 7) |
|--------|------------------------|-------------------------------|
| Architecture | Bypasses framework | Works within framework |
| Solver interaction | Multiple incremental checks | Single batch solve |
| Witness access | Extract from intermediate models | Query from final model |
| Complexity | High (new components) | Medium (extend existing) |
| Risk | Model completion bugs | Constraint complexity |

## Next Steps

1. **Prototype**: Implement minimal version for NEG_TO_SENT
2. **Validate**: Ensure approach solves known problematic examples
3. **Optimize**: Profile and improve performance
4. **Generalize**: Extend to full example suite
5. **Document**: Complete implementation guide

## Conclusion

The explicit witness relations approach offers a promising path forward that:
- Works within the existing two-phase architecture
- Avoids the pitfalls of incremental solving
- Makes witness information accessible when needed
- Maintains theoretical soundness

By encoding witnesses as explicit relations rather than inaccessible Skolem functions, we can bridge the gap between constraint generation and truth evaluation while respecting the framework's architectural constraints.