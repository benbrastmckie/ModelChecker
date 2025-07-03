# Reduced Semantics Implementation Plan

## Overview

This plan outlines a streamlined implementation that focuses on creating a complete, correct recursive semantics for exclusion operators. The implementation will start from `operators_old.py` and `semantic_old.py` as a foundation, then systematically implement proper recursive reduction to primitive semantic relations.

## Core Principles

### 1. Complete Recursive Reduction
Every formula must reduce completely to constraints stated purely in terms of semantic primitives:
- `verify(state, atom)` - for atomic sentences (Z3 Function)
- `excludes(state1, state2)` - for exclusion relations (Z3 Function)
- `main_world` - the evaluation world (Z3 BitVec)

And derived relations:
- `is_part_of(x, y)` := `fusion(x, y) == y` where `fusion` is Z3 bitwise OR
- `fusion(x, y)` := `x | y` (Z3 bitwise OR operation on BitVecs)

### 2. Recursive Forms

#### true_at Recursive Form
```python
def true_at(self, sentence, eval_point):
    """
    Base case (atomic): 
        exists v. verify(v, sentence.atom) AND is_part_of(v, eval_point["world"])
    
    Recursive case (complex):
        sentence.operator.true_at(*sentence.arguments, eval_point)
    """
```

#### extended_verify Recursive Form
```python
def extended_verify(self, state, sentence, eval_point):
    """
    Base case (atomic):
        verify(state, sentence.atom)
    
    Recursive case (complex):
        sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
    """
```

### 3. Skolemization Strategy
- Every existentially quantified function in the three conditions gets a unique Skolem function
- Skolem functions are named with unique IDs to avoid conflicts
- The h and y functions from the three conditions become h_sk_[id] and y_sk_[id]

### 4. Quantification Strategy: Custom vs Z3 Quantifiers

#### Option A: Custom Quantifiers (utils.Exists/ForAll)
**Advantages:**
- Explicit enumeration of all 2^N states
- More predictable Z3 solving (no quantifier instantiation issues)
- Easier to debug (can see expanded constraints)
- Guaranteed complete coverage of finite domain

**Disadvantages:**
- Exponential blowup in constraint size
- Slower for large N (but N is typically small: 3-5)
- More memory usage

#### Option B: Z3 Native Quantifiers (z3.Exists/z3.ForAll)
**Advantages:**
- Compact constraint representation
- Potentially faster for Z3's internal optimizations
- Scales better with N

**Disadvantages:**
- Z3 quantifier instantiation can be unpredictable
- Harder to debug when things go wrong
- May miss solutions due to incomplete instantiation

#### Recommended Approach
For exclusion semantics with small domains (N ≤ 5), use **custom quantifiers** for:
- State quantification in `true_at` (e.g., "exists verifier v")
- Universal quantification in three conditions

This ensures complete, predictable behavior and may help resolve false premise issues.

## Implementation Phases

---

## Phase 1: Foundation Setup (2-3 hours)

### Objectives
- Create clean foundation from old implementations
- Establish proper module structure
- Set up basic semantic primitives

### Tasks

#### 1.1 Create Base Files
```bash
# Copy old implementations as starting point
cp operators_old.py reduced_operators.py
cp semantic_old.py reduced_semantic.py
```

#### 1.2 Clean Up Semantic Primitives
In `reduced_semantic.py`:
- Remove all experimental exclusion strategies (QI, QI2, BQI, etc.)
- Keep only core Z3-declared primitives: `verify` and `excludes` as Z3 Functions
- Implement derived relations properly:
  ```python
  def fusion(self, x, y):
      """Fusion is just bitwise OR"""
      return x | y
      
  def is_part_of(self, x, y):
      """x is part of y iff fusion(x,y) = y"""
      return self.fusion(x, y) == y
  ```
- Add proper ID generation for Skolem functions
- Ensure `true_at` follows the two-case pattern (atomic vs complex)

#### 1.3 Simplify Operators
In `reduced_operators.py`:
- Keep only one exclusion operator implementation
- Ensure all operators properly implement both `true_at` and `extended_verify`
- Remove any hardcoded operator checks in semantic functions

### Deliverables
- `reduced_semantic.py`: Clean semantic foundation with custom quantifiers
- `reduced_operators.py`: Simplified operator definitions using `Exists`/`ForAll` from utils
- `test_reduced_foundation.py`: Basic tests for primitives

### Success Criteria
- [ ] Only two Z3 primitives declared: `verify` and `excludes`
- [ ] `fusion` and `is_part_of` implemented as derived relations
- [ ] Custom quantifiers (`Exists`/`ForAll`) used for state quantification
- [ ] No operator-specific logic in semantic functions
- [ ] Basic tests pass for atomic formulas

---

## Phase 2: Implement Correct true_at Reduction (3-4 hours)

### Objectives
- Implement proper recursive `true_at` for all operators
- Ensure complete reduction to verifier existence
- Handle atomic and complex cases correctly

### Tasks

#### 2.1 Atomic Sentence Reduction
```python
from model_checker.utils import Exists  # Use custom quantifier

def true_at(self, sentence, eval_point):
    if sentence.sentence_letter is not None:
        # Atomic case: reduce to verifier existence
        v = z3.BitVec(f"v_atom_{id(sentence)}_{self.get_unique_id()}", self.N)
        return Exists([v], z3.And(
            self.verify(v, sentence.sentence_letter),
            self.is_part_of(v, eval_point["world"])
        ))
    else:
        # Complex case: delegate to operator
        return sentence.operator.true_at(*sentence.arguments, eval_point)
```

#### 2.2 Operator true_at Methods

**Conjunction:**
```python
def true_at(self, leftarg, rightarg, eval_point):
    # Recursive reduction for both arguments
    return z3.And(
        self.semantics.true_at(leftarg, eval_point),
        self.semantics.true_at(rightarg, eval_point)
    )
```

**Disjunction:**
```python
def true_at(self, leftarg, rightarg, eval_point):
    # Recursive reduction for both arguments
    return z3.Or(
        self.semantics.true_at(leftarg, eval_point),
        self.semantics.true_at(rightarg, eval_point)
    )
```

**Exclusion:**
```python
def true_at(self, argument, eval_point):
    # Reduce to: exists s. extended_verify(s, argument) AND s part_of world
    s = z3.BitVec(f"excl_ver_{self.get_unique_id()}", self.semantics.N)
    return Exists([s], z3.And(
        self.semantics.is_part_of(s, eval_point["world"]),
        self.extended_verify(s, argument, eval_point)
    ))
```

### Deliverables
- Updated `reduced_operators.py` with correct `true_at` methods
- `test_true_at_reduction.py`: Tests verifying complete reduction

### Success Criteria
- [ ] All formulas reduce to primitive constraints
- [ ] No circular dependencies in reduction
- [ ] Tests pass for all operator types

---

## Phase 3: Implement Skolemized extended_verify (4-5 hours)

### Objectives
- Implement proper `extended_verify` with Skolem functions
- Ensure unique naming for all Skolem functions
- Correctly encode the three conditions for exclusion

### Tasks

#### 3.1 Base extended_verify in Semantics
```python
def extended_verify(self, state, sentence, eval_point):
    if sentence.sentence_letter is not None:
        # Atomic case
        return self.verify(state, sentence.sentence_letter)
    else:
        # Complex case: delegate to operator
        return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
```

#### 3.2 Operator extended_verify Methods

**Conjunction:**
```python
from model_checker.utils import Exists, ForAll

def extended_verify(self, state, leftarg, rightarg, eval_point):
    x = z3.BitVec(f"conj_x_{self.get_unique_id()}", self.semantics.N)
    y = z3.BitVec(f"conj_y_{self.get_unique_id()}", self.semantics.N)
    return Exists([x, y], z3.And(
        (x | y) == state,  # fusion is bitwise OR
        self.semantics.extended_verify(x, leftarg, eval_point),
        self.semantics.extended_verify(y, rightarg, eval_point)
    ))
```

**Exclusion with Skolem Functions:**
```python
def extended_verify(self, state, argument, eval_point):
    sem = self.semantics
    N = sem.N
    sk_id = self.get_unique_id()
    
    # Skolem functions with unique names
    h_sk = z3.Function(f"h_sk_{sk_id}", z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function(f"y_sk_{sk_id}", z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Variables
    x = z3.BitVec(f"x_{sk_id}", N)
    z = z3.BitVec(f"z_{sk_id}", N)
    
    return z3.And(
        # Condition 1: For every verifier x of argument, y_sk(x) is part of x and h_sk(x) excludes y_sk(x)
        ForAll([x], z3.Implies(
            sem.extended_verify(x, argument, eval_point),
            z3.And(
                sem.is_part_of(y_sk(x), x),
                sem.excludes(h_sk(x), y_sk(x))
            )
        )),
        
        # Condition 2: For every verifier x of argument, h_sk(x) is part of state
        ForAll([x], z3.Implies(
            sem.extended_verify(x, argument, eval_point),
            sem.is_part_of(h_sk(x), state)
        )),
        
        # Condition 3: State is minimal
        ForAll([z], z3.Implies(
            ForAll([x], z3.Implies(
                sem.extended_verify(x, argument, eval_point),
                sem.is_part_of(h_sk(x), z)
            )),
            sem.is_part_of(state, z)
        ))
    )
```

### Deliverables
- Updated `reduced_operators.py` with Skolemized `extended_verify`
- Unique ID management system for Skolem functions
- `test_extended_verify.py`: Tests for verification conditions

### Success Criteria
- [ ] All extended_verify methods properly recursive
- [ ] Skolem functions have unique names
- [ ] Three conditions correctly encoded

---

## Phase 4: Integration and Testing (3-4 hours)

### Objectives
- Integrate reduced semantics with model checker
- Test on all 34 examples
- Verify false premise issue is resolved

### Tasks

#### 4.1 Create Integration Module
```python
# reduced_theory.py
def create_reduced_operators():
    """Create operator collection for reduced semantics."""
    operators = OperatorCollection()
    operators.add_operator(ExclusionOperator)
    operators.add_operator(UniAndOperator)
    operators.add_operator(UniOrOperator)
    operators.add_operator(UniIdentityOperator)
    return operators
```

#### 4.2 Run Comprehensive Tests
- Test all 34 examples with reduced semantics
- Focus on the 8 problematic examples
- Verify no false premises occur
- Measure performance

#### 4.3 Debug and Refine
- Use trace logging to verify complete reduction
- Check Z3 constraint generation
- Ensure proper evaluation of results

### Deliverables
- `reduced_theory.py`: Complete theory implementation
- `test_reduced_comprehensive.py`: Full test suite
- `reduced_results.json`: Performance metrics

### Success Criteria
- [ ] All 34 examples pass without false premises
- [ ] Performance acceptable (< 1s average)
- [ ] Complete reduction verified through logging

---

## Phase 5: Documentation and Optimization (2-3 hours)

### Objectives
- Document the successful approach
- Optimize performance where possible
- Prepare for integration into main codebase

### Tasks

#### 5.1 Documentation
- Document the recursive reduction strategy
- Create examples showing constraint generation
- Write usage guide for reduced semantics

#### 5.2 Performance Optimization
- Profile constraint generation
- Optimize Skolem function creation
- Consider caching strategies

#### 5.3 Integration Planning
- Plan how to integrate into main exclusion theory
- Consider configuration options
- Prepare migration guide

### Deliverables
- `REDUCED_SEMANTICS_GUIDE.md`: Complete documentation
- Performance optimization report
- Integration recommendations

### Success Criteria
- [ ] Clear documentation of approach
- [ ] Performance improvements identified
- [ ] Ready for production use

---

## Expected Outcomes

1. **Correct Recursive Semantics**: All formulas reduce completely to the two Z3 primitives (`verify` and `excludes`) plus bitwise operations
2. **No False Premises**: The 8 problematic examples are resolved
3. **Maintainable Code**: Clear separation between Z3 primitives and derived relations
4. **Performance**: Acceptable performance with potential optimizations identified
5. **Extensibility**: New operators can be added without modifying core semantics

## Risk Mitigation

1. **If false premises persist**: Add detailed logging to trace exact constraint generation
2. **If performance degrades**: Consider hybrid approach with enumeration for small domains
3. **If Z3 issues arise**: Ensure proper quantifier instantiation patterns

## Timeline

- Phase 1: 2-3 hours
- Phase 2: 3-4 hours  
- Phase 3: 4-5 hours
- Phase 4: 3-4 hours
- Phase 5: 2-3 hours

**Total: 14-19 hours**

This can be completed over 2-3 days with careful implementation and testing after each phase.