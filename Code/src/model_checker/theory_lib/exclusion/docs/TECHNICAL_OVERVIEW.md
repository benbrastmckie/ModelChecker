# Technical Overview: Attempt 9 - Witness Predicate Implementation

## Executive Summary

Attempt 9 solves the False Premise Problem by making witness functions first-class model predicates that persist throughout the entire model checking process. This document provides a detailed technical overview of each module, their interactions, and the specific innovations that enabled success where previous attempts failed.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                         User Example                              │
└───────────────────────┬─────────────────────────────────────────┘
                        │
┌───────────────────────▼─────────────────────────────────────────┐
│                    semantic.py                                   │
│  - WitnessPredicateSemantics (orchestrates everything)         │
│  - PredicateModelAdapter (ModelChecker compatibility)           │
│  - WitnessPredicateProposition (formula evaluation)            │
│  - WitnessPredicateStructure (model display)                   │
└───────────┬───────────────────────────────┬─────────────────────┘
            │                               │
┌───────────▼────────────┐      ┌──────────▼─────────────────────┐
│   witness_model.py     │      │   witness_constraints.py       │
│  - WitnessAwareModel   │      │  - WitnessConstraintGenerator  │
│  - WitnessRegistry     │      │  - Three-condition semantics   │
└───────────┬────────────┘      └──────────┬─────────────────────┘
            │                               │
            └───────────────┬───────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────────┐
│                      operators.py                                │
│  - PredicateExclusionOperator (queries witness predicates)      │
│  - PredicateConjunctionOperator                                 │
│  - PredicateDisjunctionOperator                                 │
│  - PredicateIdentityOperator                                    │
└─────────────────────────────────────────────────────────────────┘
```

## Module 1: witness_model.py - The Core Innovation

This module contains the fundamental innovation that makes Attempt 9 successful.

### WitnessAwareModel Class

```python
class WitnessAwareModel(z3.ModelRef):
    """Extended Z3 model that treats witness functions as queryable predicates."""
```

**Key Innovation**: This class extends Z3's ModelRef to provide direct access to witness functions after constraint solving.

**Critical Methods**:

1. **`__init__(self, model, semantics, witness_predicates)`**
   - Wraps a standard Z3 model
   - Stores reference to semantics and witness predicates
   - Maintains the model's connection to witness functions

2. **`get_h_witness(self, formula_str: str, state: int) -> Optional[int]`**
   - Retrieves the h-witness value for a given formula and state
   - Converts between integer and BitVector representations
   - Returns None if no witness exists
   
   ```python
   def get_h_witness(self, formula_str: str, state: int) -> Optional[int]:
       h_pred = self.witness_predicates.get(f"{formula_str}_h")
       if h_pred is None:
           return None
       state_bv = z3.BitVecVal(state, self.semantics.N)
       result = self.eval(h_pred(state_bv))
       if z3.is_bv_value(result):
           return result.as_long()
       return None
   ```

3. **`get_y_witness(self, formula_str: str, state: int) -> Optional[int]`**
   - Similar to get_h_witness but for y-witness values
   - Essential for verifying the exclusion condition

**Why This Succeeds**: Previous attempts lost witness information after constraint generation. By wrapping the Z3 model and maintaining references to witness predicates, we can query witness values during the truth evaluation phase.

### WitnessPredicateRegistry Class

```python
class WitnessPredicateRegistry:
    """Centralized registry for witness predicates ensuring consistency."""
```

**Purpose**: Maintains a consistent set of witness functions across all phases of model checking.

**Key Methods**:

1. **`register_witness_predicates(self, formula_str: str)`**
   - Creates Z3 Function objects for h and y witnesses
   - Uses consistent naming scheme: `{formula}_h` and `{formula}_y`
   - Prevents duplicate registration
   
   ```python
   def register_witness_predicates(self, formula_str: str):
       if f"{formula_str}_h" not in self.predicates:
           h_pred = z3.Function(f"{formula_str}_h", 
                               z3.BitVecSort(self.N), 
                               z3.BitVecSort(self.N))
           y_pred = z3.Function(f"{formula_str}_y", 
                               z3.BitVecSort(self.N), 
                               z3.BitVecSort(self.N))
           self.predicates[f"{formula_str}_h"] = h_pred
           self.predicates[f"{formula_str}_y"] = y_pred
   ```

**Innovation**: The registry pattern ensures that the same witness functions are used during constraint generation and later during model querying, maintaining consistency across phases.

## Module 2: witness_constraints.py - Three-Condition Semantics

This module generates the constraints that define witness predicate behavior according to exclusion semantics.

### WitnessConstraintGenerator Class

```python
class WitnessConstraintGenerator:
    """Generates Z3 constraints defining witness predicate behavior."""
```

**Purpose**: Translates the three-condition exclusion semantics into Z3 constraints.

**The Three Conditions**:
1. **Exclusion Condition**: For each verifier v of A, y(v) ⊑ v and h(v) excludes y(v)
2. **Upper Bound**: For each verifier v of A, h(v) ⊑ state
3. **Minimality**: state is the smallest satisfying conditions 1 and 2

**Key Method**:

```python
def generate_witness_constraints(self, formula_str: str, argument_ast, eval_point) -> z3.BoolRef:
    """Generate constraints defining h and y for the given exclusion formula."""
    
    # Get registered predicates
    h_pred = self.semantics.witness_registry.predicates[f"{formula_str}_h"]
    y_pred = self.semantics.witness_registry.predicates[f"{formula_str}_y"]
    
    constraints = []
    
    # For each potential state
    for state_int in range(2**self.semantics.N):
        state = z3.BitVecVal(state_int, self.semantics.N)
        
        # Check if this state could verify the exclusion
        if self._could_verify_exclusion(state_int):
            # Generate three-condition constraints
            constraint = self._witness_constraints_for_state(
                state, h_pred, y_pred, argument_ast, eval_point
            )
            constraints.append(constraint)
    
    return z3.Or(*constraints) if constraints else z3.BoolVal(False)
```

**Innovation**: By generating constraints that define witness predicates as Z3 functions, we ensure they remain part of the model and can be queried later.

## Module 3: semantic.py - Orchestration and Integration

This module orchestrates the entire system and integrates with the ModelChecker framework.

### WitnessPredicateSemantics Class

```python
class WitnessPredicateSemantics(SemanticDefaults):
    """Main semantics class that orchestrates witness predicate functionality."""
```

**Key Responsibilities**:
1. Initialize and manage the witness registry
2. Override model building to include witness constraints
3. Provide formula-to-string conversion for consistent naming
4. Define semantic relations (conflicts, overlaps, exhausts)

**Critical Override - build_model()**:

```python
def build_model(self):
    """Build model with witness predicate support."""
    
    # First pass: Register all witness predicates
    self._register_witness_predicates_recursive(self.premises)
    self._register_witness_predicates_recursive(self.conclusions)
    
    # Generate standard constraints
    solver = z3.Solver()
    standard_constraints = self._generate_standard_constraints()
    solver.add(standard_constraints)
    
    # Generate witness constraints for all registered predicates
    witness_constraints = self._generate_all_witness_constraints()
    solver.add(witness_constraints)
    
    # Solve and wrap result
    if solver.check() == z3.sat:
        z3_model = solver.model()
        return WitnessAwareModel(
            z3_model, 
            self, 
            self.witness_registry.predicates
        )
    return None
```

**Innovation**: The two-pass approach (registration then constraint generation) ensures all witness predicates exist before any constraints reference them.

### Formula String Conversion

```python
def _formula_to_string(self, formula) -> str:
    """Convert formula AST to consistent string representation."""
    if hasattr(formula, 'sentence_letter'):
        return str(formula.sentence_letter)
    elif hasattr(formula, 'operator'):
        op_str = formula.operator.name
        args = [self._formula_to_string(arg) for arg in formula.arguments]
        return f"{op_str}({','.join(args)})"
    return str(formula)
```

**Purpose**: Ensures consistent naming of witness predicates across different formula representations.

## Module 4: operators.py - Semantic Operators

This module implements the logical operators that work with witness predicates.

### PredicateExclusionOperator - The Heart of the Solution

```python
class PredicateExclusionOperator(Operator):
    """Exclusion operator that queries witness predicates from the model."""
```

**Key Innovation - compute_verifiers()**:

```python
def compute_verifiers(self, argument, model, eval_point):
    """Compute verifiers by querying witness predicates."""
    
    # Get verifiers of the argument
    arg_verifiers = self.semantics.extended_compute_verifiers(
        argument, model, eval_point
    )
    
    # Get formula string for witness lookup
    formula_str = f"\\exclude({self.semantics._formula_to_string(argument)})"
    
    verifiers = []
    for state in range(2**self.semantics.N):
        if self._verifies_exclusion_with_predicates(
            state, formula_str, arg_verifiers, model
        ):
            verifiers.append(state)
    
    return verifiers
```

**The Verification Logic**:

```python
def _verifies_exclusion_with_predicates(self, state: int, formula_str: str,
                                      arg_verifiers: List[int],
                                      model: WitnessAwareModel) -> bool:
    """Check if state verifies exclusion using witness predicates."""
    
    # Verify three conditions using witness predicates
    for v in arg_verifiers:
        h_v = model.get_h_witness(formula_str, v)
        y_v = model.get_y_witness(formula_str, v)
        
        if h_v is None or y_v is None:
            return False
        
        # Condition 1: y_v ⊑ v and h_v excludes y_v
        if not self._eval_is_part_of(y_v, v, model):
            return False
        if not self._eval_excludes(h_v, y_v, model):
            return False
        
        # Condition 2: h_v ⊑ state
        if not self._eval_is_part_of(h_v, state, model):
            return False
    
    # Condition 3: minimality
    return self._check_minimality(state, formula_str, arg_verifiers, model)
```

**Why This Works**: By querying witness predicates from the model during verifier computation, we can correctly determine which states verify exclusion formulas. This was impossible in previous attempts where witness information was lost.

### Other Operators

The implementation includes standard operators that maintain compatibility:

1. **PredicateConjunctionOperator**: Standard fusion-based semantics
2. **PredicateDisjunctionOperator**: Standard union semantics  
3. **PredicateIdentityOperator**: Verifier set equality

**Important Fix**: The conjunction operator uses the correct quantifier from `model_checker.utils`:

```python
from model_checker.utils import Exists

def extended_verify(self, state, arg1, arg2, eval_point):
    x1 = z3.BitVec(f'conj_x1_{self.semantics.counter}', self.semantics.N)
    x2 = z3.BitVec(f'conj_x2_{self.semantics.counter}', self.semantics.N)
    
    return Exists(
        [x1, x2],
        z3.And(
            self.semantics.fusion(x1, x2) == state,  # fusion first
            self.semantics.extended_verify(x1, arg1, eval_point),
            self.semantics.extended_verify(x2, arg2, eval_point),
        )
    )
```

## Module 5: examples.py - Test Suite

Contains 41 test examples that validate the implementation, including previously problematic cases.

## Key Innovations Summary

1. **Persistent Witness Functions**: Making witnesses Z3 Function objects that persist in the model
2. **Model Wrapping**: WitnessAwareModel provides query interface to witness predicates
3. **Registry Pattern**: Centralized management ensures consistency across phases
4. **Two-Pass Building**: Registration before constraint generation prevents ordering issues
5. **Direct Querying**: Operators can query witness values during verifier computation
6. **Clean Integration**: Follows ModelChecker patterns while extending functionality

## Why Previous Attempts Failed

1. **Attempts 1-5**: Generated witness constraints inline but lost access after solving
2. **Attempt 6**: IncCtx approach created complex state management issues
3. **Attempt 7**: Defined functions but lacked infrastructure to query them
4. **Attempt 8**: Missing registry and model wrapping made witnesses inaccessible

## Conclusion

Attempt 9 succeeds by recognizing that witness functions must be first-class citizens of the model, not temporary artifacts. The clean architecture maintains the ModelChecker's two-phase design while ensuring witness information flows correctly between phases. This elegant solution demonstrates that complex semantic challenges can be solved through careful architectural design rather than brute force approaches.