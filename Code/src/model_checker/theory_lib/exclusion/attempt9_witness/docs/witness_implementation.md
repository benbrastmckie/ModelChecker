# Attempt 9: Witnesses as Model Predicates Implementation Plan

## Executive Summary

This document outlines the implementation of Strategy E1: Witnesses as Model Predicates, which fundamentally changes the model structure to include witness functions as first-class citizens. Instead of treating witnesses as ephemeral artifacts of constraint solving, they become persistent predicates within the model itself.

## Core Concept

Traditional approach:
- Model = {states, verify relation, exclude relation}
- Witnesses exist only during constraint generation

Witness predicate approach:
- Model = {states, verify relation, exclude relation, **witness predicates**}
- Witnesses are queryable model predicates alongside verify and exclude

This makes witness functions naturally accessible during truth evaluation because they are part of the model structure itself.

## Architecture Overview

### Key Components

1. **WitnessAwareModel**: Extended model structure with witness predicates
2. **WitnessPredicateSemantics**: Semantics that generates and uses witness predicates
3. **PredicateBasedOperators**: Operators that query witness predicates from the model
4. **WitnessConstraintGenerator**: Generates constraints for witness predicates

### Module Structure

```
attempt9_witness_predicate/
|-- __init__.py
|-- semantic.py              # WitnessPredicateSemantics
|-- operators.py             # Operators using witness predicates
|-- examples.py              # Standard examples (same syntax)
|-- witness_model.py         # WitnessAwareModel implementation
|-- witness_constraints.py   # Constraint generation for witnesses
|-- model_builder.py         # Extended model builder
```

## Detailed Implementation

### 1. witness_model.py

```python
"""
Extended model structure that includes witness functions as predicates.
"""

import z3
from typing import Dict, Optional, Set, Tuple, Any
from model_checker.model import ModelDefaults

class WitnessAwareModel:
    """
    Model that treats witness functions as first-class predicates.
    
    In addition to standard predicates (verify, exclude, fusion, etc.),
    this model includes witness predicates for exclusion formulas.
    """
    
    def __init__(self, z3_model, semantics, witness_predicates):
        self.z3_model = z3_model
        self.semantics = semantics
        self.witness_predicates = witness_predicates
        # Cache for evaluated predicates
        self._cache = {}
        
    def eval(self, expr):
        """Standard Z3 model evaluation."""
        return self.z3_model.eval(expr)
        
    def has_witness_for(self, formula_str: str) -> bool:
        """Check if model has witness predicates for given formula."""
        return f"{formula_str}_h" in self.witness_predicates
        
    def get_h_witness(self, formula_str: str, state: int) -> Optional[int]:
        """
        Get h(state) for the given formula.
        This is the key method that makes witnesses accessible.
        """
        h_pred = self.witness_predicates.get(f"{formula_str}_h")
        if h_pred is None:
            return None
            
        # Query the witness predicate
        result = self.eval(h_pred(state))
        if z3.is_bv_value(result):
            return result.as_long()
        return None
        
    def get_y_witness(self, formula_str: str, state: int) -> Optional[int]:
        """Get y(state) for the given formula."""
        y_pred = self.witness_predicates.get(f"{formula_str}_y")
        if y_pred is None:
            return None
            
        result = self.eval(y_pred(state))
        if z3.is_bv_value(result):
            return result.as_long()
        return None
        
    def get_all_witness_values(self, formula_str: str) -> Dict[int, Tuple[int, int]]:
        """Get all witness values for a formula."""
        witness_map = {}
        
        for state in range(2**self.semantics.N):
            h_val = self.get_h_witness(formula_str, state)
            y_val = self.get_y_witness(formula_str, state)
            if h_val is not None and y_val is not None:
                witness_map[state] = (h_val, y_val)
                
        return witness_map


class WitnessPredicateRegistry:
    """
    Registry for all witness predicates in the model.
    Tracks which formulas have associated witness functions.
    """
    
    def __init__(self, N: int):
        self.N = N
        self.predicates: Dict[str, z3.FuncDeclRef] = {}
        self.formula_mapping: Dict[str, Set[str]] = {}
        
    def register_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """
        Register witness predicates h and y for a formula.
        Returns (h_predicate, y_predicate).
        """
        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"
        
        # Create Z3 functions for witness predicates
        h_pred = z3.Function(h_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
        y_pred = z3.Function(y_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
        
        self.predicates[h_name] = h_pred
        self.predicates[y_name] = y_pred
        
        self.formula_mapping[formula_str] = {h_name, y_name}
        
        return h_pred, y_pred
        
    def get_all_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Get all registered witness predicates."""
        return self.predicates.copy()
        
    def clear(self):
        """Clear all registered predicates."""
        self.predicates.clear()
        self.formula_mapping.clear()
```

### 2. witness_constraints.py

```python
"""
Constraint generation for witness predicates.
"""

import z3
from typing import List, Tuple, Optional

class WitnessConstraintGenerator:
    """
    Generates constraints that define witness predicates
    based on the three-condition exclusion semantics.
    """
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.N = semantics.N
        
    def generate_witness_constraints(self, formula_str: str, formula_ast,
                                   h_pred: z3.FuncDeclRef,
                                   y_pred: z3.FuncDeclRef,
                                   eval_point) -> List[z3.BoolRef]:
        """
        Generate constraints that define the witness predicates
        for an exclusion formula.
        """
        constraints = []
        
        # For each potential verifier state
        for state in range(2**self.N):
            state_bv = z3.BitVecVal(state, self.N)
            
            # Check if this state could verify the exclusion
            if self._could_verify_exclusion(state, formula_ast, eval_point):
                # Generate constraints for witness values at this state
                state_constraints = self._witness_constraints_for_state(
                    state_bv, formula_ast, h_pred, y_pred, eval_point
                )
                constraints.extend(state_constraints)
            else:
                # No witness needed for non-verifying states
                # Could optionally constrain to undefined/zero
                pass
                
        return constraints
        
    def _could_verify_exclusion(self, state: int, formula_ast, eval_point) -> bool:
        """
        Heuristic check if a state could potentially verify an exclusion.
        This helps reduce the number of constraints.
        """
        # For now, consider all states as potential verifiers
        # Could be optimized based on formula structure
        return True
        
    def _witness_constraints_for_state(self, state, formula_ast,
                                     h_pred, y_pred, eval_point) -> List[z3.BoolRef]:
        """
        Generate witness constraints for a specific state verifying exclusion.
        """
        constraints = []
        argument = formula_ast.arguments[0]
        x = z3.BitVec('x', self.N)
        
        # If state verifies the exclusion, then:
        verify_excl = self.semantics.extended_verify(state, formula_ast, eval_point)
        
        # Condition 1: For all verifiers of argument, h and y satisfy requirements
        condition1 = z3.ForAll([x],
            z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                z3.And(
                    self.semantics.is_part_of(y_pred(x), x),
                    self.semantics.excludes(h_pred(x), y_pred(x))
                )
            )
        )
        
        # Condition 2: All h values are part of state
        condition2 = z3.ForAll([x],
            z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                self.semantics.is_part_of(h_pred(x), state)
            )
        )
        
        # Condition 3: Minimality
        z = z3.BitVec('z', self.N)
        condition3 = self._minimality_constraint(state, argument, h_pred, y_pred, eval_point)
        
        # If state verifies exclusion, then all three conditions hold
        constraints.append(
            z3.Implies(
                verify_excl,
                z3.And(condition1, condition2, condition3)
            )
        )
        
        # Conversely, if all conditions hold, state verifies exclusion
        constraints.append(
            z3.Implies(
                z3.And(condition1, condition2, condition3),
                verify_excl
            )
        )
        
        return constraints
        
    def _minimality_constraint(self, state, argument, h_pred, y_pred, eval_point):
        """Generate the minimality constraint for witness predicates."""
        z = z3.BitVec('z', self.N)
        x = z3.BitVec('x', self.N)
        
        return z3.ForAll([z],
            z3.Implies(
                z3.And(
                    self.semantics.is_part_of(z, state),
                    z != state,
                    # All h values fit in z
                    z3.ForAll([x],
                        z3.Implies(
                            self.semantics.extended_verify(x, argument, eval_point),
                            self.semantics.is_part_of(h_pred(x), z)
                        )
                    )
                ),
                # Then z doesn't satisfy condition 1
                z3.Not(
                    z3.ForAll([x],
                        z3.Implies(
                            self.semantics.extended_verify(x, argument, eval_point),
                            z3.And(
                                self.semantics.is_part_of(y_pred(x), x),
                                self.semantics.excludes(h_pred(x), y_pred(x))
                            )
                        )
                    )
                )
            )
        )
```

### 3. semantic.py

```python
"""
Witness predicate semantics implementation.
"""

import z3
from typing import List, Dict, Set, Optional
from model_checker.model import ModelDefaults
from .witness_model import WitnessAwareModel, WitnessPredicateRegistry
from .witness_constraints import WitnessConstraintGenerator

class WitnessPredicateSemantics(ModelDefaults):
    """
    Semantics that includes witness functions as model predicates.
    """
    
    def __init__(self, settings):
        super().__init__(settings)
        self.witness_registry = WitnessPredicateRegistry(self.N)
        self.constraint_generator = WitnessConstraintGenerator(self)
        self._processed_formulas = set()
        
    def build_model(self, eval_point):
        """
        Build model with witness predicates included.
        """
        # Clear previous state
        self.witness_registry.clear()
        self._processed_formulas.clear()
        
        # Create solver
        solver = z3.Solver()
        
        # Add frame constraints
        for constraint in self._get_frame_constraints():
            solver.add(constraint)
            
        # Process premises and conclusions
        premises = eval_point.get("premises", [])
        conclusions = eval_point.get("conclusions", [])
        
        # First pass: identify all exclusion formulas and create witness predicates
        all_formulas = premises + conclusions
        for formula in all_formulas:
            self._register_witness_predicates_recursive(formula)
            
        # Add witness predicate constraints
        witness_constraints = self._generate_all_witness_constraints(eval_point)
        for constraint in witness_constraints:
            solver.add(constraint)
            
        # Add premise constraints
        world = eval_point["world"]
        for premise in premises:
            solver.add(self.extended_verify(world, premise, eval_point))
            
        # Add conclusion constraints (negated)
        for conclusion in conclusions:
            solver.add(z3.Not(self.extended_verify(world, conclusion, eval_point)))
            
        # Check satisfiability
        if solver.check() == z3.sat:
            z3_model = solver.model()
            return WitnessAwareModel(
                z3_model,
                self,
                self.witness_registry.get_all_predicates()
            )
        else:
            return None
            
    def _register_witness_predicates_recursive(self, formula):
        """
        Recursively register witness predicates for all exclusion
        subformulas in the formula.
        """
        if self._is_processed(formula):
            return
            
        if formula.operator.name == "uni_excl":
            # Register witness predicates for this exclusion
            formula_str = self._formula_to_string(formula)
            self.witness_registry.register_witness_predicates(formula_str)
            self._processed_formulas.add(formula_str)
            
        # Recurse on arguments
        for arg in formula.arguments:
            self._register_witness_predicates_recursive(arg)
            
    def _is_processed(self, formula) -> bool:
        """Check if formula already has witness predicates."""
        formula_str = self._formula_to_string(formula)
        return formula_str in self._processed_formulas
        
    def _formula_to_string(self, formula) -> str:
        """Convert formula to unique string representation."""
        if hasattr(formula, 'proposition'):
            return formula.proposition
        elif hasattr(formula, 'operator'):
            args_str = ",".join(self._formula_to_string(arg) for arg in formula.arguments)
            return f"{formula.operator.name}({args_str})"
        else:
            return str(formula)
            
    def _generate_all_witness_constraints(self, eval_point) -> List[z3.BoolRef]:
        """
        Generate constraints for all registered witness predicates.
        """
        constraints = []
        
        for formula_str in self._processed_formulas:
            # Get the formula AST (would need to maintain mapping)
            formula_ast = self._get_formula_ast(formula_str)
            if formula_ast and formula_ast.operator.name == "uni_excl":
                h_pred, y_pred = self._get_witness_predicates(formula_str)
                
                formula_constraints = self.constraint_generator.generate_witness_constraints(
                    formula_str, formula_ast, h_pred, y_pred, eval_point
                )
                constraints.extend(formula_constraints)
                
        return constraints
        
    def _get_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """Get witness predicates for a formula."""
        h_pred = self.witness_registry.predicates.get(f"{formula_str}_h")
        y_pred = self.witness_registry.predicates.get(f"{formula_str}_y")
        return h_pred, y_pred
        
    def _get_formula_ast(self, formula_str: str):
        """Get formula AST from string (would need proper implementation)."""
        # This would need to maintain a mapping during registration
        # For now, placeholder
        return None


class PredicateModelAdapter:
    """
    Adapter to make witness predicate semantics compatible with ModelChecker.
    """
    
    def __init__(self, settings):
        self.semantics = WitnessPredicateSemantics(settings)
        self.settings = settings
        
    def build_model(self, eval_point):
        """Build model using witness predicate approach."""
        return self.semantics.build_model(eval_point)
        
    # Other ModelChecker interface methods...
```

### 4. operators.py

```python
"""
Operators that work with witness predicates.
"""

import z3
from model_checker.syntactic import Operator
from typing import List, Set
from .witness_model import WitnessAwareModel

class PredicateExclusionOperator(Operator):
    """
    Unilateral negation operator that queries witness predicates from the model.
    """
    
    def __init__(self, semantics):
        super().__init__("uni_excl", 1)
        self.semantics = semantics
        
    def compute_verifiers(self, argument, model, eval_point):
        """
        Compute verifiers by querying witness predicates.
        """
        if not isinstance(model, WitnessAwareModel):
            # Fallback for compatibility
            return []
            
        # Get verifiers of the argument
        arg_verifiers = self.semantics.extended_compute_verifiers(
            argument, model, eval_point
        )
        
        # Get formula string for witness lookup
        formula_str = f"uni_excl({self.semantics._formula_to_string(argument)})"
        
        verifiers = []
        for state in range(2**self.semantics.N):
            if self._verifies_exclusion_with_predicates(
                state, formula_str, arg_verifiers, model
            ):
                verifiers.append(state)
                
        return verifiers
        
    def _verifies_exclusion_with_predicates(self, state: int, formula_str: str,
                                          arg_verifiers: List[int],
                                          model: WitnessAwareModel) -> bool:
        """
        Check if state verifies exclusion using witness predicates.
        """
        # Check if model has witness predicates for this formula
        if not model.has_witness_for(formula_str):
            return False
            
        # Verify three conditions using witness predicates
        # Condition 1 & 2: For each verifier, check h and y values
        for v in arg_verifiers:
            h_v = model.get_h_witness(formula_str, v)
            y_v = model.get_y_witness(formula_str, v)
            
            if h_v is None or y_v is None:
                return False
                
            # Check condition 1: y_v ? v and h_v excludes y_v
            if not model.semantics.eval_is_part_of(y_v, v, model.z3_model):
                return False
            if not model.semantics.eval_excludes(h_v, y_v, model.z3_model):
                return False
                
            # Check condition 2: h_v ? state
            if not model.semantics.eval_is_part_of(h_v, state, model.z3_model):
                return False
                
        # Check condition 3: minimality
        if not self._check_minimality(state, formula_str, arg_verifiers, model):
            return False
            
        return True
        
    def _check_minimality(self, state: int, formula_str: str,
                         arg_verifiers: List[int],
                         model: WitnessAwareModel) -> bool:
        """
        Check minimality condition using witness predicates.
        """
        # For each proper part z of state
        for z in range(2**self.semantics.N):
            if z == state:
                continue
                
            if not model.semantics.eval_is_part_of(z, state, model.z3_model):
                continue
                
            # Check if all h values fit in z
            all_h_fit_in_z = True
            for v in arg_verifiers:
                h_v = model.get_h_witness(formula_str, v)
                if h_v is not None:
                    if not model.semantics.eval_is_part_of(h_v, z, model.z3_model):
                        all_h_fit_in_z = False
                        break
                        
            if all_h_fit_in_z:
                # z should not satisfy condition 1
                z_satisfies_cond1 = True
                for v in arg_verifiers:
                    h_v = model.get_h_witness(formula_str, v)
                    y_v = model.get_y_witness(formula_str, v)
                    
                    if h_v is None or y_v is None:
                        z_satisfies_cond1 = False
                        break
                        
                    if not (model.semantics.eval_is_part_of(y_v, v, model.z3_model) and
                           model.semantics.eval_excludes(h_v, y_v, model.z3_model)):
                        z_satisfies_cond1 = False
                        break
                        
                if z_satisfies_cond1:
                    # Minimality violated
                    return False
                    
        return True
        
    def extended_verify(self, state, argument, eval_point):
        """
        Standard constraint generation for exclusion.
        """
        # This generates the constraint that state verifies exclusion
        # The actual witness values are determined by the witness predicates
        return self.semantics._exclusion_verify_constraint(state, argument, eval_point)


# Similar implementations for other operators...


def create_operators(semantics):
    """Create operators for witness predicate semantics."""
    return {
        "uni_excl": PredicateExclusionOperator(semantics),
        "uni_and": PredicateConjunctionOperator(semantics),
        "uni_or": PredicateDisjunctionOperator(semantics),
        "uni_id": PredicateIdentityOperator(semantics)
    }
```

### 5. examples.py

```python
"""
Standard examples using witness predicate exclusion theory.
Uses exactly the same syntax as other theories.
"""

from model_checker import examples

def double_negation():
    """Double negation: NOT NOT A -> A"""
    return examples.formula_example(
        premises=["\\exclude \\exclude A"],
        conclusions=["A"],
        description="Double negation elimination"
    )

def triple_negation():
    """Triple negation: NOT NOT NOT A -> NOT A"""
    return examples.formula_example(
        premises=["\\exclude \\exclude \\exclude A"],
        conclusions=["\\exclude A"],
        description="Triple negation"
    )

def neg_to_sent():
    """NEG_TO_SENT: NOT A |- A"""
    return examples.sequent_example(
        premises=["\\exclude A"],
        conclusions=["A"],
        description="Negation to sentence (should have countermodel)"
    )

def demorgan_left_to_right():
    """DeMorgan's law: NOT(A AND B) -> (NOT A OR NOT B)"""
    return examples.formula_example(
        premises=["\\exclude (A \\and B)"],
        conclusions=["(\\exclude A) \\or (\\exclude B)"],
        description="DeMorgan's law (left to right)"
    )

def no_contradictions():
    """No contradictions: NOT(A AND NOT A)"""
    return examples.validity_example(
        formula="\\exclude (A \\and (\\exclude A))",
        description="No contradictions"
    )

# All other standard examples...

if __name__ == "__main__":
    # This allows running with dev_cli.py
    examples.run_examples(globals())
```

### 6. __init__.py

```python
"""
Witness predicate exclusion theory implementation.
"""

from .semantic import WitnessPredicateSemantics, PredicateModelAdapter
from .operators import create_operators

# For ModelChecker discovery
DefaultSemantics = PredicateModelAdapter

__all__ = ['WitnessPredicateSemantics', 'create_operators', 'DefaultSemantics']
```

## Key Design Decisions

### 1. Model Structure Extension
- Witness functions become queryable predicates in the model
- Model can answer questions like "what is h(5)?" directly
- No reconstruction or interpretation needed

### 2. Predicate Registration
- All exclusion formulas get witness predicates registered upfront
- Predicates are created before constraint generation
- Ensures all necessary witnesses exist in the model

### 3. Constraint Generation
- Constraints define the witness predicates based on three conditions
- Bidirectional constraints ensure predicates match semantics exactly
- Minimality encoded as constraints on the predicates

### 4. Operator Simplification  
- Operators simply query witness predicates from model
- No complex reconstruction logic needed
- Clean separation between constraint generation and evaluation

## Implementation Phases

### Phase 1: Model Extension (2-3 days)
1. Implement `WitnessAwareModel` with predicate queries
2. Implement `WitnessPredicateRegistry` for tracking
3. Test basic predicate storage and retrieval
4. Verify model extension doesn't break standard operations

### Phase 2: Constraint Generation (3-4 days)
1. Implement `WitnessConstraintGenerator`
2. Generate three-condition constraints for predicates
3. Handle minimality constraint encoding
4. Test constraint correctness on simple examples

### Phase 3: Semantic Integration (2-3 days)
1. Implement `WitnessPredicateSemantics`
2. Handle predicate registration for all formulas
3. Integrate constraint generation
4. Test model building with predicates

### Phase 4: Operator Implementation (2 days)
1. Implement `PredicateExclusionOperator`
2. Adapt other operators as needed
3. Test verifier computation using predicates
4. Verify semantic correctness

### Phase 5: Validation (2-3 days)
1. Run all problematic examples
2. Verify witness predicates are correctly populated
3. Compare with expected results
4. Performance testing

## Expected Outcomes

### Advantages
1. **Natural witness access**: Witnesses are just model predicates
2. **Clean architecture**: Clear separation of concerns
3. **Debugging friendly**: Can inspect witness predicates directly
4. **Extensible**: Easy to add more witness-based operators

### Challenges
1. **Constraint complexity**: More predicates mean more constraints
2. **Memory usage**: Storing witness predicates for all formulas
3. **Performance**: Querying predicates may be slower than direct computation
4. **Formula tracking**: Need to maintain formula-to-predicate mapping

## Success Criteria

1. **Correctness**:
   - NEG_TO_SENT finds correct countermodel
   - Double/triple negation work correctly
   - DeMorgan's laws validated
   - No false premises in countermodels

2. **Model Integrity**:
   - Witness predicates correctly reflect three conditions
   - Model satisfies all semantic constraints
   - Predicates are consistent with verify relation

3. **Compatibility**:
   - Works with dev_cli.py
   - Examples use standard syntax
   - No external framework changes

4. **Performance**:
   - Reasonable performance for N d 4
   - Predicate queries are efficient
   - Memory usage is manageable

## Comparison with Single-Phase Approach

| Aspect | Single-Phase (C1) | Witness Predicates (E1) |
|--------|-------------------|------------------------|
| Architecture Change | Major - unified phases | Moderate - extended model |
| Witness Access | During solving only | Anytime via predicates |
| Complexity | High - requires flow tracking | Medium - more constraints |
| Debugging | Moderate | Excellent - direct queries |
| Framework Fit | Requires significant adaptation | Natural extension |

## Conclusion

The witness predicate approach offers an elegant solution by making witnesses first-class citizens of the model. Instead of trying to extract or reconstruct witness functions, they simply exist as queryable predicates alongside verify and exclude. This approach maintains the clean separation between constraint generation and truth evaluation while ensuring witness accessibility. The main trade-off is increased constraint complexity for the benefit of natural witness access.
