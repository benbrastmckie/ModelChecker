# Attempt 8: Single-Phase Architecture Implementation Plan

## Executive Summary

This document outlines the implementation of Strategy C1: Single-Phase Architecture, which merges constraint generation and truth evaluation into one unified phase. This approach fundamentally solves the witness accessibility problem by maintaining witness functions throughout the entire model checking process.

## Core Concept

Instead of the traditional two-phase approach:
1. Generate constraints 
2. Evaluate truth

We implement a unified approach:
1. Generate constraints WITH witness tracking AND evaluate truth simultaneously

The key innovation is maintaining a **witness context** that bridges syntactic constraint generation with semantic truth evaluation.

## Architecture Overview

### Key Components

1. **SinglePhaseSemantics**: Replaces the standard ExclusionSemantics with unified constraint/evaluation
2. **WitnessContext**: Maintains witness functions and their interpretations during solving
3. **UnifiedSolver**: Extended Z3 solver that tracks witness functions
4. **SinglePhaseOperators**: Operators that generate constraints while preserving witness access

### Module Structure

```
attempt8_single_phase/
|-- __init__.py
|-- semantic.py          # SinglePhaseSemantics implementation
|-- operators.py         # Operators with witness tracking
|-- examples.py          # Standard examples (same syntax)
|-- witness_context.py   # WitnessContext implementation
|-- unified_solver.py    # Extended solver with witness tracking
|-- model_adapter.py     # Adapter to standard ModelChecker interface
```

## Detailed Implementation

### 1. witness_context.py

```python
"""
Witness context maintains the connection between syntactic witnesses
and their semantic interpretations throughout solving.
"""

import z3
from typing import Dict, Any, Optional, Tuple

class WitnessFunction:
    """Represents a witness function with its constraints and values."""
    
    def __init__(self, name: str, domain_sort, range_sort):
        self.name = name
        self.z3_func = z3.Function(name, domain_sort, range_sort)
        self.constraints = []
        self.interpretation = {}  # Will be populated during solving
        
    def add_constraint(self, constraint):
        """Add a constraint involving this witness function."""
        self.constraints.append(constraint)
        
    def set_value(self, input_val, output_val):
        """Set a specific value in the interpretation."""
        self.interpretation[input_val] = output_val
        
    def get_value(self, input_val):
        """Get the witness value for given input."""
        return self.interpretation.get(input_val)

class WitnessContext:
    """
    Maintains all witness functions and their relationships.
    This is the key to single-phase architecture.
    """
    
    def __init__(self):
        self.witnesses: Dict[str, WitnessFunction] = {}
        self.formula_witnesses: Dict[str, str] = {}  # formula_id -> witness_name
        
    def create_witness(self, formula_id: str, name: str, 
                      domain_sort, range_sort) -> WitnessFunction:
        """Create a new witness function for a formula."""
        witness = WitnessFunction(name, domain_sort, range_sort)
        self.witnesses[name] = witness
        self.formula_witnesses[formula_id] = name
        return witness
        
    def get_witness_for_formula(self, formula_id: str) -> Optional[WitnessFunction]:
        """Get the witness function associated with a formula."""
        witness_name = self.formula_witnesses.get(formula_id)
        if witness_name:
            return self.witnesses.get(witness_name)
        return None
        
    def extract_from_model(self, model):
        """
        Extract witness interpretations from Z3 model.
        This is called during solving, not after.
        """
        for witness in self.witnesses.values():
            # Extract interpretation for this witness function
            func_interp = model.eval(witness.z3_func)
            if z3.is_func_interp(func_interp):
                # Store the interpretation
                for i in range(func_interp.num_entries()):
                    entry = func_interp.entry(i)
                    args = [entry.arg_value(j) for j in range(entry.num_args())]
                    value = entry.value()
                    if len(args) == 1:
                        witness.set_value(args[0].as_long(), value.as_long())
                        
    def clear(self):
        """Clear all witness information."""
        self.witnesses.clear()
        self.formula_witnesses.clear()
```

### 2. unified_solver.py

```python
"""
Unified solver that maintains witness accessibility during solving.
"""

import z3
from typing import Optional, List, Any
from .witness_context import WitnessContext

class UnifiedSolver:
    """
    Extended Z3 solver that tracks witness functions and makes them
    accessible during and after solving.
    """
    
    def __init__(self, witness_context: WitnessContext):
        self.solver = z3.Solver()
        self.witness_context = witness_context
        self.model: Optional[z3.ModelRef] = None
        
    def add(self, constraint):
        """Add constraint to solver."""
        self.solver.add(constraint)
        
    def push(self):
        """Push solver state."""
        self.solver.push()
        
    def pop(self):
        """Pop solver state."""
        self.solver.pop()
        
    def check(self) -> z3.CheckSatResult:
        """
        Check satisfiability and extract witness interpretations
        if satisfiable.
        """
        result = self.solver.check()
        
        if result == z3.sat:
            self.model = self.solver.model()
            # Critical: Extract witness interpretations NOW
            self.witness_context.extract_from_model(self.model)
            
        return result
        
    def get_model(self) -> Optional[z3.ModelRef]:
        """Get the current model."""
        return self.model
        
    def get_witness_value(self, formula_id: str, input_val: int) -> Optional[int]:
        """
        Get witness value for a formula and input.
        This is the key method that bridges phases.
        """
        witness = self.witness_context.get_witness_for_formula(formula_id)
        if witness:
            return witness.get_value(input_val)
        return None
```

### 3. semantic.py

```python
"""
Single-phase semantics implementation for exclusion theory.
"""

import z3
from typing import List, Dict, Any, Optional, Tuple, Set
from model_checker.model import ModelDefaults
from .witness_context import WitnessContext
from .unified_solver import UnifiedSolver

class SinglePhaseSemantics(ModelDefaults):
    """
    Semantics implementation that unifies constraint generation
    and truth evaluation into a single phase.
    """
    
    def __init__(self, settings):
        super().__init__(settings)
        self.witness_context = WitnessContext()
        self.unified_solver = UnifiedSolver(self.witness_context)
        
    def build_model(self, eval_point):
        """
        Build model using single-phase approach.
        """
        # Clear previous witness context
        self.witness_context.clear()
        
        # Create new unified solver
        self.unified_solver = UnifiedSolver(self.witness_context)
        
        # Add frame constraints
        for constraint in self._get_frame_constraints():
            self.unified_solver.add(constraint)
            
        # Get atomic constraints from eval_point
        premises = eval_point.get("premises", [])
        conclusions = eval_point.get("conclusions", [])
        
        # Process premises with witness tracking
        for premise in premises:
            constraint = self._process_formula_with_witnesses(
                premise, eval_point, must_be_true=True
            )
            self.unified_solver.add(constraint)
            
        # Process conclusions with witness tracking  
        for conclusion in conclusions:
            constraint = self._process_formula_with_witnesses(
                conclusion, eval_point, must_be_true=False
            )
            self.unified_solver.add(constraint)
            
        # Check satisfiability (witness extraction happens here)
        if self.unified_solver.check() == z3.sat:
            return SinglePhaseModel(
                self.unified_solver.get_model(),
                self.witness_context,
                self
            )
        else:
            return None
            
    def _process_formula_with_witnesses(self, sentence, eval_point, 
                                      must_be_true: bool):
        """
        Process a formula, creating witness functions as needed.
        This is where we diverge from two-phase approach.
        """
        world = eval_point["world"]
        
        # For exclusion formulas, create witness function
        if sentence.operator.name == "uni_excl":
            formula_id = f"{sentence}_{world}"
            
            # Create witness functions h and y
            h_witness = self.witness_context.create_witness(
                formula_id + "_h",
                f"h_{self.counter}",
                z3.BitVecSort(self.N),
                z3.BitVecSort(self.N)
            )
            
            y_witness = self.witness_context.create_witness(
                formula_id + "_y", 
                f"y_{self.counter}",
                z3.BitVecSort(self.N),
                z3.BitVecSort(self.N)
            )
            
            self.counter += 1
            
            # Generate constraints using witness functions
            constraint = self._exclusion_constraint_with_witnesses(
                sentence, world, h_witness, y_witness, eval_point
            )
            
            # Add verification constraint
            if must_be_true:
                return z3.And(
                    constraint,
                    self.extended_verify(world, sentence, eval_point)
                )
            else:
                return z3.And(
                    constraint,
                    z3.Not(self.extended_verify(world, sentence, eval_point))
                )
        else:
            # Non-exclusion formulas use standard processing
            if must_be_true:
                return self.extended_verify(world, sentence, eval_point)
            else:
                return z3.Not(self.extended_verify(world, sentence, eval_point))
                
    def _exclusion_constraint_with_witnesses(self, sentence, world,
                                           h_witness, y_witness, eval_point):
        """
        Generate exclusion constraints with explicit witness tracking.
        """
        argument = sentence.arguments[0]
        x = z3.BitVec('x', self.N)
        
        # Three-condition constraint with witness functions
        condition1 = z3.ForAll([x],
            z3.Implies(
                self.extended_verify(x, argument, eval_point),
                z3.And(
                    self.is_part_of(y_witness.z3_func(x), x),
                    self.excludes(h_witness.z3_func(x), y_witness.z3_func(x))
                )
            )
        )
        
        condition2 = z3.ForAll([x],
            z3.Implies(
                self.extended_verify(x, argument, eval_point),
                self.is_part_of(h_witness.z3_func(x), world)
            )
        )
        
        # Minimality condition
        z = z3.BitVec('z', self.N)
        condition3 = z3.ForAll([z],
            z3.Implies(
                z3.And(
                    self.is_part_of(z, world),
                    z != world,
                    z3.ForAll([x],
                        z3.Implies(
                            self.extended_verify(x, argument, eval_point),
                            self.is_part_of(h_witness.z3_func(x), z)
                        )
                    )
                ),
                z3.Not(
                    z3.ForAll([x],
                        z3.Implies(
                            self.extended_verify(x, argument, eval_point),
                            z3.And(
                                self.is_part_of(y_witness.z3_func(x), x),
                                self.excludes(h_witness.z3_func(x), y_witness.z3_func(x))
                            )
                        )
                    )
                )
            )
        )
        
        return z3.And(condition1, condition2, condition3)


class SinglePhaseModel:
    """
    Model wrapper that provides access to witness functions.
    """
    
    def __init__(self, z3_model, witness_context, semantics):
        self.z3_model = z3_model
        self.witness_context = witness_context
        self.semantics = semantics
        
    def eval(self, expr):
        """Evaluate expression in model."""
        return self.z3_model.eval(expr)
        
    def get_witness_value(self, formula_id: str, input_val: int) -> Optional[int]:
        """Get witness value for formula."""
        return self.witness_context.get_witness_for_formula(formula_id)
```

### 4. operators.py

```python
"""
Operators implementation for single-phase architecture.
"""

from model_checker.syntactic import Operator, DefinedOperator
from typing import List, Set, Optional

class SinglePhaseExclusionOperator(Operator):
    """
    Exclusion operator that works with single-phase semantics.
    """
    
    def __init__(self, semantics):
        super().__init__("uni_excl", 1)
        self.semantics = semantics
        
    def compute_verifiers(self, argument, model, eval_point):
        """
        Compute verifiers using witness functions from the model.
        """
        if not isinstance(model, SinglePhaseModel):
            # Fallback for compatibility
            return []
            
        arg_verifiers = self.semantics.extended_compute_verifiers(
            argument, model, eval_point
        )
        
        verifiers = []
        for state in range(2**self.semantics.N):
            if self._verifies_with_witnesses(state, argument, model, 
                                           eval_point, arg_verifiers):
                verifiers.append(state)
                
        return verifiers
        
    def _verifies_with_witnesses(self, state, argument, model, 
                                eval_point, arg_verifiers):
        """
        Check if state verifies exclusion using witness functions.
        """
        # Get formula ID for witness lookup
        formula_id = f"uni_excl({argument})_{state}"
        
        # Check three conditions using witness values
        for v in arg_verifiers:
            # Get witness values from model
            h_v = model.get_witness_value(formula_id + "_h", v)
            y_v = model.get_witness_value(formula_id + "_y", v)
            
            if h_v is None or y_v is None:
                return False
                
            # Verify conditions
            if not model.semantics.eval_is_part_of(y_v, v, model.z3_model):
                return False
            if not model.semantics.eval_excludes(h_v, y_v, model.z3_model):
                return False
            if not model.semantics.eval_is_part_of(h_v, state, model.z3_model):
                return False
                
        # Check minimality
        # ... (minimality check implementation)
        
        return True
        
    def extended_verify(self, state, argument, eval_point):
        """
        Generate verification constraint (used during constraint building).
        """
        return self.semantics._process_formula_with_witnesses(
            self.create_sentence(argument), 
            {"world": state, **eval_point},
            must_be_true=True
        )


class SinglePhaseConjunctionOperator(Operator):
    """Conjunction operator for single-phase semantics."""
    
    def __init__(self, semantics):
        super().__init__("uni_and", 2)
        self.semantics = semantics
        
    def compute_verifiers(self, arg1, arg2, model, eval_point):
        """Standard conjunction semantics."""
        ver1 = self.semantics.extended_compute_verifiers(arg1, model, eval_point)
        ver2 = self.semantics.extended_compute_verifiers(arg2, model, eval_point)
        
        # Fusion of verifiers
        verifiers = []
        for v1 in ver1:
            for v2 in ver2:
                fusion = self.semantics.eval_fusion(v1, v2, model.z3_model)
                if fusion is not None:
                    verifiers.append(fusion.as_long())
                    
        return verifiers
        
    def extended_verify(self, state, arg1, arg2, eval_point):
        """Standard conjunction constraint."""
        x1 = z3.BitVec('x1', self.semantics.N)
        x2 = z3.BitVec('x2', self.semantics.N)
        
        return z3.Exists([x1, x2],
            z3.And(
                self.semantics.extended_verify(x1, arg1, eval_point),
                self.semantics.extended_verify(x2, arg2, eval_point),
                state == self.semantics.fusion(x1, x2)
            )
        )


# Similar implementations for other operators...


def create_operators(semantics):
    """Create all operators for single-phase semantics."""
    return {
        "uni_excl": SinglePhaseExclusionOperator(semantics),
        "uni_and": SinglePhaseConjunctionOperator(semantics),
        "uni_or": SinglePhaseDisjunctionOperator(semantics),
        "uni_id": SinglePhaseIdentityOperator(semantics)
    }
```

### 5. model_adapter.py

```python
"""
Adapter to make single-phase semantics compatible with standard ModelChecker.
"""

from model_checker.model import ModelConstraints
from .semantic import SinglePhaseSemantics

class SinglePhaseAdapter(ModelConstraints):
    """
    Adapts single-phase semantics to standard ModelChecker interface.
    """
    
    def __init__(self, settings):
        # Don't call super().__init__ to avoid two-phase initialization
        self.settings = settings
        self.semantics = SinglePhaseSemantics(settings)
        
    def build_model(self, eval_point):
        """
        Delegate to single-phase semantics.
        """
        return self.semantics.build_model(eval_point)
        
    def compute_verifiers(self, sentence, model, eval_point):
        """
        Delegate to operator's compute_verifiers.
        """
        operator = self.semantics.operators.get(sentence.operator.name)
        if operator:
            return operator.compute_verifiers(
                *sentence.arguments, model=model, eval_point=eval_point
            )
        return []
        
    # Other required methods delegated to semantics...
```

### 6. examples.py

```python
"""
Standard examples using single-phase exclusion theory.
Uses exactly the same syntax as other theories.
"""

from model_checker import examples

def double_negation():
    """Double negation: ??A ? A"""
    return examples.formula_example(
        premises=["\\exclude \\exclude A"],
        conclusions=["A"],
        description="Double negation elimination"
    )

def triple_negation():
    """Triple negation: ???A ? ?A"""
    return examples.formula_example(
        premises=["\\exclude \\exclude \\exclude A"],
        conclusions=["\\exclude A"],
        description="Triple negation"
    )

def neg_to_sent():
    """NEG_TO_SENT: ?A ? A"""
    return examples.sequent_example(
        premises=["\\exclude A"],
        conclusions=["A"],
        description="Negation to sentence (should have countermodel)"
    )

def demorgan_left_to_right():
    """DeMorgan's law: ?(A ' B) ? (?A ( ?B)"""
    return examples.formula_example(
        premises=["\\exclude (A \\and B)"],
        conclusions=["(\\exclude A) \\or (\\exclude B)"],
        description="DeMorgan's law (left to right)"
    )

# All other standard examples...

if __name__ == "__main__":
    # This allows running with dev_cli.py
    examples.run_examples(globals())
```

### 7. __init__.py

```python
"""
Single-phase exclusion theory implementation.
"""

from .semantic import SinglePhaseSemantics
from .operators import create_operators
from .model_adapter import SinglePhaseAdapter

# For ModelChecker discovery
DefaultSemantics = SinglePhaseAdapter

__all__ = ['SinglePhaseSemantics', 'create_operators', 'DefaultSemantics']
```

## Key Design Decisions

### 1. Witness Persistence
- Witness functions are created during constraint generation
- Their interpretations are extracted immediately when model is found
- No information loss between phases

### 2. Unified Processing
- Each formula is processed once with full context
- Constraints and witness tracking happen simultaneously
- No need to reconstruct witness values later

### 3. Compatibility Layer
- `SinglePhaseAdapter` provides standard ModelChecker interface
- Examples use identical syntax to other theories
- Can be run with dev_cli.py without modifications

### 4. Operator Integration
- Operators have access to witness values through the model
- `compute_verifiers` can query witness interpretations
- Maintains semantic correctness

## Implementation Phases

### Phase 1: Core Infrastructure (3-4 days)
1. Implement `WitnessContext` and `WitnessFunction`
2. Implement `UnifiedSolver` with witness extraction
3. Create basic `SinglePhaseSemantics` structure
4. Test witness extraction on simple examples

### Phase 2: Operator Implementation (2-3 days)
1. Implement `SinglePhaseExclusionOperator` with witness access
2. Adapt other operators for single-phase architecture
3. Ensure all operators work with witness context
4. Test operator interactions

### Phase 3: Integration (2-3 days)
1. Implement `SinglePhaseAdapter` for ModelChecker compatibility
2. Create standard examples.py
3. Test with dev_cli.py
4. Debug any integration issues

### Phase 4: Validation (2-3 days)
1. Run all problematic examples (NEG_TO_SENT, double negation, etc.)
2. Verify witness values are correctly extracted
3. Compare results with previous attempts
4. Performance testing and optimization

## Expected Outcomes

### Advantages
1. **Solves witness accessibility**: Witness functions remain accessible
2. **No approximations**: Exact semantics implementation
3. **Clean architecture**: Unified approach is conceptually simpler
4. **Debugging**: Can inspect witness values directly

### Challenges
1. **Framework integration**: Requires careful adapter implementation
2. **Performance**: May be slower due to integrated processing
3. **Complexity**: More complex than two-phase for simple formulas
4. **Testing**: Need comprehensive tests for witness extraction

## Success Criteria

1. **Correctness**: All problematic examples find correct models
   - NEG_TO_SENT finds countermodel
   - Double/triple negation work correctly
   - DeMorgan's laws validated

2. **Compatibility**: Works with dev_cli.py without external changes

3. **Performance**: Reasonable performance for N d 4

4. **Maintainability**: Clean, documented code with clear separation of concerns

## Conclusion

The single-phase architecture represents a fundamental solution to the witness accessibility problem. By maintaining witness functions throughout the solving process, we eliminate the information loss that plagues two-phase approaches. While this requires significant architectural changes within the attempt directory, it promises to finally deliver correct implementation of exclusion semantics.
