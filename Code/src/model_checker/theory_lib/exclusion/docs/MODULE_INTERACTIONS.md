# Module Interactions: Detailed Flow Analysis

## Overview

This document traces the execution flow through the Attempt 9 implementation, showing exactly how modules interact to solve the False Premise Problem.

## Phase 1: Initialization and Setup

### 1.1 Theory Loading
```
User runs: ./dev_cli.py examples.py
    ↓
ModelChecker loads exclusion_theory dict from examples.py
    ↓
Creates instance of WitnessPredicateSemantics
```

### 1.2 Semantic Initialization
```python
WitnessPredicateSemantics.__init__(settings)
    │
    ├─► Creates WitnessPredicateRegistry(N)
    │       └─► Initializes empty predicates dict
    │
    ├─► Creates WitnessConstraintGenerator(self)
    │       └─► Stores reference to semantics
    │
    └─► Initializes semantic relations and frame constraints
```

## Phase 2: Model Building - The Critical Path

### 2.1 Registration Pass
```
WitnessPredicateSemantics.build_model()
    │
    ├─► _register_witness_predicates_recursive(premises)
    │       │
    │       └─► For each exclusion formula found:
    │               │
    │               └─► WitnessPredicateRegistry.register_witness_predicates(formula_str)
    │                       │
    │                       ├─► Creates h_pred = z3.Function(f"{formula}_h", ...)
    │                       └─► Creates y_pred = z3.Function(f"{formula}_y", ...)
    │
    └─► _register_witness_predicates_recursive(conclusions)
            └─► (same process)
```

**Key Point**: All witness predicates are registered BEFORE any constraints are generated.

### 2.2 Constraint Generation
```
WitnessPredicateSemantics.build_model() (continued)
    │
    ├─► Generate standard constraints (frame, atom, operator constraints)
    │
    └─► _generate_all_witness_constraints()
            │
            └─► For each registered formula:
                    │
                    └─► WitnessConstraintGenerator.generate_witness_constraints(formula, ast, eval_point)
                            │
                            ├─► Retrieves h_pred and y_pred from registry
                            │
                            └─► For each potential verifying state:
                                    │
                                    └─► _witness_constraints_for_state(state, h_pred, y_pred, ...)
                                            │
                                            ├─► Condition 1: ∀v. y(v) ⊑ v ∧ h(v) excludes y(v)
                                            ├─► Condition 2: ∀v. h(v) ⊑ state
                                            └─► Condition 3: Minimality constraint
```

### 2.3 Model Creation
```
WitnessPredicateSemantics.build_model() (final step)
    │
    └─► If solver.check() == SAT:
            │
            └─► return WitnessAwareModel(z3_model, self, registry.predicates)
                    │
                    ├─► Wraps Z3 model
                    ├─► Stores semantics reference
                    └─► Stores witness predicates dict
```

## Phase 3: Truth Evaluation - Where Magic Happens

### 3.1 Formula Evaluation Flow
```
User query: Is ¬A true at world w?
    │
    └─► WitnessPredicateProposition.true_at(eval_point)
            │
            └─► PredicateExclusionOperator.true_at(argument, eval_point)
                    │
                    └─► Checks if ∃x. x verifies ¬A and x ⊑ w
```

### 3.2 Verifier Computation - The Core Innovation
```
PredicateExclusionOperator.compute_verifiers(argument, model, eval_point)
    │
    ├─► Get arg_verifiers via semantics.extended_compute_verifiers(argument, ...)
    │
    ├─► Convert formula to string: "\\exclude(A)"
    │
    └─► For each potential state:
            │
            └─► _verifies_exclusion_with_predicates(state, formula_str, arg_verifiers, model)
                    │
                    ├─► For each v in arg_verifiers:
                    │       │
                    │       ├─► h_v = model.get_h_witness(formula_str, v)  ← THE KEY INNOVATION
                    │       │       │
                    │       │       └─► WitnessAwareModel.get_h_witness()
                    │       │               │
                    │       │               ├─► Looks up h_pred in witness_predicates dict
                    │       │               ├─► Evaluates h_pred(v) using Z3 model
                    │       │               └─► Returns integer result
                    │       │
                    │       ├─► y_v = model.get_y_witness(formula_str, v)
                    │       │
                    │       └─► Verify three conditions using h_v and y_v
                    │
                    └─► _check_minimality(state, formula_str, arg_verifiers, model)
```

## Phase 4: Result Display

### 4.1 Model Structure Display
```
WitnessPredicateStructure.print_structure(model)
    │
    ├─► Displays state space
    ├─► Shows exclusion relations
    └─► Could be extended to show witness mappings
```

## Critical Interaction Points

### 1. Registry ↔ Constraint Generator
- Registry provides consistent predicate objects
- Constraint generator uses these to build constraints
- Ensures same functions used throughout

### 2. Model ↔ Operators
- Model stores witness predicates from registry
- Operators query model for witness values
- Direct evaluation through Z3 model

### 3. Semantics ↔ All Components
- Orchestrates registration before constraints
- Provides formula-to-string conversion
- Manages evaluation context

## Why This Architecture Succeeds

### 1. Information Persistence
```
Traditional Approach:
Constraints → Solve → Model (witnesses lost)

Attempt 9 Approach:
Register Predicates → Constraints (using predicates) → Solve → Model (includes predicates)
```

### 2. Clean Interfaces
- `get_h_witness()` and `get_y_witness()` provide simple query interface
- Operators don't need to know about constraint generation
- Model wrapping hides complexity

### 3. Two-Phase Separation Maintained
- Phase 1: Build constraints (including witness constraints)
- Phase 2: Query model (including witness queries)
- No mixing of concerns

## Example Trace: Computing ¬A Verifiers

```
1. User asks: What verifies ¬A?

2. PredicateExclusionOperator.compute_verifiers("A", model, eval_point) called

3. Get verifiers of A: [state_5] (example)

4. For each candidate state (0-7 for N=3):
   
   For state_3:
   - h_5 = model.get_h_witness("\\exclude(A)", 5) → returns 2
   - y_5 = model.get_y_witness("\\exclude(A)", 5) → returns 1
   
   Check conditions:
   - y_5 (1) ⊑ 5? Yes (binary: 001 ⊑ 101)
   - h_5 (2) excludes y_5 (1)? Yes
   - h_5 (2) ⊑ state_3 (3)? Yes (binary: 010 ⊑ 011)
   - Minimality? Yes
   
   → state_3 verifies ¬A

5. Return all verifying states
```

## Debugging Flow

To debug issues:

1. **Check Registration**: Print `registry.predicates.keys()` after registration
2. **Check Constraints**: Print generated constraints before solving
3. **Check Model**: Print `model.witness_predicates` after solving
4. **Check Queries**: Print h/y values during verification

## Conclusion

The module interactions in Attempt 9 demonstrate a clean, well-architected solution where each component has a clear responsibility. The key innovation—making witness functions queryable through the model—is achieved through careful coordination between the registry, constraint generator, model wrapper, and operators. This architecture maintains the ModelChecker's design principles while extending its capabilities to handle complex existential semantics.