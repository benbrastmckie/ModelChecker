# Research 003: Solver Integration Approach

[← Back to Research](README.md) | [Previous: Evaluation Override →](002_evaluation_override_approach.md)

## Executive Summary

The solver integration approach addresses the iterator constraint issue at its root by modifying how Z3 finds subsequent models. Instead of post-processing models to fix constraint mismatches, we guide Z3 to find models that inherently satisfy the correct constraints for each iteration.

## Concept Overview

### Core Insight

The fundamental issue is that we're asking Z3 to find a model that:
1. Differs from MODEL 1
2. Satisfies MODEL 1's constraints (with MODEL 1's verify/falsify)

But what we actually need is a model that:
1. Differs from MODEL 1
2. Would satisfy its own constraints (with its own verify/falsify)

### Solver Integration Solution

We integrate the iteration logic directly into the Z3 solving process:
1. Use Z3's incremental solving capabilities
2. Add constraints dynamically based on discovered models
3. Ensure each model is self-consistent
4. Guide Z3 toward valid countermodels

## Technical Design

### Approach 1: Iterative Constraint Refinement

```python
class IterativeSolver:
    """Solver that refines constraints based on discovered models."""
    
    def find_next_model(self, previous_models):
        """Find next model with self-consistent constraints."""
        
        # Start with base constraints
        solver = z3.Solver()
        solver.add(self.base_constraints)
        
        # Add difference constraints
        for prev_model in previous_models:
            solver.add(self._create_difference_constraint(prev_model))
        
        # Iteratively refine
        max_refinements = 10
        for i in range(max_refinements):
            if solver.check() == z3.sat:
                candidate_model = solver.model()
                
                # Check if model is self-consistent
                if self._is_self_consistent(candidate_model):
                    return candidate_model
                    
                # Add refinement constraint
                refinement = self._create_refinement_constraint(candidate_model)
                solver.add(refinement)
            else:
                return None  # No more models
                
        return None  # Couldn't find self-consistent model
```

### Approach 2: Two-Phase Solving

```python
def find_self_consistent_model(self):
    """Find model that satisfies its own constraints."""
    
    # Phase 1: Find candidate model
    candidate = self._find_candidate_model()
    if not candidate:
        return None
        
    # Phase 2: Verify and adjust
    while not self._is_self_consistent(candidate):
        # Extract candidate's verify/falsify
        candidate_vf = self._extract_vf(candidate)
        
        # Create constraints with candidate's functions
        solver = z3.Solver()
        candidate_constraints = self._create_constraints_with_vf(candidate_vf)
        solver.add(candidate_constraints)
        
        # Add similarity constraint to stay close to candidate
        solver.add(self._create_similarity_constraint(candidate))
        
        if solver.check() == z3.sat:
            candidate = solver.model()
        else:
            # Can't find self-consistent model similar to candidate
            return None
            
    return candidate
```

### Approach 3: Fixpoint Iteration

```python
class FixpointIterator:
    """Find models that are fixpoints of the constraint generation process."""
    
    def find_fixpoint_model(self):
        """Find model M such that M satisfies Constraints(VF(M))."""
        
        # Start with arbitrary verify/falsify functions
        current_vf = self._initial_vf()
        
        for iteration in range(self.max_iterations):
            # Generate constraints with current VF
            constraints = self._generate_constraints(current_vf)
            
            # Find model satisfying constraints
            solver = z3.Solver()
            solver.add(constraints)
            
            if solver.check() == z3.sat:
                model = solver.model()
                
                # Extract VF from model
                new_vf = self._extract_vf(model)
                
                # Check if we've reached a fixpoint
                if self._vf_equal(current_vf, new_vf):
                    return model
                    
                current_vf = new_vf
            else:
                # No model for current VF
                return None
                
        return None  # Didn't converge
```

## Implementation Strategy

### Key Components

1. **Self-Consistency Checker**
```python
def _is_self_consistent(self, z3_model):
    """Check if model satisfies constraints generated from its own VF."""
    # Extract model's verify/falsify
    model_vf = self._extract_verify_falsify_from_z3(z3_model)
    
    # Generate constraints with model's VF
    test_solver = z3.Solver()
    constraints = self._generate_constraints_with_vf(model_vf)
    test_solver.add(constraints)
    
    # Add model's assignments as constraints
    for var in z3_model:
        test_solver.add(var == z3_model[var])
    
    # Check if satisfiable
    return test_solver.check() == z3.sat
```

2. **Refinement Constraint Generator**
```python
def _create_refinement_constraint(self, inconsistent_model):
    """Create constraint to exclude inconsistent models."""
    # Identify why model is inconsistent
    violations = self._find_constraint_violations(inconsistent_model)
    
    # Create constraint that excludes this specific inconsistency
    refinement = z3.Or([
        violation.negation() for violation in violations
    ])
    
    return refinement
```

3. **Incremental Solver Manager**
```python
class IncrementalSolverManager:
    """Manages incremental solving with push/pop."""
    
    def __init__(self):
        self.solver = z3.Solver()
        self.checkpoint_stack = []
        
    def push_checkpoint(self):
        """Save current solver state."""
        self.solver.push()
        self.checkpoint_stack.append(len(self.solver.assertions()))
        
    def pop_to_checkpoint(self):
        """Restore previous solver state."""
        self.solver.pop()
        self.checkpoint_stack.pop()
```

## Advantages

1. **Theoretical Soundness**: Models inherently satisfy correct constraints
2. **No Post-Processing**: No need for evaluation overrides or projections
3. **Optimal Solutions**: Z3 finds genuinely valid models
4. **Clean Architecture**: Iteration logic contained in solver layer
5. **Extensibility**: Can add sophisticated search strategies

## Disadvantages

1. **Complexity**: Requires deep understanding of Z3 and fixpoint theory
2. **Performance**: Multiple solving rounds per model
3. **Convergence**: May not find models in reasonable time
4. **Z3 Limitations**: Pushes Z3 beyond typical usage patterns
5. **Debugging Difficulty**: Hard to trace through solving process

## Feasibility Assessment

### Technical Feasibility: LOW-MEDIUM

- Requires advanced Z3 techniques
- Fixpoint computation is non-trivial
- May hit Z3 performance limits
- Theoretical challenges in convergence

### Implementation Effort: VERY HIGH

- Complex algorithm design
- Extensive testing needed
- Performance optimization critical
- May require Z3 expert consultation

### Risk Assessment

- **High Risk**: May not converge for complex theories
- **High Risk**: Performance may be prohibitive
- **Medium Risk**: Z3 may not support required features
- **High Risk**: Difficult to debug and maintain

## Practical Considerations

### Performance Optimization

```python
# Cache constraint generation
self._constraint_cache = {}

def _generate_constraints_with_vf_cached(self, vf_signature):
    if vf_signature not in self._constraint_cache:
        self._constraint_cache[vf_signature] = self._generate_constraints_with_vf(vf_signature)
    return self._constraint_cache[vf_signature]
```

### Convergence Strategies

1. **Relaxation**: Allow approximate fixpoints
2. **Heuristics**: Guide search toward likely fixpoints
3. **Parallel Search**: Try multiple starting points
4. **Early Termination**: Accept "good enough" models

## Recommendation

The solver integration approach is theoretically elegant but practically challenging. It's best suited for:

1. Research implementations exploring theoretical limits
2. Cases where other approaches have failed
3. Situations requiring provable correctness
4. Teams with strong Z3 and fixpoint theory expertise

**Not recommended for initial implementation** due to:
- High complexity and development effort
- Uncertain convergence properties
- Performance concerns
- Maintenance challenges

## Alternative: Hybrid Approach

A more practical variant could combine solver integration with other approaches:

```python
def find_next_model_hybrid(self):
    """Find model using solver with fallback to overrides."""
    
    # Try fixpoint approach with timeout
    model = self._try_fixpoint_solve(timeout=5.0)
    
    if model and self._is_self_consistent(model):
        return model
        
    # Fall back to regular solve + evaluation override
    model = self._find_regular_model()
    return self._apply_evaluation_overrides(model)
```

---

[← Back to Research](README.md) | [Next: Other Model Checkers →](004_other_model_checkers.md)