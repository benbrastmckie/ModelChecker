# Research 001: Constraint Projection Approach

[← Back to Research](README.md) | [Findings →](../findings/009_iterator_constraint_issue.md)

## Executive Summary

The constraint projection approach involves projecting MODEL 1's constraints onto MODEL 2's verify/falsify function space rather than generating fresh constraints. This maintains consistency between the Z3 model and the constraints used to evaluate it.

## Concept Overview

### The Problem

When we find MODEL 2 using Z3:
1. Z3 uses MODEL 1's constraints (with MODEL 1's verify/falsify functions)
2. Z3 finds a model that satisfies those constraints
3. Creating fresh constraints with MODEL 2's verify/falsify functions creates a mismatch
4. The Z3 model may not satisfy the fresh constraints

### Constraint Projection Solution

Instead of fresh constraints, we:
1. Keep MODEL 1's constraint structure
2. Project them onto MODEL 2's verify/falsify space
3. Use transformation functions to map between spaces
4. Maintain consistency with the Z3 model

## Technical Design

### Mathematical Foundation

Given:
- V₁(s,p): MODEL 1's verify function
- F₁(s,p): MODEL 1's falsify function  
- V₂(s,p): MODEL 2's verify function
- F₂(s,p): MODEL 2's falsify function

We need a projection function P such that:
- If Z3 model M satisfies constraint C₁ using V₁,F₁
- Then M also satisfies P(C₁) using V₂,F₂

### Implementation Approach

```python
class ConstraintProjector:
    """Projects constraints from one verify/falsify space to another."""
    
    def __init__(self, source_vf, target_vf):
        self.source_vf = source_vf  # (V₁, F₁)
        self.target_vf = target_vf  # (V₂, F₂)
        
    def project_constraint(self, constraint):
        """Project a single constraint to target space."""
        # Parse constraint to identify verify/falsify calls
        # Replace with equivalent calls in target space
        # Maintain logical structure
        
    def project_all_constraints(self, constraints):
        """Project a list of constraints."""
        return [self.project_constraint(c) for c in constraints]
```

### Key Challenges

1. **Constraint Parsing**: Need to identify verify/falsify calls in Z3 constraints
2. **Semantic Preservation**: Projection must preserve logical meaning
3. **Efficiency**: Projection overhead should be minimal
4. **Completeness**: Must handle all constraint types

## Prototype Implementation

### Step 1: Constraint Analysis

```python
def analyze_constraint(constraint):
    """Extract verify/falsify calls from a Z3 constraint."""
    if z3.is_app(constraint):
        func = constraint.decl()
        if func.name() == 'verify':
            state, letter = constraint.arg(0), constraint.arg(1)
            return ('verify', state, letter)
        elif func.name() == 'falsify':
            state, letter = constraint.arg(0), constraint.arg(1)
            return ('falsify', state, letter)
        else:
            # Recursively analyze subexpressions
            children = [analyze_constraint(constraint.arg(i)) 
                       for i in range(constraint.num_args())]
            return (func.name(), children)
    return constraint
```

### Step 2: Constraint Transformation

```python
def transform_constraint(constraint, vf_mapping):
    """Transform constraint using verify/falsify mapping."""
    analysis = analyze_constraint(constraint)
    
    if isinstance(analysis, tuple):
        if analysis[0] == 'verify':
            _, state, letter = analysis
            # Look up corresponding value in MODEL 2
            return vf_mapping['verify'][(state, letter)]
        elif analysis[0] == 'falsify':
            _, state, letter = analysis
            return vf_mapping['falsify'][(state, letter)]
        else:
            # Reconstruct with transformed children
            op_name, children = analysis
            transformed = [transform_constraint(c, vf_mapping) for c in children]
            return reconstruct_operation(op_name, transformed)
    
    return constraint
```

### Step 3: Integration with Iterator

```python
def _build_new_model_structure(self, z3_model):
    # Extract MODEL 2's verify/falsify values
    model2_vf = self._extract_verify_falsify_from_z3(z3_model)
    
    # Create projection mapping
    vf_mapping = {
        'verify': {(s,l): z3.BoolVal(v) for (s,l),(v,f) in model2_vf.items()},
        'falsify': {(s,l): z3.BoolVal(f) for (s,l),(v,f) in model2_vf.items()}
    }
    
    # Project MODEL 1's constraints
    original_constraints = self.build_example.model_constraints.all_constraints
    projected_constraints = [transform_constraint(c, vf_mapping) 
                           for c in original_constraints]
    
    # Create model structure with projected constraints
    # ...
```

## Advantages

1. **Consistency**: Z3 model guaranteed to satisfy projected constraints
2. **Theoretical Soundness**: Maintains relationship between models
3. **No Re-solving**: Uses existing Z3 model without modification
4. **Preserves Intent**: Original constraint structure maintained

## Disadvantages

1. **Complexity**: Requires deep Z3 constraint manipulation
2. **Performance**: Projection overhead for each constraint
3. **Maintenance**: Tightly coupled to Z3 internals
4. **Limited Flexibility**: Constrained by original structure

## Feasibility Assessment

### Technical Feasibility: MEDIUM

- Z3 provides APIs for constraint inspection
- Constraint transformation is possible but complex
- May require Z3-specific expertise

### Implementation Effort: HIGH

- Need robust constraint parser
- Complex transformation logic
- Extensive testing required
- Edge cases in constraint types

### Risk Assessment

- **High Risk**: Deep Z3 integration may break with updates
- **Medium Risk**: Performance impact on large constraint sets
- **Low Risk**: Logical correctness easier to verify

## Recommendation

The constraint projection approach is theoretically sound but practically complex. It requires significant Z3 expertise and may be fragile to maintain. Consider this approach only if:

1. Other approaches fail
2. Team has deep Z3 expertise
3. Performance is not critical
4. Long-term maintenance is feasible

## Alternative Simplification

A simpler variant could project only the evaluation results rather than the constraints themselves:

```python
# Instead of projecting constraints, project evaluation results
def evaluate_with_projection(formula, world, model1_eval, model2_vf):
    """Evaluate formula using MODEL 1's result projected to MODEL 2's space."""
    # Use MODEL 1's evaluation but with MODEL 2's verify/falsify interpretation
    # This is simpler but less theoretically pure
```

---

[← Back to Research](README.md) | [Next: Evaluation Override →](002_evaluation_override_approach.md)