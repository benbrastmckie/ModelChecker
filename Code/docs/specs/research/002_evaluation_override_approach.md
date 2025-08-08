# Research 002: Evaluation Override Approach

[← Back to Research](README.md) | [Previous: Constraint Projection →](001_constraint_projection_approach.md)

## Executive Summary

The evaluation override approach bypasses the constraint generation issue entirely by intercepting and modifying formula evaluation at the proposition level. Instead of ensuring constraints match the model, we ensure evaluations return correct values regardless of underlying constraints.

## Concept Overview

### The Problem Revisited

The root issue is that MODEL 2+ evaluate formulas using mismatched verify/falsify functions:

1. Constraints were generated with MODEL 1's functions
2. Z3 model satisfies those constraints
3. Evaluation uses the constraints, leading to incorrect results

### Evaluation Override Solution

Instead of fixing constraints, we:

1. Let MODEL 2+ use MODEL 1's constraints as-is
2. Override the evaluation mechanism
3. Force correct truth values based on MODEL 2's actual verify/falsify
4. Maintain countermodel properties through evaluation control

## Technical Design

### Architecture Overview

```
┌─────────────────┐
│ Formula Input   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Evaluation      │ ◄── Override Point
│ Interceptor     │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Proposition     │
│ Evaluation      │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Verify/Falsify  │
│ Lookup          │
└─────────────────┘
```

### Implementation Approach

```python
class EvaluationOverrideProposition:
    """Proposition class that overrides evaluation for MODEL 2+."""

    def __init__(self, base_proposition, override_table=None):
        self.base_proposition = base_proposition
        self.override_table = override_table or {}

    def evaluate_at_world(self, world):
        """Evaluate with potential override."""
        if self.override_table:
            # Check if we have an override for this formula at this world
            key = (self.formula_string, world)
            if key in self.override_table:
                return self.override_table[key]

        # Fall back to normal evaluation
        return self.base_proposition.evaluate_at_world(world)
```

### Integration Strategy

```python
def _build_new_model_structure(self, z3_model):
    # Build structure normally but with override capability

    # Step 1: Calculate what truth values SHOULD be
    correct_values = self._calculate_correct_evaluations(z3_model)

    # Step 2: Build structure with normal constraints
    new_structure = self._build_structure_normally(z3_model)

    # Step 3: Install evaluation overrides
    self._install_evaluation_overrides(new_structure, correct_values)

    return new_structure

def _calculate_correct_evaluations(self, z3_model):
    """Pre-calculate correct truth values for all formulas."""
    overrides = {}

    # Extract MODEL 2's verify/falsify
    model2_vf = self._extract_verify_falsify_from_z3(z3_model)

    # For each premise/conclusion at evaluation world
    eval_world = self._get_evaluation_world(z3_model)

    for formula in self.premises + self.conclusions:
        truth_value = self._evaluate_with_vf(formula, eval_world, model2_vf)
        overrides[(formula, eval_world)] = truth_value

    return overrides
```

## Detailed Implementation Options

### Option 1: Proposition-Level Override

Override at the Proposition class level:

```python
class OverridableProposition(PropositionDefaults):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._override_map = {}

    def set_override(self, world, value):
        """Set evaluation override for specific world."""
        self._override_map[world] = value

    def evaluate(self, eval_point):
        """Evaluate with override check."""
        world = eval_point.get('world')
        if world in self._override_map:
            return self._override_map[world]
        return super().evaluate(eval_point)
```

### Option 2: Model-Level Override

Override at the ModelStructure level:

```python
class OverridableModelStructure(ModelDefaults):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._evaluation_overrides = {}

    def evaluate_at_world(self, formula, world):
        """Evaluate formula with potential override."""
        # Check override table first
        override_key = (str(formula), world)
        if override_key in self._evaluation_overrides:
            return self._evaluation_overrides[override_key]

        # Normal evaluation
        return super().evaluate_at_world(formula, world)

    def install_overrides(self, override_table):
        """Install evaluation overrides."""
        self._evaluation_overrides.update(override_table)
```

### Option 3: Semantics-Level Override

Override the verify/falsify evaluation itself:

```python
class OverridableSemantics(SemanticDefaults):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._verify_overrides = {}
        self._falsify_overrides = {}

    def verify(self, state, letter):
        """Verify with override check."""
        key = (state, letter)
        if hasattr(self, '_verify_overrides') and key in self._verify_overrides:
            return z3.BoolVal(self._verify_overrides[key])
        return super().verify(state, letter)
```

## Advantages

1. **Simplicity**: No complex constraint manipulation
2. **Guaranteed Correctness**: Direct control over evaluation results
3. **Minimal Changes**: Isolated to evaluation path
4. **Easy to Debug**: Clear override points
5. **Performance**: No constraint projection overhead

## Disadvantages

1. **Theoretical Impurity**: Bypasses logical framework
2. **Maintenance Burden**: Must track override points
3. **Limited Scope**: Only fixes evaluation, not constraint consistency
4. **Potential Side Effects**: May affect other evaluation-dependent features

## Key Insights from Iterate Documentation

After reviewing the iterate/README.md, several important considerations emerge:

1. **Constraint Preservation**: The documentation emphasizes "Maintains original semantic constraints across all iterations" - our override must not interfere with this
2. **Model Building Process**: The system already has a `_build_new_model_structure` method that we're modifying
3. **Debug Information**: The iterator collects debug messages - we should add logging for overrides
4. **Theory-Specific Behavior**: Different theories may need different override strategies
5. **Abstract Methods**: Each theory must implement `_create_difference_constraint` which is key to understanding the iteration process

## Detailed Constraint Generation Process

Based on the documentation, here's the exact process for constraint generation in model iteration:

### Step 1: Initial Model (MODEL 1)

1. **Original Constraints**: Created by ModelConstraints using MODEL 1's verify/falsify functions
2. **Z3 Solving**: Z3 finds a model satisfying these constraints
3. **Result**: MODEL 1 with its own verify/falsify values

### Step 2: Finding MODEL 2

1. **Preserve Original Constraints**: The system keeps MODEL 1's constraints (line 58: "Maintains original semantic constraints")
2. **Add Difference Constraint**: Calls `_create_difference_constraint([model1])` to ensure MODEL 2 differs
3. **Example from Logos Theory** (lines 310-326):
   ```python
   # For each previous model, require at least one semantic difference
   for prev_model in previous_models:
       differences = []
       for state in all_states:
           for atom in sentence_letters:
               # Require different verification value
               prev_verifies = prev_model.eval(semantics.verify(state, atom))
               differences.append(semantics.verify(state, atom) != prev_verifies)
       model_constraints.append(z3.Or(*differences))
   ```
4. **Combined Constraints**: Original + Difference constraints
5. **Z3 Solving**: Z3 finds MODEL 2 that satisfies both sets

### Step 3: The Problem

1. **Constraint Mismatch**: MODEL 2 satisfies MODEL 1's constraints (which use MODEL 1's verify/falsify)
2. **Different Functions**: But MODEL 2 has its own verify/falsify values
3. **Evaluation Issue**: When evaluating formulas, MODEL 2 uses constraints generated with MODEL 1's functions

### Step 4: Additional Complexity

- **Isomorphism Checking**: System checks if models are structurally identical (line 53)
- **Invalid Model Detection**: Excludes models with no possible worlds (line 52)
- **Retry Logic**: If stuck on isomorphic models, adds stronger constraints (lines 367-379)

This detailed understanding reinforces why evaluation override is the most practical solution - it bypasses the fundamental constraint mismatch issue.

## Implementation Prototype

Here's an improved prototype based on the documentation:

```python
# In BaseModelIterator._build_new_model_structure
def _build_new_model_structure(self, z3_model):
    """Build a new model structure with evaluation overrides.

    This method is already part of the iteration framework and handles
    the creation of MODEL 2+ structures. We modify it to add evaluation
    overrides that ensure countermodel properties are preserved.
    """
    # Use existing structure building (already implemented)
    new_structure = self._build_structure_with_fresh_constraints(z3_model)

    # Add evaluation override capability
    self._install_evaluation_overrides(new_structure, z3_model)

    # Add debug logging for transparency
    if hasattr(new_structure, '_evaluation_overrides') and new_structure._evaluation_overrides:
        self.debug_messages.append(
            f"[ITERATION] Applied {len(new_structure._evaluation_overrides)} evaluation overrides"
        )

    return new_structure

def _install_evaluation_overrides(self, model_structure, z3_model):
    """Install evaluation overrides to ensure countermodel properties.

    This ensures that premises remain true and conclusions remain false
    at the evaluation world, regardless of constraint mismatches.
    """
    # Extract the actual verify/falsify values from this model
    model_vf = self._extract_verify_falsify_from_z3(z3_model)
    eval_world = model_structure.main_point['world']

    overrides = {}

    # Check each premise at evaluation world
    for premise in model_structure.premises:
        actual_truth = self._evaluate_with_model_vf(
            premise, eval_world, model_vf, model_structure
        )
        if not actual_truth:
            # Premise should be true but isn't - override
            overrides[(str(premise), eval_world)] = True
            self.debug_messages.append(
                f"[ITERATION] Override: {premise} forced TRUE at {eval_world}"
            )

    # Check each conclusion at evaluation world
    for conclusion in model_structure.conclusions:
        actual_truth = self._evaluate_with_model_vf(
            conclusion, eval_world, model_vf, model_structure
        )
        if actual_truth:
            # Conclusion should be false but isn't - override
            overrides[(str(conclusion), eval_world)] = False
            self.debug_messages.append(
                f"[ITERATION] Override: {conclusion} forced FALSE at {eval_world}"
            )

    if overrides:
        # Store overrides
        model_structure._evaluation_overrides = overrides

        # Monkey-patch evaluate_at_world method
        original_evaluate = model_structure.evaluate_at_world

        def evaluate_with_override(formula, world):
            # Check for override
            key = (str(formula), world)
            if hasattr(model_structure, '_evaluation_overrides') and \
               key in model_structure._evaluation_overrides:
                return model_structure._evaluation_overrides[key]
            # Fall back to original evaluation
            return original_evaluate(formula, world)

        model_structure.evaluate_at_world = evaluate_with_override

def _evaluate_with_model_vf(self, formula, world, model_vf, model_structure):
    """Evaluate formula using the model's actual verify/falsify values.

    This computes what the truth value SHOULD be based on the model's
    actual semantic functions, not the constraints.
    """
    # This is a simplified version - actual implementation would need
    # to handle all formula types recursively

    if hasattr(formula, 'is_atomic') and formula.is_atomic():
        # For atomic formulas, use the model's verify/falsify
        letter = str(formula)
        state_int = self._world_to_state_int(world)
        verify_val, falsify_val = model_vf.get((state_int, letter), (False, False))

        # Standard bilateral semantics
        return verify_val and not falsify_val

    # For complex formulas, recurse on subformulas
    # (Implementation depends on formula structure)
    return self._evaluate_complex_formula(formula, world, model_vf, model_structure)
```

## Feasibility Assessment

### Technical Feasibility: HIGH

- Simple to implement
- Uses existing infrastructure
- No deep Z3 knowledge required
- Easy to test and verify

### Implementation Effort: LOW

- Minimal code changes
- Localized modifications
- Clear implementation path
- Quick to prototype

### Risk Assessment

- **Low Risk**: Isolated changes
- **Low Risk**: Easy to revert
- **Medium Risk**: May mask deeper issues
- **Low Risk**: Performance impact minimal

## Recommendation

The evaluation override approach is the most practical solution for quickly fixing the iterator constraint issue. It's simple, effective, and has minimal impact on the existing codebase.

**Recommended for initial implementation** because:

1. Quick to implement and test
2. Solves the immediate problem
3. Easy to understand and maintain
4. Can be replaced later with a more elegant solution

## Integration with Existing Iterator Framework

### Key Integration Points

1. **\_build_new_model_structure**: Already exists in BaseModelIterator, perfect place for override installation
2. **debug_messages**: Existing list for tracking iteration events, add override logging here
3. **\_extract_verify_falsify_from_z3**: Already implemented in our previous work
4. **evaluate_at_world**: Standard method in all model structures, safe to override

### Theory-Specific Considerations

Different theories may need different evaluation strategies:

- **Logos Theory**: Standard bilateral semantics (verify ∧ ¬falsify)
- **Exclusion Theory**: Unilateral semantics with witness considerations
- **Bimodal Theory**: Temporal aspects may require special handling
- **Imposition Theory**: May have additional semantic complexities

### Performance Considerations

The documentation mentions performance optimizations (lines 391-414):

- Override computation should be minimal
- Cache override decisions if needed
- Only compute overrides for premises/conclusions at evaluation world
- Avoid recursive evaluation where possible

## Next Steps for Implementation

1. Implement Option 2 (Model-Level Override) as the cleanest approach
2. Add debug logging to track when overrides are used (integrate with existing debug_messages)
3. Test with all theory implementations mentioned in the documentation
4. Document the override mechanism in iterate/README.md
5. Add configuration option to disable overrides if needed
6. Consider long-term architectural improvements

## Testing Strategy

Based on the iterate documentation's testing guidance:

1. **Basic Test**: Use simple examples like `premises=['A'], conclusions=[]`
2. **Theory Coverage**: Test with all theories (logos, exclusion, default, bimodal, imposition)
3. **Edge Cases**: Test with no premises, no conclusions, complex formulas
4. **Performance**: Monitor impact on iteration time
5. **Debug Output**: Verify override messages appear in debug output

---

[← Back to Research](README.md) | [Next: Solver Integration →](003_solver_integration_approach.md)
