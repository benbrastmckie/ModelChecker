# Iterator Architecture Contracts

**Navigation**: [← Back to Contracts](../README.md) | [Maintenance Home](../../README.md) | [Theory Licensing →](THEORY_LICENSING.md)

**Related Documentation**: 
- [Core Architecture](../core/README.md) - Framework components and contracts
- [Implementation Guidelines](../implementation/README.md) - Development standards
- [Quality Assurance](../quality/README.md) - Testing and validation

## Overview

This document defines the implicit contracts and assumptions that the iterator subsystem relies on. These contracts must be maintained during refactoring to ensure iterator functionality remains stable and consistent across all theory implementations.

## Model Structure Contracts

### Required Attributes

The iterator expects model structures to have the following attributes:

```python
# State-related attributes
model.z3_world_states      # Dict[str, Dict] - World state information
model.z3_possible_states   # Set[str] - Set of possible worlds  
model.z3_impossible_states # Set[str] - Set of impossible worlds
model.designated_world     # str - The designated world (usually "□")

# Verification/Falsification sets
model.z3_verify_sets       # Dict[str, Set[str]] - Verifier sets per proposition
model.z3_falsify_sets      # Dict[str, Set[str]] - Falsifier sets per proposition

# Z3-related attributes
model.z3_model            # z3.ModelRef - The Z3 model (may be None)
model.solver              # z3.Solver - Active solver (may be None)
model.stored_solver       # z3.Solver - Stored solver (fallback)

# Theory-specific relations (varies by theory)
model.z3_part_of          # Set[Tuple[str, str]] - Part-of relation (logos)
model.z3_exclusion        # Set[Tuple[str, str]] - Exclusion relation (exclusion)
model.z3_imposition       # Dict - Imposition function (imposition)
model.z3_accessibility_1  # Set[Tuple[str, str]] - Accessibility (bimodal)
model.z3_accessibility_2  # Set[Tuple[str, str]] - Accessibility (bimodal)
```

### World State Structure

Each world state in `z3_world_states` has this structure:

```python
{
    'world_number': int,      # Unique identifier
    'world': bool,           # Is this a world?
    'possible': bool,        # Is this world possible?
    'designated': bool,      # Is this the designated world?
    'name': str,            # State name (e.g., "a", "a.b")
    'print_name': str       # Display name
}
```

## Solver Contracts

### Solver Lifecycle

1. **Original Solver Preservation**: The iterator must not modify the original model's solver
2. **Solver Availability**: Iterator checks `model.solver` first, then `model.stored_solver`
3. **Fresh Solver Creation**: Iterator creates its own solver with constraints copied

### Constraint Management

```python
# Iterator preserves these types of constraints:
1. Original model constraints (from model_constraints.constraints)
2. Premise constraints (satisfying the premises)
3. Conclusion constraints (falsifying conclusions)
4. Theory-specific constraints (e.g., coherence, non-triviality)
```

## BuildExample Contracts

The iterator expects BuildExample to provide:

```python
build_example.model_structure        # ModelStructure - The MODEL 1
build_example.model_constraints      # ModelConstraints - Constraint builder
build_example.status                # str - "Countermodel" or "Theorem"
build_example.semantic_theory       # SemanticTheory - Theory definition
build_example.settings              # Dict - All settings including 'iterate'
```

## ModelConstraints Contracts

For building MODEL 2+, the iterator expects:

```python
# Ability to create fresh constraints
model_constraints = ModelConstraints(...)

# These methods must be available:
model_constraints.verify(prop, state)    # Create verify constraint
model_constraints.falsify(prop, state)   # Create falsify constraint
model_constraints.possible(state)        # Create possibility constraint
model_constraints.world(state)          # Create world constraint

# Access to semantics
model_constraints.semantics             # TheorySemantics instance
```

## Theory Iterator Contracts

Each theory's iterator must implement:

```python
class TheoryModelIterator(BaseModelIterator):
    def _create_difference_constraint(self, previous_models):
        """Must return z3.BoolRef ensuring difference from all previous models"""
        
    def _create_non_isomorphic_constraint(self, z3_model):
        """Must return z3.BoolRef preventing isomorphic models"""
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Must return z3.BoolRef with aggressive anti-isomorphism"""
        
    def _calculate_differences(self, new_structure, previous_structure):
        """Must return dict describing differences for display"""
```

## Z3 Value Extraction Contract

When extracting values from Z3 models:

1. **Boolean Evaluation**: Must handle these Z3 return types:
   - `True`/`False` - Python booleans
   - `z3.BoolRef` - Symbolic expressions needing evaluation
   - `z3.RatNumRef` - Numeric values that need comparison
   - String representations as fallback

2. **Model Evaluation**: `model.eval(expr, model_completion=True)` may return:
   - Concrete values
   - Symbolic expressions (when model is partial)
   - Same expression (when variable not in model)

## Display Contracts

The iterator provides difference information in this format:

```python
{
    "structural": {
        "worlds": (old_count, new_count),
        "possible_worlds": (old_count, new_count)
    },
    "theory_specific": {
        # Varies by theory
    }
}
```

## Performance Contracts

1. **Timeout Handling**: Respects `iteration_solver_timeout` setting
2. **Invalid Model Limit**: Stops after `max_invalid_attempts` invalid models
3. **Escape Attempts**: Tries `escape_attempts` times to break isomorphism

## Error Handling Contracts

The iterator must handle:

1. **Missing Attributes**: Graceful handling of missing model attributes
2. **Z3 Exceptions**: Timeout, model not available, etc.
3. **Invalid Models**: Models with no possible worlds
4. **Isomorphism Loops**: Repeated isomorphic models

## Interface Migration Path

To support gradual refactoring, the iterator should:

1. Support both direct attribute access AND interface-based access
2. Prefer interfaces when available
3. Fall back to direct access for compatibility
4. Log deprecation warnings for direct access (future)

## Contract Validation

### Testing Requirements

Iterator contracts must be validated through:

1. **Unit Tests**: Test each contract individually
2. **Integration Tests**: Test contract compliance across theories
3. **Regression Tests**: Ensure contracts remain stable during refactoring

### Validation Checklist

When modifying iterator-related code:

- [ ] All required model attributes remain accessible
- [ ] World state structure preserved
- [ ] Solver lifecycle contracts maintained
- [ ] Z3 value extraction handles all return types
- [ ] Error handling covers all specified cases
- [ ] Performance contracts respected
- [ ] Display format contracts maintained

## Breaking Changes Protocol

If iterator contracts must change:

1. **Document Impact**: Identify all affected components
2. **Migration Plan**: Create step-by-step migration guide
3. **Backward Compatibility**: Provide temporary compatibility layer if possible
4. **Update All Theories**: Ensure all theories comply with new contracts
5. **Test Thoroughly**: Run comprehensive test suite across all theories

## See Also

- [Core Architecture](../core/README.md) - Framework component contracts
- [Implementation Guidelines](../implementation/README.md) - Development standards
- [Testing Framework](../development/TESTING_FRAMEWORK.md) - Contract validation methods
- [Quality Assurance](../quality/README.md) - Code quality standards

---

**Navigation**: [← Back to Contracts](../README.md) | [Maintenance Home](../../README.md) | [Theory Licensing →](THEORY_LICENSING.md)