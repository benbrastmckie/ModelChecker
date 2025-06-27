# Skolemization Implementation Plan for Exclusion Theory

## Executive Summary

This document provides a detailed implementation plan to properly skolemize the exclusion theory to eliminate the false premise issue. The root cause is a disconnect between constraint generation and truth evaluation phases, where different formulas with different Skolem functions are created. The solution requires ensuring formula consistency across both phases.

## Problem Analysis

### Current Architecture Issues

1. **Dual Code Paths**
   - **Constraint Generation**: Uses `premise_behavior` → `true_at` → `operator.true_at` → `extended_verify`
   - **Truth Evaluation**: Uses `truth_value_at` → `true_at` → creates new formulas
   - These paths generate different formulas even for the same logical content

2. **Existential Quantifier Locations**
   - **Atomic Sentences**: `∃x. (x ⊑ w ∧ x ⊨ A)` in `true_at`
   - **Exclusion Operator**: `∃x. (x ⊨ ¬φ ∧ x ⊑ w)` in `operator.true_at`
   - **Exclusion Definition**: `∃h. ∀x. (x ⊨ φ) → ∃y. (y ⊑ x ∧ h(x) excludes y)` in `extended_verify`

3. **Formula Mismatch**
   - Constraint formulas are created once during initialization
   - Evaluation formulas are created fresh each time, with new Skolem functions
   - Z3 cannot find witnesses for the evaluation functions since they weren't part of constraint solving

### Root Cause

The fundamental issue is that **Z3 treats each Skolem function as a distinct uninterpreted function**. When we create `f_atom_1` during constraints and `f_atom_2` during evaluation, Z3 has no knowledge about `f_atom_2`'s behavior since it wasn't part of the constraint system.

## Implementation Strategy

### Design Principles

1. **Single Source of Truth**: Each formula should be created exactly once
2. **Deterministic Naming**: Skolem functions should have predictable, reproducible names
3. **Explicit Caching**: Store and reuse formulas rather than regenerating them
4. **Minimal Changes**: Modify the system incrementally to maintain stability

### Proposed Solution: Formula Registry Pattern

Implement a formula registry that ensures each logical formula is created exactly once and reused consistently across constraint generation and evaluation.

## Detailed Implementation Plan

### Phase 1: Formula Registry Infrastructure

#### 1.1 Create Formula Registry Class

```python
# In semantic.py or a new formula_registry.py

class FormulaRegistry:
    """Registry to ensure formulas are created once and reused."""
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.atomic_formulas = {}  # Maps (sentence_letter, world) -> formula
        self.compound_formulas = {}  # Maps (operator, args, world) -> formula
        self.skolem_functions = {}  # Maps function_name -> z3.Function
        self.skolem_counter = 0
        
    def get_atomic_formula(self, sentence_letter, eval_world):
        """Get or create formula for atomic sentence."""
        key = (str(sentence_letter), str(eval_world))
        
        if key not in self.atomic_formulas:
            # Create Skolem function
            func_name = f"f_atom_{sentence_letter}"
            if func_name not in self.skolem_functions:
                self.skolem_counter += 1
                f_atom = z3.Function(
                    func_name,
                    z3.BitVecSort(self.semantics.N),
                    z3.BitVecSort(self.semantics.N)
                )
                self.skolem_functions[func_name] = f_atom
            else:
                f_atom = self.skolem_functions[func_name]
            
            # Create formula
            formula = z3.And(
                self.semantics.is_part_of(f_atom(eval_world), eval_world),
                self.semantics.verify(f_atom(eval_world), sentence_letter)
            )
            self.atomic_formulas[key] = formula
            
        return self.atomic_formulas[key]
    
    def get_exclusion_formula(self, operator, argument, eval_world):
        """Get or create formula for exclusion operator."""
        key = (operator.name, str(argument), str(eval_world))
        
        if key not in self.compound_formulas:
            # Create the formula using consistent Skolem functions
            formula = self._create_exclusion_formula(operator, argument, eval_world)
            self.compound_formulas[key] = formula
            
        return self.compound_formulas[key]
```

#### 1.2 Integrate Registry with Semantics

```python
# In ExclusionSemantics.__init__
def __init__(self, settings):
    # ... existing initialization ...
    
    # Initialize formula registry
    self.formula_registry = FormulaRegistry(self)
    
    # Modify premise/conclusion behaviors to use registry
    self.premise_behavior = lambda premise: self.true_at_cached(premise, self.main_point)
    self.conclusion_behavior = lambda conclusion: self.false_at_cached(conclusion, self.main_point)
```

### Phase 2: Modified True_At Implementation

#### 2.1 Create Cached Version of true_at

```python
def true_at_cached(self, sentence, eval_point):
    """Cached version of true_at that uses formula registry."""
    eval_world = eval_point["world"] if isinstance(eval_point, dict) else eval_point
    
    # Handle atomic sentences
    sentence_letter = sentence.sentence_letter
    if sentence_letter is not None:
        return self.formula_registry.get_atomic_formula(sentence_letter, eval_world)
    
    # Handle compound sentences
    operator = sentence.operator
    arguments = sentence.arguments or ()
    
    # For exclusion operator, use cached formula
    if operator and operator.name == "\\exclude":
        return self.formula_registry.get_exclusion_formula(
            operator, arguments[0], eval_world
        )
    
    # For other operators, delegate as before
    return operator.true_at(*arguments, eval_point)
```

#### 2.2 Update UnilateralProposition

```python
def truth_value_at(self, eval_point):
    """Modified to use cached formulas."""
    semantics = self.model_structure.semantics
    z3_model = self.model_structure.z3_model
    
    # Use the cached version
    formula = semantics.true_at_cached(self.sentence, eval_point)
    result = z3_model.evaluate(formula)
    return z3.is_true(result)
```

### Phase 3: Exclusion Operator Modifications

#### 3.1 Update Exclusion Operator Base

```python
class ExclusionOperatorBase(syntactic.Operator):
    def true_at(self, arg, eval_point):
        """Modified to work with formula registry."""
        semantics = self.semantics
        eval_world = eval_point["world"] if isinstance(eval_point, dict) else eval_point
        
        # Use registry for consistency
        if hasattr(semantics, 'formula_registry'):
            return semantics.formula_registry.get_exclusion_formula(self, arg, eval_world)
        
        # Fallback to original implementation
        x = z3.BitVec(f"ver_exclude_{arg}", semantics.N)
        return Exists(
            x,
            z3.And(
                semantics.extended_verify(x, arg, eval_point),
                semantics.is_part_of(x, eval_world)
            )
        )
```

#### 3.2 Implement Skolemized Exclusion Formula

```python
def _create_exclusion_formula(self, operator, argument, eval_world):
    """Create skolemized exclusion formula."""
    N = self.semantics.N
    
    # Create or reuse Skolem function for verifying states
    func_name = f"f_exclude_{self.skolem_counter}"
    if func_name not in self.skolem_functions:
        self.skolem_counter += 1
        f_exclude = z3.Function(
            func_name,
            z3.BitVecSort(N),  # world
            z3.BitVecSort(N)   # verifying state
        )
        self.skolem_functions[func_name] = f_exclude
    else:
        f_exclude = self.skolem_functions[func_name]
    
    # Skolemized formula: f_exclude(w) verifies ¬φ and is part of w
    return z3.And(
        self.semantics.extended_verify(f_exclude(eval_world), argument, {"world": eval_world}),
        self.semantics.is_part_of(f_exclude(eval_world), eval_world)
    )
```

### Phase 4: Extended Verify Skolemization

For the SK2 strategy, also skolemize the extended_verify method:

```python
class ExclusionOperatorSkolemized2(ExclusionOperatorBase):
    def extended_verify(self, state, argument, eval_point):
        """Fully skolemized version."""
        semantics = self.semantics
        N = semantics.N
        
        # Use deterministic names based on argument structure
        arg_hash = hash(str(argument))
        h_name = f"h_sk2_{arg_hash}"
        y_name = f"y_sk2_{arg_hash}"
        
        # Get or create Skolem functions from registry
        registry = semantics.formula_registry if hasattr(semantics, 'formula_registry') else None
        
        if registry:
            if h_name not in registry.skolem_functions:
                h_sk = z3.Function(h_name, z3.BitVecSort(N), z3.BitVecSort(N))
                y_sk = z3.Function(y_name, z3.BitVecSort(N), z3.BitVecSort(N))
                registry.skolem_functions[h_name] = h_sk
                registry.skolem_functions[y_name] = y_sk
            else:
                h_sk = registry.skolem_functions[h_name]
                y_sk = registry.skolem_functions[y_name]
        else:
            # Fallback
            h_sk = z3.Function(h_name, z3.BitVecSort(N), z3.BitVecSort(N))
            y_sk = z3.Function(y_name, z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Build constraints with consistent functions
        # ... rest of implementation ...
```

### Phase 5: Testing and Validation

#### 5.1 Create Test Suite

```python
# test_skolemization.py

def test_formula_consistency():
    """Ensure same formulas are used in both phases."""
    semantics = ExclusionSemantics(settings)
    
    # Create a sentence
    sentence = create_test_sentence()
    
    # Get constraint formula
    constraint_formula = semantics.premise_behavior(sentence)
    
    # Get evaluation formula
    eval_formula = semantics.true_at_cached(sentence, semantics.main_point)
    
    # They should be the same object
    assert constraint_formula is eval_formula
```

#### 5.2 Regression Tests

- Test all examples in exclusion theory
- Verify no false premises in Triple Negation or Disjunctive DeMorgan
- Ensure counterexamples are still found correctly
- Check performance impact

### Phase 6: Configuration and Documentation

#### 6.1 Make Skolemization Configurable

```python
class ExclusionSemantics(model.SemanticDefaults):
    def __init__(self, settings):
        # ... existing init ...
        
        # Make skolemization configurable
        self.use_skolemization = settings.get('skolemize', True)
        
        if self.use_skolemization:
            self.formula_registry = FormulaRegistry(self)
            self.true_at = self.true_at_cached
```

#### 6.2 Update Documentation

- Add docstrings explaining the skolemization approach
- Document the formula registry pattern
- Update theory README with skolemization details

## Implementation Timeline

### Week 1: Foundation
- [ ] Implement FormulaRegistry class
- [ ] Create test harness for formula consistency
- [ ] Integrate registry with ExclusionSemantics

### Week 2: Core Implementation  
- [ ] Implement true_at_cached
- [ ] Update UnilateralProposition.truth_value_at
- [ ] Modify exclusion operator true_at

### Week 3: Extended Skolemization
- [ ] Implement skolemized extended_verify for SK2
- [ ] Create deterministic naming scheme
- [ ] Test on problematic examples

### Week 4: Testing and Polish
- [ ] Comprehensive regression testing
- [ ] Performance optimization
- [ ] Documentation updates
- [ ] Configuration options

## Alternative Approaches

### 1. Constraint Formula Caching (Proven Working)
As demonstrated in the investigation, caching constraint formulas and reusing them during evaluation works:

```python
# Store constraint formula in proposition
self.constraint_formula = model_constraints.premise_constraints[i]

# Use it during evaluation
def truth_value_at(self, eval_point):
    if hasattr(self, 'constraint_formula'):
        return z3.is_true(self.z3_model.evaluate(self.constraint_formula))
```

**Pros**: Simple, proven to work
**Cons**: Requires modifying proposition initialization

### 2. Two-Phase Approach
Separate model finding from truth evaluation:

1. Find model with existential quantifiers
2. Extract witness functions
3. Use witnesses for deterministic evaluation

**Pros**: Preserves mathematical semantics
**Cons**: Complex implementation, Z3 limitations

### 3. Global Skolem Functions
Define all Skolem functions globally at module level:

```python
# Global functions
F_ATOM_A = z3.Function("f_atom_A", z3.BitVecSort(N), z3.BitVecSort(N))
F_EXCLUDE_1 = z3.Function("f_exclude_1", z3.BitVecSort(N), z3.BitVecSort(N))
```

**Pros**: Guarantees consistency
**Cons**: Less flexible, requires pre-declaration

## Recommendations

1. **Start with Formula Registry**: It's the most principled approach that maintains flexibility
2. **Implement Incrementally**: Test each phase before proceeding
3. **Keep Backward Compatibility**: Use configuration flags to enable/disable skolemization
4. **Document Thoroughly**: The solution involves subtle architectural changes

## Success Criteria

1. **No False Premises**: Triple Negation and Disjunctive DeMorgan examples show true premises
2. **No True Conclusion**: Conclusions remain false in counterexamples (not affected by the fix)
3. **Correct Counterexamples**: Counterexamples are still found when expected
4. **Performance**: No significant slowdown compared to current implementation
5. **Maintainability**: Code remains clear and modifiable

## Conclusion

The formula registry pattern provides a clean solution to the false premise issue by ensuring formula consistency between constraint generation and truth evaluation. This approach maintains the mathematical elegance of the exclusion semantics while working within Z3's constraints.