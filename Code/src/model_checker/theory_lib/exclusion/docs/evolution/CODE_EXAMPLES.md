# Code Examples: From Failed Approaches to Successful Implementation

## Introduction

This document provides concrete code examples showing the evolution from failed approaches to the successful witness predicate implementation. Each section includes "Before" and "After" comparisons with detailed explanations of why the changes were necessary.

## 1. Existential Quantification: The Core Problem

### Failed Approach: Existentially Quantified Variables

```python
# FAILED APPROACH (Attempts 1-5)
class FailedExclusionOperator(Operator):
    def extended_verify(self, state, argument, eval_point):
        """Generate constraints for exclusion using existential quantification."""
        
        # Create existentially quantified witness variables
        h_var = z3.BitVec(f'h_witness_{self.counter}', self.semantics.N)
        y_var = z3.BitVec(f'y_witness_{self.counter}', self.semantics.N)
        self.counter += 1
        
        x = z3.BitVec('x', self.semantics.N)
        
        # The three conditions using existential quantification
        condition1 = z3.ForAll([x], 
            z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                z3.And(
                    self.semantics.is_part_of(y_var, x),
                    self.semantics.excludes(h_var, y_var)
                )
            )
        )
        
        condition2 = z3.ForAll([x],
            z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                self.semantics.is_part_of(h_var, state)
            )
        )
        
        # Wrap in existential quantification
        return z3.Exists([h_var, y_var], 
            z3.And(condition1, condition2, minimality_constraint)
        )
    
    def compute_verifiers(self, argument, model, eval_point):
        """Attempt to compute verifiers - but witnesses are inaccessible!"""
        
        # Problem: No way to access h_var and y_var values from the model
        # The existential variables are out of scope and internal to Z3
        
        # Failed attempt 1: Try to recreate the constraints
        for state in range(2**self.semantics.N):
            # This creates NEW witness variables, not the ones used during solving
            constraint = self.extended_verify(state, argument, eval_point)
            if z3.is_true(model.eval(constraint)):
                # This might work by chance but is fundamentally wrong
                pass
                
        # Result: False premises because verifier computation is incorrect
        return []  # Often returns empty, causing "no verifiers" problems
```

**Why This Failed:**
1. `h_var` and `y_var` are **temporary variables** that disappear after constraint generation
2. Z3's existential handling creates **internal Skolem functions** not accessible to user code
3. `compute_verifiers` cannot access the **specific witness values** Z3 found during solving
4. Results in **false premise problems** because truth evaluation is incomplete

### Successful Approach: Z3 Function Objects

```python
# SUCCESSFUL APPROACH (Attempt 9)
class SuccessfulExclusionOperator(Operator):
    def extended_verify(self, state, argument, eval_point):
        """Generate constraints using registered witness predicates."""
        
        # Get the formula string for witness lookup
        formula_str = f"\\exclude({self.semantics._formula_to_string(argument)})"
        
        # Get registered witness predicates (created during registration phase)
        h_pred = self.semantics.witness_registry.predicates[f"{formula_str}_h"]
        y_pred = self.semantics.witness_registry.predicates[f"{formula_str}_y"]
        
        x = z3.BitVec('x', self.semantics.N)
        
        # The three conditions using witness predicates
        condition1 = z3.ForAll([x], 
            z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                z3.And(
                    self.semantics.is_part_of(y_pred(x), x),
                    self.semantics.excludes(h_pred(x), y_pred(x))
                )
            )
        )
        
        condition2 = z3.ForAll([x],
            z3.Implies(
                self.semantics.extended_verify(x, argument, eval_point),
                self.semantics.is_part_of(h_pred(x), state)
            )
        )
        
        # No existential quantification needed - predicates are persistent
        return z3.And(condition1, condition2, minimality_constraint)
    
    def compute_verifiers(self, argument, model, eval_point):
        """Compute verifiers using accessible witness predicates."""
        
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
        
    def _verifies_exclusion_with_predicates(self, state, formula_str, 
                                          arg_verifiers, model):
        """Check exclusion conditions using accessible witness predicates."""
        
        for v in arg_verifiers:
            # THE KEY BREAKTHROUGH: Direct witness access!
            h_v = model.get_h_witness(formula_str, v)
            y_v = model.get_y_witness(formula_str, v)
            
            if h_v is None or y_v is None:
                return False
                
            # Verify the three conditions using concrete witness values
            if not self._eval_is_part_of(y_v, v, model):
                return False
            if not self._eval_excludes(h_v, y_v, model):
                return False
            if not self._eval_is_part_of(h_v, state, model):
                return False
                
        return self._check_minimality(state, formula_str, arg_verifiers, model)
```

**Why This Succeeds:**
1. **Z3 Function objects** persist in the model and are accessible after solving
2. **Registry ensures consistency** - same functions used in constraint generation and evaluation
3. **Direct witness access** via `model.get_h_witness()` and `model.get_y_witness()`
4. **Complete truth evaluation** leads to correct verifier computation

## 2. Model Building: Two-Pass Architecture

### Failed Approach: Single-Pass with Circular Dependencies

```python
# FAILED APPROACH 
class FailedSemantics(SemanticDefaults):
    def build_model(self, eval_point):
        """Single-pass approach that fails with circular dependencies."""
        
        solver = z3.Solver()
        
        # Try to generate all constraints at once
        premises = eval_point.get("premises", [])
        conclusions = eval_point.get("conclusions", [])
        
        all_constraints = []
        
        # Problem: Nested formulas like ¬¬A need witnesses for ¬A 
        # but we're trying to create witnesses for ¬¬A at the same time
        for formula in premises + conclusions:
            if self._has_exclusion(formula):
                # Try to register witness and generate constraints simultaneously
                witness_constraints = self._create_witness_constraints(formula, eval_point)
                all_constraints.extend(witness_constraints)
                
        # This fails because some constraints reference witnesses 
        # that haven't been created yet
        try:
            solver.add(all_constraints)
        except z3.Z3Exception as e:
            # Circular dependency - witness for ¬¬A references witness for ¬A
            return None
            
        if solver.check() == z3.sat:
            return solver.model()  # Standard model without witness access
        return None
```

### Successful Approach: Two-Pass Registration and Constraint Generation

```python
# SUCCESSFUL APPROACH
class SuccessfulSemantics(SemanticDefaults):
    def __init__(self, settings):
        super().__init__(settings)
        self.witness_registry = WitnessRegistry(settings['N'])
        self.constraint_generator = WitnessConstraintGenerator(self)
        self._processed_formulas = set()
        
    def build_model(self, eval_point):
        """Two-pass approach that handles dependencies correctly."""
        
        # Clear previous state for clean builds
        self.witness_registry.clear()
        self._processed_formulas.clear()
        
        solver = z3.Solver()
        
        # PASS 1: Register ALL witness predicates first
        premises = eval_point.get("premises", [])
        conclusions = eval_point.get("conclusions", [])
        
        for formula in premises + conclusions:
            self._register_witness_predicates_recursive(formula)
            
        # PASS 2: Generate constraints using registered predicates
        # Standard constraints first
        standard_constraints = self._generate_standard_constraints(eval_point)
        solver.add(standard_constraints)
        
        # Witness constraints second (can now reference any registered predicate)
        witness_constraints = self._generate_all_witness_constraints(eval_point)
        solver.add(witness_constraints)
        
        # Solve and wrap in WitnessAwareModel
        if solver.check() == z3.sat:
            z3_model = solver.model()
            return WitnessAwareModel(
                z3_model,
                self,
                self.witness_registry.get_all_predicates()
            )
        return None
        
    def _register_witness_predicates_recursive(self, formula):
        """Recursively register witnesses for all exclusion subformulas."""
        
        if formula in self._processed_formulas:
            return  # Already processed
            
        self._processed_formulas.add(formula)
        
        # Process arguments first (for nested exclusions)
        if hasattr(formula, 'arguments'):
            for arg in formula.arguments:
                self._register_witness_predicates_recursive(arg)
        
        # Register witnesses for this formula if it's an exclusion
        if hasattr(formula, 'operator') and formula.operator.name == 'uni_excl':
            formula_str = f"\\exclude({self._formula_to_string(formula.arguments[0])})"
            self.witness_registry.register_witness_predicates(formula_str)
```

**Key Improvements:**
1. **Two-pass separation** ensures all witnesses exist before any constraints are generated
2. **Recursive registration** handles nested exclusions (¬¬A, ¬(A ∧ ¬B), etc.)
3. **Processed formula tracking** prevents infinite recursion and duplicate registration
4. **WitnessAwareModel wrapping** preserves witness access after solving

## 3. Witness Registry: Consistency Management

### Failed Approach: Ad-hoc Function Creation

```python
# FAILED APPROACH - No consistency management
class InconsistentImplementation:
    def create_witness_constraint(self, formula):
        """Creates witness functions without consistency."""
        
        # Different parts of the system create different functions
        h_func = z3.Function(f"h_{self.counter}", domain, range)
        y_func = z3.Function(f"y_{self.counter}", domain, range) 
        self.counter += 1
        
        # Problem: Each call creates NEW functions, even for the same formula
        return self.generate_constraint_with_functions(h_func, y_func)
        
    def evaluate_with_witnesses(self, formula, model):
        """Tries to evaluate but uses wrong functions."""
        
        # Creates DIFFERENT functions than constraint generation used
        h_func = z3.Function(f"h_{self.counter}", domain, range)
        y_func = z3.Function(f"y_{self.counter}", domain, range)
        self.counter += 1
        
        # These are not the same as the functions used during solving!
        h_val = model.eval(h_func(some_arg))  # Wrong function!
        return self.compute_with_wrong_witnesses(h_val)
```

**Problems:**
1. **Identity issues** - different function objects for the same logical function
2. **No consistency** between constraint generation and evaluation phases
3. **Counter-based naming** creates different names each time

### Successful Approach: Centralized Registry

```python
# SUCCESSFUL APPROACH - Registry ensures consistency
class WitnessRegistry:
    def __init__(self, N):
        self.N = N
        self.predicates = {}  # Single source of truth
        
    def register_witness_predicates(self, formula_str):
        """Register witness predicates for a formula (idempotent)."""
        
        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"
        
        # Only create if they don't already exist
        if h_name not in self.predicates:
            h_pred = z3.Function(h_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
            y_pred = z3.Function(y_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
            
            self.predicates[h_name] = h_pred
            self.predicates[y_name] = y_pred
            
        return self.predicates[h_name], self.predicates[y_name]
        
    def get_witness_predicates(self, formula_str):
        """Get registered witness predicates."""
        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"
        return self.predicates.get(h_name), self.predicates.get(y_name)
        
    def get_all_predicates(self):
        """Get all registered predicates for model wrapping."""
        return dict(self.predicates)  # Return copy
        
    def clear(self):
        """Clear registry for clean builds."""
        self.predicates.clear()

# Usage ensures consistency:
class ConsistentImplementation:
    def __init__(self):
        self.registry = WitnessRegistry(3)
        
    def create_witness_constraint(self, formula_str):
        """Creates constraints using registry functions."""
        
        # Get consistent functions from registry
        h_func, y_func = self.registry.register_witness_predicates(formula_str)
        
        # Same functions will be returned for the same formula_str
        return self.generate_constraint_with_functions(h_func, y_func)
        
    def evaluate_with_witnesses(self, formula_str, model):
        """Evaluates using the SAME functions."""
        
        # Gets the SAME functions used during constraint generation
        h_func, y_func = self.registry.get_witness_predicates(formula_str)
        
        if h_func is None or y_func is None:
            return None  # Not registered
            
        # These are the correct functions!
        h_val = model.eval(h_func(some_arg))
        return self.compute_with_correct_witnesses(h_val)
```

**Key Advantages:**
1. **Idempotent registration** - same formula always gets same functions
2. **Consistent naming** based on formula structure, not counters
3. **Single source of truth** for all witness predicates
4. **Clean state management** with clear() method

## 4. Model Wrapping: Direct Witness Access

### Failed Approach: No Witness Access

```python
# FAILED APPROACH - Standard Z3 model with no witness access
class FailedModelUsage:
    def compute_verifiers_incorrectly(self, formula, model, eval_point):
        """Cannot access witness values from standard model."""
        
        # Standard Z3 model has no witness access methods
        # We know witnesses exist but cannot query them
        
        # Failed attempt 1: Try to extract from model declarations
        for decl in model.decls():
            if 'witness' in str(decl):
                # Model declarations don't give us the function objects
                pass
                
        # Failed attempt 2: Try to recreate constraint and re-solve
        new_constraint = self.generate_constraint_again(formula)
        # This creates NEW functions, not the original ones
        
        # Result: No way to verify the three exclusion conditions
        return []  # Leads to false premise problems
```

### Successful Approach: Model Wrapper with Direct Access

```python
# SUCCESSFUL APPROACH - Wrapped model with witness access
class WitnessAwareModel:
    """Extended model that provides direct witness access."""
    
    def __init__(self, z3_model, semantics, witness_predicates):
        self.z3_model = z3_model
        self.semantics = semantics
        self.witness_predicates = witness_predicates  # The key addition!
        self._witness_cache = {}  # Optional caching for performance
        
    def eval(self, expr):
        """Delegate standard evaluation to Z3 model."""
        return self.z3_model.eval(expr)
        
    def get_h_witness(self, formula_str, state):
        """Get h witness value for formula at state."""
        
        # Check cache first (optional optimization)
        cache_key = (formula_str, 'h', state)
        if cache_key in self._witness_cache:
            return self._witness_cache[cache_key]
            
        # Get the h predicate for this formula
        h_pred = self.witness_predicates.get(f"{formula_str}_h")
        if h_pred is None:
            return None
            
        # Evaluate h(state) using the Z3 model
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.z3_model.eval(h_pred(state_bv))
        
        # Convert to integer if it's a concrete value
        if z3.is_bv_value(result):
            value = result.as_long()
            self._witness_cache[cache_key] = value  # Cache for future queries
            return value
            
        return None  # Undefined or symbolic
        
    def get_y_witness(self, formula_str, state):
        """Get y witness value for formula at state."""
        # Similar implementation to get_h_witness
        cache_key = (formula_str, 'y', state)
        if cache_key in self._witness_cache:
            return self._witness_cache[cache_key]
            
        y_pred = self.witness_predicates.get(f"{formula_str}_y")
        if y_pred is None:
            return None
            
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.z3_model.eval(y_pred(state_bv))
        
        if z3.is_bv_value(result):
            value = result.as_long()
            self._witness_cache[cache_key] = value
            return value
            
        return None
        
    def has_witness_for(self, formula_str):
        """Check if model has witness predicates for a formula."""
        return (f"{formula_str}_h" in self.witness_predicates and
                f"{formula_str}_y" in self.witness_predicates)

# Usage with direct witness access:
class SuccessfulModelUsage:
    def compute_verifiers_correctly(self, formula, model, eval_point):
        """Can now access witness values directly."""
        
        formula_str = self.formula_to_string(formula)
        arg_verifiers = self.get_argument_verifiers(formula, model, eval_point)
        
        verifiers = []
        for state in range(2**self.N):
            # Check if this state verifies the exclusion
            verifies = True
            
            for v in arg_verifiers:
                # THE BREAKTHROUGH: Direct witness access!
                h_v = model.get_h_witness(formula_str, v)
                y_v = model.get_y_witness(formula_str, v)
                
                if h_v is None or y_v is None:
                    verifies = False
                    break
                    
                # Verify the three conditions with concrete values
                if not self.check_condition_1(v, y_v, h_v, model):
                    verifies = False
                    break
                if not self.check_condition_2(state, h_v, model):
                    verifies = False
                    break
                    
            if verifies and self.check_minimality(state, formula_str, model):
                verifiers.append(state)
                
        return verifiers  # Correct verifier computation!
```

**Key Improvements:**
1. **Direct witness access** through clean methods
2. **Caching for performance** (optional optimization)
3. **Proper error handling** for missing predicates
4. **Clean delegation** to base model for standard operations

## 5. Common Pitfalls and Solutions

### Pitfall 1: Function Identity Confusion

```python
# WRONG: Different function objects for the same logical function
def create_witnesses_wrong():
    # Each call creates new function objects
    h1 = z3.Function('h', domain, range)  # Object ID: 12345
    h2 = z3.Function('h', domain, range)  # Object ID: 67890 - Different!
    return h1 != h2  # True! Even though they have the same name

# RIGHT: Registry ensures same objects
registry = WitnessRegistry()
def create_witnesses_right():
    h1 = registry.get_or_create('h', domain, range)  # Object ID: 12345
    h2 = registry.get_or_create('h', domain, range)  # Object ID: 12345 - Same!
    return h1 is h2  # True! Same object
```

### Pitfall 2: Scope Issues with Variables vs. Functions

```python
# WRONG: Variables go out of scope
def generate_constraint_wrong():
    x = z3.BitVec('x', N)  # Local variable
    return z3.Exists([x], condition(x))  # x is no longer accessible

def use_constraint_wrong():
    constraint = generate_constraint_wrong()
    # Cannot access x here - it was local to generate_constraint_wrong
    
# RIGHT: Functions persist
def generate_constraint_right():
    f = z3.Function('f', z3.BitVecSort(N), z3.BitVecSort(N))  # Function object
    x = z3.BitVec('x', N)
    return f, z3.ForAll([x], condition(f(x)))  # f is returned and accessible

def use_constraint_right():
    f, constraint = generate_constraint_right()
    # Can still access and use f here
    model_value = model.eval(f(5))  # Can query f values from model
```

### Pitfall 3: Model Evaluation Without Checking Types

```python
# WRONG: Assuming all evaluations return concrete values
def unsafe_evaluation(model, func, arg):
    result = model.eval(func(arg))
    return result.as_long()  # Crashes if result is symbolic!

# RIGHT: Check result type before conversion
def safe_evaluation(model, func, arg):
    result = model.eval(func(arg))
    if z3.is_bv_value(result):
        return result.as_long()  # Safe conversion
    elif z3.is_bool(result):
        return z3.is_true(result)
    else:
        return None  # Undefined or symbolic
```

## 6. Testing Strategies

### Testing Failed Implementations

```python
# Test to detect false premise problems
def test_false_premises(implementation):
    """Test that detects the false premise problem."""
    
    # Create example: A ⊢ ¬A (should have countermodel)
    example = {
        'premises': ['A'], 
        'conclusions': ['\\exclude A'],
        'settings': {'N': 3}
    }
    
    # Build model
    model = implementation.build_model(example)
    
    # Critical test: Check if premises are true in the "countermodel"
    for premise in example['premises']:
        premise_verifiers = implementation.compute_verifiers(premise, model)
        world_states = implementation.get_world_states(model)
        
        # If any world verifies the premise, it should be true
        premise_true_somewhere = any(
            any(implementation.is_part_of(v, w, model) for v in premise_verifiers)
            for w in world_states
        )
        
        if not premise_true_somewhere:
            raise AssertionError(f"FALSE PREMISE: {premise} has no verifiers in 'countermodel'")
    
    # If we get here, implementation passed the false premise test
```

### Testing Successful Implementations

```python
# Comprehensive test for correct implementation
def test_witness_predicate_implementation(implementation):
    """Comprehensive test suite for witness predicate approach."""
    
    # Test 1: Direct witness access
    model = implementation.build_model({'premises': ['\\exclude A'], 'conclusions': []})
    
    # Should be able to access witness values
    h_val = model.get_h_witness('\\exclude(A)', 5)
    y_val = model.get_y_witness('\\exclude(A)', 5)
    
    assert h_val is not None, "Should be able to access h witness"
    assert y_val is not None, "Should be able to access y witness"
    assert isinstance(h_val, int), "Witness values should be concrete integers"
    
    # Test 2: Consistency across calls
    h_val_2 = model.get_h_witness('\\exclude(A)', 5)
    assert h_val == h_val_2, "Multiple calls should return same value"
    
    # Test 3: False premise detection
    test_false_premises(implementation)
    
    # Test 4: Complex nested formulas
    nested_example = {
        'premises': ['\\exclude \\exclude A'],  # ¬¬A
        'conclusions': ['A'],
        'settings': {'N': 3}
    }
    
    nested_model = implementation.build_model(nested_example)
    
    # Should have witnesses for both ¬A and ¬¬A
    assert nested_model.has_witness_for('\\exclude(A)'), "Should have witnesses for ¬A"
    assert nested_model.has_witness_for('\\exclude(\\exclude(A))'), "Should have witnesses for ¬¬A"
    
    print("All tests passed! Implementation is correct.")
```

## Conclusion

The code examples show the crucial differences between failed and successful approaches:

1. **Existential variables** → **Z3 Function objects**
2. **Single-pass processing** → **Two-pass registration and generation**  
3. **Ad-hoc function creation** → **Registry-based consistency management**
4. **Standard models** → **Wrapped models with witness access**
5. **Unsafe assumptions** → **Defensive programming with type checking**

The successful witness predicate approach demonstrates that elegant theoretical ideas can be made computationally tractable through careful architectural design, proper abstraction, and systematic testing.

Each transformation addresses a specific architectural limitation while preserving the theoretical elegance of the original semantic definition. The result is a clean, correct, and maintainable implementation that serves as a model for other complex semantic implementations.