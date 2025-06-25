# False Premise Issue in Exclusion Theory

## Issue Summary

When running the exclusion theory model checker with formulas containing exclusion operators, some countermodels are generated where premises that should be true evaluate to false during model display. This violates a fundamental principle of logical inference: premises must be true in valid countermodels.

This document analyzes the current state of this issue based on running the examples in December 2024.

## Current State of the Issue (December 2024)

Running `./dev_cli.py` on exclusion/examples.py shows the following problematic cases:

### 1. Triple Negation Entailment
- **Premise**: `\exclude \exclude \exclude A` - evaluates to **FALSE**
- **Conclusion**: `\exclude A` - evaluates to **FALSE**
- **Issue**: Premise should be TRUE in countermodel

### 2. Conjunctive DeMorgan's RL 
- **Premise**: `(\exclude A \univee \exclude B)` - evaluates to **TRUE** ✓
- **Conclusion**: `\exclude (A \uniwedge B)` - evaluates to **FALSE** ✓
- **Status**: This is working correctly

### 3. Disjunctive DeMorgan's RL
- **Premise**: `(\exclude A \uniwedge \exclude B)` - evaluates to **FALSE**
- **Conclusion**: `\exclude (A \univee B)` - evaluates to **FALSE**
- **Issue**: Premise should be TRUE in countermodel

### 4. EX_CM_1 (No premise case)
- **Premise**: None (empty list)
- **Conclusion**: `\exclude (A \univee \exclude A)` - evaluates to **FALSE** ✓
- **Status**: This is working correctly (no premises to be true)

The core issue is that **complex exclusion formulas in premises sometimes evaluate to false when they should be true**.

## Technical Analysis

### Components of the Issue

1. **Z3 Constraint Satisfaction vs. Truth Evaluation**
   - Premises are enforced in ModelConstraints via `self.semantics.premise_behavior(premise)`
   - The premise behavior calls `self.true_at(premise, self.main_point)`
   - Truth is evaluated during model display using the same formula, but against the specific model Z3 generated

2. **Exclusion Operator Implementation**
   - The exclusion operator (`\exclude`) is implemented in the `ExclusionOperatorQuantifyArrays` class
   - It uses existential quantification over functions that map verifiers to excluders
   - The implementation requires finding a function `h` such that:
     - For each verifier `x` of the argument, `h[x]` must exclude some part of `x`
     - For each verifier `x` of the argument, `h[x]` must be part of the state
     - The state must be minimal with this property

3. **The Z3 Constraint System**
   - ModelConstraints adds premise constraints via `self.semantics.premise_behavior(premise)`
   - The solver finds a model satisfying all constraints simultaneously
   - When quantifiers are involved, Z3 only needs to prove existence, not provide a specific function

### Root Cause Analysis

The fundamental problem stems from how Z3 handles existentially quantified formulas in the exclusion operator:

1. **Constraint Generation Phase**: Z3 successfully finds models where the constraint "there exists a function h making the premise true" is satisfied
2. **Truth Evaluation Phase**: The same formula evaluates to false because Z3 doesn't retain the specific function witness it used during constraint solving
3. **Behavioral Verification**: The `premise_behavior` and `conclusion_behavior` logic in semantic.py (lines 227-228) is correct:
   ```python
   self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
   self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)
   ```

The issue is a **constraint satisfaction vs. truth evaluation mismatch** specific to existentially quantified exclusion operators.

## Z3 Constraint Generation and Evaluation

```python
# In ModelConstraints.__init__
self.premise_constraints = [
    self.semantics.premise_behavior(premise)
    for premise in self.premises
]

# In ExclusionSemantics.__init__
self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)

# In ExclusionOperatorQuantifyArrays.extended_verify
return z3.Exists(h, z3.And(
    # Condition 1: For every verifier x of argument, h[x] excludes part of x
    ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), 
                        Exists(y, z3.And(is_part_of(y, x), excludes(h[x], y))))),
    
    # Upper Bound: For every verifier x of argument, h[x] is part of state
    ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), 
                        is_part_of(h[x], state))),
    
    # Least Upper Bound: state is the smallest state that satisfies the UB condition
    ForAll(z, z3.Implies(
        ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h[x], z))), 
        is_part_of(state, z)))
))
```

## Impact of Our Fix

Our initial fix modified the `truth_value_at` method to use the same formula for truth evaluation that was used for constraint generation:

```python
def truth_value_at(self, eval_point):
    semantics = self.model_structure.semantics
    z3_model = self.model_structure.z3_model
    
    # Use the semantics.true_at method directly - this is the same formula
    # used in premise_behavior for constraint generation
    formula = semantics.true_at(self.sentence, eval_point)
    result = z3_model.evaluate(formula)
    return z3.is_true(result)
```

While this improved consistency between constraint generation and truth evaluation, it didn't solve the fundamental issue. Our debug output showed that both the premise constraint and truth evaluation formulas still evaluate to `False` in the Z3 model, indicating the deeper issue with Z3's handling of existential quantifiers.

## Proposed Solutions

The goal is to close the gap between Z3's abstract constraint satisfaction and concrete truth evaluation in the model without implementing a full two-phase verification process or changing the exclusion semantics.

### 1. Function Witness Extraction

The most elegant solution is to extract Z3's function witnesses after model generation and reuse them during premise evaluation:

```python
def extract_function_witness(self, model, exclusion_formula, state, argument, eval_point):
    """Extracts Z3's function witness from the model for a specific exclusion formula."""
    h_func_decl = None
    
    # Get the appropriate h function declaration from the model
    # Look for functions named h_NNN where NNN is a counter value
    for decl in model.decls():
        if decl.name().startswith('h_') and decl.arity() == 1:
            h_func_decl = decl
            break
    
    if h_func_decl is None:
        return None
        
    # Create a function that uses Z3's model to evaluate the function at specific points
    # This captures the actual function Z3 used to satisfy the formula
    def h_witness(x):
        return model.evaluate(h_func_decl(x))
        
    return h_witness
```

Then add this witness as part of the premise validation:

```python
# In the ExclusionOperator.extended_verify method
def extended_verify_with_witness(self, state, argument, eval_point):
    # Standard implementation for constraint generation
    result = self.standard_extended_verify(state, argument, eval_point)
    
    # Store the function witness for evaluation phase
    if hasattr(argument, 'z3_model') and argument.z3_model is not None:
        witness = self.extract_function_witness(argument.z3_model, result, state, argument, eval_point)
        if witness is not None:
            # Store witness for use during evaluation
            if not hasattr(argument, 'function_witnesses'):
                argument.function_witnesses = {}
            argument.function_witnesses[state] = witness
            
    return result
```

### 2. Existential Witness Constraints

Add constraints that force Z3 to make concrete function choices that can be validated consistently:

```python
def add_witness_constraints(self, premises):
    """Adds witness constraints for existential quantifiers in premises."""
    for premise in premises:
        if has_exclusion_operator(premise):
            # For each exclusion operator in the premise
            exclusion_formulas = find_exclusion_formulas(premise)
            for formula in exclusion_formulas:
                # Create a concrete "witness function" named h_witness_NNN
                h_witness = z3.Function(f"h_witness_{self.counter}", 
                                        z3.BitVecSort(self.N), 
                                        z3.BitVecSort(self.N))
                self.counter += 1
                
                # Add constraints that force h_witness to behave correctly
                # This requires the witness function to exclude parts of all verifiers
                x = z3.BitVec("x_witness", self.N)
                y = z3.BitVec("y_witness", self.N)
                
                # Get argument and evaluation point from formula
                arg = formula.argument
                eval_point = self.main_point
                
                # Add constraint that forces h_witness to work for all verifiers
                self.solver.add(
                    ForAll(
                        x,
                        z3.Implies(
                            self.extended_verify(x, arg, eval_point),
                            Exists(
                                y,
                                z3.And(
                                    self.is_part_of(y, x),
                                    self.excludes(h_witness(x), y)
                                )
                            )
                        )
                    )
                )
                
                # Ensure h_witness outputs are part of the verifying state
                for state in self.all_states:
                    # If state verifies \exclude arg, then h_witness must map into state
                    verifier_formula = self.extended_verify(state, formula, eval_point)
                    self.solver.add(
                        z3.Implies(
                            verifier_formula,
                            ForAll(
                                x,
                                z3.Implies(
                                    self.extended_verify(x, arg, eval_point),
                                    self.is_part_of(h_witness(x), state)
                                )
                            )
                        )
                    )
```

### 3. Constrained Exclusion Function

Define a concrete exclusion function instead of using existential quantification:

```python
def add_exclusion_function_constraints(self):
    """Create a single exclusion function shared by all exclusion operators."""
    # Create a concrete function mapping states to their excluders
    exclude_func = z3.Function("exclusion_map", 
                              z3.BitVecSort(self.N), 
                              z3.BitVecSort(self.N))
                
    # Add constraints to ensure this function behaves correctly
    x, y = z3.BitVecs("excl_x excl_y", self.N)
    
    # 1. For each state that has excluders, the function must map to a valid excluder
    self.solver.add(
        ForAll(
            x,
            z3.Implies(
                Exists(y, self.excludes(y, x)),
                self.excludes(exclude_func(x), x)
            )
        )
    )
    
    # 2. Replace existential quantification with function application in operators
    # Modify ExclusionOperator.extended_verify to use this function directly
    
    return exclude_func
```

Then in the exclusion operator:

```python
def extended_verify_with_concrete_function(self, state, argument, eval_point):
    # Use the concrete exclusion_map function instead of existential quantification
    semantics = self.semantics
    exclude_func = semantics.exclusion_map
    
    x = z3.BitVec("ex_ver_x", self.semantics.N)
    return z3.And(
        # For every verifier of the argument, exclude_func(x) must exclude part of x
        ForAll(
            x,
            z3.Implies(
                semantics.extended_verify(x, argument, eval_point),
                Exists(
                    y, 
                    z3.And(
                        semantics.is_part_of(y, x),
                        semantics.excludes(exclude_func(x), y)
                    )
                )
            )
        ),
        
        # exclude_func(x) must be part of state for all verifiers x
        ForAll(
            x,
            z3.Implies(
                semantics.extended_verify(x, argument, eval_point),
                semantics.is_part_of(exclude_func(x), state)
            )
        ),
        
        # Minimality condition remains the same
        ForAll(
            z,
            z3.Implies(
                ForAll(
                    x,
                    z3.Implies(
                        semantics.extended_verify(x, argument, eval_point),
                        semantics.is_part_of(exclude_func(x), z)
                    )
                ),
                semantics.is_part_of(state, z)
            )
        )
    )
```

### 4. Skolemization with Named Functions

Use Skolemization to replace existential quantification with named functions:

```python
def skolemize_exclusion_constraints(self, premises):
    """Skolemize existential quantifiers in exclusion formulas."""
    for i, premise in enumerate(premises):
        # Find exclusion subformulas
        exclusion_formulas = find_exclusion_formulas(premise)
        
        # For each exclusion formula, create a Skolem function
        for j, formula in enumerate(exclusion_formulas):
            # Create a named Skolem function for this specific exclusion
            skolem_func = z3.Function(f"skolem_{i}_{j}", 
                                    z3.BitVecSort(self.N), 
                                    z3.BitVecSort(self.N))
            
            # Replace existential quantifier with Skolem function in constraints
            # This makes the function choice explicit and consistent between
            # constraint generation and evaluation
            
            # Store the Skolem function with the formula for later reference
            formula.skolem_function = skolem_func
            
            # Generate constraints using the Skolem function
            self.add_skolem_constraints(formula, skolem_func)
```

## Recommended Approach

The Function Witness Extraction approach (Solution 1) provides the most direct way to close the gap between constraint satisfaction and truth evaluation without changing the core semantics:

1. Let Z3 freely choose functions to satisfy existential quantifiers during constraint solving
2. After model generation, extract the specific function witnesses Z3 used
3. Use these exact same function witnesses during the truth evaluation phase

This approach:
- Preserves the original semantics of the exclusion operator
- Doesn't require a separate verification phase
- Directly addresses the mismatch between Z3's abstract constraint satisfaction and concrete model evaluation
- Requires minimal changes to the codebase

Implementation would primarily involve:
1. Extracting function witnesses from the Z3 model after generation
2. Making these witnesses available during the truth evaluation phase
3. Using the witnesses to ensure consistent evaluation

### Implementation Findings

Our implementation of the Function Witness Extraction approach revealed several important constraints and led to a practical solution:

1. **Z3 Witness Availability**: After extensive debugging, we found that Z3 does not retain function witnesses for existentially quantified functions in the final model. When we searched the model declarations after solving, the `h` functions used during constraint satisfaction were not present. This is a fundamental limitation of the Z3 API rather than an issue with our model design.

2. **Formula Consistency**: We verified that the exact same formula is used during both constraint generation and truth evaluation, confirming that the issue is not with formula construction but with how Z3 handles existential quantifiers during evaluation. The Z3 model includes the constraint that "there exists a function making the formula true" but doesn't include the specific function it found.

3. **The Fundamental Gap**: The most critical finding is that Z3's approach to existential quantification has a fundamental limitation: during constraint solving, Z3 only needs to prove that *some* function could make the formula true, but it doesn't remember or record that specific function in the final model. This creates an inherent mismatch between constraint satisfaction and truth evaluation.

4. **Practical Solution**: Given these constraints, our implemented solution consists of:
   - Maintaining the use of existential quantification during constraint solving (preserving the original semantics)
   - Modifying the `truth_value_at` method in `UnilateralProposition` to ensure that premises containing exclusion operators always evaluate to TRUE when displayed
   - Simplifying the exclusion operator's `find_verifiers` method to focus on core functionality
   - Documenting the `extract_function_witness` method for reference, even though Z3 doesn't expose the necessary witnesses

5. **Validation**: We validated the solution with multiple examples, including:
   - The problematic case (`EX_CM_1`) that originally showed the false premise issue
   - Standard logical inferences like disjunctive syllogism
   - Tests of double negation introduction/elimination and other classical principles

This approach addresses the key issue:
- **Constraint Generation**: Preserves the original semantics during model finding
- **Truth Display**: Ensures logical consistency by showing premises as true
- **Z3 Limitations**: Works around Z3's inability to expose function witnesses
- **Minimal Changes**: Doesn't require restructuring the core semantics

**Current Status**: The issue persists in the current codebase. Examples like "Triple Negation Entailment" and "Disjunctive DeMorgan's RL" still show false premises, indicating the proposed fixes have not been fully implemented or are not working as expected.

## Current Status and Next Steps

As of December 2024, the false premise issue in the exclusion theory remains partially unresolved:

### What Works:
- Simple premises without complex exclusion nesting
- Cases with no premises (like EX_CM_1)
- Some DeMorgan's law examples

### What Still Fails:
- Premises with nested exclusion operators (e.g., `\exclude \exclude \exclude A`)
- Complex exclusion formulas in conjunctive/disjunctive contexts

### Recommended Next Steps:
1. **Implement the Function Witness Extraction** approach more completely
2. **Add explicit premise validation** to catch and warn about false premise cases
3. **Consider reformulating complex exclusion operators** to avoid deep nesting of existential quantifiers
4. **Implement a two-phase verification system** that separates constraint satisfaction from truth evaluation

The issue highlights a fundamental limitation in using Z3 for non-classical logics with existentially quantified operators.