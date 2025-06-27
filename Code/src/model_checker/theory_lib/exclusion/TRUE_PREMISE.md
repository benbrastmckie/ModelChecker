# Exclusion Theory False Premise Analysis - Current Status (December 2024)

## Problem Overview

The exclusion theory's model checker is finding countermodels where some premises containing complex exclusion operators evaluate to false during model display, which violates a core requirement of logical inference: premises must be true in valid countermodels.

## Technical Investigation

### Relationship to FALSE_PREMISE.md

This analysis builds upon and supports the detailed investigation in FALSE_PREMISE.md. Both documents identify the same core issue: **Z3's inability to provide consistent evaluation of existentially quantified formulas between constraint satisfaction and model evaluation phases**.

### Current Implementation Status (December 2024)

After running the current examples and examining the code, here's what's actually happening:

**Examples with Issues**:
1. **"Triple Negation Entailment"**: 
   - Premise: `\exclude \exclude \exclude A` → **FALSE** ❌ (should be TRUE)
   - Conclusion: `\exclude A` → **FALSE** ✓
   
2. **"Disjunctive DeMorgan's RL"**: 
   - Premise: `(\exclude A \uniwedge \exclude B)` → **FALSE** ❌ (should be TRUE) 
   - Conclusion: `\exclude (A \univee B)` → **FALSE** ✓

**Examples Working Correctly**:
1. **"Conjunctive DeMorgan's RL"**:
   - Premise: `(\exclude A \univee \exclude B)` → **TRUE** ✓
   - Conclusion: `\exclude (A \uniwedge B)` → **FALSE** ✓

**Core Implementation**:
- The `premise_behavior` and `conclusion_behavior` logic in semantic.py:227-228 is correct
- The issue is specifically with Z3's evaluation of complex exclusion formulas during the display phase
- Simple exclusion formulas work fine; nested/complex ones fail

### Root Cause

The fundamental issue is a mismatch between Z3's constraint satisfaction and truth evaluation phases:

1. During constraint solving, Z3 only needs to prove that *some* function `h` exists that would make the formula true.
2. During truth evaluation, Z3 needs to use a specific function to evaluate the formula, but it doesn't retain the function witness it found during constraint solving.
3. This creates a gap where the formula can be satisfiable (there exists a function that works) but evaluates to false (the specific model doesn't reveal what function was used).

This issue specifically affects formulas with existential quantifiers like the exclusion operator, which need to find a mapping function from verifiers to excluders.

### Alignment with FALSE_PREMISE.md Analysis

The FALSE_PREMISE.md document provides a comprehensive analysis of the issue and recommends **Function Witness Extraction** as the primary solution approach. This document supports that recommendation.

**Current Implementation Status**: The `truth_value_at` method (semantic.py:788-804) uses standard Z3 evaluation without any special handling:

```python
def truth_value_at(self, eval_point):
    semantics = self.model_structure.semantics
    z3_model = self.model_structure.z3_model
    
    # Evaluate the formula directly in the Z3 model
    formula = semantics.true_at(self.sentence, eval_point)
    result = z3_model.evaluate(formula)
    return z3.is_true(result)
```

**Key Finding**: The false premise issue is **not a bug in the truth evaluation logic** but rather a **fundamental limitation in Z3's handling of existential quantifiers**. The solution requires addressing the root cause in the exclusion operator implementation.

## Current Testing Results (December 2024)

Running `./dev_cli.py /path/to/exclusion/examples.py` shows:

**Working Cases**:
- **EX_CM_1**: No premises, conclusion false ✓
- **Conjunctive DeMorgan's RL**: True premise, false conclusion ✓

**Problematic Cases**:
- **Triple Negation Entailment**: False premise ❌, false conclusion ✓
- **Disjunctive DeMorgan's RL**: False premise ❌, false conclusion ✓

**Analysis**:
1. Z3 model generation succeeds and finds valid countermodels
2. The state spaces, conflicts, and exclusion relations look correct
3. The issue is specifically with **truth evaluation of complex exclusion formulas**
4. Simple exclusion formulas evaluate correctly, complex/nested ones don't

## Recommended Solution: Function Witness Extraction

Following the analysis in FALSE_PREMISE.md, the most principled approach is **Function Witness Extraction** rather than special-case handling of premises.

### Core Approach

The goal is to bridge the gap between Z3's constraint satisfaction and truth evaluation by extracting and reusing the function witnesses that Z3 used during model generation:

1. **During Model Generation**: Z3 finds functions `h` that satisfy existential quantifiers in exclusion formulas
2. **After Model Generation**: Extract these function witnesses from the Z3 model
3. **During Truth Evaluation**: Use the same extracted functions to ensure consistent evaluation

### Implementation Strategy

As detailed in FALSE_PREMISE.md, the recommended implementation involves:

```python
def extract_function_witness(self, z3_model, counter_value=None):
    """Extracts Z3's function witnesses from the model for exclusion formulas."""
    if not z3_model:
        return {}
        
    result = {}
    h_funcs = {}
    
    # Extract all h_ function declarations from the model
    for decl in z3_model.decls():
        if decl.name().startswith('h_') or decl.name() == 'h':
            if decl.name() == 'h':
                h_funcs['h'] = decl
            elif decl.arity() == 1:
                h_funcs[decl.name()] = decl
    
    # Create witness functions for evaluation
    for name, decl in h_funcs.items():
        if name == 'h':
            def array_witness(x):
                x_val = z3.BitVecVal(x, self.N) if isinstance(x, int) else x
                return z3_model.evaluate(decl[x_val])
            result[name] = array_witness
        else:
            def make_function_witness(func_decl):
                def witness(x):
                    x_val = z3.BitVecVal(x, self.N) if isinstance(x, int) else x
                    return z3_model.evaluate(func_decl(x_val))
                return witness
            result[name] = make_function_witness(decl)
    
    self.function_witnesses.update(result)
    return result
```

### Current Status and Limitations

**Z3 Limitation**: As documented in FALSE_PREMISE.md, our investigation revealed that Z3 does not retain function witnesses for existentially quantified functions in the final model. This is a fundamental limitation of the Z3 API.

**Alternative Approaches** (from FALSE_PREMISE.md):
1. **Skolemization with Named Functions**: Replace existential quantifiers with named Skolem functions
2. **Constrained Exclusion Functions**: Define concrete exclusion functions instead of using existential quantification
3. **Existential Witness Constraints**: Add constraints that force Z3 to make concrete function choices

### Long-term Solution Path

Rather than implementing workarounds that mask the underlying issue, the recommended path is:

1. **Reformulate Exclusion Operators**: Modify the exclusion operator implementation to avoid existential quantification entirely
2. **Use Concrete Functions**: Replace the existentially quantified function `h` with a concrete, globally defined function
3. **Maintain Semantic Consistency**: Ensure the reformulated operators preserve the intended exclusion semantics

## Current Status and Next Steps

As of December 2024, the false premise issue **persists in the exclusion theory**:

### Current State:
1. **False premises appear** in "Triple Negation Entailment" and "Disjunctive DeMorgan's RL"
2. **Root cause identified**: Z3's existential quantifier handling prevents function witness access
3. **All current strategies affected**: MS, SK, CD, UF all use existential quantification

### Investigation Summary (December 2024):

Through detailed analysis, we've confirmed:

1. **The Problem Pattern**:
   - Formulas with nested exclusions (e.g., `\exclude \exclude \exclude A`) consistently fail
   - Each exclusion layer adds existential quantifiers: ∃h₁.∃h₂.∃h₃...
   - Z3 proves satisfiability but cannot provide the witness functions

2. **Strategy Analysis**:
   - **MS (Multi-Sort)**: Current default, 50% success rate but 47% false premises
   - **SK (Skolemization)**: Attempts to eliminate ∃ but still uses them for witnesses
   - **CD (Constraints)**: Limited by enumeration size
   - **UF (Axioms)**: Clean approach but retains existential quantifiers

3. **Why Current Strategies Fail**:
   All strategies ultimately generate formulas like:
   ```
   ∃h. ∀x. (x verifies φ) → ∃y. (y ⊑ x ∧ h(x) excludes y)
   ```
   The nested ∃h and ∃y cannot be evaluated after solving.

### Recommended Implementation Path:

**Phase 1: True Skolemization Implementation**
```python
class ExclusionOperatorSkolemized2(ExclusionOperatorBase):
    def extended_verify(self, state, argument, eval_point):
        # Create Skolem functions WITHOUT existential quantifiers
        h_sk = z3.Function(f"h_sk_{self.counter}", BitVec(N), BitVec(N))
        y_sk = z3.Function(f"y_sk_{self.counter}", BitVec(N), BitVec(N))
        
        # Direct constraints, no ∃
        return z3.And(
            # For all verifiers, constraints hold
            z3.ForAll(x, z3.Implies(
                verify(x, argument),
                z3.And(
                    is_part_of(y_sk(x), x),
                    excludes(h_sk(x), y_sk(x)),
                    is_part_of(h_sk(x), state)
                )
            )),
            # Minimality without existential quantifiers
            ...
        )
```

**Phase 2: Global Function Alternative**
```python
# Define once at module level
EXCLUSION_FUNC = z3.Function("excl_global", BitVec(N), BitVec(N), BitVec(N))

class ExclusionOperatorGlobal(ExclusionOperatorBase):
    def extended_verify(self, state, argument, eval_point):
        # Use global function with argument encoding
        arg_id = self.encode_argument(argument)
        return self.verify_with_global(state, arg_id, EXCLUSION_FUNC)
```

**Phase 3: Validation and Comparison**
- Test both approaches on all 34 examples
- Measure: success rate, reliability, false premise elimination
- Document semantic differences from original

### Expected Outcomes:

1. **Elimination of False Premises**: No existential quantifiers means consistent evaluation
2. **Trade-offs**:
   - May find different models than original semantics
   - Potentially more restrictive (fewer models found)
   - But all found models will be valid

3. **Performance**: Should be faster (no quantifier alternation)

### Long-term Research Directions:
1. **Semantic Reformulation**: Design exclusion semantics without problematic quantifier patterns
2. **Custom Verification**: Build specialized model checker for exclusion logic
3. **Hybrid Approaches**: Use Z3 for core logic, custom solver for exclusion

The focus should be on **eliminating existential quantifiers entirely** rather than trying to work around Z3's limitations. This requires accepting that the computational implementation may differ slightly from the pure mathematical semantics.

## SK2 Implementation Results (December 2024)

### What Was Implemented

The SK2 (True Skolemization) strategy was implemented as recommended above:

```python
class ExclusionOperatorSkolemized2(ExclusionOperatorBase):
    """True Skolemization (SK2) strategy - completely eliminates ALL existential quantifiers."""
    
    def extended_verify(self, state, argument, eval_point):
        # Create Skolem functions for both h and y
        h_sk = z3.Function(f"h_sk2_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
        y_sk = z3.Function(f"y_sk2_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # No existential quantifiers - direct constraints
        return z3.And(
            # Condition 1 with Skolemized y
            ForAll(x, z3.Implies(
                extended_verify(x, argument, eval_point),
                z3.And(
                    is_part_of(y_sk(x), x),
                    excludes(h_sk(x), y_sk(x))
                )
            )),
            # Upper bound condition
            ForAll(x, z3.Implies(
                extended_verify(x, argument, eval_point),
                is_part_of(h_sk(x), state)
            )),
            # Least upper bound condition
            ForAll(z, z3.Implies(
                ForAll(x, z3.Implies(
                    extended_verify(x, argument, eval_point),
                    is_part_of(h_sk(x), z)
                )),
                is_part_of(state, z)
            ))
        )
```

### Test Results

Testing revealed that **SK2 does NOT solve the false premise issue**:

#### Triple Negation Entailment (`\exclude \exclude \exclude A ⊢ \exclude A`)
- **MS Strategy**: Premise evaluates to FALSE ❌
- **SK2 Strategy**: Premise evaluates to FALSE ❌

#### Disjunctive DeMorgan's RL (`(\exclude A \uniwedge \exclude B) ⊢ \exclude (A \univee B)`)
- **MS Strategy**: Premise evaluates to FALSE ❌
- **SK2 Strategy**: Premise evaluates to FALSE ❌

### Critical Discovery

The investigation uncovered a fundamental architectural issue:

1. **Constraint Generation** (in `operators.py`):
   - Uses `extended_verify` method
   - SK2 successfully eliminates existential quantifiers here
   - Creates Skolem functions h_sk2 and y_sk2

2. **Truth Evaluation** (in `semantic.py`):
   - Uses `truth_value_at` → `semantics.true_at` → `operator.true_at`
   - This uses a DIFFERENT method than constraint generation
   - Still uses existential quantifiers from the original semantics

### The Disconnect

```python
# During constraint generation (works with SK2):
operator.extended_verify(state, argument, eval_point)  # Uses Skolemization

# During truth evaluation (ignores SK2):
operator.true_at(argument, eval_point)  # Uses original existential quantifiers
```

The two phases use **completely different code paths**, so modifying only the constraint generation strategy cannot solve the evaluation problem.

### Conclusion

The SK2 implementation confirmed that:

1. **Skolemization alone is insufficient** - it only affects constraint generation
2. **The architecture prevents a strategy-only solution** - evaluation uses different methods
3. **A deeper refactoring is required** - either:
   - Modify both `extended_verify` AND `true_at` to use Skolemization
   - Create a unified evaluation mechanism
   - Implement witness extraction and reuse between phases

The false premise issue is not just about Z3's handling of existential quantifiers, but about the **fundamental separation between constraint generation and truth evaluation** in the codebase architecture.
