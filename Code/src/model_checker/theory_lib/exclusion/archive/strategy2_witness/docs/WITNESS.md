# Witness Predicates in Exclusion Semantics

## Overview

This document explains how witness predicates enable the implementation of Champollion-Bernard (CB) preclusion semantics in the ModelChecker, contrasting this approach with Fine's set-based preclusion semantics. It is designed to be accessible to readers new to both Z3 and programmatic semantics.

> **Background**: For an introduction to Z3 and SMT solvers, see [Z3_BACKGROUND.md](/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/Z3_BACKGROUND.md).

## Table of Contents

1. [Introduction: Two Approaches to Preclusion](#introduction-two-approaches-to-preclusion)
2. [The Challenge: Quantifying Over Functions](#the-challenge-quantifying-over-functions)
3. [Witness Predicates: Making Functions Explicit](#witness-predicates-making-functions-explicit)
4. [CB Preclusion with Witnesses](#cb-preclusion-with-witnesses)
5. [Fine Preclusion: A Function-Free Alternative](#fine-preclusion-a-function-free-alternative)
6. [Comparing the Approaches](#comparing-the-approaches)
7. [Implementation Details](#implementation-details)
8. [Key Insights](#key-insights)

## Introduction: Two Approaches to Preclusion

In exclusion semantics, we want to formalize when one state "precludes" or "excludes" a proposition. Two prominent approaches are:

1. **Champollion-Bernard (CB) Preclusion**: Uses functions to map verifiers to their excluded parts
2. **Fine Preclusion**: Uses sets and relations without function quantification

Both capture the intuition that a state precludes a proposition by containing parts that exclude parts of the proposition's verifiers. The key difference lies in *how* they formalize this relationship.

## The Challenge: Quantifying Over Functions

### CB Preclusion's Three Conditions

A state `e` CB-precludes a proposition `A` when there exist functions `h` and `y` such that:

1. **Exclusion**: For every verifier `v` of `A`, `h(v)` excludes `y(v)` where `y(v)` is part of `v`
2. **Upper Bound**: For every verifier `v` of `A`, `h(v)` is part of `e`  
3. **Minimality**: `e` is the smallest state satisfying conditions 1 and 2

In logical notation:
```
∃h ∃y: 
  (∀v ∈ Ver(A): y(v) ⊑ v ∧ h(v) excludes y(v)) ∧
  (∀v ∈ Ver(A): h(v) ⊑ e) ∧
  (∀e' ⊂ e: ¬(conditions 1 & 2 hold for e'))
```

### The Problem

Z3 struggles with formulas that quantify over functions (∃h ∃y). While it can handle:
- Quantification over values: `∃x: P(x)`
- Properties of functions: `∀x: f(x) > 0`

It has difficulty with:
- Quantification over functions: `∃f: ∀x: P(f(x))`

## Witness Predicates: Making Functions Explicit

### The Solution

Instead of asking Z3 to "find" functions `h` and `y`, we:

1. **Pre-declare** specific functions for each formula
2. **Add constraints** that define their behavior
3. **Use them** in our semantic definitions

### How It Works

For each formula `\exclude(A)` in our model:

```python
# 1. Create witness functions
h_A = z3.Function('exclude_A_h', BitVecSort(N), BitVecSort(N))
y_A = z3.Function('exclude_A_y', BitVecSort(N), BitVecSort(N))

# 2. Add constraints linking them to CB preclusion
# If state e verifies \exclude(A), then h_A and y_A witness this
solver.add(
    Implies(
        verifies(e, '\exclude(A)'),
        And(
            # Condition 1: Exclusion
            ForAll([v], Implies(
                verifies(v, 'A'),
                And(is_part_of(y_A(v), v),
                    excludes(h_A(v), y_A(v)))
            )),
            # Condition 2: Upper bound
            ForAll([v], Implies(
                verifies(v, 'A'),
                is_part_of(h_A(v), e)
            )),
            # Condition 3: Minimality
            ForAll([z], Implies(
                And(
                    is_part_of(z, e),  # z is a proper part of e
                    z != e,
                    # All h values fit in z
                    ForAll([v], Implies(
                        verifies(v, 'A'),
                        is_part_of(h_A(v), z)
                    ))
                ),
                # Then z fails condition 1 (exclusion property)
                Not(ForAll([v], Implies(
                    verifies(v, 'A'),
                    And(is_part_of(y_A(v), v),
                        excludes(h_A(v), y_A(v)))
                )))
            ))
        )
    )
)
```

The minimality condition ensures that `e` is the *smallest* state that can serve as a CB-precluder. It says: if any proper part `z` of `e` could contain all the `h` values, then `z` must fail to satisfy the exclusion property. This prevents "bloated" precluders that contain unnecessary parts.

### The Key Insight

We transform:
- **Existential quantification over functions**: `∃h ∃y: P(h, y)`
- Into **constraints on pre-declared functions**: `P(h_A, y_A)`

This makes the functions part of the model structure rather than something to be discovered during solving.

## CB Preclusion with Witnesses

### Implementation in UniNegationOperator

The `UniNegationOperator` implements CB preclusion using witness predicates:

```python
class UniNegationOperator(Operator):
    name = "\\func_unineg"
    
    def extended_verify(self, state, argument, eval_point):
        """State verifies \exclude(A) using witness predicates"""
        
        # Get pre-registered witness functions
        formula_str = f"\\func_unineg({argument})"
        h_pred = sem.witness_registry[f"{formula_str}_h"]
        y_pred = sem.witness_registry[f"{formula_str}_y"]
        
        # Express CB conditions using these witnesses
        return And(
            # Condition 1: Exclusion property
            ForAll([x], Implies(
                verifies(x, argument),
                And(is_part_of(y_pred(x), x),
                    excludes(h_pred(x), y_pred(x)))
            )),
            
            # Condition 2: Upper bound
            ForAll([x], Implies(
                verifies(x, argument),
                is_part_of(h_pred(x), state)
            )),
            
            # Condition 3: Minimality - state is smallest satisfying 1 & 2
            ForAll([z], Implies(
                ForAll([x], Implies(
                    verifies(x, argument),
                    is_part_of(h_pred(x), z)
                )),
                is_part_of(state, z)
            ))
        )
```

### Witness Registration Flow

1. **Parse Formula**: Identify all `\exclude` subformulas
2. **Register Witnesses**: Create `h` and `y` functions for each
3. **Generate Constraints**: Link witnesses to semantic conditions
4. **Solve**: Z3 finds values for all witnesses simultaneously
5. **Query Model**: Extract witness values for inspection

## Fine Preclusion: A Function-Free Alternative

### The Fine Approach

Fine avoids function quantification entirely by using sets:

A state `e` Fine-precludes `A` when `e = ⊔T` (fusion of set T) where:
1. **Coverage**: Every verifier of A has some part excluded by some member of T
2. **Relevance**: Every member of T excludes some part of some verifier of A

### Implementation in FineUniNegation

```python
class FineUniNegation(Operator):
    name = "\\set_unineg"
    
    def _verifies_fine_preclusion(self, e, S_verifiers, model):
        """Check if e Fine-precludes the set S_verifiers"""
        
        # Try all possible subsets T
        for T_subset in all_subsets_of_states():
            # Check if e is fusion of T
            if fusion_of(T_subset) != e:
                continue
                
            # Check coverage: ∀s∈S ∃t∈T: t excludes part of s
            if not all(
                any(excludes_some_part(t, s) for t in T_subset)
                for s in S_verifiers
            ):
                continue
                
            # Check relevance: ∀t∈T ∃s∈S: t excludes part of s
            if not all(
                any(excludes_some_part(t, s) for s in S_verifiers)
                for t in T_subset
            ):
                continue
                
            return True  # Found valid T
            
        return False
```

### Key Differences

- **No witness functions**: Works directly with state sets
- **Finite search**: Enumerates possible T subsets
- **Set operations**: Uses fusion and part-hood relations only

## Comparing the Approaches

### CB Preclusion (with Witnesses)

**Advantages:**
- More expressive: Can capture function-based relationships
- Inspectable: Witness values visible in model output
- Modular: Each formula has independent witnesses

**Challenges:**
- Complexity: Requires witness infrastructure
- Performance: Additional functions and constraints
- Learning curve: Function quantification concepts

### Fine Preclusion

**Advantages:**
- Simpler: No function quantification
- Direct: Works with finite sets
- Efficient: Potentially faster for small domains

**Challenges:**
- Less expressive: Cannot capture all CB relationships
- Exponential search: Must check all subsets
- Different intuition: Set-based rather than functional

### Logical Relationship

Our tests confirm:
- **CB implies Fine**: Every CB precluder is a Fine precluder
- **Fine does not imply CB**: Some Fine precluders are not CB precluders

This shows CB preclusion is strictly stronger than Fine preclusion.

## Implementation Details

### Witness Architecture Components

1. **WitnessRegistry** (`semantic.py`)
   - Manages witness function declarations
   - Maps formula strings to Z3 functions
   - Ensures unique witnesses per formula

2. **WitnessConstraintGenerator** (`semantic.py`)
   - Creates bidirectional constraints
   - Links witness behavior to verification
   - Handles minimality conditions

3. **WitnessAwareModel** (`semantic.py`)
   - Wraps Z3 model with witness access
   - Provides `get_h_witness()` and `get_y_witness()`
   - Enables witness value inspection

### Example Output

When running examples, witness values appear in the model:

```
Witness Functions for \exclude(A):
  h(□) = □
  h(a) = b
  h(b) = a
  h(a.b) = a.b
  
  y(□) = □
  y(a) = a
  y(b) = b
  y(a.b) = a
```

This shows exactly how each verifier is mapped to its excluding/excluded parts.

## Key Insights

### 1. Witnesses Enable Function Quantification

By pre-declaring witness functions, we transform a difficult quantification problem into a standard constraint satisfaction problem that Z3 handles well.

### 2. Architecture Matters More Than Logic

The witness infrastructure is an *architectural* choice to make function quantification tractable, not a *logical* requirement of CB semantics.

### 3. Different Semantics, Different Techniques

- **CB Preclusion**: Benefits from witness predicates due to function quantification
- **Fine Preclusion**: Works naturally without witnesses due to set-based definition

### 4. Trade-offs Are Context-Dependent

Choose witnesses when:
- You need function-based semantics
- Debugging and inspection are priorities
- Working with complex nested formulas

Choose direct approaches when:
- Semantics are naturally set-based
- Performance is critical
- Simplicity is valued

## Conclusion

Witness predicates provide an elegant solution to implementing CB preclusion semantics in Z3. By making existentially quantified functions explicit in the model structure, they enable complex semantic definitions that would otherwise be intractable. The contrast with Fine's function-free approach illuminates both the power and complexity of function-based semantics in formal logic.
