# Z3 and SMT Solving: Background for Model Checking

## Table of Contents
1. [What is Z3?](#what-is-z3)
2. [SMT Solving Fundamentals](#smt-solving-fundamentals)
3. [Bitvectors in Z3](#bitvectors-in-z3)
4. [Constraint Generation and Solving](#constraint-generation-and-solving)
5. [Model Extraction and Interpretation](#model-extraction-and-interpretation)
6. [Arrays vs Functions in Z3](#arrays-vs-functions-in-z3)
7. [Incremental Solving](#incremental-solving)
8. [Existential Quantification and Skolemization](#existential-quantification-and-skolemization)

## What is Z3?

Z3 is a **Satisfiability Modulo Theories (SMT) solver** developed by Microsoft Research. Unlike traditional SAT solvers that work only with boolean formulas, Z3 can reason about formulas involving:

- **Boolean logic**: AND, OR, NOT, implications
- **Arithmetic**: integers, reals, bitvectors
- **Arrays**: read/write operations on arrays
- **Functions**: uninterpreted functions
- **Quantifiers**: universal and existential quantification

### Key Capabilities

1. **Constraint Satisfaction**: Given a set of constraints, Z3 determines if there exists an assignment of values to variables that satisfies all constraints.

2. **Model Generation**: When constraints are satisfiable, Z3 produces a concrete model - an assignment of values to all variables.

3. **Unsatisfiable Core**: When constraints are unsatisfiable, Z3 can identify a minimal subset of conflicting constraints.

## SMT Solving Fundamentals

### The SMT Problem

<!-- TODO: bad symbols in next line -->
The SMT problem asks: Given a formula � in first-order logic with background theories, is � satisfiable?

```python
# Example: Is there an x where x > 5 AND x < 3?
from z3 import *
x = Int('x')
solver = Solver()
solver.add(x > 5)
solver.add(x < 3)
print(solver.check())  # Output: unsat
```

### Theory Combination

Z3 combines multiple theories using the **Nelson-Oppen** framework:

1. **Theory Solvers**: Each theory (arithmetic, arrays, etc.) has specialized decision procedures
2. **DPLL(T)**: Combines boolean reasoning with theory-specific reasoning
3. **Theory Propagation**: Theories communicate discovered facts to guide search

## Bitvectors in Z3

Bitvectors are fixed-width binary representations crucial for modeling finite domains.

### Why Bitvectors for State Representation?

In the state semantics, we represent states as bitvectors where:
- **Bit position i**: Represents atomic state i
- **Bit value 1**: State i is present in the fusion
- **Bit value 0**: State i is absent from the fusion

```python
# Example: 3-bit bitvector representing state {0, 2}
state = BitVecVal(0b101, 3)  # Binary: 101
# Bit 0 = 1 (present), Bit 1 = 0 (absent), Bit 2 = 1 (present)
```

### Bitvector Operations for Mereology

```python
# Part-of relation: x ⊑ y iff (x & y) == x
def is_part_of(x, y):
    return (x & y) == x

# Fusion: x ⊔ y = x | y
def fusion(x, y):
    return x | y

# Proper part: x ⊏ y iff x ⊑ y AND x ≠ y
def is_proper_part_of(x, y):
    return And(is_part_of(x, y), x != y)
```

### Advantages of Bitvector Encoding

1. **Efficient Mereological Operations**: Part-hood check `x ⊑ y` becomes `(x & y) == x`, which verifies that all bits set to 1 in x are also set to 1 in y
2. **Finite Domain**: Naturally represents finite state spaces
3. **Fast SMT Solving**: Bit-blasting enables efficient SAT reduction

## Constraint Generation and Solving

### The Constraint Generation Process

1. **Syntactic Parsing**: Convert formula strings to AST
2. **Recursive Decomposition**: Break complex formulas into atomic constraints
3. **Theory Translation**: Convert logical operators to Z3 constraints
4. **Primitive Grounding**: Connect to semantic primitives (verify, excludes)

### Example: Constraint Generation for ¬¬A

```python
# Step 1: Parse "¬¬A" into AST
formula = Exclude(Exclude(Atom("A")))

# Step 2: Generate constraints recursively
def generate_constraints(formula, world):
    if isinstance(formula, Atom):
        # Base case: ∃v. verify(v, A) ∧ v ⊑ world
        v = BitVec(f"v_{fresh_id()}", N)
        return Exists([v], And(
            verify(v, formula.letter),
            is_part_of(v, world)
        ))
    elif isinstance(formula, Exclude):
        # Recursive case: Handle exclusion operator
        return generate_exclusion_constraints(formula.argument, world)

# Step 3: Exclusion constraints (three conditions)
def generate_exclusion_constraints(argument, state):
    # Create Skolem functions
    h_sk = Function(f"h_{id}", BitVecSort(N), BitVecSort(N))
    y_sk = Function(f"y_{id}", BitVecSort(N), BitVecSort(N))
    
    # Generate three-condition constraints
    return And(
        condition_1(h_sk, y_sk, argument),
        condition_2(h_sk, state),
        condition_3(h_sk, state)
    )
```

### Constraint Solving Process

1. **Constraint Collection**: Gather all generated constraints
2. **Theory Preprocessing**: Simplify and normalize constraints
3. **Search**: DPLL(T) algorithm explores boolean structure
4. **Theory Checking**: Invoke theory solvers for non-boolean constraints
5. **Model Construction**: Build satisfying assignment if SAT

## Model Extraction and Interpretation

### From Z3 Model to Semantic Structure

When Z3 finds a satisfying assignment, we extract:

1. **Variable Assignments**: Concrete values for all variables
2. **Function Interpretations**: Tables mapping inputs to outputs
3. **Relation Extensions**: Sets of tuples satisfying relations

```python
# After solving
if solver.check() == sat:
    model = solver.model()
    
    # Extract main world value
    main_world_value = model.evaluate(main_world)
    
    # Extract verify relation extension
    verify_extension = {}
    for state in all_states:
        for atom in atoms:
            if is_true(model.evaluate(verify(state, atom))):
                verify_extension.setdefault(atom, set()).add(state)
    
    # Extract exclusion relation
    exclusion_pairs = []
    for s1 in all_states:
        for s2 in all_states:
            if is_true(model.evaluate(excludes(s1, s2))):
                exclusion_pairs.append((s1, s2))
```

### Interpretation Layers

1. **Z3 Level**: Raw satisfying assignment
2. **Semantic Level**: Interpreted relations (verify, excludes, possible)
3. **Model Structure Level**: States, worlds, propositions
4. **Presentation Level**: Human-readable state space visualization

## Arrays vs Functions in Z3

### Functions in Z3

```python
# Uninterpreted function
f = Function('f', IntSort(), IntSort())

# Constraints on f
solver.add(f(0) == 5)
solver.add(f(1) == 7)

# After solving, f is a "black box" - can only query specific values
```

**Limitations**:
- Cannot enumerate all mappings
- Model contains only ground instances
- Inaccessible for universal quantification over domain

### Arrays in Z3

```python
# Array (function with special theory support)
arr = Array('arr', IntSort(), IntSort())

# Constraints using array theory
solver.add(arr[0] == 5)
solver.add(arr[1] == 7)

# Arrays support:
# - Point-wise equality
# - Constant arrays
# - Array updates
# - Quantification over indices
```

**Advantages**:
- First-class model citizens
- Can extract complete interpretation
- Support theory of arrays axioms

### Why Arrays Don't Solve the Two-Phase Problem

Even with arrays, the fundamental issue remains:
1. **Phase 1**: Arrays created and constrained
2. **Phase 2**: Need to know which array corresponds to which formula instance
3. **Context Loss**: No systematic way to preserve formula-array mapping

## Incremental Solving

### Traditional Batch Solving

```python
# All constraints added at once
solver = Solver()
solver.add(all_constraints)
result = solver.check()  # Single solving attempt
```

### Incremental Approach

```python
# Constraints added incrementally
solver = Solver()
for constraint in constraint_generator:
    solver.add(constraint)
    result = solver.check()
    
    if result == unsat:
        # Early termination
        break
    elif result == sat:
        # Extract partial model
        partial_model = solver.model()
        # Use partial results to guide further generation
```

**Benefits**:
1. **Early Conflict Detection**: Stop as soon as unsatisfiability detected
2. **Learned Clauses Reuse**: Solver remembers learned facts
3. **Interactive Refinement**: Adjust strategy based on partial results

### Push/Pop Mechanism

```python
solver = Solver()
solver.add(base_constraints)

# Create backtrack point
solver.push()
solver.add(tentative_constraint)

if solver.check() == unsat:
    # Backtrack
    solver.pop()
    # Try alternative
    solver.add(alternative_constraint)
```

## Existential Quantification and Skolemization

### The Existential Quantification Problem

Consider: ∃h.∀x ∈ Ver(φ): P(h(x), x)

This requires:
1. **Witness Function**: h must map each x to appropriate value
2. **Universal Property**: Constraint must hold for all verifiers
3. **Constructive Content**: Need actual h values, not just existence

### Skolemization Process

```python
# Original existential formula
# ∃h. ∀x. P(h, x)

# Skolemized version
h_sk = Function('h_sk', Domain, Codomain)
# ∀x. P(h_sk, x)

# The problem: h_sk becomes opaque after solving
```

### Why Skolem Functions Cause Issues

1. **Opaque Interpretation**: Z3 models treat Skolem functions as uninterpreted
2. **No Enumeration**: Cannot extract complete function table
3. **Context Sensitivity**: Function interpretation depends on specific constraints

### Alternatives to Standard Skolemization

1. **Explicit Witness Arrays**: Use array theory instead of functions
2. **Finite Domain Expansion**: Enumerate all possible mappings
3. **Incremental Witness Construction**: Build witnesses during solving
4. **Witness Certificates**: Maintain explicit witness-formula mappings

## Summary: Implications for Model Checking

### Two-Phase Limitations

1. **Semantic Gap**: Skolem functions created in Phase 1 are inaccessible in Phase 2
2. **Context Loss**: Formula-constraint mapping lost between phases
3. **Interpretation Opacity**: Cannot reconstruct witness mappings from model

### Single-Phase Advantages

1. **Continuous Access**: Maintain witness information throughout
2. **Incremental Construction**: Build interpretation alongside constraints
3. **Context Preservation**: Formula-witness mapping never lost
4. **Early Feedback**: Detect issues as they arise

This background provides the technical foundation for understanding how the ModelChecker transforms syntactic formulas into semantic models, and why the architectural choice between two-phase and single-phase approaches has profound implications for handling existential quantification in exclusion semantics.
