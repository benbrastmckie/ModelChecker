# Z3 and SMT Solver Background

[← Back to Docs](../README.md) | [Methodology →](../architecture/README.md) | [Hyperintensional →](HYPERINTENSIONAL.md)

## Table of Contents
1. [Introduction to SMT Solvers](#introduction-to-smt-solvers)
2. [What is Z3?](#what-is-z3)
3. [Core Concepts](#core-concepts)
4. [Z3 in Python](#z3-in-python)
5. [Quantifiers in Z3](#quantifiers-in-z3)
6. [Functions vs Predicates](#functions-vs-predicates)
7. [Common Patterns](#common-patterns)
8. [Performance Considerations](#performance-considerations)

## Introduction to SMT Solvers

### What is an SMT Solver?

SMT stands for **Satisfiability Modulo Theories**. An SMT solver is a program that determines whether a set of logical formulas can be satisfied (made true) under certain mathematical theories.

Think of it as asking: "Is there a way to assign values to variables such that all these conditions are true?"

### Example Problem

```python
# Can we find integers x and y such that:
# - x > 0
# - y > 0  
# - x + y = 10
# - x * y = 24

# Answer: Yes! x = 4, y = 6 (or x = 6, y = 4)
```

## What is Z3?

Z3 is a high-performance SMT solver developed by Microsoft Research. It can work with:
- **Boolean logic**: AND, OR, NOT
- **Integer/Real arithmetic**: +, -, *, <, >
- **Bit-vectors**: Fixed-width integers (like computer integers)
- **Arrays**: Mappings from indices to values
- **Uninterpreted functions**: Abstract functions with properties

## Core Concepts

### 1. Variables and Sorts

In Z3, every variable has a **sort** (type):

```python
import z3

# Boolean variable
p = z3.Bool('p')

# Integer variable  
x = z3.Int('x')

# Bit-vector (4-bit integer)
bv = z3.BitVec('bv', 4)
```

### 2. Constraints

Constraints are conditions that must be satisfied:

```python
# Create solver
solver = z3.Solver()

# Add constraints
solver.add(x > 0)
solver.add(x < 10)
solver.add(x * x == 16)

# Check if satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    print(f"x = {model[x]}")  # x = 4
```

### 3. Models

A **model** is an assignment of values to variables that satisfies all constraints:

```python
# The model tells us what values make our constraints true
model = solver.model()
for var in model:
    print(f"{var} = {model[var]}")
```

## Z3 in Python

### Basic Workflow

```python
import z3

# 1. Create variables
x, y = z3.Ints('x y')

# 2. Create solver
solver = z3.Solver()

# 3. Add constraints
solver.add(x + y == 10)
solver.add(x > y)
solver.add(y > 0)

# 4. Check satisfiability
result = solver.check()

# 5. Extract model if SAT
if result == z3.sat:
    model = solver.model()
    print(f"x = {model[x]}, y = {model[y]}")
else:
    print("No solution exists")
```

### Constraint Types

```python
# Arithmetic
solver.add(x + y > 10)
solver.add(x * 2 == y)

# Boolean
p, q = z3.Bools('p q')
solver.add(z3.Or(p, q))
solver.add(z3.Implies(p, q))

# Bit-vector
bv1 = z3.BitVec('bv1', 8)
solver.add(bv1 & 0xFF == 0x42)
```

## Quantifiers in Z3

### Universal Quantifier (ForAll)

"For all values of x, property P holds":

```python
x = z3.Int('x')
# ForAll x: x * 0 == 0
constraint = z3.ForAll([x], x * 0 == 0)
```

### Existential Quantifier (Exists)

"There exists a value of x such that property P holds":

```python
x = z3.Int('x')
# Exists x: x * x == 4
constraint = z3.Exists([x], x * x == 4)
```

### Nested Quantifiers

```python
x, y = z3.Ints('x y')
# ForAll x: Exists y: x + y == 0
# (Every number has an additive inverse)
constraint = z3.ForAll([x], z3.Exists([y], x + y == 0))
```

## Functions vs Predicates

### Uninterpreted Functions

Functions that map inputs to outputs without specifying the mapping:

```python
# Declare a function from Int to Int
f = z3.Function('f', z3.IntSort(), z3.IntSort())

x = z3.Int('x')
solver = z3.Solver()

# We can constrain properties of f
solver.add(f(0) == 5)
solver.add(f(1) == 7)
solver.add(z3.ForAll([x], f(x) >= 0))  # f is non-negative
```

### Predicates (Boolean Functions)

Functions that return boolean values:

```python
# Predicate: is_even(x)
is_even = z3.Function('is_even', z3.IntSort(), z3.BoolSort())

x = z3.Int('x')
# Define is_even for some values
solver.add(is_even(0) == True)
solver.add(is_even(1) == False)
solver.add(is_even(2) == True)
```

### Skolem Functions

When eliminating existential quantifiers, Z3 introduces **Skolem functions**:

```python
# Original: Exists y: P(x, y)
# Skolemized: P(x, sk(x)) where sk is a new function

# This happens automatically in Z3 during solving
```

## Common Patterns

### 1. Finding Counter-examples

```python
# To prove P implies Q, we look for a counter-example where P is true but Q is false
solver = z3.Solver()
solver.add(P)
solver.add(z3.Not(Q))

if solver.check() == z3.sat:
    print("Found counter-example!")
    print(solver.model())
else:
    print("P implies Q is valid")
```

### 2. Encoding Finite Domains

```python
# Represent finite sets using bit-vectors
N = 3  # 3 bits = 8 possible states
state = z3.BitVec('state', N)

# state can be 0, 1, 2, ..., 7
# Each bit represents membership in a subset
```

### 3. Defining Relations

```python
# Binary relation using a function to Bool
N = 4
rel = z3.Function('rel', z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())

x, y = z3.BitVecs('x y', N)

# Make relation symmetric
solver.add(z3.ForAll([x, y], rel(x, y) == rel(y, x)))
```

## Performance Considerations

### 1. Quantifier Alternation

Formulas with alternating quantifiers are harder to solve:
- Easy: `ForAll x: P(x)`
- Harder: `ForAll x: Exists y: P(x, y)`
- Very hard: `ForAll x: Exists y: ForAll z: P(x, y, z)`

### 2. Finite vs Infinite Domains

- **Finite domains** (like bit-vectors) allow Z3 to enumerate possibilities
- **Infinite domains** (like integers) require more sophisticated techniques

### 3. Incremental Solving

```python
solver = z3.Solver()
solver.push()  # Save state
solver.add(constraint1)
result1 = solver.check()

solver.pop()   # Restore state
solver.push()
solver.add(constraint2)
result2 = solver.check()
```

### 4. Tactics and Simplification

```python
# Use tactics to preprocess formulas
tactic = z3.Tactic('simplify')
simplified = tactic(formula)[0]

# Combine tactics
combined = z3.Then('simplify', 'solve-eqs', 'bit-blast')
```

## Key Takeaways

1. **Z3 is declarative**: You specify *what* constraints must hold, not *how* to find solutions
2. **Models provide witnesses**: When SAT, the model gives concrete values
3. **Quantifiers add complexity**: Each quantifier alternation increases difficulty
4. **Functions are first-class**: Can constrain properties without defining the function
5. **Finite domains help**: Bit-vectors enable efficient reasoning about finite sets

## Further Reading

- [Z3 Tutorial](https://rise4fun.com/z3/tutorial)
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- [SMT-LIB Standard](http://smtlib.cs.uiowa.edu/)
- [SAT/SMT by Example](https://sat-smt.codes/)

## Application to Exclusion Semantics

In the ModelChecker's exclusion theory, we use Z3 to implement two types of unilateral negation:

1. **Function-based negation** (`\neg`): Uses witness functions h and y (Champollion-Bernard semantics)
2. **Set-based negation** (`\set_neg`): Uses set operations without functions (Fine semantics)

The challenge of implementing `\neg` motivated the witness predicate architecture described in the exclusion theory documentation.

---

[← Back to Docs](../README.md) | [Methodology →](../architecture/README.md) | [Hyperintensional →](HYPERINTENSIONAL.md)
