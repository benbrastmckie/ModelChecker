# Z3 Python API Reference

Core Z3 SMT solver API patterns for Python.

## Installation

```bash
pip install z3-solver
```

## Import

```python
import z3
from z3 import (
    Bool, Int, Real, BitVec, Array,
    And, Or, Not, Implies, Xor,
    ForAll, Exists,
    Solver, sat, unsat, unknown,
    simplify,
)
```

## Core Types

### Boolean

```python
# Boolean variables
a = z3.Bool('a')
b = z3.Bool('b')

# Boolean constants
true = z3.BoolVal(True)
false = z3.BoolVal(False)

# Operations
z3.And(a, b)
z3.Or(a, b)
z3.Not(a)
z3.Implies(a, b)
z3.Xor(a, b)
z3.If(a, b, c)  # if-then-else
```

### Integers

```python
x = z3.Int('x')
y = z3.Int('y')

# Operations
x + y
x - y
x * y
x / y  # integer division
x % y  # modulo

# Comparisons
x == y
x < y
x <= y
x > y
x >= y
```

### Reals

```python
r = z3.Real('r')
s = z3.Real('s')

# Real from int
z3.RealVal(3)
z3.RealVal('3.14')

# Operations same as Int
r + s
r * s
r / s  # true division
```

### BitVectors

Most important for ModelChecker (state representation):

```python
# Create bitvector with N bits
bv = z3.BitVec('bv', 16)

# Bitvector from integer
z3.BitVecVal(5, 16)  # 5 as 16-bit bitvector

# Bit operations
bv1 & bv2   # bitwise AND
bv1 | bv2   # bitwise OR
bv1 ^ bv2   # bitwise XOR
~bv1        # bitwise NOT

# Shifts
bv << n     # left shift
bv >> n     # logical right shift
z3.LShR(bv, n)  # explicit logical right shift

# Arithmetic (treats as unsigned)
bv1 + bv2
bv1 - bv2
bv1 * bv2

# Extraction
z3.Extract(high, low, bv)  # extract bits [high:low]

# Concatenation
z3.Concat(bv1, bv2)
```

### Arrays

```python
# Array from sort to sort
arr = z3.Array('arr', z3.IntSort(), z3.IntSort())

# Operations
z3.Select(arr, index)  # read
z3.Store(arr, index, value)  # write (returns new array)
```

## Quantifiers

### ForAll

```python
x = z3.Int('x')

# For all x: if x > 0 then x >= 1
constraint = z3.ForAll([x], z3.Implies(x > 0, x >= 1))

# Multiple variables
y = z3.Int('y')
z3.ForAll([x, y], body)

# With patterns (for efficiency)
z3.ForAll([x], body, patterns=[x + 1])
```

### Exists

```python
# There exists x such that x > 0
constraint = z3.Exists([x], x > 0)

# Nested quantifiers
z3.ForAll([x], z3.Exists([y], x < y))
```

## Solver

### Basic Usage

```python
solver = z3.Solver()

# Add constraints
solver.add(x > 0)
solver.add(y > x)

# Check satisfiability
result = solver.check()
if result == z3.sat:
    model = solver.model()
    print(model[x])  # Get value of x
elif result == z3.unsat:
    print("No solution")
else:  # z3.unknown
    print("Timeout or unknown")
```

### Configuration

```python
# Timeout in milliseconds
solver.set('timeout', 10000)

# Other options
solver.set('unsat_core', True)
```

### Incremental Solving

```python
solver = z3.Solver()
solver.add(base_constraints)

# Save state
solver.push()

# Add temporary constraints
solver.add(temp_constraint)
result1 = solver.check()

# Restore state
solver.pop()

# Try different constraint
solver.add(other_constraint)
result2 = solver.check()
```

### Assumptions

```python
# Check with temporary assumptions
result = solver.check([assumption1, assumption2])

# Get unsat core if unsat
if result == z3.unsat:
    core = solver.unsat_core()
```

## Model Extraction

```python
if solver.check() == z3.sat:
    model = solver.model()

    # Get value of variable
    val = model[x]

    # Evaluate expression
    result = model.eval(x + y)

    # Iterate declarations
    for decl in model.decls():
        print(f"{decl.name()} = {model[decl]}")
```

## Simplification

```python
# Simplify expression
simplified = z3.simplify(complex_expr)

# With options
z3.simplify(expr, som=True)  # sum of monomials
z3.simplify(expr, sort_sums=True)
```

## Tactics

```python
# Create tactic
tactic = z3.Tactic('simplify')

# Apply to goal
goal = z3.Goal()
goal.add(constraints)
result = tactic(goal)

# Common tactics
z3.Tactic('simplify')
z3.Tactic('solve-eqs')
z3.Tactic('bit-blast')
z3.Tactic('qe')  # quantifier elimination
```

## Combinators

```python
# Sequential application
t1 = z3.Tactic('simplify')
t2 = z3.Tactic('solve-eqs')
combined = z3.Then(t1, t2)

# Parallel (try both, use first to succeed)
z3.OrElse(t1, t2)

# Repeat until fixpoint
z3.Repeat(tactic)
```

## Utility Functions

```python
# Check if expression is satisfiable
z3.is_true(expr)
z3.is_false(expr)

# Sort checking
z3.is_bool(expr)
z3.is_int(expr)
z3.is_bv(expr)

# Create fresh variable
fresh = z3.FreshConst(z3.IntSort())
```

## Common Patterns

### Bounded Quantification

```python
# Instead of ForAll with range, enumerate
z3.And([constraint(i) for i in range(N)])
```

### Cardinality Constraints

```python
# At most k of bools are true
from z3 import AtMost, AtLeast, PbEq, PbLe, PbGe

bools = [z3.Bool(f'b{i}') for i in range(10)]
z3.AtMost(*bools, k)
z3.AtLeast(*bools, k)
z3.PbEq([(b, 1) for b in bools], k)  # exactly k
```

### If-Then-Else

```python
result = z3.If(condition, then_value, else_value)
```

## Error Handling

```python
try:
    result = solver.check()
except z3.Z3Exception as e:
    print(f"Z3 error: {e}")
```

## Version Check

```python
import z3
print(z3.get_version())
# Returns tuple: (major, minor, build, revision)
```
