# Constraint Generation Patterns

Z3 constraint building patterns used in the ModelChecker framework.

## Overview

ModelChecker generates Z3 constraints for truthmaker semantic evaluation. Constraints encode:
- Model structure (states, part-whole relations)
- Verification conditions (what makes sentences true/false)
- Example-specific requirements (contingency, non-emptiness)

## Constraint Architecture

```
Sentence → Parse → AST → Constraint Generator → Z3 Constraints → Solver
                              ↓
                       Model Constraints
                              ↓
                       Result / Countermodel
```

## Model Constraints

### State Space

```python
import z3

N = 16  # Number of atomic states
full_state = (1 << N) - 1  # All bits set

# State variable
state = z3.BitVec('state', N)

# Non-null constraint (state is not null/0)
non_null = state != 0

# Full state constraint
is_full = state == full_state
```

### Part-Whole Relations

```python
def is_part(s1, s2):
    """s1 is a part of s2 (mereological containment)."""
    return (s1 & s2) == s1

def proper_part(s1, s2):
    """s1 is a proper part of s2 (contained but not equal)."""
    return z3.And(is_part(s1, s2), s1 != s2)

def fusion(s1, s2):
    """Mereological sum of s1 and s2."""
    return s1 | s2

def overlap(s1, s2):
    """s1 and s2 share a common part."""
    return (s1 & s2) != 0

def disjoint(s1, s2):
    """s1 and s2 share no common part."""
    return (s1 & s2) == 0
```

### Example Settings Constraints

```python
def build_settings_constraints(settings, verifier, falsifier):
    """Build constraints from example settings."""
    constraints = []

    if settings.get('non_empty', True):
        # Verifier must be non-empty
        constraints.append(verifier != 0)

    if settings.get('non_null', True):
        # Falsifier must be non-null
        constraints.append(falsifier != 0)

    if settings.get('disjoint', True):
        # Verifier and falsifier must not overlap
        constraints.append(disjoint(verifier, falsifier))

    if settings.get('contingent', True):
        # Both verifier and falsifier must exist
        constraints.append(z3.And(verifier != 0, falsifier != 0))

    return z3.And(constraints) if constraints else z3.BoolVal(True)
```

## Sentence Constraints

### Atomic Propositions

```python
def atomic_constraint(letter, state, verifiers, falsifiers):
    """Constraint for atomic proposition at state."""
    # verifiers[letter] and falsifiers[letter] are Z3 BitVec variables
    v = verifiers[letter]
    f = falsifiers[letter]

    # State verifies if it equals the verifier
    verify = state == v

    # State falsifies if it equals the falsifier
    falsify = state == f

    return verify, falsify
```

### Negation

```python
def negation_constraint(inner_verify, inner_falsify):
    """NOT swaps verification and falsification."""
    return inner_falsify, inner_verify
```

### Conjunction (Exact)

```python
def conjunction_constraint(left_verify, right_verify, state, N):
    """AND: state = fusion of left verifier and right verifier."""
    s1 = z3.BitVec('conj_s1', N)
    s2 = z3.BitVec('conj_s2', N)

    verify = z3.Exists([s1, s2], z3.And(
        state == (s1 | s2),
        left_verify(s1),
        right_verify(s2)
    ))
    return verify
```

### Disjunction

```python
def disjunction_constraint(left_verify, right_verify, state):
    """OR: state verifies either disjunct."""
    return z3.Or(left_verify(state), right_verify(state))
```

### Implication

```python
def implication_constraint(antecedent_verify, consequent_verify, state, N):
    """A implies B: verify B wherever A is verified."""
    from model_checker.utils import ForAll

    x = z3.BitVec('impl_x', N)
    verify = ForAll([x], z3.Implies(
        z3.And(is_part(x, state), antecedent_verify(x)),
        z3.Exists([y := z3.BitVec('impl_y', N)], z3.And(
            is_part(y, state),
            consequent_verify(y)
        ))
    ))
    return verify
```

## Quantifier Patterns

### Universal (ForAll)

```python
from model_checker.utils import ForAll

# All parts of state s satisfy property P
x = z3.BitVec('x', N)
constraint = ForAll([x], z3.Implies(is_part(x, s), property(x)))
```

### Existential (Exists)

```python
from model_checker.utils import Exists

# Some part of state s satisfies property P
x = z3.BitVec('x', N)
constraint = Exists([x], z3.And(is_part(x, s), property(x)))
```

### Bounded Quantification

For finite domains, enumerate instead:

```python
# Instead of ForAll over all possible states
# Use explicit enumeration for small N
constraints = [property(i) for i in range(1 << N)]
z3.And(constraints)
```

## Modal Constraints

### Accessibility Relation

```python
# Accessibility function: world -> set of accessible worlds
accessible = z3.Function('R', z3.IntSort(), z3.IntSort(), z3.BoolSort())

# R(w1, w2) means w2 is accessible from w1
def accessible_from(w1, w2):
    return accessible(w1, w2)
```

### Necessity

```python
def necessity_constraint(inner_verify, state, world, worlds, accessible):
    """NECESSARILY(A): A holds at all accessible worlds."""
    from model_checker.utils import ForAll

    w = z3.Int('modal_w')
    return ForAll([w], z3.Implies(
        z3.And(w >= 0, w < worlds, accessible(world, w)),
        inner_verify(state, w)
    ))
```

### Possibility

```python
def possibility_constraint(inner_verify, state, world, worlds, accessible):
    """POSSIBLY(A): A holds at some accessible world."""
    from model_checker.utils import Exists

    w = z3.Int('modal_w')
    return Exists([w], z3.And(
        w >= 0, w < worlds,
        accessible(world, w),
        inner_verify(state, w)
    ))
```

## Solver Integration

### Building the Solver

```python
def build_solver(model_constraints, sentence_constraints, settings):
    """Create solver with all constraints."""
    solver = z3.Solver()

    # Set timeout
    timeout_ms = settings.get('max_time', 10) * 1000
    solver.set('timeout', timeout_ms)

    # Add model structure constraints
    solver.add(model_constraints)

    # Add sentence-specific constraints
    solver.add(sentence_constraints)

    return solver
```

### Checking and Extracting

```python
def check_validity(solver):
    """Check and extract result."""
    result = solver.check()

    if result == z3.sat:
        model = solver.model()
        return True, extract_countermodel(model)
    elif result == z3.unsat:
        return False, None
    else:
        return None, "timeout or unknown"
```

### Model Extraction

```python
def extract_countermodel(model):
    """Extract human-readable countermodel from Z3 model."""
    from model_checker.utils import bitvec_to_substates

    result = {}
    for decl in model.decls():
        name = decl.name()
        value = model[decl]

        if z3.is_bv(value):
            # Convert bitvector to state set
            int_val = value.as_long()
            result[name] = bitvec_to_substates(int_val, N)
        else:
            result[name] = value

    return result
```

## Performance Tips

### Simplify Before Solving

```python
from z3 import simplify

constraint = simplify(complex_constraint)
solver.add(constraint)
```

### Minimize Quantifiers

```python
# Avoid nested quantifiers when possible
# Use concrete enumeration for small domains
# Add patterns to help instantiation
z3.ForAll([x], body, patterns=[trigger_pattern])
```

### Incremental Solving

```python
solver = z3.Solver()
solver.add(base_constraints)

for test in tests:
    solver.push()
    solver.add(test_constraint)
    result = solver.check()
    solver.pop()
```
