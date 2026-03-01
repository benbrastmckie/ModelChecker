# Semantic Evaluation Patterns

Truthmaker semantic evaluation patterns used in the ModelChecker framework.

## Core Concept: Truthmaker Semantics

Truthmaker semantics evaluates sentences not just as true/false, but with explicit **verifiers** and **falsifiers** - states that make sentences true or false.

```
Traditional: sentence S is true in world w
Truthmaker:  state s VERIFIES sentence S
             state s FALSIFIES sentence S
```

## Bilateral Evaluation

The framework uses bilateral semantics with both verification and falsification:

```python
def verify(self, state, sentence):
    """Check if state verifies sentence."""
    # Returns Z3 boolean constraint
    pass

def falsify(self, state, sentence):
    """Check if state falsifies sentence."""
    # Returns Z3 boolean constraint
    pass
```

## State Representation

States are represented as Z3 BitVectors:

```python
import z3
from model_checker.utils import bitvec_to_substates

# N is the number of atomic states
N = 16
state = z3.BitVec('s', N)

# Convert to set of atomic states
substates = bitvec_to_substates(state, N)
# e.g., BitVec 5 (binary 0101) -> {0, 2}
```

## Part-Whole Structure

States have mereological (part-whole) structure:

```python
def is_part_of(s1, s2):
    """Check if s1 is a part of s2."""
    return s1 & s2 == s1  # Bitwise containment

def fusion(s1, s2):
    """Compute fusion (mereological sum) of states."""
    return s1 | s2  # Bitwise union
```

## Verification Patterns

### Atomic Propositions

```python
def verify_atom(self, state, letter):
    """State verifies atomic proposition."""
    # Each atom has a designated verifier set
    verifiers = self.get_verifiers(letter)
    return state in verifiers
```

### Negation (Bilateral)

```python
def verify_negation(self, state, sentence):
    """State verifies NOT(sentence) iff it falsifies sentence."""
    return self.falsify(state, sentence.argument)

def falsify_negation(self, state, sentence):
    """State falsifies NOT(sentence) iff it verifies sentence."""
    return self.verify(state, sentence.argument)
```

### Conjunction (Exact)

```python
def verify_conjunction(self, state, sentence):
    """State verifies A AND B iff state is fusion of verifiers."""
    # state = s1 fusion s2 where s1 verifies A and s2 verifies B
    s1 = z3.BitVec('s1', N)
    s2 = z3.BitVec('s2', N)
    return z3.Exists([s1, s2],
        z3.And(
            state == (s1 | s2),
            self.verify(s1, sentence.left),
            self.verify(s2, sentence.right)
        )
    )
```

### Disjunction (Either Verifier)

```python
def verify_disjunction(self, state, sentence):
    """State verifies A OR B iff state verifies A or state verifies B."""
    return z3.Or(
        self.verify(state, sentence.left),
        self.verify(state, sentence.right)
    )
```

## Z3 Constraint Patterns

### ForAll with Implication

```python
from model_checker.utils import ForAll

# "All verifiers of A are parts of state s"
ForAll([x], z3.Implies(
    self.verify(x, sentence),
    is_part_of(x, s)
))
```

### Exists with Conjunction

```python
from model_checker.utils import Exists

# "There exists a verifier of A that is part of state s"
Exists([x], z3.And(
    self.verify(x, sentence),
    is_part_of(x, s)
))
```

## Modal Evaluation

Modal operators evaluate across possible worlds:

```python
def verify_necessity(self, state, world, sentence):
    """State verifies NECESSARILY(sentence) at world."""
    # Verify at all accessible worlds
    return ForAll([w], z3.Implies(
        self.accessible(world, w),
        Exists([s], z3.And(
            is_part_of(s, state),
            self.verify(s, w, sentence)
        ))
    ))
```

## Counterfactual Evaluation

Counterfactuals use closest-world semantics:

```python
def verify_counterfactual(self, state, world, antecedent, consequent):
    """State verifies 'if A were the case, B would be'."""
    # In closest A-worlds, B holds
    return ForAll([w], z3.Implies(
        self.closest_where_true(w, world, antecedent),
        self.verify(state, w, consequent)
    ))
```

## Constraint Generation Flow

1. Parse sentence into AST
2. Recursively generate Z3 constraints
3. Combine constraints with model constraints
4. Send to solver

```python
def evaluate(self, sentence, settings):
    """Full evaluation pipeline."""
    # 1. Build model constraints
    model = self.build_model(settings)

    # 2. Generate sentence constraints
    constraints = self.generate_constraints(sentence, model)

    # 3. Create solver and add constraints
    solver = z3.Solver()
    solver.add(model.constraints)
    solver.add(constraints)

    # 4. Check satisfiability
    result = solver.check()
    if result == z3.sat:
        return solver.model()
    return None
```

## Performance Patterns

### Simplification

```python
from z3 import simplify

# Simplify complex constraints before solving
constraint = simplify(complex_constraint)
```

### Timeout Handling

```python
solver = z3.Solver()
solver.set('timeout', settings['max_time'] * 1000)  # milliseconds
result = solver.check()
if result == z3.unknown:
    # Timeout occurred
    pass
```

### Incremental Solving

```python
solver = z3.Solver()
solver.push()  # Save state
solver.add(constraint1)
result1 = solver.check()
solver.pop()   # Restore state
solver.add(constraint2)
result2 = solver.check()
```
