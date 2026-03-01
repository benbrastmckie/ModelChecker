# BitVector Operations

BitVec patterns for state representation in the ModelChecker framework.

## Overview

ModelChecker represents states as Z3 BitVectors where:
- N bits = N atomic states
- Bit i set = atomic state i is part of the state
- Part-whole relations map to bitwise operations

## Core Concepts

### State Space

```python
N = 16  # Configurable, typically 8, 16, or 32

# Full state (all atomic states)
FULL = (1 << N) - 1  # 0xFFFF for N=16

# Null state (no atomic states)
NULL = 0

# Number of possible states
total_states = 1 << N  # 2^N = 65536 for N=16
```

### Creating BitVectors

```python
import z3

# Z3 variable
state = z3.BitVec('state', N)

# From integer
concrete = z3.BitVecVal(5, N)  # Binary: ...0101

# Named states
verifier = z3.BitVec('verifier_A', N)
falsifier = z3.BitVec('falsifier_A', N)
```

## Part-Whole Operations

### Containment (Part-of)

```python
def is_part(s1, s2):
    """s1 is part of s2."""
    # s1 is contained in s2 if their AND equals s1
    return (s1 & s2) == s1

# Examples:
# 0101 is part of 0111 (true: 0101 & 0111 = 0101)
# 0101 is part of 0100 (false: 0101 & 0100 = 0100)
```

### Proper Part

```python
def proper_part(s1, s2):
    """s1 is a proper part of s2 (contained but smaller)."""
    return z3.And(is_part(s1, s2), s1 != s2)
```

### Fusion (Sum)

```python
def fusion(s1, s2):
    """Mereological sum of s1 and s2."""
    return s1 | s2

# Example: fusion(0101, 0011) = 0111
```

### Overlap

```python
def overlap(s1, s2):
    """s1 and s2 share at least one common part."""
    return (s1 & s2) != 0

def disjoint(s1, s2):
    """s1 and s2 share no common part."""
    return (s1 & s2) == 0
```

### Difference

```python
def difference(s1, s2):
    """Parts of s1 that are not parts of s2."""
    return s1 & ~s2

# Example: difference(0111, 0011) = 0100
```

### Intersection

```python
def intersection(s1, s2):
    """Common parts of s1 and s2."""
    return s1 & s2

# Example: intersection(0111, 0011) = 0011
```

## Utility Functions

### bitvec_to_substates

From `model_checker.utils`:

```python
from model_checker.utils import bitvec_to_substates

def bitvec_to_substates(bitvec_val, N):
    """Convert integer/BitVec to set of atomic state indices."""
    if hasattr(bitvec_val, 'as_long'):
        bitvec_val = bitvec_val.as_long()

    substates = set()
    for i in range(N):
        if bitvec_val & (1 << i):
            substates.add(i)
    return substates

# Example: bitvec_to_substates(5, 4) -> {0, 2}  (binary 0101)
```

### int_to_binary

```python
from model_checker.utils import int_to_binary

def int_to_binary(n, width):
    """Convert integer to binary string with fixed width."""
    return format(n, f'0{width}b')

# Example: int_to_binary(5, 8) -> "00000101"
```

### pretty_set_print

```python
from model_checker.utils import pretty_set_print

def pretty_set_print(state_set):
    """Format set of states for display."""
    if not state_set:
        return "{}"
    return "{" + ", ".join(str(s) for s in sorted(state_set)) + "}"

# Example: pretty_set_print({0, 2, 5}) -> "{0, 2, 5}"
```

## Constraint Patterns

### Non-Empty States

```python
# State must have at least one atomic part
non_empty = state != 0

# State must have at least k parts
# (popcount >= k, approximated with constraints)
```

### Covering

```python
def covers(s1, s2):
    """s1 completely covers s2 (s2 is part of s1)."""
    return is_part(s2, s1)
```

### Exact Size

```python
def has_exactly_n_parts(state, n, N):
    """State has exactly n atomic parts."""
    # Create boolean for each bit
    bits = [z3.Extract(i, i, state) == 1 for i in range(N)]
    # Use PbEq for pseudo-boolean equality
    return z3.PbEq([(b, 1) for b in bits], n)
```

### At Least / At Most

```python
def has_at_least_n_parts(state, n, N):
    """State has at least n atomic parts."""
    bits = [z3.Extract(i, i, state) == 1 for i in range(N)]
    return z3.PbGe([(b, 1) for b in bits], n)

def has_at_most_n_parts(state, n, N):
    """State has at most n atomic parts."""
    bits = [z3.Extract(i, i, state) == 1 for i in range(N)]
    return z3.PbLe([(b, 1) for b in bits], n)
```

## Iteration Patterns

### Enumerate All States

```python
def enumerate_states(N):
    """Generator for all possible states."""
    for i in range(1 << N):
        yield i
```

### Enumerate Non-Empty States

```python
def enumerate_nonempty_states(N):
    """Generator for all non-empty states."""
    for i in range(1, 1 << N):
        yield i
```

### Enumerate Parts

```python
def enumerate_parts(state_val, N):
    """Generator for all parts of a given state."""
    for i in range(1 << N):
        if (i & state_val) == i and i != 0:
            yield i
```

## Model Extraction

```python
def extract_state_value(model, bitvec_var):
    """Extract concrete state value from Z3 model."""
    val = model[bitvec_var]
    if val is None:
        return None
    return val.as_long()

def format_state(state_val, N):
    """Format state value for display."""
    substates = bitvec_to_substates(state_val, N)
    binary = int_to_binary(state_val, N)
    return f"{substates} (binary: {binary})"
```

## Common Operations Matrix

| Operation | Python | Z3 | Description |
|-----------|--------|-----|-------------|
| Union | `\|` | `\|` | Mereological sum |
| Intersection | `&` | `&` | Common parts |
| Difference | `& ~` | `& ~` | Parts not in other |
| Part-of | `(a & b) == a` | Same | Containment check |
| Overlap | `(a & b) != 0` | Same | Share parts? |
| Disjoint | `(a & b) == 0` | Same | No shared parts? |
| Complement | `~a & FULL` | Same | All except a |
| Empty check | `a == 0` | Same | Null state? |
| Full check | `a == FULL` | Same | Full state? |

## Performance Considerations

### Small N for Testing

```python
# Use small N (4-8) for unit tests
# Use larger N (16-32) for realistic examples
TEST_N = 4
PROD_N = 16
```

### Avoid Expensive Operations

```python
# Counting bits is expensive in Z3
# Use constraints instead of computing popcount

# Instead of: popcount(state) == k
# Use: PbEq constraint (more efficient)
```

### Cache State Conversions

```python
# For repeated conversions, cache results
_state_cache = {}

def cached_substates(val, N):
    key = (val, N)
    if key not in _state_cache:
        _state_cache[key] = bitvec_to_substates(val, N)
    return _state_cache[key]
```
