# Research Report: ISemantics Protocol Refactoring

## Summary

The codebase contains three vestigial `ISemantics`/`Semantics` Protocol definitions that are:
1. Never actually used for type checking
2. Underspecified relative to actual usage
3. Causing pyright to complain since the concrete types (`SemanticDefaults`, `LogosSemantics`) do not match the minimal Protocol definitions

This report analyzes the current state and recommends replacing `ISemantics` with concrete types in the Operator base class.

## Current State Analysis

### Protocol Definitions Found

| Location | Protocol Name | Methods Defined |
|----------|--------------|-----------------|
| `syntactic/types.py:17` | `ISemantics` | `evaluate(*args) -> BoolRef` |
| `models/types.py:44` | `ISemantics` | `generate_constraints()`, `true_at()`, `false_at()` |
| `theory_lib/types.py:42` | `Semantics` | `evaluate()`, `generate_constraints()` |
| `theory_lib/logos/protocols.py:154` | `SemanticsProtocol` | Full specification with 10+ methods |

**Key observation**: Only `SemanticsProtocol` in `logos/protocols.py` is properly specified. The other three are vestigial minimal definitions that do not match actual usage patterns.

### Operator Base Class Current Definition

```python
# syntactic/operators.py:51
def __init__(self, semantics: ISemantics) -> None:
```

The `ISemantics` imported from `syntactic/types.py` only defines `evaluate(*args) -> BoolRef`, but operators actually access many more methods:

### Methods Actually Used by Operators

From analyzing all operator files, the following `self.semantics` attributes are accessed:

**From SemanticDefaults (base class)**:
- `N` - bit width
- `null_state` - BitVecVal(0, N)
- `all_states` - list of all states
- `fusion(bit_s, bit_t)` - bitwise OR
- `is_part_of(bit_s, bit_t)` - part-whole relation
- `product(set_A, set_B)` - pairwise fusion
- `coproduct(set_A, set_B)` - union closed under fusion

**From LogosSemantics (Logos-specific)**:
- `true_at(sentence, eval_point)` - truth at evaluation point
- `false_at(sentence, eval_point)` - falsity at evaluation point
- `extended_verify(state, sentence, eval_point)` - verification
- `extended_falsify(state, sentence, eval_point)` - falsification
- `is_world(state)` - world predicate
- `with_world(eval_point, world)` - new eval point with world
- `is_alternative(u, y, w)` - counterfactual alternatives
- `get_assignment(eval_point)` - first-order assignment
- `with_assignment(eval_point, assignment)` - new eval point with assignment

## Design Alternatives Analysis

### Option A: Replace ISemantics with SemanticDefaults

**Approach**: Use concrete `SemanticDefaults` type in `Operator.__init__`

```python
from model_checker.models.semantic import SemanticDefaults

class Operator:
    def __init__(self, semantics: SemanticDefaults) -> None:
        self.semantics = semantics
```

**Pros**:
- Simple, direct solution
- No circular import issues (SemanticDefaults is in models, Operator is in syntactic)
- Handles all non-Logos theories

**Cons**:
- Pyright will still complain when Logos operators access LogosSemantics-specific methods
- Does not capture the narrower type for Logos operators

### Option B: Class-level annotation to narrow the type

**Approach**: Keep `SemanticDefaults` in base `Operator`, but add class-level annotation in Logos operators

```python
# In each Logos subtheory operator file
from model_checker.theory_lib.logos.semantic import LogosSemantics

class NecessityOperator(syntactic.Operator):
    semantics: LogosSemantics  # Type narrowing annotation
    name = "\\Box"
    arity = 1
```

**Pros**:
- Each operator class documents its semantic requirements
- Pyright sees the correct type
- No changes to base class needed beyond Option A

**Cons**:
- Repetitive: must add annotation to every Logos operator class
- 20+ operator classes need modification

### Option C: LogosOperator base class

**Approach**: Create a `LogosOperator` subclass that narrows the type

```python
# theory_lib/logos/operators.py or base.py
from model_checker.syntactic import Operator
from .semantic import LogosSemantics

class LogosOperator(Operator):
    """Base class for Logos theory operators with narrowed semantics type."""
    semantics: LogosSemantics
```

Then all Logos operators inherit from `LogosOperator`:

```python
class NecessityOperator(LogosOperator):
    name = "\\Box"
    arity = 1
```

**Pros**:
- Single point of type narrowing
- Clear inheritance hierarchy
- Documents the theory-operator relationship

**Cons**:
- Breaking change: all Logos operators must change their base class
- Adds an inheritance layer
- Need to update ~25 operator class definitions

### Option D: Expand ISemantics Protocol

**Approach**: Expand the minimal `ISemantics` Protocol to include all needed methods

**Assessment**: NOT RECOMMENDED. This would:
- Create a massive Protocol with 20+ methods
- Still not capture the semantic differences between theories
- Protocol definitions are hard to maintain
- Runtime checking (`@runtime_checkable`) has overhead

### Option E: TYPE_CHECKING conditional imports

**Approach**: Use `TYPE_CHECKING` to import `LogosSemantics` only for type hints

```python
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from model_checker.theory_lib.logos.semantic import LogosSemantics

class NecessityOperator(syntactic.Operator):
    semantics: "LogosSemantics"
```

**Pros**:
- No runtime import overhead
- Type checker sees correct types

**Cons**:
- Still repetitive across 20+ classes
- String annotations are less IDE-friendly

## Recommended Approach

**Recommendation: Option A + Option B (Hybrid)**

1. **Replace `ISemantics` with `SemanticDefaults`** in the base `Operator` class
2. **Add class-level `semantics: LogosSemantics` annotations** only where pyright complains
3. **Delete the three vestigial Protocol definitions**
4. **Keep `SemanticsProtocol`** in `logos/protocols.py` as documentation

### Rationale

This approach is elegant because:

1. **Minimal changes**: Only modify base class once, then add annotations only where needed
2. **No circular imports**: `SemanticDefaults` is in `models/`, `Operator` is in `syntactic/`
3. **Incremental**: Can add LogosSemantics annotations one-by-one as pyright complains
4. **Explicit**: Each operator that needs LogosSemantics documents that requirement
5. **No new classes**: Avoids the complexity of a LogosOperator base class

### Import Pattern

The cleanest import pattern for LogosSemantics in operator files:

```python
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from model_checker.theory_lib.logos.semantic import LogosSemantics

class MyOperator(syntactic.Operator):
    semantics: "LogosSemantics"  # Type narrowing for pyright

    def true_at(self, argument, eval_point):
        sem = self.semantics  # pyright now knows this is LogosSemantics
        return sem.true_at(argument, eval_point)
```

This pattern:
- Avoids runtime imports of LogosSemantics in operator files
- Gives pyright full type information
- Does not affect runtime behavior

## Impact Assessment

### Files Requiring Changes

**Phase 1: Base class and cleanup (4 files)**
1. `syntactic/operators.py` - Change `ISemantics` to `SemanticDefaults`
2. `syntactic/types.py` - Remove `ISemantics` Protocol definition
3. `models/types.py` - Remove `ISemantics` Protocol definition
4. `theory_lib/types.py` - Remove `Semantics` Protocol definition

**Phase 2: Type annotations (operator files with pyright errors)**
Likely 5-10 operator files will need `semantics: LogosSemantics` annotations:
- `subtheories/modal/operators.py` (uses `is_world`, `with_world`)
- `subtheories/counterfactual/operators.py` (uses `is_alternative`)
- `subtheories/first-order/operators.py` (uses `get_assignment`, `with_assignment`)
- Others as pyright identifies them

### Circular Import Analysis

**No circular import risk**:
- `syntactic/operators.py` imports `SemanticDefaults` from `models/semantic.py`
- `models/semantic.py` does NOT import from `syntactic/` (verified by inspection)
- `LogosSemantics` is only imported under `TYPE_CHECKING` in operator files

### Runtime Behavior

**No runtime changes**: All changes are type annotations only. The actual semantics objects passed at runtime are already `LogosSemantics` instances.

## Implementation Checklist

### Phase 1: Core Changes
- [ ] Edit `syntactic/operators.py`: Change import and parameter type to `SemanticDefaults`
- [ ] Edit `syntactic/operators.py`: Add `SemanticDefaults` import from `model_checker.models.semantic`
- [ ] Delete `ISemantics` class from `syntactic/types.py`
- [ ] Delete `ISemantics` class from `models/types.py`
- [ ] Delete `Semantics` class from `theory_lib/types.py`
- [ ] Run pyright to identify remaining type errors

### Phase 2: Type Narrowing
- [ ] Add `TYPE_CHECKING` import block to operator files with errors
- [ ] Add `semantics: "LogosSemantics"` class annotation where needed
- [ ] Verify pyright is satisfied

### Phase 3: Verification
- [ ] Run full test suite: `pytest code/`
- [ ] Run pyright: `pyright code/src/model_checker/`
- [ ] Verify no runtime regressions

## Files to Preserve

Keep the following as documentation:
- `theory_lib/logos/protocols.py` - Contains well-specified `SemanticsProtocol`
- `models/semantic.py` - Contains `SemanticDefaults` concrete class
- `theory_lib/logos/semantic.py` - Contains `LogosSemantics` concrete class
