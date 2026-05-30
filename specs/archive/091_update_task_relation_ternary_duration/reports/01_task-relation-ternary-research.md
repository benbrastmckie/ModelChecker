# Research Report: Update Task Relation to Ternary with Duration Parameter

**Task**: 91
**Status**: RESEARCHED
**Date**: 2026-05-29
**Session**: sess_1748539200_r91z3

## Executive Summary

This research analyzes the refactoring required to update the bimodal task relation from binary `task(w, u)` to ternary `task_rel(w, d, u)` where `d` represents duration. The current ModelChecker implementation only supports unit transitions (+/-1 time shifts), while the ProofChecker (Lean) supports arbitrary duration tasks with the full ternary signature.

## 1. Current Implementation Analysis

### 1.1 Task Relation Definition (semantic.py:153-158)

The current task relation is defined as a binary Z3 function:

```python
self.task = z3.Function(
    "Task",
    self.WorldStateSort,   # source world state
    self.WorldStateSort,   # target world state
    z3.BoolSort()          # boolean result
)
```

**Signature**: `Task: BitVec[N] x BitVec[N] -> Bool`

This binary relation represents that there exists a valid transition between two world states, but does **not** encode the duration of that transition.

### 1.2 Usage Sites in semantic.py

| Line | Context | Usage |
|------|---------|-------|
| 374-379 | `build_frame_constraints()` - lawful constraint | `self.task(state_at_t, state_at_t+1)` |
| 425 | `build_frame_constraints()` - task restriction | `self.task(some_state, next_state)` |
| 997-999 | `inject_z3_model_values()` - model iteration | `self.task(state1, state2)` |

### 1.3 Frame Constraint: Lawful Worlds (lines 356-381)

```python
lawful = z3.ForAll(
    [lawful_world, lawful_time],
    z3.Implies(
        z3.And(
            self.is_world(lawful_world),
            self.is_valid_time(lawful_time, -1),
            self.is_valid_time_for_world(lawful_world, lawful_time),
            self.is_valid_time_for_world(lawful_world, lawful_time + 1),
        ),
        # Current: binary task between consecutive states
        self.task(
            z3.Select(self.world_function(lawful_world), lawful_time),
            z3.Select(self.world_function(lawful_world), lawful_time + 1)
        )
    )
)
```

**Issue**: This constraint only connects consecutive time points (t, t+1), which hardcodes duration=1. With ternary task relation, this would become `task_rel(state_at_t, 1, state_at_t+1)`.

### 1.4 Task Restriction Constraint (lines 417-445)

The task restriction ensures that task relations only hold between states that actually appear in some world history:

```python
task_restriction = z3.ForAll(
    [some_state, next_state],
    z3.Implies(
        self.task(some_state, next_state),
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                self.is_world(task_world),
                # ... time validity checks ...
                some_state == z3.Select(world_function(task_world), time_shifted),
                next_state == z3.Select(world_function(task_world), time_shifted + 1)
            )
        )
    )
)
```

**Issue**: Again hardcodes `time_shifted + 1`, implying unit duration.

## 2. Reference Implementation: Lean ProofChecker

### 2.1 TaskFrame Structure (Frame.lean:68-72)

```lean
structure TaskFrame (S Q : Type*) [CompleteLattice S]
    [AddCommGroup Q] [LinearOrder Q]
    [CovariantClass Q Q (. + .) (. <= .)] where
  /-- The task relation: R(s, q, t) means state s transitions to state t in duration q -/
  taskRel : S -> Q -> S -> Prop
```

**Key Design Decisions**:
1. **State Type S**: Complete lattice (mereological state space)
2. **Quantity Type Q**: Totally ordered commutative group (durations)
3. **Relation Signature**: `S -> Q -> S -> Prop` (ternary)

### 2.2 Duration Semantics

The quantity type Q represents durations with:
- **Addition**: `q + r` (composition of durations)
- **Zero**: `0` (null duration / identity task)
- **Subtraction**: `q - r` (duration difference)
- **Ordering**: `q <= r` (temporal comparison)

### 2.3 Key Frame Axioms

**Compositionality** (Frame.lean:108-114):
```lean
class Compositional ... where
  compose : forall s t r : S, forall x y : Q,
    f.taskRel s x t -> f.taskRel t y r -> f.taskRel s (x + y) r
```

If `s ->_x t` and `t ->_y r`, then `s ->_(x+y) r`.

**State Possibility** (Frame.lean:156-157):
```lean
def StatePossible (f : TaskFrame S Q) (s : S) : Prop :=
  f.taskRel s 0 s
```

A state is possible if it admits a self-task of zero duration.

### 2.4 Evolution Definition (Frame.lean:299-301)

```lean
def IsEvolution (f : TaskFrame S Q) (tau : Q -> S) (X : Set Q) : Prop :=
  Set.OrdConnected X /\
  forall x in X, forall y in X, x <= y -> f.taskRel (tau x) (y - x) (tau y)
```

For any two times x <= y in the domain, the task relation holds with duration `y - x`.

## 3. Semantic Differences

| Aspect | Current (Binary) | Target (Ternary) |
|--------|------------------|------------------|
| Signature | `task(w, u) : Bool` | `task_rel(w, d, u) : Bool` |
| Duration | Implicit (always 1) | Explicit parameter `d` |
| Compositionality | N/A | `task(s,x,t) /\ task(t,y,r) => task(s,x+y,r)` |
| Self-task | N/A | `task(s,0,s)` defines possibility |
| Evolution | Consecutive only | Any duration `y - x` |

## 4. All Usage Sites Requiring Update

### 4.1 Primary Files

| File | Changes Required |
|------|------------------|
| `semantic.py` | Task function definition, frame constraints, injection |
| `operators.py` | No direct task usage (uses world arrays) |
| `iterate.py` | Task relation difference tracking (line 95, 257) |

### 4.2 Detailed Change Map

**semantic.py**:
1. **Line 153-158**: Change task function signature to ternary
2. **Line 374-379**: Update lawful constraint to use duration=1
3. **Line 425**: Update task restriction to include duration
4. **Line 997-999**: Update injection to iterate over durations

**iterate.py**:
1. **Line 95**: Update `task_relations` structure for ternary
2. **Line 257**: Update difference extraction for ternary

### 4.3 Test Files

The following test files reference task relations and may need updates:

- `tests/unit/test_bimodal.py`
- `tests/integration/test_injection.py`
- `tests/integration/test_iterate.py`
- `tests/integration/test_data_extraction.py`

## 5. Proposed Approach

### Phase 1: Update Task Function Signature

```python
# New ternary task relation
self.task_rel = z3.Function(
    "TaskRel",
    self.WorldStateSort,  # source state w
    z3.IntSort(),         # duration d (integer for now, could be Z3 Real)
    self.WorldStateSort,  # target state u
    z3.BoolSort()         # boolean result
)
```

**Duration Type Options**:
- `z3.IntSort()` - Simple, aligns with time being integer
- `z3.RealSort()` - More general, matches Lean's ordered group
- Recommend: Start with `IntSort()` for simplicity

### Phase 2: Update Frame Constraints

**Lawful constraint** with explicit duration:
```python
lawful = z3.ForAll(
    [lawful_world, lawful_time],
    z3.Implies(
        # ... validity conditions ...
        self.task_rel(
            z3.Select(self.world_function(lawful_world), lawful_time),
            z3.IntVal(1),  # explicit unit duration
            z3.Select(self.world_function(lawful_world), lawful_time + 1)
        )
    )
)
```

**Task restriction** with duration:
```python
task_restriction = z3.ForAll(
    [some_state, some_duration, next_state],
    z3.Implies(
        self.task_rel(some_state, some_duration, next_state),
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                # ... validity conditions ...
                some_state == z3.Select(world_function(task_world), time_shifted),
                next_state == z3.Select(world_function(task_world), time_shifted + some_duration)
            )
        )
    )
)
```

### Phase 3: Add Compositionality Axiom (Optional)

```python
# Compositionality: task(s,x,t) /\ task(t,y,r) => task(s,x+y,r)
compose_s = z3.BitVec('compose_s', self.N)
compose_t = z3.BitVec('compose_t', self.N)
compose_r = z3.BitVec('compose_r', self.N)
compose_x = z3.Int('compose_x')
compose_y = z3.Int('compose_y')

compositionality = z3.ForAll(
    [compose_s, compose_t, compose_r, compose_x, compose_y],
    z3.Implies(
        z3.And(
            self.task_rel(compose_s, compose_x, compose_t),
            self.task_rel(compose_t, compose_y, compose_r)
        ),
        self.task_rel(compose_s, compose_x + compose_y, compose_r)
    )
)
```

### Phase 4: Update Model Injection

```python
# Inject task relation constraints for each state pair and duration
for state1 in range(num_states):
    for state2 in range(num_states):
        for duration in range(-self.M + 1, self.M):  # All possible durations
            task_val = z3_model.eval(
                original_semantics.task_rel(state1, duration, state2),
                model_completion=True
            )
            if is_true(task_val):
                model_constraints.all_constraints.append(
                    self.task_rel(state1, duration, state2)
                )
            else:
                model_constraints.all_constraints.append(
                    z3.Not(self.task_rel(state1, duration, state2))
                )
```

**Performance Note**: This expands the state space significantly. Consider limiting duration range or using lazy enumeration.

### Phase 5: Backward Compatibility

Keep the old `task` function as a convenience wrapper:
```python
def task(self, w, u):
    """Backward-compatible binary task (duration=1)."""
    return self.task_rel(w, z3.IntVal(1), u)
```

## 6. Potential Risks and Complications

### 6.1 Performance Impact

The ternary relation increases constraint space:
- Binary: O(N^2) constraints (where N = 2^state_bits)
- Ternary: O(N^2 * D) constraints (where D = duration range)

**Mitigation**: Limit duration range based on world interval size (typically M values).

### 6.2 Quantifier Complexity

Adding duration quantification may stress Z3's quantifier handling:
```python
z3.ForAll([some_state, some_duration, next_state], ...)
```

**Mitigation**: Use bounded quantification over duration range.

### 6.3 Model Extraction Complexity

Extracting ternary relations from Z3 models requires iterating over durations:
- Current: Iterate state pairs (N^2)
- New: Iterate state pairs * durations (N^2 * D)

**Mitigation**: Only extract task relations for durations that appear in world histories.

### 6.4 Test Coverage

Current tests assume binary task relation. All bimodal tests need review:
- Unit tests in `tests/unit/test_bimodal.py`
- Integration tests in `tests/integration/`
- E2E tests that exercise bimodal theory

### 6.5 Downstream Dependency: Task 92

Task 92 ("Add frame constraints for bimodal task relation") depends on this task and adds:
- `nullity_identity`: `task_rel(w, 0, u) <-> w = u`
- `forward_comp`: compositionality for non-negative durations
- `converse`: `task_rel(w, d, u) <-> task_rel(u, -d, w)`

These axioms assume the ternary signature is in place.

## 7. Implementation Order

1. **Define new task_rel function** (ternary signature)
2. **Update lawful constraint** (use explicit duration=1)
3. **Update task restriction** (add duration parameter)
4. **Add backward-compatible wrapper** (keep `task()` working)
5. **Update model injection** (iterate over durations)
6. **Update iterate.py** (ternary difference tracking)
7. **Run existing tests** (verify backward compatibility)
8. **Add new tests** (test duration parameter explicitly)

## 8. References

- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 153-158, 356-381, 417-445)
- `Logos/Theory/Logos/Foundations/Constitutive/Frame.lean` (full TaskFrame structure)
- Task 92 description (downstream frame constraints)

## 9. Conclusion

The refactoring from binary `task(w, u)` to ternary `task_rel(w, d, u)` is well-defined and follows the Lean ProofChecker's design. The main challenges are:

1. **Constraint space expansion** - mitigated by bounded duration ranges
2. **Quantifier complexity** - mitigated by bounded quantification
3. **Test updates** - straightforward with backward-compatible wrapper

The change is foundational for task 92's frame constraints and aligns the ModelChecker with the ProofChecker's semantics.
