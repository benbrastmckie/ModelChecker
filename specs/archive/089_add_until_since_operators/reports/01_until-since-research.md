# Research Report: Until and Since Temporal Operators

**Task 89** | Session: sess_1780075673_900b5e | 2026-05-29

## 1. ProofChecker Semantics Analysis

From `Truth.lean` (lines 122-131), the `truth_at` definition specifies Until and Since as primitive constructors:

```lean
| Formula.untl phi psi => exists s : D, t < s ∧ truth_at M Omega tau s phi ∧
    forall r : D, t < r -> r < s -> truth_at M Omega tau r psi
| Formula.snce phi psi => exists s : D, s < t ∧ truth_at M Omega tau s phi ∧
    forall r : D, s < r -> r < t -> truth_at M Omega tau r psi
```

**Burgess Convention** (event, guard): `untl(phi, psi)` means "phi is the event (eventually true), psi is the guard (holds in between)".

**Key semantic properties**:
- **Strict witness**: `t < s` (strictly future) for Until, `s < t` (strictly past) for Since
- **Open guard**: The guard formula psi must hold for all r in the open interval (t, s) for Until, (s, t) for Since
- **Current time excluded**: The guard does NOT need to hold at time t or at the witness time s

This is documented in Truth.lean lines 10-14: "Until uses strict witness (s > t) with open guard (t, s). Since uses strict witness (s < t) with open guard (s, t)."

## 2. Current ModelChecker Analysis

### FutureOperator Pattern (lines 503-648)

The existing `FutureOperator` implements G (all_future) using:

```python
def true_at(self, argument, eval_point):
    future_time = z3.Int('future_true_time')
    return semantics.ForAllTime(
        eval_world,
        future_time,
        z3.Implies(
            eval_time < future_time,  # Strict ordering
            semantics.true_at(argument, {"world": eval_world, "time": future_time})
        )
    )
```

**Key patterns to follow**:
1. Use `semantics.ForAllTime()` and `semantics.ExistsTime()` for bounded quantification
2. Use `z3.Int()` for time variables
3. Pass `eval_point` dict with "world" and "time" keys
4. Handle both `true_at` and `false_at` methods
5. Implement `find_truth_condition` for extension computation

### PastOperator Pattern (lines 651-811)

Mirror of FutureOperator with `past_time < eval_time` instead of `eval_time < future_time`.

## 3. Z3 Encoding Strategy

### UntilOperator.true_at

```python
def true_at(self, event_arg, guard_arg, eval_point):
    """U(event, guard) is true at t iff:
    exists s > t where event(s) AND forall r in (t,s): guard(r)
    """
    semantics = self.semantics
    eval_world = eval_point["world"]
    eval_time = eval_point["time"]
    
    witness_time = z3.Int('until_witness_time')
    guard_time = z3.Int('until_guard_time')
    
    return semantics.ExistsTime(
        eval_world,
        witness_time,
        z3.And(
            # Strict witness: s > t
            eval_time < witness_time,
            # Event holds at witness
            semantics.true_at(event_arg, {"world": eval_world, "time": witness_time}),
            # Guard holds for all r in (t, s)
            semantics.ForAllTime(
                eval_world,
                guard_time,
                z3.Implies(
                    z3.And(eval_time < guard_time, guard_time < witness_time),
                    semantics.true_at(guard_arg, {"world": eval_world, "time": guard_time})
                )
            )
        )
    )
```

### UntilOperator.false_at

```python
def false_at(self, event_arg, guard_arg, eval_point):
    """U(event, guard) is false at t iff:
    forall s > t: either event(s) is false OR exists r in (t,s) where guard(r) is false
    """
    semantics = self.semantics
    eval_world = eval_point["world"]
    eval_time = eval_point["time"]
    
    witness_time = z3.Int('until_false_witness_time')
    guard_time = z3.Int('until_false_guard_time')
    
    return semantics.ForAllTime(
        eval_world,
        witness_time,
        z3.Implies(
            eval_time < witness_time,
            z3.Or(
                # Event fails at potential witness
                semantics.false_at(event_arg, {"world": eval_world, "time": witness_time}),
                # Or guard fails at some intermediate point
                semantics.ExistsTime(
                    eval_world,
                    guard_time,
                    z3.And(
                        eval_time < guard_time,
                        guard_time < witness_time,
                        semantics.false_at(guard_arg, {"world": eval_world, "time": guard_time})
                    )
                )
            )
        )
    )
```

### SinceOperator

Mirror of UntilOperator with reversed time ordering:
- `witness_time < eval_time` (past witness)
- Guard interval: `witness_time < guard_time < eval_time`

## 4. Implementation Recommendations

### File: operators.py

Add two new operator classes after `PastOperator`:

```python
class UntilOperator(syntactic.Operator):
    """Temporal operator U(event, guard): event holds at some future time s > t,
    and guard holds for all times in the open interval (t, s).
    
    Burgess convention: untl(event, guard) - event is what eventually happens,
    guard is what holds until then.
    """
    name = "\\Until"
    arity = 2
    
    # true_at, false_at, find_truth_condition, print_method

class SinceOperator(syntactic.Operator):
    """Temporal operator S(event, guard): event held at some past time s < t,
    and guard held for all times in the open interval (s, t).
    """
    name = "\\Since"
    arity = 2
    
    # true_at, false_at, find_truth_condition, print_method
```

### Registration in bimodal_operators

Add to the `OperatorCollection` at end of file:

```python
bimodal_operators = syntactic.OperatorCollection(
    # ... existing operators ...
    UntilOperator,
    SinceOperator,
    # ... existing defined operators ...
)
```

### find_truth_condition Implementation

For computing extensions, iterate over all times and check the Until/Since condition:

```python
def find_truth_condition(self, event_arg, guard_arg, eval_point):
    """Compute extension for Until operator."""
    model_structure = event_arg.proposition.model_structure
    semantics = model_structure.semantics
    truth_condition = {}
    
    for world_id in event_arg.proposition.extension.keys():
        true_times, false_times = [], []
        start_time, end_time = semantics.world_time_intervals[world_id]
        
        for t in range(start_time, end_time + 1):
            # Check if Until holds at time t
            found_witness = False
            for s in range(t + 1, end_time + 1):  # s > t
                event_holds = s in event_arg.proposition.extension[world_id][0]
                if event_holds:
                    # Check guard for all r in (t, s)
                    guard_ok = all(
                        r in guard_arg.proposition.extension[world_id][0]
                        for r in range(t + 1, s)
                    )
                    if guard_ok:
                        found_witness = True
                        break
            
            if found_witness:
                true_times.append(t)
            else:
                false_times.append(t)
        
        truth_condition[world_id] = (true_times, false_times)
    
    return truth_condition
```

## 5. Test Cases

### Basic Validity Tests

```python
# U(p, top) should be equivalent to F(p) - "p eventually"
# Test: At time 0, with p true only at time 2, U(p, top) should be true

# U(bot, p) should be always false - no witness can satisfy bot
# Test: U(bot, p) should be false at all times

# S(p, top) should be equivalent to P(p) - "p occurred"
# Test: At time 2, with p true only at time 0, S(p, top) should be true
```

### Open Guard Tests

```python
# U(p, q) with q false at current time but true in (t, s) should be true
# This tests that guard is evaluated on open interval excluding t

# Key test: t=0, p true at t=2, q true at t=1, q false at t=0
# U(p, q) should be TRUE at t=0 because guard only needs to hold in (0, 2) = {1}
```

### BX Axiom Tests (Priority)

From Axioms.lean, key axioms to validate:

```python
# BX1: serial_future - top -> F(top)
# BX2G: G(phi -> chi) -> (U(psi, phi) -> U(psi, chi))
# BX3: G(phi -> psi) -> (U(phi, chi) -> U(psi, chi))
# BX5: U(psi, phi) -> U(psi, phi AND U(psi, phi))  # Self-accumulation
# BX6: U(phi AND U(psi, phi), phi) -> U(psi, phi)  # Absorption
```

### Bounded Model Edge Cases

```python
# Test at boundary times (start/end of world interval)
# Test with M=2 (minimal temporal extent)
# Test vacuous truth when no future/past times exist
```

## 6. Risks and Considerations

### Bounded Model Limitations

The ModelChecker uses bounded time intervals (centered around 0, from -M+1 to M-1). This means:
- Until may be vacuously false at the last time point (no future witness possible)
- Since may be vacuously false at the first time point (no past witness possible)
- This is correct semantically but differs from unbounded models

**Mitigation**: Document this behavior; ensure M is sufficient for test formulas.

### Nested Quantifier Performance

Until/Since encoding uses nested quantifiers (ExistsTime containing ForAllTime). This can impact Z3 performance.

**Mitigation**: 
1. Use unique variable names to avoid capture
2. Consider Skolemization if performance issues arise
3. Keep test models small (M=2 or M=3)

### Variable Name Collisions

Each operator invocation should use unique Z3 variable names to prevent collision in nested formulas.

**Recommendation**: Use prefixes like `until_witness_`, `until_guard_`, `since_witness_`, etc.

### Seriality Assumption

The BX axioms assume seriality (every point has a future/past). The ModelChecker's bounded model naturally satisfies this within the interval, but boundary points may not have future/past.

**Consideration**: The frame constraints already include `serial_future` and `serial_past` via the abundance constraint. Verify this covers Until/Since requirements.

## Summary

Implementation requires two new operator classes (`UntilOperator`, `SinceOperator`) following the existing temporal operator pattern. Key design decisions:
1. Strict witness semantics (s > t for Until, s < t for Since)
2. Open guard interval (t, s) for Until, (s, t) for Since
3. Burgess convention: `untl(event, guard)` - event first, guard second
4. Use existing `ForAllTime`/`ExistsTime` utilities for bounded quantification

Estimated implementation effort: 200-300 lines of code in operators.py plus test coverage.
