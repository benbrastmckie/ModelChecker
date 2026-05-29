# Research Report: Clean-Break Refactoring to Ternary Task Relation

**Task**: 91  
**Status**: RESEARCHED  
**Date**: 2026-05-29  
**Session**: sess_1748539800_r91cb  
**Round**: 2 (Follow-up to backward-compatible approach)

## Executive Summary

This research report provides a clean-break design for refactoring the task relation from binary `task(w, u)` to ternary `task_rel(w, d, u)`. Unlike the previous backward-compatible approach (Report 01), this design completely removes the old binary signature and restructures the codebase for long-term quality, following the Lean ProofChecker's semantics exactly.

## 1. Design Rationale

### 1.1 Why Clean-Break Over Backward Compatibility

The user explicitly requested a clean-break approach with no backward compatibility wrappers. This is the correct choice for several reasons:

1. **Semantic Clarity**: The binary relation `task(w, u)` implicitly assumes duration=1, which is semantically misleading. The ternary relation makes duration explicit.

2. **Alignment with ProofChecker**: The Lean ProofChecker uses ternary `taskRel : S -> Q -> S -> Prop` (Frame.lean:72). Matching this exactly eliminates semantic drift between implementations.

3. **No Technical Debt**: Wrapper functions add complexity and hide the true API. Removing them entirely creates a cleaner architecture.

4. **Test Clarity**: Tests written against the new API directly verify the correct semantics rather than testing through compatibility layers.

### 1.2 Key Design Principles

| Principle | Application |
|-----------|-------------|
| **Single Source of Truth** | One task relation signature: `task_rel(w, d, u)` |
| **Explicit over Implicit** | Duration is always explicit, never defaulted |
| **ProofChecker Alignment** | Match Lean naming and semantics exactly |
| **Fail-Fast** | Remove deprecated code paths entirely |

## 2. API Design

### 2.1 New Task Relation Signature

```python
# semantic.py: Define ternary task relation
self.task_rel = z3.Function(
    "TaskRel",
    self.WorldStateSort,  # source state w : BitVec[N]
    z3.IntSort(),         # duration d : Int
    self.WorldStateSort,  # target state u : BitVec[N]
    z3.BoolSort()         # result : Bool
)
```

**Signature**: `TaskRel : BitVec[N] x Int x BitVec[N] -> Bool`

**Naming Convention**: Use `task_rel` (snake_case) in Python to match the `taskRel` (camelCase) in Lean, following each language's conventions while maintaining semantic correspondence.

### 2.2 Duration Type Analysis

| Option | Pros | Cons | Decision |
|--------|------|------|----------|
| `z3.IntSort()` | Simple, matches time type | Limited to integers | **Selected** |
| `z3.RealSort()` | More general (matches Q in Lean) | More complex constraints | Not needed currently |

**Rationale**: The ModelChecker uses integer time points (`self.TimeSort = z3.IntSort()`), so integer durations are the natural choice. This can be generalized later if needed.

### 2.3 Complete Primitive Removal

Remove the old binary `task` function entirely:

```python
# REMOVE from define_primitives():
# self.task = z3.Function("Task", self.WorldStateSort, self.WorldStateSort, z3.BoolSort())
```

## 3. Frame Constraint Refactoring

### 3.1 Lawful Constraint (Consecutive States)

**Current** (lines 356-381):
```python
self.task(
    z3.Select(self.world_function(lawful_world), lawful_time),
    z3.Select(self.world_function(lawful_world), lawful_time + 1)
)
```

**Clean-Break**:
```python
self.task_rel(
    z3.Select(self.world_function(lawful_world), lawful_time),
    z3.IntVal(1),  # explicit unit duration
    z3.Select(self.world_function(lawful_world), lawful_time + 1)
)
```

### 3.2 Task Restriction Constraint

**Current** (lines 417-445):
```python
task_restriction = z3.ForAll(
    [some_state, next_state],
    z3.Implies(
        self.task(some_state, next_state),
        z3.Exists(...)
    )
)
```

**Clean-Break**:
```python
# Add duration variable
some_duration = z3.Int('task_restrict_duration')

task_restriction = z3.ForAll(
    [some_state, some_duration, next_state],
    z3.Implies(
        self.task_rel(some_state, some_duration, next_state),
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                self.is_world(task_world),
                # Duration bounds: must fit within time domain
                some_duration > -2 * self.M,
                some_duration < 2 * self.M,
                # Time validity for both endpoints
                self.is_valid_time(time_shifted),
                self.is_valid_time(time_shifted + some_duration),
                # Time in world bounds
                self.is_valid_time_for_world(task_world, time_shifted),
                self.is_valid_time_for_world(task_world, time_shifted + some_duration),
                # State matching
                some_state == z3.Select(self.world_function(task_world), time_shifted),
                next_state == z3.Select(self.world_function(task_world), time_shifted + some_duration)
            )
        )
    )
)
```

### 3.3 Duration-Generalized Lawful Constraint (Optional Enhancement)

For full alignment with the ProofChecker's `IsEvolution` definition (Frame.lean:299-301):

```python
def build_evolution_constraint(self):
    """For any two times x <= y in a world, task_rel(tau(x), y-x, tau(y)) holds."""
    evo_world = z3.Int('evo_world')
    evo_time_x = z3.Int('evo_time_x')
    evo_time_y = z3.Int('evo_time_y')
    
    return z3.ForAll(
        [evo_world, evo_time_x, evo_time_y],
        z3.Implies(
            z3.And(
                self.is_world(evo_world),
                self.is_valid_time_for_world(evo_world, evo_time_x),
                self.is_valid_time_for_world(evo_world, evo_time_y),
                evo_time_x <= evo_time_y
            ),
            self.task_rel(
                z3.Select(self.world_function(evo_world), evo_time_x),
                evo_time_y - evo_time_x,  # duration = y - x
                z3.Select(self.world_function(evo_world), evo_time_y)
            )
        )
    )
```

**Note**: This is a stronger constraint than the consecutive-only version. Consider whether to include it in this task or defer to Task 92.

## 4. Model Injection Refactoring

### 4.1 Current Implementation (lines 990-999)

```python
for state1 in range(num_states):
    for state2 in range(num_states):
        task_val = z3_model.eval(original_semantics.task(state1, state2), ...)
```

### 4.2 Clean-Break Implementation

```python
def inject_z3_model_values(self, z3_model, original_semantics, model_constraints):
    """Inject task relation constraints with explicit duration enumeration."""
    num_states = 2 ** model_constraints.settings['N']
    
    # Duration range based on time domain
    # For M time points, durations range from -(M-1) to (M-1)
    M = model_constraints.settings['M']
    duration_range = range(-M + 1, M)
    
    # Inject task_rel constraints
    for state1 in range(num_states):
        for duration in duration_range:
            for state2 in range(num_states):
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

### 4.3 Performance Considerations

**Constraint Count**:
- Old: O(N^2) where N = 2^bits (state count)
- New: O(N^2 * D) where D = 2*M - 1 (duration count)

**Mitigation**: For typical values (N=4 states, M=2 times, D=3 durations):
- Old: 16 constraints
- New: 48 constraints (3x increase, still manageable)

## 5. Iterate Module Refactoring

### 5.1 Current Implementation (lines 217-257)

```python
if hasattr(semantics, 'task'):
    for state1 in all_states:
        for state2 in all_states:
            old_value = previous_model.eval(semantics.task(state1, state2), ...)
            new_value = new_model.eval(semantics.task(state1, state2), ...)
```

### 5.2 Clean-Break Implementation

```python
def _calculate_bimodal_differences(self, new_structure, previous_structure):
    """Compare task_rel with explicit duration."""
    # ... existing code ...
    
    # 3. Compare task relations with duration parameter
    if hasattr(semantics, 'task_rel'):
        task_diffs = {}
        M = new_structure.semantics.M
        duration_range = range(-M + 1, M)
        
        for state1 in all_states:
            for duration in duration_range:
                for state2 in all_states:
                    try:
                        old_value = bool(previous_model.eval(
                            semantics.task_rel(state1, duration, state2),
                            model_completion=True
                        ))
                        new_value = bool(new_model.eval(
                            semantics.task_rel(state1, duration, state2),
                            model_completion=True
                        ))
                        
                        if old_value != new_value:
                            key = f"{state1}--[{duration}]-->{state2}"
                            task_diffs[key] = {"old": old_value, "new": new_value}
                    except Exception:
                        pass
        
        if task_diffs:
            differences["task_relations"] = task_diffs
```

### 5.3 Difference Printing Update

```python
# In print_model_differences (lines 433-437)
if 'task_relations' in differences and differences['task_relations']:
    print("\nTask Relation Changes:", file=output)
    for transition, change in differences['task_relations'].items():
        # transition format: "state1--[duration]-->state2"
        old_value = change.get('old', False)
        new_value = change.get('new', False)
        status = "added" if new_value and not old_value else "removed"
        print(f"  Task {transition}: {status}", file=output)
```

## 6. Test Restructuring

### 6.1 Files Requiring Updates

| File | Changes Required |
|------|-----------------|
| `tests/integration/test_injection.py` | Update `test_inject_task_constraints` |
| `tests/unit/test_bimodal.py` | Update any task relation tests |
| `tests/e2e/*.py` | Review bimodal test cases |

### 6.2 Updated Test Example

```python
# test_injection.py (lines 88-119)
def test_inject_task_constraints(self):
    """Test injection handles ternary task relations with duration."""
    # Verify new API
    self.assertTrue(hasattr(self.semantics, 'task_rel'))
    self.assertFalse(hasattr(self.semantics, 'task'))  # Old API removed
    
    # Create solver with ternary task constraints
    solver = z3.Solver()
    
    # Set task relations with explicit durations
    solver.add(self.semantics.task_rel(0, 1, 1))  # state 0 -> state 1 in duration 1
    solver.add(z3.Not(self.semantics.task_rel(0, 1, 2)))  # NOT state 0 -> state 2 in duration 1
    solver.add(self.semantics.task_rel(1, 1, 2))  # state 1 -> state 2 in duration 1
    solver.add(self.semantics.task_rel(0, 2, 2))  # state 0 -> state 2 in duration 2 (composition)
    
    # ... rest of test ...
    
    # Verify constraint count: 4 states * 3 durations * 4 states = 48
    task_constraints = [c for c in constraints if 'TaskRel(' in str(c)]
    expected_count = 4 * 3 * 4  # states * durations * states
    self.assertEqual(len(task_constraints), expected_count)
```

## 7. Documentation Strategy

### 7.1 Code Documentation

**Docstring Updates**:

```python
def define_primitives(self):
    """Define Z3 primitives for bimodal logic.
    
    Primitives:
    - task_rel: Ternary relation R(s, d, u) where:
        - s: source world state (BitVec[N])
        - d: duration of task (Int)
        - u: target world state (BitVec[N])
      Represents: "state s transitions to state u over duration d"
      
      ProofChecker Alignment: Matches taskRel : S -> Q -> S -> Prop
      from Frame.lean:72. The quantity type Q is represented as Int.
    
    - world_function: Maps world IDs to world histories (time -> state arrays)
    - truth_condition: Assigns truth values to atoms at world states
    - is_world: Validates world IDs
    """
```

### 7.2 Migration Notes

Add a note at the top of semantic.py:

```python
"""Bimodal Logic Semantics

Migration Note (Task 91, 2026-05-29):
  The task relation has been refactored from binary task(w, u) to 
  ternary task_rel(w, d, u) where d is the explicit duration parameter.
  
  This aligns with the Lean ProofChecker's taskRel : S -> Q -> S -> Prop.
  All code using the old binary task() function must be updated to use
  task_rel() with an explicit duration argument.
  
  See: specs/091_update_task_relation_ternary_duration/reports/02_clean-break-research.md
"""
```

## 8. Code Organization Recommendations

### 8.1 Suggested File Structure

No new files needed. Changes are contained within existing modules:

```
code/src/model_checker/theory_lib/bimodal/
  semantic.py      # task_rel definition, frame constraints
  iterate.py       # difference tracking with duration
  operators.py     # No changes needed (uses world arrays, not task directly)
```

### 8.2 Refactoring Opportunities

1. **Extract Duration Constants**: Define `MIN_DURATION` and `MAX_DURATION` based on M

2. **Duration Validation Helper**:
```python
def is_valid_duration(self, duration):
    """Check if duration is within valid range."""
    return z3.And(duration > -self.M, duration < self.M)
```

3. **Task Relation Builder**:
```python
def build_task_rel_at(self, world, time, duration):
    """Build task_rel constraint at specific world and time."""
    return self.task_rel(
        z3.Select(self.world_function(world), time),
        duration,
        z3.Select(self.world_function(world), time + duration)
    )
```

## 9. Migration Checklist

### Phase 1: Core Changes
- [ ] Remove `self.task` from `define_primitives()`
- [ ] Add `self.task_rel` with ternary signature
- [ ] Update lawful constraint to use `task_rel(..., 1, ...)`
- [ ] Update task restriction constraint with duration variable

### Phase 2: Supporting Code
- [ ] Update `inject_z3_model_values()` to enumerate durations
- [ ] Update `iterate.py` difference tracking for ternary
- [ ] Update `print_model_differences()` for new format

### Phase 3: Tests
- [ ] Update `test_inject_task_constraints`
- [ ] Run full bimodal test suite
- [ ] Add new tests for duration-specific behavior

### Phase 4: Documentation
- [ ] Add migration note to semantic.py
- [ ] Update docstrings for task_rel
- [ ] Update any external documentation

## 10. Relationship to Task 92

Task 92 ("Add frame constraints for bimodal task relation") will add additional axioms:

| Axiom | Definition | Depends on Task 91 |
|-------|------------|-------------------|
| `nullity_identity` | `task_rel(w, 0, u) <-> w = u` | Yes - requires ternary signature |
| `forward_comp` | Compositionality for d >= 0 | Yes - requires duration parameter |
| `converse` | `task_rel(w, d, u) <-> task_rel(u, -d, w)` | Yes - requires signed duration |

**Recommendation**: Complete Task 91 fully before starting Task 92. The ternary signature is a prerequisite for all Task 92 axioms.

## 11. References

### Codebase
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (lines 153-158, 356-381, 417-445, 990-999)
- `code/src/model_checker/theory_lib/bimodal/iterate.py` (lines 217-257)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py` (lines 88-119)

### Lean ProofChecker
- `Logos/Theory/Logos/Foundations/Constitutive/Frame.lean` (lines 68-72, 108-114, 299-301)

### External Resources
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html)
- [Z3 API in Python](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)

## 12. Conclusion

The clean-break approach provides a cleaner, more maintainable codebase that exactly matches the Lean ProofChecker's semantics. The key changes are:

1. **Remove** the binary `task(w, u)` function entirely
2. **Add** the ternary `task_rel(w, d, u)` function with explicit duration
3. **Update** all usage sites to pass explicit duration (typically `1` for consecutive states)
4. **Extend** iteration to enumerate over the duration dimension
5. **Align** naming and semantics with the ProofChecker's `taskRel`

The implementation is straightforward with no compatibility layers to maintain. The constraint count increase (3x for typical parameters) is acceptable and can be optimized if needed by lazy enumeration.
