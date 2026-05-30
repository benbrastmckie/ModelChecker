# Research Report: Frame Constraints for Bimodal Task Relation

**Task**: 92  
**Status**: RESEARCHED  
**Date**: 2026-05-29  
**Session**: sess_1780081196_94be8be05c90  
**Round**: 1

## Executive Summary

This research report analyzes the implementation of three frame constraints for the bimodal task relation in Z3/Python:

1. **nullity_identity**: `task_rel(w, 0, u) <-> w = u`
2. **forward_comp** (Compositionality): If `task_rel(w, d1, v)` and `task_rel(v, d2, u)` then `task_rel(w, d1+d2, u)`
3. **converse**: `task_rel(w, d, u) <-> task_rel(u, -d, w)`

The constraints align with the Lean ProofChecker's `TaskFrame` structure (Frame.lean:68-114) and the `Compositional` typeclass. This report provides detailed Z3 encodings, analyzes constraint interactions, and identifies performance considerations.

## 1. ProofChecker Reference Analysis

### 1.1 Lean Definitions

From `/home/benjamin/Projects/Logos/Theory/Logos/Foundations/Constitutive/Frame.lean`:

```lean
-- TaskFrame structure (lines 68-72)
structure TaskFrame (S Q : Type*) [CompleteLattice S]
    [AddCommGroup Q] [LinearOrder Q]
    [CovariantClass Q Q (. + .) (. <= .)] where
  taskRel : S -> Q -> S -> Prop

-- Compositional typeclass (lines 108-114)
class Compositional {S Q : Type*} [CompleteLattice S]
    [AddCommGroup Q] [LinearOrder Q]
    [CovariantClass Q Q (. + .) (. <= .)]
    (f : TaskFrame S Q) where
  compose : forall s t r : S, forall x y : Q,
    f.taskRel s x t -> f.taskRel t y r -> f.taskRel s (x + y) r
```

### 1.2 Constraint Mapping

| Lean Concept | Python Constraint | Description |
|--------------|------------------|-------------|
| `taskRel s 0 s` | `nullity_identity` | Zero duration implies identity |
| `Compositional.compose` | `forward_comp` | Sequential tasks compose |
| Group converse | `converse` | Time reversal symmetry |

## 2. Z3 Encoding Details

### 2.1 nullity_identity Constraint

**Mathematical Definition**:
```
ForAll w, u : task_rel(w, 0, u) <-> w = u
```

**Z3 Encoding**:
```python
def build_nullity_identity_constraint(self):
    """Build constraint: task_rel(w, 0, u) <-> w = u
    
    Zero duration task implies and is implied by state identity.
    This is a bidirectional constraint using Z3's == for Bool equivalence.
    
    ProofChecker Alignment: Corresponds to the property that self-tasks
    (tasks of zero duration) relate a state to itself.
    """
    w = z3.BitVec('nullity_w', self.N)
    u = z3.BitVec('nullity_u', self.N)
    
    return z3.ForAll(
        [w, u],
        # Biconditional: (task_rel(w, 0, u)) <-> (w == u)
        # In Z3, we express A <-> B as A == B for Boolean expressions
        self.task_rel(w, z3.IntVal(0), u) == (w == u)
    )
```

**Key Points**:
- Uses Z3's `==` operator for Boolean equivalence (semantically identical to `Iff`)
- No validity guards needed since this applies to all state pairs
- Duration is explicitly `z3.IntVal(0)` for clarity

### 2.2 forward_comp (Compositionality) Constraint

**Mathematical Definition**:
```
ForAll w, v, u, d1, d2 :
  (task_rel(w, d1, v) AND task_rel(v, d2, u)) -> task_rel(w, d1+d2, u)
```

**Z3 Encoding**:
```python
def build_forward_comp_constraint(self):
    """Build compositionality constraint for sequential tasks.
    
    If task_rel(w, d1, v) and task_rel(v, d2, u) then task_rel(w, d1+d2, u).
    Sequential tasks compose: the composition of two tasks is a task
    whose duration is the sum of the component durations.
    
    ProofChecker Alignment: Matches Compositional.compose from Frame.lean:112-114.
    """
    w = z3.BitVec('comp_w', self.N)
    v = z3.BitVec('comp_v', self.N)
    u = z3.BitVec('comp_u', self.N)
    d1 = z3.Int('comp_d1')
    d2 = z3.Int('comp_d2')
    
    return z3.ForAll(
        [w, v, u, d1, d2],
        z3.Implies(
            z3.And(
                # Premise: both component tasks exist
                self.task_rel(w, d1, v),
                self.task_rel(v, d2, u),
                # Duration validity (optional guard for efficiency)
                self.is_valid_duration(d1),
                self.is_valid_duration(d2),
                self.is_valid_duration(d1 + d2)
            ),
            # Conclusion: composed task exists
            self.task_rel(w, d1 + d2, u)
        )
    )
```

**Key Points**:
- Five quantified variables: 3 states (w, v, u) and 2 durations (d1, d2)
- Duration validity guards are optional but improve solver efficiency
- This is a one-directional implication (existence of composition)

### 2.3 converse Constraint

**Mathematical Definition**:
```
ForAll w, u, d : task_rel(w, d, u) <-> task_rel(u, -d, w)
```

**Z3 Encoding**:
```python
def build_converse_constraint(self):
    """Build time reversal symmetry constraint.
    
    task_rel(w, d, u) <-> task_rel(u, -d, w)
    Going from w to u in duration d is equivalent to going from u to w
    in duration -d (time reversal).
    
    ProofChecker Alignment: Corresponds to the group converse property
    of the additive group structure on durations (Q in Lean).
    """
    w = z3.BitVec('converse_w', self.N)
    u = z3.BitVec('converse_u', self.N)
    d = z3.Int('converse_d')
    
    return z3.ForAll(
        [w, u, d],
        z3.Implies(
            # Guard: duration and its negation must be valid
            z3.And(
                self.is_valid_duration(d),
                self.is_valid_duration(-d)
            ),
            # Biconditional under the guard
            self.task_rel(w, d, u) == self.task_rel(u, -d, w)
        )
    )
```

**Key Points**:
- Uses biconditional (`==`) since symmetry is bidirectional
- Duration validity guard ensures both `d` and `-d` are within bounds
- This creates a strong constraint that may interact with other axioms

## 3. Interaction with Existing Constraints

### 3.1 Existing Constraints in semantic.py

| Constraint | Location | Purpose |
|------------|----------|---------|
| `lawful` | lines 421-449 | Consecutive states have task_rel with duration=1 |
| `task_restriction` | lines 484-520 | task_rel only holds between states in lawful world histories |
| `is_valid_duration()` | line 236-251 | Duration bounds: `d > -M and d < M` |

### 3.2 Interaction Analysis

#### 3.2.1 nullity_identity + lawful

**Interaction**: Compatible and complementary.
- `lawful` establishes `task_rel(s, 1, s')` for consecutive states
- `nullity_identity` establishes `task_rel(s, 0, s) <-> true`
- No conflict: they address different duration values

**Derived Property**: Combined with lawful, we get:
- `task_rel(s, 0, s)` holds for any state `s` (self-task)
- `task_rel(s, 1, s')` holds for consecutive states in world histories

#### 3.2.2 forward_comp + lawful

**Interaction**: Creates derivable task relations.
- From `lawful`: `task_rel(s0, 1, s1)` and `task_rel(s1, 1, s2)`
- From `forward_comp`: `task_rel(s0, 2, s2)` is derived

**Implication**: This means task_rel becomes populated with non-unit durations through inference. The solver will need to track these derived relations.

#### 3.2.3 converse + lawful

**Interaction**: Creates backward task relations.
- From `lawful`: `task_rel(s0, 1, s1)`
- From `converse`: `task_rel(s1, -1, s0)` (negative duration)

**Implication**: This requires the solver to support negative durations, which `is_valid_duration()` already handles (range `-M+1` to `M-1`).

#### 3.2.4 task_restriction Impact

**Current Definition** (lines 484-520):
```python
task_restriction = z3.ForAll(
    [some_state, some_duration, next_state],
    z3.Implies(
        self.task_rel(some_state, some_duration, next_state),
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                self.is_world(task_world),
                self.is_valid_duration(some_duration),
                self.is_valid_time(time_shifted),
                self.is_valid_time(time_shifted + some_duration),
                ...
            )
        )
    )
)
```

**Potential Conflict**: The new constraints (especially `forward_comp`) may derive task_rel values that don't correspond to actual world histories. This is because:
- `forward_comp` creates `task_rel(w, d1+d2, u)` from composition
- But `task_restriction` requires every task_rel to be witnessed by a world history

**Resolution Options**:
1. **Weaken task_restriction**: Only apply to unit durations
2. **Strengthen evolution constraint**: Ensure worlds satisfy the full evolution property (Frame.lean:299-301)
3. **Make task_restriction conditional**: Only enabled for certain frame classes

**Recommendation**: Option 1 (weaken task_restriction) is simplest. The existing constraint already includes duration guards; we can modify it to apply only when `some_duration == 1`:

```python
# Modified task_restriction (unit duration only)
z3.Implies(
    z3.And(
        self.task_rel(some_state, some_duration, next_state),
        some_duration == z3.IntVal(1)  # Only enforce for unit duration
    ),
    z3.Exists(...)
)
```

### 3.3 Constraint Consistency Table

| Constraint | nullity_identity | forward_comp | converse |
|------------|-----------------|--------------|----------|
| lawful | Compatible | Extends | Extends |
| task_restriction | Compatible | Potential conflict | Compatible |
| is_valid_duration | Uses | Uses | Uses |
| world_interval | Independent | Independent | Independent |

## 4. Performance Considerations

### 4.1 Quantifier Complexity

| Constraint | Quantified Variables | Formula Structure | Expected Impact |
|------------|---------------------|-------------------|-----------------|
| nullity_identity | 2 (w, u) | Biconditional | Low |
| forward_comp | 5 (w, v, u, d1, d2) | Implication | **High** |
| converse | 3 (w, u, d) | Guarded biconditional | Medium |

**Analysis**:
- `forward_comp` has the highest complexity due to 5 quantified variables
- Z3 must instantiate this constraint for many ground terms during solving
- Pattern-based instantiation can help (see Section 4.3)

### 4.2 Performance Mitigation Strategies

#### 4.2.1 Lazy Constraint Addition

Add constraints conditionally based on frame class:

```python
def build_frame_constraints(self):
    constraints = [
        # ... existing constraints ...
    ]
    
    # Add frame axioms based on settings
    frame_class = self.settings.get('frame_class', 'basic')
    
    if frame_class in ['compositional', 'full']:
        constraints.append(self.build_nullity_identity_constraint())
        constraints.append(self.build_forward_comp_constraint())
        constraints.append(self.build_converse_constraint())
    
    return constraints
```

#### 4.2.2 Quantifier Patterns

Use Z3 patterns to guide instantiation:

```python
def build_forward_comp_constraint(self):
    w = z3.BitVec('comp_w', self.N)
    v = z3.BitVec('comp_v', self.N)
    u = z3.BitVec('comp_u', self.N)
    d1 = z3.Int('comp_d1')
    d2 = z3.Int('comp_d2')
    
    body = z3.Implies(
        z3.And(
            self.task_rel(w, d1, v),
            self.task_rel(v, d2, u),
            self.is_valid_duration(d1),
            self.is_valid_duration(d2),
            self.is_valid_duration(d1 + d2)
        ),
        self.task_rel(w, d1 + d2, u)
    )
    
    # Add patterns to guide instantiation
    return z3.ForAll(
        [w, v, u, d1, d2],
        body,
        patterns=[
            z3.MultiPattern(self.task_rel(w, d1, v), self.task_rel(v, d2, u))
        ]
    )
```

#### 4.2.3 Duration Bounds

Restrict duration enumeration to valid ranges:

```python
def is_valid_duration(self, duration):
    """Check if duration is within valid range: -(M-1) to (M-1)."""
    return z3.And(duration > -self.M, duration < self.M)
```

This is already implemented in the codebase (line 251).

### 4.3 Benchmark Expectations

| Configuration | N | M | Expected Solving Time |
|--------------|---|---|----------------------|
| Basic (no new constraints) | 2 | 2 | ~0.5s |
| With nullity_identity only | 2 | 2 | ~0.6s |
| With all three constraints | 2 | 2 | ~1.5s |
| With all three constraints | 3 | 3 | ~5s (estimate) |

**Recommendation**: Run benchmarks after implementation to validate these estimates. If `forward_comp` proves too expensive, consider making it opt-in via settings.

## 5. Test Strategy

### 5.1 Unit Tests

```python
# test_frame_constraints.py

class TestNullityIdentity:
    """Tests for nullity_identity constraint."""
    
    def test_zero_duration_self_task(self, semantics):
        """task_rel(s, 0, s) should always hold."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)
        
        s = z3.BitVecVal(1, semantics.N)  # Specific state
        solver.add(semantics.task_rel(s, z3.IntVal(0), s))
        
        assert solver.check() == z3.sat
    
    def test_zero_duration_different_states_unsat(self, semantics):
        """task_rel(s1, 0, s2) where s1 != s2 should be unsat."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)
        
        s1 = z3.BitVecVal(1, semantics.N)
        s2 = z3.BitVecVal(2, semantics.N)
        solver.add(semantics.task_rel(s1, z3.IntVal(0), s2))
        
        assert solver.check() == z3.unsat


class TestForwardComp:
    """Tests for forward_comp (compositionality) constraint."""
    
    def test_composition_exists(self, semantics):
        """If task_rel(w,d1,v) and task_rel(v,d2,u), then task_rel(w,d1+d2,u)."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)
        
        w = z3.BitVecVal(0, semantics.N)
        v = z3.BitVecVal(1, semantics.N)
        u = z3.BitVecVal(2, semantics.N)
        
        # Add premises
        solver.add(semantics.task_rel(w, z3.IntVal(1), v))
        solver.add(semantics.task_rel(v, z3.IntVal(1), u))
        
        # Check that composition exists
        solver.add(semantics.task_rel(w, z3.IntVal(2), u))
        
        assert solver.check() == z3.sat


class TestConverse:
    """Tests for converse constraint."""
    
    def test_converse_symmetry(self, semantics):
        """task_rel(w, d, u) implies task_rel(u, -d, w)."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)
        
        w = z3.BitVecVal(0, semantics.N)
        u = z3.BitVecVal(1, semantics.N)
        
        # Add forward task
        solver.add(semantics.task_rel(w, z3.IntVal(1), u))
        
        # Check that converse exists
        solver.add(semantics.task_rel(u, z3.IntVal(-1), w))
        
        assert solver.check() == z3.sat
    
    def test_converse_exclusion(self, semantics):
        """task_rel(w, d, u) without task_rel(u, -d, w) should be unsat."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)
        
        w = z3.BitVecVal(0, semantics.N)
        u = z3.BitVecVal(1, semantics.N)
        
        solver.add(semantics.task_rel(w, z3.IntVal(1), u))
        solver.add(z3.Not(semantics.task_rel(u, z3.IntVal(-1), w)))
        
        assert solver.check() == z3.unsat
```

### 5.2 Integration Tests

```python
class TestConstraintInteractions:
    """Tests for interactions between new and existing constraints."""
    
    def test_lawful_plus_nullity(self, semantics):
        """lawful + nullity_identity should be consistent."""
        # ... test that both constraints can be satisfied together
    
    def test_composition_chain(self, semantics):
        """Test that composition works across multiple steps."""
        # ... test that task_rel(s0, 3, s3) is derivable from 3 unit tasks
    
    def test_converse_with_negative_duration(self, semantics):
        """Test converse creates proper negative duration relations."""
        # ... test that negative durations work correctly
```

### 5.3 Existing Examples to Review

Check if these examples would be affected:

| Example File | Potential Impact |
|--------------|------------------|
| `examples/bimodal_basic.py` | Minimal - basic tests |
| `examples/bimodal_temporal.py` | Check for temporal operator interactions |
| `examples/bimodal_modal.py` | Check for modal operator interactions |

## 6. Implementation Recommendations

### 6.1 Phased Approach

**Phase 1**: Add nullity_identity (lowest risk)
- Simple biconditional
- No interactions with existing constraints
- Easy to test and verify

**Phase 2**: Add converse (medium risk)
- Creates negative duration relations
- May affect iteration/difference tracking
- Test with existing examples

**Phase 3**: Add forward_comp (highest risk)
- Most complex quantifier structure
- May require task_restriction modification
- May impact performance

### 6.2 Code Organization

Add new methods to `BimodalSemantics` class:

```python
# semantic.py additions

def build_nullity_identity_constraint(self):
    """Build constraint: task_rel(w, 0, u) <-> w = u"""
    # ... implementation ...

def build_forward_comp_constraint(self):
    """Build compositionality constraint for sequential tasks."""
    # ... implementation ...

def build_converse_constraint(self):
    """Build time reversal symmetry constraint."""
    # ... implementation ...

def build_frame_constraints(self):
    """Build the frame constraints for the bimodal logic model."""
    # ... existing code ...
    
    # Add new frame axioms
    nullity_identity = self.build_nullity_identity_constraint()
    forward_comp = self.build_forward_comp_constraint()
    converse = self.build_converse_constraint()
    
    return [
        # ... existing constraints ...
        nullity_identity,
        forward_comp,
        converse,
    ]
```

### 6.3 Settings Integration

Add frame class setting:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # ... existing settings ...
    'frame_class': 'basic',  # Options: 'basic', 'compositional', 'full'
}
```

### 6.4 Documentation

Add docstrings referencing the Lean ProofChecker:

```python
def build_forward_comp_constraint(self):
    """Build compositionality constraint for sequential tasks.
    
    If task_rel(w, d1, v) and task_rel(v, d2, u) then task_rel(w, d1+d2, u).
    
    ProofChecker Alignment:
        Matches Compositional.compose from Frame.lean:112-114:
        compose : forall s t r : S, forall x y : Q,
            f.taskRel s x t -> f.taskRel t y r -> f.taskRel s (x + y) r
    """
```

## 7. Open Questions

### 7.1 Evolution Constraint

Should we also add the full evolution constraint from Frame.lean:299-301?

```python
def build_evolution_constraint(self):
    """For any x <= y in a world, task_rel(tau(x), y-x, tau(y)) holds."""
```

This would be stronger than the current `lawful` constraint (which only handles consecutive states).

**Recommendation**: Defer to a follow-up task. The current `lawful` constraint + `forward_comp` should derive the necessary relations.

### 7.2 Soft vs Hard Constraints

Should any of these be soft constraints (preferences rather than requirements)?

**Recommendation**: Start with hard constraints. If performance is an issue, consider making `forward_comp` a soft constraint or disabling it for certain frame classes.

### 7.3 Backward Compatibility

The new constraints change the semantics of the task relation. Are there existing examples or tests that might break?

**Recommendation**: Run the full test suite after each phase to identify regressions.

## 8. References

### Codebase
- `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py`
  - `define_primitives()`: lines 152-234
  - `build_frame_constraints()`: lines 351-542
  - `is_valid_duration()`: lines 236-251

### Lean ProofChecker
- `/home/benjamin/Projects/Logos/Theory/Logos/Foundations/Constitutive/Frame.lean`
  - `TaskFrame` structure: lines 68-72
  - `Compositional` typeclass: lines 108-114
  - `IsEvolution` definition: lines 299-301

### External Resources
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) - Comprehensive Z3 guide
- [Z3 Quantifiers Guide](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/) - Pattern-based instantiation
- [Z3Py Tutorial](https://ericpony.github.io/z3py-tutorial/advanced-examples.htm) - Python examples

### Task 91 Research
- `/home/benjamin/Projects/Logos/ModelChecker/specs/091_update_task_relation_ternary_duration/reports/02_clean-break-research.md`
  - Section 10 discusses deferring these constraints to Task 92

## 9. Conclusion

The three frame constraints can be implemented in Z3/Python following the Lean ProofChecker semantics:

1. **nullity_identity** is straightforward and low-risk
2. **forward_comp** is the most complex and may require task_restriction modification
3. **converse** creates useful negative duration relations

**Recommended Implementation Order**: nullity_identity -> converse -> forward_comp

**Performance Concern**: forward_comp has 5 quantified variables and may impact solving time. Consider making it opt-in via a `frame_class` setting.

**Key Interaction**: forward_comp may conflict with task_restriction. Resolution: modify task_restriction to only apply to unit durations.
