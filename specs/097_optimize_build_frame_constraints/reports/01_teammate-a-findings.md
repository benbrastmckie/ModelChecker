# Teammate A Findings: Direct Z3 Optimization Techniques

## Key Findings

### Finding 1: `classical_truth` is Genuinely Tautological -- Remove It

The constraint at lines 509-517 of `semantic.py` is:

```python
classical_truth = z3.ForAll(
    [world_state, sentence_letter],
    z3.Or(
        self.truth_condition(world_state, sentence_letter),
        z3.Not(self.truth_condition(world_state, sentence_letter))
    )
)
```

This is literally `ForAll([ws, sl], P(ws, sl) OR NOT P(ws, sl))`, which is the law of excluded middle applied to any boolean-valued function. Since `truth_condition` is declared as a Z3 uninterpreted function returning `BoolSort`, the formula `truth_condition(ws, sl) OR NOT truth_condition(ws, sl)` is a tautology in classical logic -- it is true in every possible interpretation, and Z3 can recognize this as `True` during preprocessing.

**Effect on Z3**: Z3's preprocessing simplifies tautological constraints to `True` before search, but this still costs:
1. Memory to store the `ForAll` AST node (quantifier over BitVec x DeclareSort -- the uninterpreted AtomSort means Z3 must track it symbolically).
2. A simplification pass over the quantifier body.
3. Potential E-matching overhead: even tautological quantifiers with function symbols can generate pattern candidates in the E-matching engine.

Removing this constraint is completely safe. It adds zero expressible information -- all boolean functions in Z3's model already satisfy excluded middle by definition of BoolSort. The fact that `truth_condition` is uninterpreted does not change this: uninterpreted functions in Z3 MBQI always return Bool values, never a third value.

**Verification**: The constraint does not appear in the logic the other constraints depend on. None of the other constraints reference `classical_truth` as a precondition or conjunct. Removing it cannot change SAT/UNSAT status.

---

### Finding 2: Pattern Annotations for `lawful`

The `lawful` constraint (lines 553-577) uses 2 quantified variables `[lawful_world, lawful_time]` and tests `is_world(lawful_world)` plus two calls to `is_valid_time_for_world` before asserting `task_rel(...)`. It currently has no pattern annotation.

Z3's E-matching engine needs a "trigger" to know when to instantiate this axiom. Without patterns, Z3 uses default patterns derived from the function symbols in the body.

The most useful trigger is the appearance of `world_function(lawful_world)` -- since that function is called when evaluating a specific world's history, and `lawful` should fire whenever Z3 has a concrete world in scope:

```python
lawful_world_arr = self.world_function(lawful_world)

lawful = z3.ForAll(
    [lawful_world, lawful_time],
    z3.Implies(
        z3.And(
            self.is_world(lawful_world),
            self.is_valid_time(lawful_time, -1),
            self.is_valid_time_for_world(lawful_world, lawful_time),
            self.is_valid_time_for_world(lawful_world, lawful_time + 1),
        ),
        self.task_rel(
            z3.Select(lawful_world_arr, lawful_time),
            z3.IntVal(1),
            z3.Select(lawful_world_arr, lawful_time + 1)
        )
    ),
    patterns=[
        z3.MultiPattern(
            self.world_function(lawful_world),
            self.world_interval_start(lawful_world)
        )
    ]
)
```

The multi-pattern on `(world_function(lawful_world), world_interval_start(lawful_world))` fires when both a world's history and its interval start are known -- precisely when lawfulness is checkable. This avoids spurious instantiation while ensuring instantiation when needed.

Alternative single pattern: `z3.MultiPattern(self.is_world(lawful_world))` -- simpler but may fire too eagerly.

---

### Finding 3: Pattern Annotation for `skolem_abundance`

The `capped_skolem_abundance_constraint` (lines 1187-1248) uses 2 quantified variables `[source_world, shift_amount]`. The Skolem function `shift_of_capped(source_world, shift_amount)` is the natural trigger term.

Currently there is no pattern annotation. Adding a pattern on `shift_of_capped(source_world, shift_amount)` itself is self-referential (the trigger IS the conclusion), but the premise contains `is_world(source_world)` and `world_interval_start(source_world)` which are the right triggers:

```python
return z3.ForAll(
    [source_world, shift_amount],
    z3.Implies(
        z3.And(
            self.is_world(source_world),
            source_start + shift_amount >= z3.IntVal(-self.M + 1),
            source_end + shift_amount <= z3.IntVal(self.M - 1),
            shift_amount != z3.IntVal(0),
        ),
        z3.And(
            self.is_world(shift_of_capped(source_world, shift_amount)),
            ...
        )
    ),
    patterns=[
        z3.MultiPattern(
            self.world_interval_start(source_world),
            self.world_interval_end(source_world)
        )
    ]
)
```

This fires when Z3 has determined interval bounds for a world, which is the precondition for the shift being applicable.

**Important caution**: For Skolem abundance, this pattern can dramatically increase instantiation if there are many worlds and shifts. A tighter pattern would be `is_world(source_world)` alone -- which fires once per grounded world and lets Z3 check shifts lazily. The risk is that the body contains a nested `ForAll` via `matching_states_when_shifted_var`, making this a source of quantifier explosion.

---

### Finding 4: Pattern Annotation for `world_uniqueness`

The `world_uniqueness` constraint (lines 596-616) has a `ForAll/Exists` structure:

```python
world_uniqueness = z3.ForAll(
    [world_one, world_two],
    z3.Implies(
        z3.And(
            self.is_world(world_one),
            self.is_world(world_two),
            world_one != world_two
        ),
        z3.Exists(
            [some_time],
            z3.And(...)
        )
    )
)
```

The Exists is not Skolemized here (unlike `skolem_abundance`). For MBQI, nested Exists inside ForAll is handled via MBQI's instantiation, not E-matching. However for the E-matching pass, adding a pattern prevents spurious instantiations:

```python
world_uniqueness = z3.ForAll(
    [world_one, world_two],
    z3.Implies(
        z3.And(...),
        z3.Exists([some_time], ...)
    ),
    patterns=[
        z3.MultiPattern(
            self.world_function(world_one),
            self.world_function(world_two)
        )
    ]
)
```

This fires only when Z3 has grounded both `world_function(world_one)` and `world_function(world_two)`, meaning it has concrete arrays for two distinct worlds -- the exact precondition for checking uniqueness. This is the most targeted pattern possible.

---

### Finding 5: Constraint Ordering

The current return list order in `build_frame_constraints` (lines 667-687) is:

```python
return [
    valid_main_world,       # Boolean
    valid_main_time,        # Boolean
    classical_truth,        # TAUTOLOGICAL - remove
    enumeration_constraint, # ForAll 1-var
    convex_world_ordering,  # ForAll 1-var
    lawful,                 # ForAll 2-var
    nullity_identity,       # ForAll 2-var
    converse,               # ForAll 3-var
    forward_comp,           # ForAll 5-var (has MultiPattern)
    skolem_abundance,       # ForAll 2-var (heavy body, nested ForAll)
    world_uniqueness,       # ForAll 2-var / Exists 1-var
    world_interval,         # ForAll 1-var (large Or of interval options)
]
```

Z3 processes assertions in order for CDCL+theory propagation, but for MBQI the order affects the initial seed for quantifier instantiation. The comment "NOTE: order matters!" reflects this.

**Recommended order after removing classical_truth**:

1. Simple boolean facts first (`valid_main_world`, `valid_main_time`) -- these are ground facts that immediately narrow the search space.
2. Small-arity structural constraints (`enumeration_constraint`, `convex_world_ordering`) -- ForAll 1-var constraints that restrict what world IDs can exist.
3. Interval constraint (`world_interval`) -- this bounds the interval functions early, which is a precondition for many other constraints to fire their patterns.
4. Frame axioms (`nullity_identity`, `converse`, `forward_comp`) -- these are "local" constraints on task_rel that Z3 can propagate eagerly.
5. Lawfulness (`lawful`) -- depends on world intervals being established.
6. Abundance (`skolem_abundance`) -- heavy, should come after intervals and worlds are established.
7. Uniqueness (`world_uniqueness`) -- most expensive, should come last.

**Proposed order**:

```python
return [
    valid_main_world,
    valid_main_time,
    # Structural: restrict universe
    enumeration_constraint,
    convex_world_ordering,
    # Interval bounds early (precondition for many patterns)
    world_interval,
    # Frame axioms (local task_rel properties)
    nullity_identity,
    converse,
    forward_comp,
    # Transition law (depends on intervals)
    lawful,
    # Abundance (heavy, triggers after worlds/intervals known)
    skolem_abundance,
    # Uniqueness (most expensive, last)
    world_uniqueness,
]
```

---

### Finding 6: Z3 Solver Parameter Tuning

The current `z3_adapter.py` (lines 36-39) sets:

```python
self._solver.set('auto_config', False)
self._solver.set('smt.mbqi', True)
self._solver.set('smt.ematching', True)
self._solver.set('smt.mbqi.max_iterations', 1000)
```

Additional parameters relevant to this constraint profile:

**`smt.qi.eager_threshold`**: Controls when E-matching instances are added eagerly vs lazily. Default is 10. For heavy Skolem constraints, raising this reduces premature instantiation:

```python
self._solver.set('smt.qi.eager_threshold', 100)
```

**`smt.qi.max_instances`**: Hard cap on quantifier instantiations. The bimodal constraints with 5-variable `forward_comp` can generate exponential instantiations. Setting a cap prevents OOM but risks incompleteness -- appropriate for timeout-bounded checking:

```python
self._solver.set('smt.qi.max_instances', 10000)
```

**`smt.qi.profile`**: Debugging parameter that prints instantiation statistics. Useful for profiling which quantifiers generate most instances (non-production use only):

```python
# For profiling only, not production:
self._solver.set('smt.qi.profile', True)
```

**`smt.mbqi.max_iterations`**: Currently set to 1000. For hard verification cases (no countermodel expected, like BM_TH_1/BM_TH_2), higher values help Z3 prove UNSAT before giving up:

```python
self._solver.set('smt.mbqi.max_iterations', 5000)
```

**`smt.pull_nested_quantifiers`**: Boolean parameter that can simplify nested ForAll/Exists to single-level quantifiers where possible. The `world_uniqueness` and `matching_states_when_shifted_var` (which embeds a ForAll inside another ForAll) could benefit:

```python
self._solver.set('smt.pull_nested_quantifiers', True)
```

---

### Finding 7: Ground-Instantiation for Small-Domain Constraints

The `enumeration_constraint` and `convex_world_ordering` use ForAll over world IDs. Since `max_world_id = M * 2^(M*N)` is a small finite number for typical settings (e.g., M=2, N=2 gives max_world_id=8), these can be grounded:

```python
# Replace ForAll-based enumeration_constraint with ground conjunction:
enumeration_facts = z3.And(*[
    z3.Implies(self.is_world(i), i >= 0)
    for i in range(self.max_world_id)
])

# Replace ForAll-based convex_world_ordering with ground conjunction:
convex_facts = z3.And(*[
    z3.Implies(
        z3.And(self.is_world(i), i > 0),
        self.is_world(i - 1)
    )
    for i in range(self.max_world_id)
])
```

For M=2, N=2 this is 8 ground implications instead of an unbounded ForAll. Z3 handles ground clauses much faster than quantified ones (no E-matching/MBQI needed).

**Note**: `time_interval_constraint` (lines 830-876) already does exactly this grounding for world intervals and is commented out in the main return list in favor of `world_interval_constraint`. The `time_interval_constraint` approach is architecturally correct for performance -- the existing grounded version should be preferred over the ForAll version.

---

### Finding 8: Nested ForAll in `matching_states_when_shifted_var`

The `capped_skolem_abundance_constraint` calls `matching_states_when_shifted_var` in its body (lines 1241-1245), which internally creates ANOTHER `ForAll` (lines 1111-1124):

```python
def matching_states_when_shifted_var(self, source_world, shift, target_world):
    time = z3.Int('shift_var_check_time')
    return z3.ForAll(
        [time],
        z3.Implies(...)
    )
```

This creates a nested `ForAll [source_world, shift_amount] ... ForAll [time] ...` structure inside `capped_skolem_abundance_constraint`. Z3 must process a 3-level deep quantifier (outer 2-var ForAll wrapping inner 1-var ForAll).

Z3 can flatten this via `smt.pull_nested_quantifiers`, but it may not always succeed automatically. A manual flattening would convert:

```
ForAll([src, shift], Implies(P(src, shift), And(Q(src,shift), ForAll([t], R(src,shift,t)))))
```

to:

```
ForAll([src, shift], Implies(P(src, shift), Q(src, shift)))
AND
ForAll([src, shift, t], Implies(P(src, shift), R(src, shift, t)))
```

This is the "prenex normal form" approach. For the abundance constraint, splitting it into two top-level ForAlls (one for the validity/interval assertions, one for the state matching) could improve performance by giving Z3 better structure to work with.

---

## Recommended Approach

### Priority 1 (High Confidence, Zero Risk): Remove `classical_truth`

Simply delete lines 507-517 and remove `classical_truth` from the return list. This has zero semantic effect and eliminates unnecessary quantifier overhead.

```python
# DELETE: lines 507-517 (classical_truth)
# DELETE: line 671 (classical_truth in return list)
```

### Priority 2 (High Confidence, Low Risk): Move `world_interval` Earlier

Move `world_interval` before `lawful` in the return list. This is a reordering with no semantic effect but gives Z3 interval bounds early so other constraints can fire their patterns sooner.

### Priority 3 (Medium Confidence, Low Risk): Add Pattern Annotations

Add `patterns=[...]` to `lawful`, `world_uniqueness`, and `capped_skolem_abundance_constraint`. These guide E-matching and reduce spurious instantiation. The patterns described in Findings 2-4 are well-targeted.

### Priority 4 (Medium Confidence, Medium Effort): Use `time_interval_constraint` Instead of `world_interval_constraint`

The `time_interval_constraint` (lines 830-876) is already implemented and uses ground instantiation for each concrete world ID. It is commented out but should be preferred over the ForAll-based `world_interval_constraint`. Switch the return list to use `time_interval` instead of `world_interval`.

### Priority 5 (Medium Confidence, Medium Effort): Ground `enumeration_constraint` and `convex_world_ordering`

Replace the ForAll versions with ground conjunctions over concrete world IDs (0..max_world_id-1), following the same pattern as `time_interval_constraint`.

### Priority 6 (Low Confidence, Higher Risk): Solver Parameter Tuning

Add `smt.qi.eager_threshold` and `smt.pull_nested_quantifiers` settings. These are solver-global and could affect correctness on edge cases. Requires systematic benchmarking across all examples before deployment.

---

## Evidence and Examples

### Evidence for `classical_truth` Removal

The formula `Or(P, Not(P))` for any Z3 boolean expression `P` is simplified to `True` by Z3's built-in simplifier in preprocessing. A simple test:

```python
import z3
s = z3.Solver()
ws = z3.BitVec('ws', 2)
truth = z3.Function('truth', z3.BitVecSort(2), z3.BoolSort())
taut = z3.ForAll([ws], z3.Or(truth(ws), z3.Not(truth(ws))))
s.add(taut)
print(s.check())  # sat, trivially
# Removing it changes nothing:
s2 = z3.Solver()
print(s2.check())  # sat, same result
```

The constraint adds no information about `truth_condition`'s actual values.

### Evidence for Pattern Effectiveness

`build_forward_comp_constraint` (lines 382-388) already uses a `MultiPattern` for its 5-variable ForAll. The pattern comment (lines 379-381) explicitly states this "reduces spurious instantiations." Applying the same technique to the other heavy ForAlls is a direct extension of existing codebase practice.

### Evidence for Ground Instantiation

`time_interval_constraint` (lines 830-876) demonstrates the ground instantiation pattern already in use. It iterates `range(self.max_world_id)` and creates concrete constraints per world ID, avoiding ForAll entirely. This is the right pattern for small-domain constraints.

### Evidence for Constraint Ordering

The `# NOTE: order matters!` comment on line 668 confirms that ordering affects Z3 performance. In CDCL+theory solvers, earlier assertions give the solver "seed" facts that guide subsequent search. Moving simple structural constraints (`valid_main_world`, `enumeration_constraint`) and interval bounds (`world_interval`) early means Z3 has these facts available before encountering the heavier ForAll constraints.

---

## Confidence Levels

| Recommendation | Confidence | Risk | Effort |
|----------------|------------|------|--------|
| Remove `classical_truth` | High | Zero | Trivial (2 line deletions) |
| Move `world_interval` earlier in list | High | Zero | Trivial (reorder) |
| Add patterns to `lawful` | Medium | Low | Low |
| Add patterns to `world_uniqueness` | Medium | Low | Low |
| Add patterns to `skolem_abundance` | Medium | Medium | Low |
| Use `time_interval_constraint` instead of `world_interval_constraint` | Medium | Low | Trivial (swap commented line) |
| Ground `enumeration_constraint` | Medium | Low | Low |
| Ground `convex_world_ordering` | Medium | Low | Low |
| `smt.pull_nested_quantifiers` setting | Low | Medium | Low |
| `smt.qi.eager_threshold` tuning | Low | Medium | Low |
| Split `matching_states_when_shifted_var` (prenex form) | Low | Medium | Medium |

### Highest Impact / Lowest Risk Combination

Apply these three changes together for a safe first optimization pass:

1. Remove `classical_truth` (zero risk, minor overhead reduction)
2. Reorder constraints to put `world_interval` before `lawful` and `forward_comp` (zero risk, may improve MBQI seed)
3. Add `MultiPattern(world_function(w1), world_function(w2))` to `world_uniqueness` (low risk, targets the most expensive ForAll/Exists)

These can be applied and verified by running the full example suite. If the example classifications are unchanged, proceed to the grounding optimizations.
