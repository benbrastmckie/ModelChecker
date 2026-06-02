# Research: Fix skolem_abundance Over-constraint at M>=3

**Task**: 114 | **Date**: 2026-06-01 | **Session**: sess_1780358991_673a3b

---

## Summary

The `capped_skolem_abundance_constraint` in `semantic.py:1432-1463` is a triply-nested
quantifier formula `ForAll[src, shift] -> ForAll[time]` that triggers exponential MBQI
blowup at M>=3, causing solver timeouts and spurious UNSAT on no-premise queries. The
workaround in `provider.py:215` caps M at `max(depth, 2)` instead of the semantically
correct `max(depth+2, 3)`, introducing boundary-vacuity errors for depth>=2 formulas
(e.g., G(G(p)) is spuriously reported valid). Replacing the doubly-quantified constraint
with the already-implemented `build_grounded_abundance_constraints()` function (which
enumerates concrete (interval, shift) pairs as independent `ForAll[src]` constraints)
eliminates the MBQI trigger while preserving the shift-closure invariant needed for
perpetuity principles BM_TH_1/BM_TH_2.

---

## Current Behavior

### The M Workaround (provider.py:206-215)

```
provider.py:214  depth = temporal_depth(formula_json)
provider.py:215  M = max(depth, 2)          # should be max(depth+2, 3)
```

The comment at lines 207-213 explicitly acknowledges that `max(depth+2, 3)` is the
boundary-safe formula but cannot be used because `capped_skolem_abundance_constraint`
causes timeouts/spurious UNSAT at M>=3.

Consequences:
- depth=0: M=2, boundary_safe=True (2>1) — correct
- depth=1: M=2, boundary_safe=False (2>2) — boundary effects possible
- depth=2: M=2, boundary_safe=False (2>3) — formulas like G(G(p)) spuriously valid
- depth>=3: M=depth, boundary_safe=False always

The `boundary_safe` field in serialized countermodels (`serialization.py:190`) is
`M > depth + 1`, which is `False` for all depth>=1 with the current formula.

### The Constraint Structure (semantic.py:1395-1463)

`capped_skolem_abundance_constraint` produces a single Z3 formula:

```
ForAll([skcap_src, skcap_shift],
  Implies(
    And(
      is_world(skcap_src),
      world_start(skcap_src) + skcap_shift >= -M+1,   # shift stays in domain
      world_end(skcap_src)   + skcap_shift <= M-1,    # shift stays in domain
      skcap_shift != 0,
    ),
    And(
      is_world(shift_of_capped(skcap_src, skcap_shift)),
      world_start(shift_of_capped(...)) == world_start(skcap_src) + skcap_shift,
      world_end(shift_of_capped(...))   == world_end(skcap_src)   + skcap_shift,
      matching_states_when_shifted_var(skcap_src, skcap_shift, shift_of_capped(...))
    )
  )
)
```

`matching_states_when_shifted_var` (semantic.py:1241-1255) adds a third quantifier:

```
ForAll([shift_var_check_time],
  Implies(
    And(
      time >= world_start(src),   time <= world_end(src),
      time+shift >= world_start(target), time+shift <= world_end(target),
    ),
    Select(world_fn(src), time) == Select(world_fn(target), time+shift)
  )
)
```

The full constraint is therefore `ForAll[src, shift] -> ForAll[time]` — three nested
integer quantifiers with nonlinear interactions (array selects with arithmetic offsets
on quantified index). This is precisely the pathological pattern for Z3's MBQI heuristic.

### How It Is Used (semantic.py:640-660)

`capped_skolem_abundance_constraint` is called once during `build_frame_constraints()`
at line 658 and added directly to the frame constraint list. It is constraint #8 of ~10
frame constraints. The comment at lines 647-657 notes this is required for perpetuity
principles and cites the JPL paper's `app:auto_existence` and the Lean
`ShiftClosed` property.

### The Deprecated Alternative (semantic.py:1317-1393)

`build_grounded_abundance_constraints()` was implemented as Task 98 alternative but
labeled counterproductive in comments at semantic.py:1411-1416 and provider.py comment
at lines 653-657. The Task 98 conclusion was that the grounded form was _slower_:

> "per-interval grounded form creates MORE ground terms via eager E-matching (one Skolem
> term per world per valid shift immediately), while the quantified MBQI form is lazy"

However, the Task 98 benchmarks were conducted at M=2 (where the doubly-quantified form
has only 1 ForAll[src,shift] and the grounded form produces 2 ForAll[src] constraints).
The regression was SAT (BM_CM_1: 9s -> 15s timeout) and UNSAT (BM_TH_1/2: 30s -> 75s+)
at M=2. The Task 98 conclusion does NOT apply at M=3 where the grounded form produces
6 independent ForAll[src] constraints (vs 1 ForAll[src,shift,time]) — a fundamentally
different tradeoff.

---

## Root Cause: Why M>=3 Causes Blowup

### Quantifier Structure

At M=2, the constraint is:
- `ForAll[src, shift]` with antecedent that allows only 2 valid (interval, shift) pairs
- `matching_states_when_shifted_var` adds `ForAll[time]` over 3 time points

At M=3, the number of valid (interval, shift) pairs triples to 6:

| Interval | Valid shifts | Count |
|----------|-------------|-------|
| [-2, 0]  | +1, +2      | 2     |
| [-1, 1]  | -1, +1      | 2     |
| [0, 2]   | -2, -1      | 2     |

Total: 6 valid pairs, time domain grows to 5 points ({-2,-1,0,1,2}).

Z3's MBQI must instantiate `ForAll[src, shift]` for each of N worlds × 6 shifts = 12
potential instantiations. Each instantiation involves a Skolem function application
`shift_of_capped(src, shift)` which creates new terms, triggering further `ForAll[time]`
instantiations. With the three-quantifier nesting, MBQI faces combinatorial instantiation
growth that is manageable at M=2 (2 pairs × 3 time points) but becomes intractable at
M=3 (6 pairs × 5 time points) and worse at higher M.

The critical problem with no-premise queries (empty premise set): Z3 must prove the
full shift-closure invariant holds across ALL valid (world, shift) combinations
simultaneously. Without premises to narrow the world structure, MBQI enters a loop
instantiating the doubly-quantified constraint, finding partial candidates, and
attempting to extend them — a pattern that causes the observed timeouts and spurious UNSAT.

### Why build_grounded_abundance_constraints Avoids the Blowup

At M=3, `build_grounded_abundance_constraints()` produces 6 independent `ForAll[src]`
constraints, one per valid (interval, shift) pair. Each has the form:

```
ForAll([src],
  Implies(
    And(is_world(src), world_start(src)==start, world_end(src)==end),
    And(
      is_world(shift_of_capped(src, delta)),
      world_start(shift_of_capped(src, delta)) == new_start,   # concrete integer
      world_end(shift_of_capped(src, delta)) == new_end,       # concrete integer
      state_eq_at_t1, state_eq_at_t2, state_eq_at_t3,         # M concrete equalities
    )
  )
)
```

All shift amounts and time indices are concrete Python integers. Z3 uses E-matching
(not MBQI) for these — guiding instantiation directly rather than requiring universal
quantifier enumeration. The Skolem function `shift_of_capped` is shared with the
doubly-quantified form for backward compatibility.

The Task 98 concern ("eager E-matching creates more ground terms") is a real tradeoff,
but at M=3+ the blowup from the doubly-quantified form (timeouts) dominates the cost
of eager E-matching. The grounded form's constraint count grows as O(M²) while the
doubly-quantified form's MBQI work grows super-linearly.

---

## Options

### Option 1: Switch to build_grounded_abundance_constraints at M>=3

Replace `capped_skolem_abundance_constraint` with `build_grounded_abundance_constraints`
in `build_frame_constraints()` when M>=3. At M=2, keep the existing form (matching Task
98 benchmark). This is a conditional dispatch in `build_frame_constraints()`.

**Pros**:
- Minimal code change (both functions already exist)
- Eliminates MBQI trigger at M>=3 entirely
- Preserves M=2 performance characteristics validated by Task 98
- Constraint counts are O(M²): M=3→6, M=4→12, M=5→20 — manageable

**Cons**:
- Two code paths to maintain
- Task 98 benchmarks showed grounded form is slower at M=2; need to verify M=3 grounded
  is actually faster than M=3 quantified (not benchmarked)
- `build_grounded_abundance_constraints` uses concrete state equalities per time point,
  not `matching_states_when_shifted_var` — removes the third quantifier layer differently

**Implementation**: Change `build_frame_constraints()` at semantic.py:658:

```python
if self.M >= 3:
    skolem_abundance = self.build_grounded_abundance_constraints()
else:
    skolem_abundance = [self.capped_skolem_abundance_constraint()]
```

Note: `build_grounded_abundance_constraints` returns a list; the frame constraint
aggregation must handle both cases (list vs single constraint). Lines 796-803 show
the current return statement — need to verify list flattening.

### Option 2: Weaken Constraint to Formula's Temporal Depth

Instead of requiring all shifts for all worlds, require only shifts up to
`temporal_depth` from the formula being checked. Pass `depth` to
`capped_skolem_abundance_constraint` and limit shift_amount to `[-depth, +depth]`.

**Pros**: Reduces quantifier domain size proportionally to formula needs
**Cons**:
- Requires threading `depth` through `BimodalSemantics` (a settings parameter)
- Does not eliminate the three-quantifier nesting — MBQI still triggers, just on smaller
  domain
- Shift-closure guarantee weakens: may miss validity for formulas using shifts > depth
- Architecturally invasive: constraint semantics depend on formula content

**Verdict**: Not recommended. The nesting structure, not domain size, is the blowup cause.

### Option 3: Reformulate with Bit-vector or Bounded Int Quantification

Replace `ForAll[shift: Int]` with an unrolled finite disjunction over concrete shifts
(equivalent to grounded form) or use Z3's bounded quantifier optimization.

**Pros**: Could eliminate MBQI entirely while keeping a single formula
**Cons**:
- Effectively equivalent to Option 1 but more complex to implement
- Z3's `z3.Sum` / unrolled disjunction is harder to read than separate ForAll[src]
- No advantage over the existing `build_grounded_abundance_constraints`

**Verdict**: Not recommended. Option 1 already implements this via enumeration.

---

## Recommendation

**Implement Option 1** (conditional dispatch to `build_grounded_abundance_constraints`
at M>=3) because:

1. Both functions are already implemented and tested in the codebase.
2. The fix is localized to `build_frame_constraints()` (one line change + list handling).
3. `build_grounded_abundance_constraints` uses concrete integers for all Skolem terms,
   guiding Z3's E-matching instead of requiring MBQI — this directly addresses the root cause.
4. After fixing `semantic.py`, `provider.py:215` can be updated from `max(depth, 2)`
   to `max(depth+2, 3)`, restoring boundary safety for depth>=1 formulas.
5. The `xfail` test at `test_soundness_regression.py:502-555` becomes a genuine test
   of shift closure at M=3 that should pass after the fix.

The M=2 path is unchanged, preserving Task 98 performance for the default case.

---

## Gate Criteria

The fix is verified when:

1. **Timeout regression gone**: `test_shift_closure_on_extracted_worlds_m3` (currently
   xfail at `test_soundness_regression.py:502-555`) passes without timeout or UNSAT
   at M=3 with N=2 and formula `atom(p)`.

2. **M formula restored**: `provider.py:215` returns `max(depth+2, 3)` and:
   - `test_depth0_boundary_safe_is_true` still passes (depth=0: M=3, boundary_safe=True)
   - `test_depth1_boundary_safe_is_false` is updated: depth=1 now uses M=3, boundary_safe=(3>2)=True
   - `test_depth2_boundary_safe_is_false` is updated: depth=2 now uses M=4, boundary_safe=(4>3)=True
   - `test_gg_p_returns_none_at_m2` should become `test_gg_p_returns_countermodel_at_m4`
     (G(G(p)) now returns non-None at M=max(2+2,3)=4)

3. **`boundary_safe=True`** in countermodel output for all depth-d formulas with
   the new M formula (since M=max(depth+2,3) > depth+1 always).

4. **Frame axiom tests pass**: Tests for nullity, converse, and forward_comp continue
   to pass — these are independent of the abundance constraint.

5. **Existing UNSAT tests pass**: BM_TH_1, BM_TH_2 and related perpetuity tests
   continue to produce UNSAT (valid) results — shift closure at M>=3 must still hold.

---

## Key Files Needing Changes

| File | Lines | Change |
|------|-------|--------|
| `code/src/model_checker/theory_lib/bimodal/semantic.py` | 658 | Dispatch to `build_grounded_abundance_constraints` when M>=3 |
| `code/src/model_checker/theory_lib/bimodal/semantic.py` | 796-803 | Handle list return from grounded variant in frame constraint aggregation |
| `code/src/bimodal_logic/provider.py` | 215 | Change `max(depth, 2)` to `max(depth+2, 3)` |
| `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` | 502-555 | Remove xfail marker; update expected M values in boundary tests |

### Critical: Frame Constraint Return Statement

`build_frame_constraints` currently passes `skolem_abundance` (a single formula) to
the return list (semantic.py:796-803). `build_grounded_abundance_constraints` returns
a list. The aggregation must be updated:

```python
# Current (approximate):
return [..., skolem_abundance, ...]

# After fix (if using conditional dispatch):
if isinstance(skolem_abundance, list):
    return [..., *skolem_abundance, ...]
else:
    return [..., skolem_abundance, ...]
```

Verify the actual return statement in semantic.py:775-803 before implementing.

---

## Supporting Evidence

- `semantic.py:1411-1416`: Task 98 comment explains the grounded vs. quantified tradeoff
  at M=2. The conclusion was M=2-specific.
- `semantic.py:1332-1336`: Docstring for `build_grounded_abundance_constraints` gives
  exact constraint counts (M=3: 18, M=4: 48, M=5: 100 total equalities from 6/12/20 pairs).
- `test_soundness_regression.py:502-506`: xfail explicitly documents the M=3 timeout.
- `provider.py:207-213`: Comment acknowledges the ideal formula and the workaround.
- `translation.py:214`: `M_safe(d) = max(d+2, 3)` is the documented correct formula.
