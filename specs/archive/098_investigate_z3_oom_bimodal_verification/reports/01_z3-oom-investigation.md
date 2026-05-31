# Z3 OOM Investigation: Bimodal Theorem Verification

**Task**: 98 - Investigate Z3 OOM kills during bimodal theorem verification
**Date**: 2026-05-29
**Session**: sess_1780110528_g5f

## Executive Summary

earlyoom kills `python3.12` when running bimodal examples with M>=3, specifically the BX5-BX13 (M=4, 20-30s timeouts) and BX7 (M=5, 60s timeout) examples. The OOM is caused by a multi-constraint amplification loop: `capped_skolem_abundance_constraint` contains a nested `ForAll[time]` inside `ForAll[src, shift]`, which combined with `world_uniqueness` (ForAll/Exists) and `forward_comp` (5 quantified variables) creates an unbounded ground term explosion under MBQI. Task 97 already added `max_memory=4096 MB` per-solver to `Z3SolverAdapter`, which is the right first line of defense. The primary remaining mitigation is to ground `capped_skolem_abundance_constraint` by eliminating the `shift` quantifier and the nested `ForAll[time]`, replacing them with concrete integer constants for M's finite set of valid (interval, shift) pairs.

## Current Constraint Architecture

### Frame Constraints Generating Quantifiers

`build_frame_constraints()` in `semantic.py` (lines 467-673) returns 11 constraints. The quantifier-heavy ones are:

**1. `forward_comp`** (lines 338-388, in return list at line 668)
- Pattern: `ForAll [w, v, u, d1, d2]` (5 vars: 3 BitVec + 2 Int)
- Multi-pattern on `(task_rel(w,d1,v), task_rel(v,d2,u))` -- guards E-matching well
- Only fires when both premises are ground terms
- **Assessment**: Well-guarded, low memory risk on its own

**2. `capped_skolem_abundance_constraint`** (lines 1173-1234, in return list at line 670)
- Pattern: `ForAll [source_world, shift_amount]` containing `matching_states_when_shifted_var`
- `matching_states_when_shifted_var` adds a NESTED `ForAll [time]` inside
- Shape: `ForAll [src, shift] -> ... ForAll [time] -> world_fn(shift_of(src,shift))[time+shift] == world_fn(src)[time]`
- **Critical**: This is a doubly-quantified constraint over INTEGER variables (world IDs and shift amounts are `IntSort`, not bounded BitVec)
- MBQI must instantiate over integer domain, creating unbounded candidates

**3. `world_uniqueness`** (lines 592-613, in return list at line 671)
- Pattern: `ForAll [world_one, world_two] -> Exists [some_time]`
- All three variables are `IntSort` -- pure integer domain, MBQI-required
- The Exists inside ForAll forces MBQI to find witness times for every world pair MBQI proposes
- **Assessment**: Major MBQI work generator; each proposed world pair requires witness search

**4. `lawful`** (lines 541-567, in return list at line 665)
- Pattern: `ForAll [lawful_world, lawful_time]` with `is_world` and `is_valid_time_for_world` guards
- **Assessment**: Integer quantifiers but well-guarded; fires on known worlds

**5. `world_interval`** (via `world_interval_constraint`, lines 783-814)
- Pattern: `ForAll [interval_world] -> Or(interval_options)`
- Single integer variable; manageable

**Note**: `task_restriction` (lines 624-652) and `task_minimization` (lines 655, 1236-1261) are constructed but NOT included in the return list. They have no impact on current behavior.

### The Amplification Loop

The OOM is caused by a feedback cycle between three constraints:

```
[Step 1] capped_skolem_abundance fires for world pair (src=w0, shift=k)
         -> creates shift_of_capped(w0, k) = new world w1
         -> asserts is_world(w1), interval constraints, and state equality ForAlls

[Step 2] world_uniqueness fires on (w0, w1)
         -> MBQI must find some_time t where state[w0][t] != state[w1][t]
         -> generates ground terms for is_valid_time(t), Select(world_fn(w0), t), etc.

[Step 3] forward_comp fires on new task_rel pairs from lawful applied to w1
         -> generates new task_rel(s, d, u) ground terms
         -> these satisfy forward_comp Exists premises
         -> creates more task_rel facts

[Step 4] lawful fires on w1 at each time point
         -> asserts task_rel(state[w1,t], 1, state[w1,t+1]) for each t
         -> more task_rel facts feed back into forward_comp

[Step 5] capped_skolem fires again for w1 with all valid shifts
         -> creates more shifted worlds w2, w3, ...
         -> each new world feeds steps 2-4 again
```

For M=4: max_world_id = 4 * 2^(4*2) = 1024 potential world IDs, each triggering 12 abundance constraints with 4 time-state equality assertions. The ground term count grows multiplicatively with each MBQI round, consuming memory unboundedly until earlyoom intervenes.

## Z3 Memory Control Options

### Current Implementation (Task 97)

`Z3SolverAdapter._configure_quantifier_mode()` already sets:
```python
self._solver.set('max_memory', 4096)  # 4 GB per solver instance
```

This prevents earlyoom from killing the process by having Z3 return `'unknown'` gracefully at 4 GB. However, Z3 still accumulates up to 4 GB before stopping.

### Z3 Memory Parameters

**Per-solver limit** (recommended, already in use):
```python
solver.set('max_memory', N)  # N in MB; causes 'unknown' at limit
```

**Global process limit** (alternative, affects all Z3 instances):
```python
z3.set_param('memory_max_size', N)  # N in MB
```

**Behavior**: When `max_memory` is hit, `solver.check()` returns `'unknown'` and `solver.reason_unknown()` returns `'max. memory exceeded'`. This is the correct behavior -- the code in `runner.py` already handles `'unknown'` as a timeout.

**Key finding**: Reducing `max_memory` from 4096 to 1024 MB would cause faster unknown returns and reduce per-example peak memory, at the risk of missing solutions for harder instances. The 4 GB limit is the right trade-off for a system with 30 GB RAM.

### Quantifier Instantiation Cap

```python
solver.set('smt.qi.max_instances', 100000)  # max E-matching instantiations
```

**Status**: Tested in Task 97, caused regressions. BM_CM_2 and BM_CM_4 require more than 100,000 instantiations. Not safe to enable globally.

## Quantifier Instantiation Strategies

### MBQI vs E-matching

The current configuration uses both:
```python
self._solver.set('smt.mbqi', True)
self._solver.set('smt.ematching', True)
self._solver.set('smt.mbqi.max_iterations', 1000)
```

**E-matching** (pattern-driven):
- Fires when specific patterns appear in ground terms
- Predictable and bounded by pattern triggers
- Cannot handle formulas like `ForAll [x] -> Exists [y] -> f(x,y)` without extra patterns
- `forward_comp` uses multi-pattern to guide E-matching well

**MBQI** (model-based quantifier instantiation):
- Tries to find counterexamples to ForAll by constructing candidate models
- Required for mixed ForAll/Exists patterns (world_uniqueness)
- Required for integer-domain quantifiers (world IDs, time points)
- Memory intensive: each round can add many ground terms

**Key observation**: The integer-domain quantifiers in `world_uniqueness` and `capped_skolem_abundance` cannot be handled by E-matching alone -- they require MBQI. However, grounding the shift and time variables into concrete constants would make these constraints solvable by E-matching.

### Pattern Annotations

`build_forward_comp_constraint()` already uses `MultiPattern`:
```python
z3.ForAll([w, v, u, d1, d2], body,
    patterns=[z3.MultiPattern(self.task_rel(w, d1, v), self.task_rel(v, d2, u))])
```

This prevents spurious instantiations. Testing in Task 97 found that adding MultiPattern to `lawful` and `converse` caused regressions on countermodel examples (BM_CM_2, BM_CM_4) because patterns prevented instantiations needed for SAT search.

**Pattern annotation for world_uniqueness**: Not straightforward because the outer quantifier needs to fire for ALL world pairs, not just those matching specific patterns. Adding a pattern like `z3.MultiPattern(is_world(w1), is_world(w2))` might work but needs careful testing.

## Constraint Restructuring: Grounding for Small M

### Grounding `capped_skolem_abundance_constraint`

**Current form** (2 quantified vars + 1 nested quantifier):
```
ForAll [src, shift]:
  is_world(src) AND in_bounds(src, shift) AND shift != 0 ->
  is_world(shift_of(src, shift)) AND intervals_shifted AND
  ForAll [time]: time_in_src AND time+shift_in_target ->
    world_fn(shift_of(src,shift))[time+shift] == world_fn(src)[time]
```

**Proposed grounded form** (1 quantified var, no nested quantifier):

For M=3, there are 3 intervals and 6 valid (interval, shift) pairs:
- `([-2,0], +1)`, `([-2,0], +2)`, `([-1,1], +1)`, `([-1,1], -1)`, `([0,2], -1)`, `([0,2], -2)`

For each pair, e.g., `(interval=[-2,0], shift=+1, target=[-1,1])`:
```python
ForAll [src]:
  (is_world(src) AND world_interval_start(src)==-2 AND world_interval_end(src)==0) ->
  is_world(shift_of_capped(src, 1)) AND
  world_interval_start(shift_of_capped(src, 1)) == -1 AND
  world_interval_end(shift_of_capped(src, 1)) == 1 AND
  world_fn(shift_of_capped(src, 1))[-1] == world_fn(src)[-2] AND
  world_fn(shift_of_capped(src, 1))[0] == world_fn(src)[-1] AND
  world_fn(shift_of_capped(src, 1))[1] == world_fn(src)[0]
```

**Constraint counts by M**:

| M | Intervals | Valid (interval, shift) pairs | Concrete state equalities per pair | Total equalities |
|---|-----------|------------------------------|------------------------------------|-----------------|
| 3 | 3         | 6                            | 3                                  | 18              |
| 4 | 4         | 12                           | 4                                  | 48              |
| 5 | 5         | 20                           | 5                                  | 100             |

**Benefits**:
1. Eliminates `shift` as a quantified integer variable (the main MBQI trigger)
2. Eliminates the nested `ForAll [time]` quantifier entirely
3. Concrete integer values (time indices) guide E-matching to fire only on relevant terms
4. Reduces from `ForAll [Int, Int]` to `ForAll [Int]` per constraint
5. Generates only M specific constraints instead of one open-ended one

**Implementation**: New method `build_grounded_abundance_constraints()` returning a list of M*shifts ForAll formulas, replacing the single `capped_skolem_abundance_constraint()` call in `build_frame_constraints()`.

### Grounding `world_uniqueness`

**Current form** (ForAll/Exists over integer domain):
```
ForAll [w1, w2]:
  is_world(w1) AND is_world(w2) AND w1 != w2 ->
  Exists [t]: is_valid_time(t) AND ... AND state[w1][t] != state[w2][t]
```

**Proposed grounded form** (Exists replaced by concrete Or):

For worlds with the same interval `[a, b]`:
```python
ForAll [w1, w2]:
  (is_world(w1) AND interval(w1)==[a,b] AND is_world(w2) AND interval(w2)==[a,b] AND w1!=w2) ->
  Or(
    world_fn(w1)[a] != world_fn(w2)[a],
    world_fn(w1)[a+1] != world_fn(w2)[a+1],
    ...
    world_fn(w1)[b] != world_fn(w2)[b]
  )
```

For worlds with different intervals, they differ by definition at interval boundaries (since `valid_array_domain` constrains arrays to return undefined values outside intervals). However, the current `is_valid_time_for_world` guard in the Exists requires both worlds to have the same time in domain -- this makes the grounded Or safe.

**Benefit**: Eliminates the Exists quantifier from world_uniqueness, converting MBQI's most expensive operation into pure E-matching on concrete terms.

**Constraint counts**: M intervals, each needing one ForAll constraint with an Or of M disjuncts. Total: M constraints per M (manageable).

### Interaction Between Grounded Abundance and World Uniqueness

The amplification loop described above is broken when abundance is grounded:

1. `build_grounded_abundance` fires only when E-matching sees `is_world(src) AND world_interval_start(src)==k` for specific k values
2. No new shifts are inferred beyond the concrete set
3. The Skolem function `shift_of_capped(src, k)` with concrete k creates typed ground terms, not open-ended ones
4. `world_uniqueness` with grounded Or stops requiring MBQI witness search

## Specific Recommendations

### Rank 1: Ground `capped_skolem_abundance_constraint` [HIGHEST IMPACT]

**Action**: Add `build_grounded_abundance_constraints()` method to `BimodalSemantics`:
- Iterate over all valid `(interval, shift)` pairs for the given M
- For each pair, create `ForAll [src]: ...` with concrete integer time indices in the conclusion
- Replace the `skolem_abundance` call in `build_frame_constraints()` with the grounded list

**Expected impact**: Eliminates the most expensive quantifier (nested ForAll over integers), reducing memory usage by an estimated 50-70% for M=4 examples.

**Regression risk**: LOW. The grounded form is logically equivalent to the original -- it asserts the same facts using concrete values instead of universally quantified ones. The Skolem function `shift_of_capped` is preserved.

**Code sketch**:
```python
def build_grounded_abundance_constraints(self):
    """Ground the abundance constraint by enumerating all valid (interval, shift) pairs."""
    constraints = []
    shift_of_capped = z3.Function(
        'shift_of_capped', self.WorldIdSort, self.TimeSort, self.WorldIdSort
    )
    intervals = self.generate_time_intervals(self.M)

    for (start, end) in intervals:
        for delta in range(-(2*self.M-1), 2*self.M):
            if delta == 0:
                continue
            new_start = start + delta
            new_end = end + delta
            if not (-self.M + 1 <= new_start and new_end <= self.M - 1):
                continue
            # Concrete constraint for this (interval, shift) pair
            src = z3.Int(f'grounded_src_{start}_{end}_{delta}')
            target = shift_of_capped(src, z3.IntVal(delta))
            # Build concrete state equalities at each time point
            state_eqs = []
            for t in range(start, end + 1):
                t_val = z3.IntVal(t)
                shifted_t = z3.IntVal(t + delta)
                state_eqs.append(
                    z3.Select(self.world_function(target), shifted_t) ==
                    z3.Select(self.world_function(src), t_val)
                )
            body = z3.Implies(
                z3.And(
                    self.is_world(src),
                    self.world_interval_start(src) == z3.IntVal(start),
                    self.world_interval_end(src) == z3.IntVal(end),
                ),
                z3.And(
                    self.is_world(target),
                    self.world_interval_start(target) == z3.IntVal(new_start),
                    self.world_interval_end(target) == z3.IntVal(new_end),
                    *state_eqs
                )
            )
            constraints.append(z3.ForAll([src], body))
    return constraints
```

### Rank 2: Ground `world_uniqueness` Exists [HIGH IMPACT]

**Action**: Replace `world_uniqueness` with grounded per-interval ForAll constraints:
- For each interval `[a, b]`, create `ForAll [w1, w2]` with concrete Or over times a..b
- For worlds with different intervals, use a structural argument (different interval start/end suffices)

**Expected impact**: Eliminates MBQI's most expensive witness-search operation. Estimated additional 20-40% memory reduction beyond Rank 1.

**Regression risk**: LOW for same-interval worlds. The different-interval case needs careful handling to avoid regressions.

### Rank 3: Add E-matching pattern to `world_uniqueness` [MODERATE IMPACT, SAFE]

If full grounding of `world_uniqueness` is too risky, add an E-matching pattern:
```python
z3.ForAll([world_one, world_two], ...,
    patterns=[z3.MultiPattern(is_world(world_one), is_world(world_two))])
```

This limits MBQI to only proposing world pairs that are already ground terms (known worlds), preventing unbounded world ID generation.

**Expected impact**: 10-20% memory reduction.

**Regression risk**: MODERATE. If the pattern is too restrictive, MBQI may miss needed world pairs for theorem proofs.

### Rank 4: Reduce `max_memory` from 4096 MB to 1024 MB [FAST WIN]

**Action**: Change in `Z3SolverAdapter._configure_quantifier_mode()`:
```python
self._solver.set('max_memory', 1024)  # 1 GB instead of 4 GB
```

**Expected impact**: Prevents Z3 from consuming more than 1 GB per solver instance. Earlier unknown returns for OOM examples, preserving system memory for concurrent processes.

**Regression risk**: LOW if most examples fit in 1 GB. If any hard examples genuinely need 1-4 GB, they will start returning `unknown` instead of eventually finding a solution. Given that BX7 examples have 60s timeouts, 1 GB may be too conservative; 2048 MB is a safer compromise.

### Rank 5: Add `smt.mbqi.max_cexs` limit [SAFE, SMALL IMPACT]

```python
self._solver.set('smt.mbqi.max_cexs', 50)  # Limit counterexamples per MBQI round
```

This limits how many candidate substitutions MBQI generates per round, bounding ground term growth. Lower risk than `qi.max_instances` but requires testing.

## Summary Table

| Recommendation | Impact | Risk | Effort |
|----------------|--------|------|--------|
| Ground `capped_skolem_abundance` | High (50-70%) | Low | Medium |
| Ground `world_uniqueness` Exists | High (20-40%) | Low-Med | Medium |
| Pattern on `world_uniqueness` | Medium (10-20%) | Moderate | Low |
| Reduce max_memory to 2048 MB | Medium | Low | Trivial |
| Add `smt.mbqi.max_cexs` | Low | Low | Trivial |

The most impactful path is to implement Rank 1 (ground abundance) first, verify no regressions across the full 43-test bimodal suite, then attempt Rank 2 (ground world_uniqueness). Together these should eliminate OOM kills for the BX5-BX13 examples (M=4) and significantly reduce memory pressure for BX7 (M=5, N=4) -- the most expensive case.

## Files Investigated

- `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py` - All frame constraint implementations
- `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` - Quantifier usage in temporal/modal operators
- `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/examples.py` - BX5-BX13, BX7 example definitions
- `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/solver/z3_adapter.py` - Current max_memory=4096 configuration
- `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/utils/context.py` - isolated_z3_context() implementation
- `/home/benjamin/Projects/Logos/ModelChecker/specs/097_optimize_build_frame_constraints/summaries/01_optimize-frame-constraints-summary.md` - Task 97 findings and deviations
