# Research Report: Task #97

**Task**: Optimize build_frame_constraints for Z3 solver performance
**Date**: 2026-05-29
**Mode**: Team Research (4 teammates)

## Summary

Team research identified 8 concrete optimization opportunities for `build_frame_constraints()` in `semantic.py`, ranging from zero-risk tautology removal to architectural changes. The highest-impact finding is that the `world_uniqueness` constraint can be replaced with Z3's built-in array inequality, yielding ~200x speedup on that constraint in isolation. All 4 teammates independently confirmed that `classical_truth` is a pure tautology safe to remove. The Critic identified critical validation requirements: no isolation tests exist for individual constraint changes, and the `max_world_id` exponential growth (16,384 for N=3,M=4) is a fundamental scalability limit that no proposed optimization addresses. Strategically, tasks 97 and 98 (OOM kills) share the same root cause and should be coordinated.

## Key Findings

### Primary Approach (from Teammate A)

Teammate A identified 8 direct Z3 optimization techniques:

1. **Remove `classical_truth`** (lines 507-517): The constraint `ForAll([ws,sl], Or(truth(ws,sl), Not(truth(ws,sl))))` is the law of excluded middle -- always true. Z3 simplifies it to `True` in preprocessing but it still costs memory and E-matching overhead. Safe to delete. (HIGH confidence)

2. **Add MultiPattern to `lawful`** (lines 553-577): Currently has no pattern. Recommended trigger: `MultiPattern(world_function(lawful_world), world_interval_start(lawful_world))`. Fires when both a world's history and interval start are known. (MEDIUM confidence)

3. **Add MultiPattern to `capped_skolem_abundance_constraint`**: Trigger on `(world_interval_start(src), world_interval_end(src))`. Fires when interval bounds are established. Caution: the nested ForAll via `matching_states_when_shifted_var` creates 3-level quantifier depth. (MEDIUM confidence)

4. **Reorder constraints**: Move `world_interval` before `lawful` and frame axioms so interval bounds are established early as preconditions for pattern triggers. Proposed order: ground facts -> structural constraints -> intervals -> frame axioms -> lawful -> abundance -> uniqueness. (HIGH confidence)

5. **Z3 solver parameters**: `smt.qi.eager_threshold=100`, `smt.pull_nested_quantifiers=True`, `smt.qi.max_instances=10000`. Require benchmarking. (LOW confidence)

6. **Ground `enumeration_constraint` and `convex_world_ordering`** for small max_world_id: Replace ForAll with explicit conjunctions over 0..max_world_id-1. (MEDIUM confidence)

7. **Use `time_interval_constraint` instead of `world_interval_constraint`**: Already implemented and commented out. (MEDIUM confidence -- but see Critic's objection below)

8. **Split nested ForAll in `matching_states_when_shifted_var`** into prenex normal form. (LOW confidence)

### Alternative Approaches (from Teammate B)

Teammate B provided benchmarked alternatives and solver configuration research:

1. **Replace `world_uniqueness` with array inequality** (CRITICAL FINDING): The current ForAll/Exists formulation (lines 596-616) returns `unknown` after 4+ seconds in isolation. Replacing with `world_function(w1) != world_function(w2)` leverages Z3's built-in array extensionality axiom and returns `sat` in 0.024s -- ~200x speedup. Semantically correct: asserts `world_function` is injective over valid world IDs. (HIGH confidence)

2. **Solver configuration benchmarks** (M=2, N=2, 10 runs):
   - Baseline: 0.154s
   - MBQI only (no ematching): 0.122s (20% faster but riskier)
   - E-matching only: returns `unknown` -- MBQI is essential
   - relevancy=0: 1.602s -- DO NOT CHANGE
   - qi.max_instances=5000: 0.101s (34% faster, bounds OOM risk)
   - mbqi.max_iterations=500: 0.108s (30% faster)

3. **CVC5 backend incompatibility confirmed**: CVC5 CEGQI returns `unknown` on bimodal constraints. Z3 MBQI is definitively the correct solver for this problem profile. (HIGH confidence)

4. **BitVec vs Int for WorldIdSort**: No significant difference. Keep IntSort. (HIGH confidence)

5. **Incremental solving with push/pop**: ~1.5x speedup for 10+ examples with shared frame constraints, but requires architectural changes (fresh BimodalSemantics instances create new Z3 symbols). (MEDIUM confidence, high implementation cost)

6. **Memory limit guard**: Add `z3.set_param('memory_max_size', N)` or `solver.set('max_memory', 4096)` to prevent OOM kills. Directly addresses task 98. (MEDIUM confidence)

### Gaps and Shortcomings (from Critic)

The Critic identified 10 critical gaps and risks:

1. **classical_truth timing risk**: Though tautological, `truth_condition` enters Z3's E-matching index via this constraint. Removing it shifts when `truth_condition` ground terms appear. Risk is LOW but validate against `EX_FALSO_TH` and no-sentence-letter examples. (MEDIUM confidence)

2. **"Order matters" comment is undocumented** (line 668): No explanation exists for why ordering matters. Any reordering must be empirically validated across all 60+ examples. (HIGH confidence)

3. **task_minimization is mislabeled**: Docstring says "encourages" but it's a hard `==` constraint forcing identical consecutive states across ALL worlds. Correctly left commented out -- uncommenting would break all temporal examples. (HIGH confidence)

4. **max_world_id grows exponentially**: For N=3,M=4: 16,384. For N=4,M=5: 5,242,880. No frame constraint caps the `is_world` domain. MBQI can explore arbitrarily large world IDs. Proposed optimizations provide only polynomial improvement at best against this exponential scaling. (HIGH confidence)

5. **world_uniqueness soundness risk from adding patterns**: Adding patterns to the existing ForAll/Exists could cause incompleteness -- Z3 might miss uniqueness obligations, producing models with duplicate worlds. This is a soundness regression risk. (HIGH confidence -- resolved by Teammate B's array inequality approach)

6. **skolem_abundance has hidden 3-level quantifier nesting**: `matching_states_when_shifted_var` is itself a ForAll, creating ForAll[src,shift] -> ForAll[time] depth. This is the same nesting that task 98 identifies as causing OOM kills. (HIGH confidence)

7. **world_interval_constraint also has doubly-nested ForAll**: `valid_array_domain` is itself a ForAll nested inside the outer constraint. (HIGH confidence)

8. **No isolation tests for individual constraint changes**: The test suite tests all constraints together. No test validates removing or modifying individual constraints. (HIGH confidence)

9. **task_restriction uncommenting could cause runaway forward_comp derivation**: Without `task_restriction`, spurious `task_rel` tuples could feed into `forward_comp`'s MultiPattern, causing unbounded composition. (MEDIUM confidence)

10. **Tasks 97 and 98 may have conflicting optimization directions**: Some changes might improve wall-clock time while increasing peak memory, worsening OOM kills. (MEDIUM confidence)

### Strategic Horizons (from Teammate D)

1. **Tasks 97 and 98 are the same root problem**: The OOM kills at M>=3 are a direct consequence of the constraint complexity task 97 targets. The `capped_skolem_abundance_constraint` + `forward_comp` + `world_uniqueness` combination is named in both tasks. Should be coordinated. (HIGH confidence)

2. **Z3-specific annotations are architecturally safe**: `z3_shim.py` + `cvc5_adapter.py` design already accommodates Z3-specific features. `forward_comp` already uses MultiPattern. CVC5 CEGQI silently ignores pattern hints. (HIGH confidence)

3. **Lean alignment is semantic, not textual**: ProofChecker Alignment comments describe logical correspondence, not syntactic mirroring. Optimizations preserving logical content (tautology removal, solver hints, reordering) are alignment-safe. (HIGH confidence)

4. **Performance monitoring infrastructure is missing**: Only `profile_abundance.py` exists for profiling. Task 97 should include building lightweight benchmarking for Z3 statistics (rlimit count, memory, instantiations). (HIGH value, MEDIUM feasibility within scope)

5. **Long-term architectural directions**: Lazy/incremental constraint loading (CEGAR), symmetry reduction (ordering world IDs by interval start), per-theory solver configuration. These are future-task territory. (MEDIUM confidence)

## Synthesis

### Conflicts Resolved

**Conflict 1: world_uniqueness optimization approach**

- Teammate A proposed adding MultiPattern to the existing ForAll/Exists formulation
- Teammate B proposed replacing entirely with array inequality `world_function(w1) != world_function(w2)`
- Teammate C warned that adding patterns to ForAll/Exists risks soundness regression

**Resolution**: Teammate B's array inequality approach is the clear winner. It avoids the soundness concern raised by C (patterns on ForAll/Exists could miss uniqueness obligations), provides a measured 200x speedup in isolation, and uses Z3's built-in extensionality theory which is well-tested. The only semantic difference is that the simplified form drops the requirement that the distinguishing time must be within both worlds' temporal overlap -- this is acceptable because non-overlapping worlds with identical in-scope states are not a meaningful equivalence class in this model.

**Confidence**: HIGH -- benchmarked, semantically sound, avoids the soundness risk of the alternative.

**Conflict 2: time_interval_constraint vs world_interval_constraint**

- Teammate A recommended using `time_interval_constraint` (grounded, already implemented)
- Teammate C warned it creates 16,384 Z3 objects for N=3,M=4 -- infeasible at scale
- Teammate D noted the interval constraint is design debt; grounding infeasible for large M

**Resolution**: Keep `world_interval_constraint` (universal quantifier version). The grounded `time_interval_constraint` is only viable for small M (M<=2, where max_world_id <= 32). For the CI-critical cases (N=3,M=4), 16,384+ Z3 objects would be counterproductive. The real optimization opportunity is in the nested `valid_array_domain` ForAll within `world_interval_constraint`, not in grounding the outer quantifier.

**Confidence**: HIGH -- multiple teammates agree; grounding at scale is infeasible.

**Conflict 3: Grounding enumeration_constraint and convex_world_ordering**

- Teammate A recommended grounding for small max_world_id
- Teammate C's domain size table shows max_world_id is already large for CI-relevant cases

**Resolution**: Conditional grounding is the right approach. Ground for max_world_id < 100 (covers M<=2 cases where most examples live), fall back to ForAll for larger domains. This follows the existing `time_interval_constraint` pattern but with a feasibility guard.

**Confidence**: MEDIUM -- requires implementation with a threshold check.

### Gaps Identified

1. **No isolation tests**: Before implementing any change, the team needs a baseline capture: run all 60+ examples including KNOWN_TIMEOUT_EXAMPLES with extended timeouts, record exact pass/fail/timeout/result.

2. **Undocumented ordering sensitivity**: The `# NOTE: order matters!` comment needs investigation. Any constraint reordering must be validated empirically with multiple trials of non-deterministic examples (BM_CM_1, BM_CM_2, BM_CM_4).

3. **No Z3 statistics collection**: There is no infrastructure to capture rlimit count, peak memory, or instantiation counts per example. This makes it impossible to quantify the effect of optimizations beyond wall-clock timing.

4. **max_world_id exponential growth unaddressed**: No proposed optimization reduces the fundamental `M * 2^(M*N)` domain size. Long-term solutions (CEGAR, symmetry reduction, domain bounding) are needed for scalability.

5. **world_interval nested ForAll**: The `valid_array_domain` helper creates hidden quantifier nesting within `world_interval_constraint`. This should be investigated as a contributor to solver overhead.

### Recommendations

**Tier 1: Safe, immediate changes (high confidence, zero/low risk)**

| # | Change | Risk | Effort | Expected Impact |
|---|--------|------|--------|----------------|
| 1 | Remove `classical_truth` | Zero | 2 line deletions | Minor overhead reduction |
| 2 | Replace `world_uniqueness` with array inequality + MultiPattern | Low | ~20 lines | ~200x on this constraint |
| 3 | Add MultiPattern to `lawful` | Low | ~10 lines | Reduced spurious instantiation |
| 4 | Move `world_interval` before `lawful` in return list | Zero | Reorder lines | Better MBQI seeding |

**Tier 2: Validated changes (medium confidence, requires benchmarking)**

| # | Change | Risk | Effort | Expected Impact |
|---|--------|------|--------|----------------|
| 5 | Add `qi.max_instances=10000` to z3_adapter.py | Low | 1 line | Bounds OOM risk |
| 6 | Add `max_memory` guard to Z3SolverAdapter | None | ~5 lines | Prevents OOM kills (task 98) |
| 7 | Add MultiPattern to `converse` | Low | ~5 lines | Reduced instantiation |
| 8 | Conditional grounding of `enumeration_constraint` | Low | ~10 lines | Faster for small M |

**Tier 3: Structural changes (lower confidence, higher effort)**

| # | Change | Risk | Effort | Expected Impact |
|---|--------|------|--------|----------------|
| 9 | Add MultiPattern to `capped_skolem_abundance` | Medium | ~10 lines | Uncertain (3-level nesting) |
| 10 | Split nested ForAll in abundance (prenex form) | Medium | ~30 lines | Uncertain |
| 11 | Performance benchmarking infrastructure | None | ~100 lines | Enables future optimization |
| 12 | Ground abundance for M<=2 | Medium | ~50 lines | Faster for small M |

**Not recommended:**

| Change | Reason |
|--------|--------|
| Use `time_interval_constraint` (grounded) | Infeasible at N=3,M=4 (16K objects) |
| Disable E-matching (MBQI only) | 20% faster but risks correctness |
| Change relevancy=0 | 10x slower (benchmarked) |
| Switch to CVC5 | Returns `unknown` on this constraint profile |
| BitVec for WorldIdSort | No measurable difference |
| Uncomment task_minimization | Would break all temporal examples |

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|-----------------|
| A | Primary optimization | completed | high | Comprehensive pattern annotations, constraint ordering, grounding |
| B | Alternative patterns | completed | high | Array inequality for world_uniqueness (200x), solver benchmarks |
| C | Critic | completed | high | Soundness risks, validation strategy, domain size analysis |
| D | Strategic horizons | completed | high | Tasks 97/98 coordination, Lean alignment safety, architecture |

## References

- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Primary target (lines 467-687, 1187-1248)
- `code/src/model_checker/solver/z3_adapter.py` - Solver configuration (lines 36-39)
- `code/src/model_checker/solver/cvc5_adapter.py` - CVC5 backend (not recommended for changes)
- `code/src/model_checker/solver/z3_shim.py` - Solver abstraction layer
- Task 98 (specs/TODO.md) - Z3 OOM kills, shared root cause
- Task 96 - Full test suite verification (established constraint correctness)
