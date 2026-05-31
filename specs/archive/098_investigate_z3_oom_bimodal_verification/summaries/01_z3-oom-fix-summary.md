# Implementation Summary: Task #98

- **Task**: 98 - Investigate Z3 OOM kills during bimodal theorem verification
- **Status**: COMPLETED
- **Session**: sess_1780110528_g5f
- **Date**: 2026-05-29

## What Was Implemented

Task 97 already addressed the root OOM problem by adding `max_memory=4096` to `Z3SolverAdapter._configure_quantifier_mode()`. This task investigated whether constraint grounding could further reduce memory usage and verified that the full bimodal test suite passes without regressions.

### Phase 1: Grounded Abundance Constraints (Tested, Reverted)

Added `build_grounded_abundance_constraints()` to `BimodalSemantics` in `semantic.py`. This method generates one `ForAll[src]` constraint per valid (interval, shift) pair (6 for M=3, 12 for M=4, 20 for M=5), replacing the single `ForAll[src, shift] -> ForAll[time]` in `capped_skolem_abundance_constraint()`.

Testing revealed the grounded form caused regressions:
- BM_CM_1 (M=2, SAT): 9s -> 15s timeout (eager E-matching creates more ground terms than lazy MBQI)
- BM_TH_1/2 (M=3, UNSAT): 30s -> 75s+ timeout (same root cause)

Root cause: E-matching fires for ALL valid shifts per world immediately when the guard triggers (`is_world(w) AND world_interval_start(w)==k`). MBQI is lazy and only instantiates when the current model is a counterexample to the quantifier. For these problems, MBQI's laziness is a feature, not a bug.

Decision: Reverted `build_frame_constraints()` to use `capped_skolem_abundance_constraint()`. The method `build_grounded_abundance_constraints()` is preserved in code for future reference.

### Phase 2: World Uniqueness Grounding (Skipped)

Given Phase 1's findings that eager grounding is counterproductive for these constraint patterns, Phase 2 (grounding the `world_uniqueness` Exists quantifier) was skipped. The same fundamental issue would apply.

### Phase 3: Test Suite Verification

Full bimodal test suite results:
- Unit tests: 43/43 pass (56s total)
- E2E CLI tests: 1/1 pass (1.4s)
- BX7 (N=4, M=5): 0.1s via max_memory guard (returns unknown immediately)
- BM_CM_1/2/4 countermodel examples: pass in 7s/0.6s/0.2s respectively
- No earlyoom kills observed

### Phase 4: Z3 Parameter Evaluation

Evaluated `smt.mbqi.max_cexs=50` but did not add it -- max_memory=4096 is sufficient. Documented the evaluation in z3_adapter.py comments.

## Files Modified

- `code/src/model_checker/theory_lib/bimodal/semantic.py`:
  - Added `build_grounded_abundance_constraints()` (not called, for reference)
  - Updated `build_frame_constraints()` docstring with Task 98 investigation note
  - Updated `capped_skolem_abundance_constraint()` docstring with experimental findings
  - Minor docstring corrections from pre-existing Task 97 state

- `code/src/model_checker/solver/z3_adapter.py`:
  - Added documentation comment about `smt.mbqi.max_cexs` evaluation

## Plan Deviations

- **Phase 1**: `build_grounded_abundance_constraints()` was implemented and tested but reverted from active use due to regressions. The method is preserved in code as documentation of the approach.
- **Phase 2**: Skipped based on Phase 1's empirical finding that eager grounding is counterproductive.
- **Phase 4**: No parameter changes made -- current configuration (max_memory=4096) is sufficient and correct.

## Key Finding

The research hypothesis (grounding eliminates MBQI's unbounded instantiation) was incorrect in practice. Z3's lazy MBQI is actually beneficial for both SAT and UNSAT on these constraint patterns because:
1. For SAT: MBQI only instantiates quantifiers when needed to extend a potential model
2. For UNSAT: MBQI terminates as soon as it proves no ground-term extension can satisfy the formula

Eager E-matching creates ALL ground terms immediately, which paradoxically increases the solver's work. The OOM issue was already handled by `max_memory=4096` from Task 97, which causes Z3 to return `unknown` gracefully instead of consuming the OS's memory.
