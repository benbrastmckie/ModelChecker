# Implementation Summary: Task #97

- **Task**: 97 - Optimize build_frame_constraints for Z3 solver performance
- **Status**: COMPLETED
- **Session**: sess_1780101648_c73e7e
- **Date**: 2026-05-29

## What Was Implemented

### Phase 1: Baseline Capture
- Captured full bimodal test suite baseline: 43/43 tests passing (~93s)
- Created `specs/097_optimize_build_frame_constraints/baseline_results.txt`
- Created `code/scripts/compare_bimodal_baseline.sh` for future regression comparison

### Phase 2: Tautology Removal and Reordering
- **Removed `classical_truth` tautological constraint**: The constraint `ForAll([world_state, sentence_letter], Or(P, Not(P)))` was always true by the Law of Excluded Middle and added no solver information while wasting E-matching index budget.
- **Moved `world_interval` before `lawful` in return list**: Interval bounds are now established before the lawful axiom fires, enabling better MBQI seeding.
- **Updated docstring** in `build_frame_constraints()` to reflect the removed constraint and new ordering rationale.

### Phase 3: Pattern Annotations (SKIPPED)
- Attempted `MultiPattern` annotations on `lawful` and `converse` constraints.
- Both caused consistent regressions on countermodel examples (BM_CM_2, BM_CM_4).
- Root cause: MultiPattern requires both terms to be in the ground term set before firing, causing missed instantiations needed for SAT (countermodel) search.
- Reverted. The `forward_comp` MultiPattern (pre-existing from before Task 97) is safe because it fires on existing task_rel facts, not world structure axioms.

### Phase 4: Solver Configuration Guards
- **Added `max_memory=4096` MB** per-solver memory limit to `Z3SolverAdapter._configure_quantifier_mode()`. This prevents OOM kills by having Z3 return 'unknown' gracefully when memory exceeds 4 GB, directly mitigating the OOM kills described in task 98.
- **qi.max_instances SKIPPED**: Caused regressions (2 failures) even at 100000 cap. Countermodel examples (BM_CM_2, BM_CM_4) require more instantiations than expected.

### Phase 5: Final Verification and Cleanup
- Removed dead variable `time_interval` assignment, replaced with explanatory comment about the grounded alternative.
- Updated return list comments to be accurate and informative.
- Ran test suite 3 times: 43/43 passing each time (~50s each, vs ~93s baseline = 46% improvement).

## Performance Results

- **Baseline**: 43/43 tests, ~93 seconds
- **After optimization**: 43/43 tests, ~50 seconds
- **Improvement**: ~46% faster (43 seconds saved per full suite run)
- The speedup comes primarily from removing the `classical_truth` tautology (which generated expensive ForAll constraints on atomic sentence letters) and the reordering of `world_interval` before `lawful`.

## Files Modified

- `code/src/model_checker/theory_lib/bimodal/semantic.py` - `build_frame_constraints()` docstring, removed `classical_truth`, reordered constraints, cleaned up dead code
- `code/src/model_checker/solver/z3_adapter.py` - Added `max_memory=4096` MB guard to `_configure_quantifier_mode()`
- `code/scripts/compare_bimodal_baseline.sh` - New baseline comparison script
- `specs/097_optimize_build_frame_constraints/baseline_results.txt` - Captured baseline data

## Plan Deviations

- **world_uniqueness array inequality (Phase 2)**: SKIPPED. Z3 array disequality (`world_function(w1) != world_function(w2)`) was tested but caused 8 regressions (all countermodel examples). The array theory checks all indices, not just the shared interval, conflicting with `valid_array_domain` constraints.
- **lawful MultiPattern (Phase 3)**: SKIPPED. Caused regressions on BM_CM_2, BM_CM_4. Pattern too restrictive for countermodel search.
- **converse MultiPattern (Phase 3)**: SKIPPED. Caused regression on BM_CM_4.
- **qi.max_instances (Phase 4)**: SKIPPED. Even 100000 cap caused regressions on BM_CM_2, BM_CM_4.
- **time_interval variable cleanup**: Removed dead variable assignment (minor deviation from plan description; plan said "verify if needed", we removed the assignment and added a comment).
