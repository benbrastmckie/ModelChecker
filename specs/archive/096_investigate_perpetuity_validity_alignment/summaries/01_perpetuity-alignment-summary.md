# Implementation Summary: Task #96

- **Task**: 96 - Investigate perpetuity principle validity alignment
- **Status**: [COMPLETED]
- **Session**: sess_1780094455_86573c
- **Plan**: plans/01_perpetuity-alignment.md
- **Date**: 2026-05-29

## Summary

Fixed two compounding semantic divergences in the bimodal ModelChecker that caused spurious countermodels to the perpetuity principles (BM_TH_1: `Box A -> Future A`, BM_TH_2: `Box A -> Past A`). These principles are proven valid in the JPL paper and Lean BimodalLogic formalization. After the fixes, both theorems produce no countermodel, and three previously-timing-out countermodel examples (BM_CM_1, BM_CM_2, BM_CM_4) now reliably find countermodels.

## Phases Completed

### Phase 1: Fix Box Operator Scope Guard [COMPLETED]
Removed the `is_valid_time_for_world` guard from `NecessityOperator.true_at` and `NecessityOperator.false_at` in `operators.py`. Previously, Box quantified only over worlds whose interval contained the evaluation time, but the paper and Lean semantics require Box to quantify over ALL worlds unconditionally (atoms are false outside a world's interval, not the modal quantifier's responsibility).

### Phase 2: Extend Abundance Constraint with Performance Profiling [COMPLETED]
Replaced the +/-1 Skolem abundance constraint with `capped_skolem_abundance_constraint`, which provides time-shifted world copies for all shift amounts that keep the shifted interval within the global time range. Profiled four strategies on BM_TH_1:
- Original +/-1 (still finds countermodel at M=2)
- full_abundance_constraint (existential, timed out at M=3)
- skolem_full_abundance_constraint (Skolem, timed out at M=3)
- capped_skolem_abundance_constraint (Skolem + caps) -- selected, produces no countermodel at M=3

Updated BM_TH_1 and BM_TH_2 settings to M=3 and integrated `capped_skolem_abundance_constraint` as the default in `build_frame_constraints`.

### Phase 3: Validate Perpetuity Principles [COMPLETED]
Updated `examples.py` expectations for BM_TH_1 and BM_TH_2 from `True` (countermodel expected) to `False` (no countermodel expected). Updated comments to document the theorems as valid, aligned with the JPL paper and Lean formalization. BM_TH_1 and BM_TH_2 remain in `KNOWN_TIMEOUT_EXAMPLES` with updated comments explaining they take 30s each at M=3 (too slow for CI but correct behavior).

### Phase 4: Assess Countermodel Examples [COMPLETED]
Evaluated the impact of semantic corrections on previously-timing-out examples:
- BM_CM_1: Now finds countermodel in ~0.8s. Removed from KNOWN_TIMEOUT_EXAMPLES.
- BM_CM_2: Now finds countermodel in ~0.6s. Removed from KNOWN_TIMEOUT_EXAMPLES.
- BM_CM_4: Now finds countermodel in ~3s. Removed from KNOWN_TIMEOUT_EXAMPLES.
- BM_CM_3: Non-deterministic (sometimes <5s, sometimes 10-15s). Kept in KNOWN_TIMEOUT_EXAMPLES.
- TN_CM_2: Still times out. Kept in KNOWN_TIMEOUT_EXAMPLES.

### Phase 5: Full Test Suite Verification and Cleanup [COMPLETED]
- 43 bimodal unit tests pass (all non-timeout examples)
- Integration tests pass for system imports, formula system, and model building sync
- Pre-existing performance test failures in logos theory (N=16 timeout, N=64 segfault) confirmed unrelated to bimodal changes
- Added DEPRECATED docstring headers to `build_abundance_constraint` and `skolem_abundance_constraint`
- Updated `build_frame_constraints` docstring to document capped Skolem strategy, JPL paper alignment, and connection to perpetuity principles
- BM_TH_3 and BM_TH_4 verified passing (BM_TH_5 not in theorem_examples dict; BM_TH_6 does not exist)

## Files Modified

- `code/src/model_checker/theory_lib/bimodal/operators.py` -- Removed `is_valid_time_for_world` guard from `NecessityOperator.true_at` and `NecessityOperator.false_at`
- `code/src/model_checker/theory_lib/bimodal/semantic.py` -- Added `full_abundance_constraint`, `skolem_full_abundance_constraint`, `capped_skolem_abundance_constraint`; updated `build_frame_constraints` to use capped Skolem; added deprecation comments to old methods; updated docstrings
- `code/src/model_checker/theory_lib/bimodal/examples.py` -- Updated BM_TH_1, BM_TH_2 expectations and settings (M=3); updated BM_CM_1, BM_CM_2, BM_CM_4 max_time settings
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` -- Updated KNOWN_TIMEOUT_EXAMPLES (removed BM_CM_1, BM_CM_2, BM_CM_4; kept BM_TH_1, BM_TH_2; added detailed comments)

## Plan Deviations

- BM_TH_1 and BM_TH_2 were KEPT in KNOWN_TIMEOUT_EXAMPLES (plan said to remove them). At M=3, Z3 takes 30s to exhaust the search space. Including them in CI would add 60s+. Updated comments document this as intentional for CI speed, not a semantic issue.
- `can_shift_forward` and `can_shift_backward` were NOT given deprecation comments (plan said to add them if not used by new strategy). These remain used by the deprecated `build_abundance_constraint` and `skolem_abundance_constraint` methods, and those methods' own DEPRECATED docstrings make the deprecation chain clear.
- BM_TH_5 and BM_TH_6 verification was impossible as expected: BM_TH_5 is defined in examples.py but not in `theorem_examples` (pre-existing state), and BM_TH_6 does not exist. BM_TH_3 and BM_TH_4 were verified instead.
