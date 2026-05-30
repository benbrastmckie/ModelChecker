# Phase 3 Handoff: Test Validation and Timeout Tuning

**Date**: 2026-05-29
**Status**: COMPLETED

## Findings

### BM_CM_3 and BM_CM_1 Behavior

Both BM_CM_3 (max_time=2) and BM_CM_1 (max_time=5) time out consistently when
run in isolation AND when run in sequence in the full bimodal suite. This is the
CORRECT behavior after the isolation fix:

- **Before fix**: They would sometimes find countermodels when run after other examples, because Z3's C-level context retained learned lemmas from previous examples, making the search easier.
- **After fix**: Each example runs in a genuinely fresh context with no borrowed knowledge. The searches are harder and exceed the tight timeouts.

Both examples have `expectation: True` in their settings (countermodel expected), which means they are documented as expected to find countermodels. The comment in `examples.py` line 1372 already noted that BM_CM_3 "Doesn't find countermodel if run in isolation."

### Timeout Tuning

Tested BM_CM_3 with max_time=10 and BM_CM_1 with max_time=10 -- both still time out. The searches appear to require substantially more time or different search parameters (larger N/M) to succeed without state leakage. This is a Z3 MBQI nondeterminism issue (Z3 issue #7525) and is beyond the scope of this task.

**Decision**: Leave timeouts as-is. The isolation fix is correct. The BM_CM_3 and BM_CM_1 examples may need to be reclassified or given much larger timeouts in a future task.

### Test Suite

- Updated `test_z3_isolation.py`: Fixed Z3 variable creation to occur inside `isolated_z3_context()` blocks (Z3 variables are context-bound and cannot be shared across context boundaries).
- All 12 isolation/context tests pass.
- Pre-existing failures (unrelated to our changes): `test_attribute_initialization_order` (mock issue), `test_ask_generate_without_subtheories` (missing 'exclusion' theory), `test_memory_limit_handling` (hangs with N=64).
- Logos examples run correctly (24 examples, 11 countermodels, 11 theorems).

## Deviations from Plan

- Timeout tuning was investigated but increasing max_time to 10s did not help BM_CM_3 or BM_CM_1. This is documented above. Timeouts were NOT adjusted in the example files (they would need much larger values).
- Test file `test_z3_isolation.py` needed additional fixes beyond what Phase 2 addressed: Z3 expressions must be created inside isolated_z3_context() blocks.

## Next Phase

Phase 4: Add conftest.py Z3 isolation fixtures.
