# Phase 3 Handoff — Relax the packaging contract assertions

**Status**: COMPLETED

## What changed
- `code/tests/packaging/test_inclusions.py`: removed `"VERSION"` from `REQUIRED_ROOT_FILES`.
- `code/tests/packaging/test_parity.py`: removed `"VERSION"` from `_is_data_path()`'s name set
  and updated the module docstring's parity-definition prose that named it.
- `code/tests/packaging/test_exclusions.py`: left untouched per plan (no `VERSION` reference;
  files still on disk until Phase 4, so no `EXCLUSION_CLASSES` entry is warranted).

## Verification
- `grep -rn -w VERSION code/tests/packaging/` → no matches.
- `PYTHONPATH=code/src pytest code/tests/packaging/test_inclusions.py code/tests/packaging/test_parity.py -v`
  → 78 passed, 4 skipped (skips are the pre-existing notebook-conditional ones).
- Collected-test-count reconciliation: 90 → 82 tests collected across these two files, an 8-test
  drop, matching the plan's expected 4 theories x 2 artifacts = 8 `VERSION` assertions removed.

## Files touched this phase
- code/tests/packaging/test_inclusions.py
- code/tests/packaging/test_parity.py

## Next
Phase 4: stop shipping and delete the four `VERSION` files (now safe — nothing requires or
asserts them). Depends on Phases 2 and 3, both now closed.
