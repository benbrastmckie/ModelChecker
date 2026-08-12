# Phase 2 Handoff — Relax the on-disk contract requirements

**Status**: COMPLETED

## What changed
- `code/src/model_checker/builder/project.py`: moved `'VERSION'` from `REQUIRED_COPY_ITEMS` to
  `OPTIONAL_COPY_ITEMS`, with a comment explaining that per-theory versioning is carried by
  `__init__.py`'s `__version__` and the entry remains only to tolerate a third-party theory that
  still carries the file.
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py`: removed `'VERSION'` from
  `REQUIRED_ROOT_ITEMS`.
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md`: amended the Theory Contract
  bullet to drop `VERSION` from the required metadata set and state that per-theory version is
  `__init__.py`'s `__version__`.

## Verification
- `grep -rn -w VERSION code/src/model_checker/theory_lib/*/tests/ code/src/model_checker/theory_lib/*/docs/`
  → no matches (as hypothesized).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_theory_conformance.py -v`
  → 50 passed.
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v` → 232 passed, 75 subtests
  passed.

## Files touched this phase
- code/src/model_checker/builder/project.py
- code/src/model_checker/theory_lib/tests/test_theory_conformance.py
- code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md

## Next
Phase 3: relax the packaging contract assertions (`code/tests/packaging/test_inclusions.py`,
`test_parity.py`). VERSION files are still on disk and still shipped — tree remains green.
