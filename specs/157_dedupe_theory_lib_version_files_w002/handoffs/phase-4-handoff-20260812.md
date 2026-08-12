# Phase 4 Handoff — Stop shipping and delete the four VERSION files

**Status**: COMPLETED

## What changed
- `code/pyproject.toml`: removed `"VERSION",` from `[tool.setuptools.package-data]`'s `"*"`
  allowlist and dropped `VERSION` from the mirroring comment at (former) line 71.
- `code/MANIFEST.in`: removed `recursive-include src VERSION`.
- Deleted (via `git rm`) the four `VERSION` files:
  `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/VERSION`.

## Pre-edit gate probe
`find code/src/model_checker/theory_lib -name VERSION` returned exactly 4 matches before
deletion (matching the plan's Scope Hypothesis), 0 after.

## Verification
- `find code/src/model_checker/theory_lib -name VERSION` → no output (0 matches).
- `grep -n -w VERSION code/pyproject.toml code/MANIFEST.in` → no matches.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_theory_conformance.py -v`
  → 50 passed (contract already relaxed in Phase 2, so this still passes with the files gone).

## Files touched this phase
- code/pyproject.toml
- code/MANIFEST.in
- code/src/model_checker/theory_lib/bimodal/VERSION (deleted)
- code/src/model_checker/theory_lib/exclusion/VERSION (deleted)
- code/src/model_checker/theory_lib/imposition/VERSION (deleted)
- code/src/model_checker/theory_lib/logos/VERSION (deleted)

## Next
Phase 5: rebuild from scratch and confirm plain `check-wheel-contents` exits 0 with no `--ignore`.
