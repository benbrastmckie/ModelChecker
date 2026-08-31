# Phase 1 Handoff: Baseline capture and RED tests for the source selector

**Status**: COMPLETED

## What was done

- Recorded the pre-change packaging-suite baseline: `106 passed, 4 skipped` (skip reasons: two
  theories with no on-disk `notebooks/` directory -- pre-existing, unrelated to this task).
  Written to `baselines/01_packaging-suite-baseline.md`.
- Created `code/tests/packaging/test_install_source_selection.py`, marked `packaging`, with RED
  tests for the four pure helpers Phase 2 will add to `conftest.py`:
  `_resolve_install_source()`, `_resolve_install_version(source)`, `_pypi_json_api_url(source)`,
  `_pip_install_args(source, version, wheel_path=None)`.

## Verification

- New module fails collection with `ImportError: cannot import name
  'MODEL_CHECKER_PACKAGING_INSTALL_SOURCE' from 'tests.packaging.conftest'` -- the right reason
  (missing helper/constant), not an unrelated import error.
- Full suite minus the new module: `106 passed, 4 skipped in 98.90s` -- identical to baseline.

## Deviations

None. Followed the plan's Phase 1 task list and helper signatures as specified, with one
clarifying addition not spelled out in the plan: `_pip_install_args` takes an optional
`wheel_path` keyword (only required for the `local` branch) rather than a bare positional,
since `testpypi`/`pypi` calls have no wheel path to pass.

## Next phase

Phase 2: implement the four helpers (plus the two env-var name constants and
`_pyproject_version()`/`_latest_published_version()`) in `code/tests/packaging/conftest.py` to
turn this RED module GREEN, with no fixture rewiring yet.
