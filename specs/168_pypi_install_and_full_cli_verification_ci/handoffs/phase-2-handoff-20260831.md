# Phase 2 Handoff: Implement the selector and version-resolution helpers

**Status**: COMPLETED

## What was done

Added to `code/tests/packaging/conftest.py`, in a new `# --- Install-source selection and
version resolution (D1/D2/D3) ---` section (no fixture rewiring):

- Constants: `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE`, `MODEL_CHECKER_PACKAGING_INSTALL_VERSION`
  env-var names; `_VALID_INSTALL_SOURCES`; `_LATEST_VERSION_SENTINEL`; `_PYPI_JSON_API_URLS`.
- `_resolve_install_source()`, `_pyproject_version()`, `_pypi_json_api_url(source)`,
  `_latest_published_version(source)` (via `urllib.request`, 30s timeout, loud
  `pytest.fail` on non-200/parse failure), `_resolve_install_version(source)`,
  `_pip_install_args(source, version, wheel_path=None)`.
- Extended the module docstring with the env-var/version-resolution subsection named in the
  plan's Phase 2 tasks.

## Verification

- `tests/packaging/test_install_source_selection.py -v`: 13 passed.
- `tests/packaging/ -v -m packaging -rs`: `119 passed, 4 skipped` -- exactly the Phase 1
  baseline's `106 passed, 4 skipped` plus the 13 new helper tests, same skip reasons. Nothing
  else moved; helpers are pure additions with no call sites yet.

## Deviations

None from the plan's task list. `_pip_install_args`'s `wheel_path` parameter is keyword-only
with a default of `None` (documented in Phase 1's handoff) rather than a bare positional, since
only the `local` branch needs it.

## Next phase

Phase 3: wire these helpers into `installed_venv` (lazy `built_artifacts`, retry loop for
non-local sources, `pytest_collection_modifyitems` not-applicable skip for the four byte-level
modules), with the default (both env vars unset) path proven byte-for-byte unchanged.
