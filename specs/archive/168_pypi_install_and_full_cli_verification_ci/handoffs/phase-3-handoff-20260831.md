# Phase 3 Handoff: Parameterize `installed_venv` and gate the byte-level tests

**Status**: COMPLETED

## What was done

In `code/tests/packaging/conftest.py`:

- `installed_venv` now takes `request` and no longer declares `built_artifacts` directly;
  the `local` branch calls `request.getfixturevalue("built_artifacts")` lazily. `_add_cxx_runtime_to_env(env)`
  is unconditional, before the install, on every branch. Non-local branches resolve the version
  via `_resolve_install_version`, build the pip args via `_pip_install_args`, and install through
  a bounded 10-attempt/15s retry loop, failing via `_provisioning_failure` (attempt count + last
  stderr tail) on exhaustion. In index mode, after install, the fixture asserts the venv's
  `model_checker.__version__` matches the resolved version (stale-index detection).
- Added `pytest_collection_modifyitems`, applying a not-applicable skip marker (naming the
  resolved source) to any collected item whose `fixturenames` includes `built_artifacts`, when
  the (raw, un-validated) install source is non-`local`.
- **One deviation from the plan's literal Phase-2/3 split, documented here**: the collection
  hook reads the raw `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE` env var directly rather than
  calling `_resolve_install_source()`. Calling `pytest.fail()` from inside
  `pytest_collection_modifyitems` (a collection hook, not a test/fixture) surfaces as a pytest
  `INTERNALERROR` rather than a normal red test -- confirmed directly by running the suite with
  `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=bogus`. Strict validation and the loud,
  offending-value-naming failure remain solely in `_resolve_install_source()`, which every
  `installed_venv`-consuming test still exercises at fixture-setup time (confirmed: 3 clean
  `ERROR ... Failed: Unrecognized MODEL_CHECKER_PACKAGING_INSTALL_SOURCE='bogus'; ...` results,
  no INTERNALERROR). An invalid value only affects the hook's skip/no-skip choice (treated as
  non-local), never bypasses validation for a test that actually needs the venv.

## Verification (all commands run from `code/`, `PYTHONPATH=src`)

- **Default path** (both env vars unset): `pytest tests/packaging/ -v -m packaging -rs` ->
  `119 passed, 4 skipped` -- identical to Phase 2's result (Phase 1 baseline `106 passed, 4
  skipped` + the 13 selector-helper tests), same skip reasons. No regression.
- **Invalid-value path**: `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=bogus pytest
  tests/packaging/test_entry_point.py -v` -> 3 clean `ERROR ... Failed: Unrecognized
  MODEL_CHECKER_PACKAGING_INSTALL_SOURCE='bogus'; must be one of ('local', 'testpypi', 'pypi')`
  results, no INTERNALERROR.
- **`pypi` index path** (real published artifact, version unset -> exact pin to
  `code/pyproject.toml`'s `1.3.7`): `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi pytest
  tests/packaging/ -v -m "packaging and not unstable" -rs` -> `26 passed, 97 skipped`. All 97
  skips carry the `not applicable for install source 'pypi': ...` reason across the four
  byte-level modules (`test_build_smoke.py`, `test_exclusions.py`, `test_inclusions.py`,
  `test_parity.py`); 26 + 97 = 123, matching the default path's 119 + 4 total collected item
  count (the notebook-related skips are subsumed into the D4 skip for those parametrizations
  rather than double-counted). No `built_artifacts`/`packaging_toolchain` fixture setup appeared
  in the verbose log -- no local build occurred. This exercised the real published
  `model-checker` 1.3.7 from this NixOS host through `_add_cxx_runtime_to_env`'s repair, not the
  `libz3` skip backstop.
- **`testpypi` path**: `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=testpypi pytest
  tests/packaging/test_entry_point.py -v -m "packaging and not unstable"` -> `3 passed in 6.13s`
  (TestPyPI currently carries `1.3.7`, so the exact-pin default resolved and installed cleanly;
  no fallback needed).
- **`latest` version-resolution path (D2.2) independently**:
  `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi MODEL_CHECKER_PACKAGING_INSTALL_VERSION=latest
  pytest tests/packaging/test_entry_point.py -v -m "packaging and not unstable"` -> `3 passed in
  6.41s` -- resolved via the live PyPI JSON API, not the pyproject.toml pin.

## Next phase

Phases 4 and 5 (independent, both depend only on Phase 3): `verify-pypi` matrix job in
`.github/workflows/release.yml`, and the new `.github/workflows/pypi-smoke.yml`.
