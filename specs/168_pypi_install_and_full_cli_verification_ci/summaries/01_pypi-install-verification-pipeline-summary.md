# Implementation Summary: PyPI Install and Full-CLI Verification Pipeline

- **Task**: 168 - Pypi install and full cli verification ci
- **Plan**: `plans/01_pypi-install-verification-pipeline.md`
- **Status**: All 6 phases completed

## What was built

`code/tests/packaging/conftest.py`'s `installed_venv` fixture is now parameterized over install
source via two env vars (`MODEL_CHECKER_PACKAGING_INSTALL_SOURCE` / `_INSTALL_VERSION`), with
the default (unset) path byte-for-byte unchanged. That one parameterization is now consumed
twice in CI: a new `verify-pypi` 3x3-OS/Python confirmation matrix in `.github/workflows/release.yml`
running after `publish-pypi` and gating `github-release`, and a new
`.github/workflows/pypi-smoke.yml` (daily `schedule:` + `workflow_dispatch:`, opt-in
failure-gated tmate) that answers "is the currently published artifact still installable and
runnable today" independent of any release event.

## Design decisions as implemented

- **D1 (env-var selector)**: `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE` (`local`/`testpypi`/`pypi`,
  default `local`) and `MODEL_CHECKER_PACKAGING_INSTALL_VERSION` (unset/`latest`/explicit
  literal), both implemented exactly as specified, with `pytest.fail` naming the offending value
  for an unrecognized source.
- **D2 (version resolution)**: `_pyproject_version()` parses `code/pyproject.toml` for the
  default pin; `_latest_published_version(source)` queries the PyPI/TestPyPI JSON API via
  `urllib.request` for the `latest` sentinel; an explicit literal is used verbatim. All three
  paths independently verified live (see Verification below).
- **D3 (index URLs/retry)**: `_pip_install_args` mirrors `verify-testpypi`'s dual-index-URL
  shape for `testpypi` and default-index `==`-pin for `pypi`; `installed_venv`'s non-local
  branch retries 10x/15s on install failure, mirroring `verify-testpypi`'s loop.
- **D4 (byte-level tests not applicable in index mode)**: implemented as planned --
  `request.getfixturevalue("built_artifacts")` lazily in the `local` branch only, plus a
  `pytest_collection_modifyitems` skip for any item whose fixture closure includes
  `built_artifacts`, when source is non-local. **One implementation deviation from the plan's
  literal wording**, discovered and resolved in Phase 3: the hook reads the raw env var
  directly rather than calling `_resolve_install_source()`, because `pytest.fail()` raised
  from inside a collection hook (as opposed to a test/fixture) surfaces as a pytest
  `INTERNALERROR` rather than a normal red test -- confirmed directly by running the suite with
  an invalid source value before the fix, and again cleanly after it. Strict validation and the
  loud, offending-value-naming failure remain solely in `_resolve_install_source()`, exercised at
  fixture-setup time by every `installed_venv`-consuming test; the hook's own behavior on an
  invalid value is unaffected in substance (still treated as non-local, still skips the
  byte-level tests) -- only *how* the loud failure surfaces changed, for the better.
- **D5 (`release.yml` job graph)**: `verify-pypi`, `needs: [publish-pypi]`, `fail-fast: false`,
  the same 3x3 matrix as `test-and-release`; `github-release`'s `needs:` extended to
  `[publish-pypi, verify-pypi]`. `github-release` carried no explicit `if:` before this change,
  so no `if:` edit was needed -- confirmed by re-reading the file before editing, per the plan's
  Scope Hypothesis.
- **D6 (`pypi-smoke.yml` tmate shape)**: `mxschmitt/action-tmate@v3`, `if: ${{ failure() &&
  inputs.debug_tmate }}`, `debug_tmate` defaults `false`, step-level `timeout-minutes: 15`
  alongside the job-level `timeout-minutes: 20`.
- **D7 (`and not unstable`)**: present in both new pytest invocations (`verify-pypi` and
  `pypi-smoke`).
- **NixOS clause**: `_add_cxx_runtime_to_env(env)` remains unconditional on every `installed_venv`
  branch, unchanged in substance; `handle_known_venv_libz3_link_failure` was not touched.

## Verification (observed output, not claims)

All commands run from `code/` with `PYTHONPATH=src` (this development host has no installed/
editable `model_checker`; CI's `packaging.yml`/`release.yml` invoke the equivalent command
without an explicit `PYTHONPATH` since they run against the installed package).

| Check | Command | Result |
|---|---|---|
| Pre-change baseline (Phase 1) | `pytest tests/packaging/ -v -m packaging -rs` | `106 passed, 4 skipped` (skip reasons: 2 theories with no on-disk `notebooks/`) |
| Helpers added, not wired (Phase 2) | same | `119 passed, 4 skipped` (106 + 13 new selector-helper tests) |
| Default path after fixture rewiring (Phase 3) | same | `119 passed, 4 skipped` -- identical, no regression |
| Default path, final re-check (Phase 6) | same | `119 passed, 4 skipped` -- identical, no regression |
| Invalid `INSTALL_SOURCE` value | `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=bogus pytest tests/packaging/test_entry_point.py -v` | 3 clean `ERROR ... Failed: Unrecognized MODEL_CHECKER_PACKAGING_INSTALL_SOURCE='bogus'; must be one of ('local', 'testpypi', 'pypi')`, no INTERNALERROR |
| `pypi` index mode, full suite | `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi pytest tests/packaging/ -v -m "packaging and not unstable" -rs` | `26 passed, 97 skipped`; all 97 skips carry the `not applicable for install source 'pypi': ...` reason; no `built_artifacts`/local build triggered |
| `pypi` end-to-end from NixOS host, 13 CLI tests (Phase 6) | `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi pytest tests/packaging/test_entry_point.py tests/packaging/test_cli_console_script.py tests/packaging/test_generate_then_execute.py -v -m "packaging and not unstable"` | `13 passed` against the real published `model-checker` 1.3.7 (exact pin, `INSTALL_VERSION` unset -- D2.1), including `generate_then_execute` across every registered theory (bimodal/logos/imposition/exclusion), through `_add_cxx_runtime_to_env`'s NixOS repair, not the `libz3` skip backstop |
| `latest` version resolution (D2.2) | `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=pypi MODEL_CHECKER_PACKAGING_INSTALL_VERSION=latest pytest tests/packaging/test_entry_point.py -v -m "packaging and not unstable"` | `3 passed` -- resolved live via the PyPI JSON API |
| `testpypi` path (D3) | `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE=testpypi pytest tests/packaging/test_entry_point.py -v -m "packaging and not unstable"` | `3 passed` -- TestPyPI currently carries `1.3.7`, exact pin resolved and installed cleanly |
| CI-contract suite | `pytest tests/ci/ -v` | `83 passed` |
| Workflow YAML validity | `python -c "import yaml; yaml.safe_load(open(...))"` for both `.github/workflows/release.yml` and `.github/workflows/pypi-smoke.yml` | both parse clean |
| `actionlint` | `which actionlint` | not installed on this host; YAML parse + scripted structural assertions used as the plan's documented fallback for both files |
| `release.yml` structural assertions | scripted (`verify-pypi.needs`, matrix shape, `fail-fast: false`, `github-release.needs`, `github-release` gained no `if:`, `and not unstable` present) | all pass |
| `pypi-smoke.yml` structural assertions | scripted (both triggers, `debug_tmate` default `false`, tmate `if:` shape, tmate `timeout-minutes`, `and not unstable` present) | all pass |
| No unintended `needs:`/`if:` drift | `git diff .github/workflows/release.yml \| grep needs:\|if:` | exactly the two intended `needs:` changes |
| `pypi-smoke.yml` non-gating | `grep -rn 'pypi-smoke' .github/workflows/` | appears only in its own file |

## Deviations from plan

- Phase 3's `pytest_collection_modifyitems` reads the raw env var rather than calling
  `_resolve_install_source()` -- see D4 above. This is a bugfix discovered during Phase 3's own
  implementation, not a scope change: the skip/no-skip *decision* is exactly what the plan
  specified; only the internal mechanism for reading the source value changed, to avoid an
  `INTERNALERROR`.
- No other deviations. All phases followed the plan's task lists as written.

## Follow-ups (deliberately out of file_scope, per the plan's Non-Goals)

1. Fold `test-and-release`'s and `verify-testpypi`'s existing inline shell smoke scripts in
   `.github/workflows/release.yml` onto the now-parameterized `installed_venv` fixture, so all
   post-publish verification in that file goes through one code path. Not done here: those
   scripts already work and are on 158's just-landed gating path; touching them was explicitly
   scoped out as unnecessary churn for this task.
2. Extend `code/tests/ci/test_unstable_deselection_wiring.py`'s scanned-driver list (currently
   `tests.yml`, `flake.nix`, `differential-tests.yml`, `run-oracle-suite.sh`) to also scan
   `release.yml` and the new `pypi-smoke.yml` for the `and not unstable` marker expression.
   `code/tests/ci/` is outside this task's file_scope.
3. Fix `code/docs/development/PYPI_RELEASE_GUIDE.md:149`'s stale `pip index versions` advice
   (flagged originally by task 158). That file is outside this task's file_scope and remains
   unowned.

## Artifacts

- `code/tests/packaging/conftest.py` (modified) - source selector, version resolution,
  parameterized `installed_venv`, collection hook
- `code/tests/packaging/test_install_source_selection.py` (new) - helper contract tests
- `.github/workflows/release.yml` (modified) - `verify-pypi` matrix job; `github-release`
  `needs:` gating
- `.github/workflows/pypi-smoke.yml` (new) - scheduled + dispatchable smoke workflow
- `specs/168_pypi_install_and_full_cli_verification_ci/baselines/01_packaging-suite-baseline.md`
  (new) - pre-change suite baseline
- `specs/168_pypi_install_and_full_cli_verification_ci/handoffs/phase-{1..5}-handoff-20260831.md`
  (new) - per-phase handoffs

## Plan Deviations

- None beyond the one documented above (Phase 3's collection-hook implementation detail).
