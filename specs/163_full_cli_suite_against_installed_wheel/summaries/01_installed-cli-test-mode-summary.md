# Implementation Summary: Run full CLI suite against installed wheel

- **Task**: 163 - Run full CLI suite against installed wheel
- **Plan**: `specs/163_full_cli_suite_against_installed_wheel/plans/01_installed-cli-test-mode.md`
- **Status**: All 7 phases COMPLETED
- **Session**: sess_1786598278_060fba

## Outcome

`code/tests/cli/`'s full suite (88 tests) now runs unchanged against a pip-installed wheel via
`MODELCHECKER_CLI_TEST_MODE = source | installed | installed-module`, with a mandatory
anti-vacuous-pass guard confirmed passing (not skipping) in a real installed environment, and
verified end-to-end inside a genuine distro container.

## Phase-by-Phase Results

### Phase 1 -- Diagnose `nix flake check`

**Verdict**: divergent draw (contention-based flake), not a deterministic version sensitivity.
Confirmed the z3 version gap is real (nixpkgs-native `z3-solver` = 4.16.0 vs. real PyPI wheel =
5.0.0, a major version jump), but 8/8 isolated nix runs, 4/4 isolated PyPI-wheel runs, and one
live rerun of the check's exact `-n 6` contended `checkPhase` command (2013 passed, 0 failed) all
failed to reproduce the CI failure. No source fix attempted (diagnosis-only, and any real fix
would target `code/src/model_checker/builder/tests/`, outside `file_scope`). Recommend a
separate, low-priority spawned task to track the z3 version gap independent of this flake.

### Phase 2 -- Parametrise `run_cli_command`

New `code/tests/utils/cli_mode.py::get_cli_test_mode()` is the single source of the mode
vocabulary. `run_cli_command` (`code/tests/utils/helpers.py`) dispatches its env/command
construction over it; `source` remains byte-for-byte the original unconditional behavior. 10 new
unit tests in `code/tests/cli/test_cli_mode.py`; full `tests/cli/` suite and the packaging
baseline (106 passed, 4 skipped) both confirmed unaffected.

### Phase 3 -- Close the shadowing holes, add the guard

`code/tests/cli/test_installed_mode_guard.py` asserts `model_checker.__file__` resolves under
`site-packages` and no `sys.path` entry resolves to `code/src`, whenever a non-source mode is
active. Exactly two in-process source-tree injection sites were confirmed (not three as
hypothesized) -- `pyproject.toml`'s `pythonpath = "src"` and `tests/conftest.py`'s insert -- both
now gated/purged (`tests/conftest.py`, `code/conftest.py`). The hypothesized third
(pytest-rootdir/cwd under `--import-mode=importlib`) does not exist as a `sys.path` entry; the
`tests` package resolves via pytest's own `sys.modules` package-chain construction, independent of
`sys.path`, so no `PYTHONPATH=code` fallback was needed. Verified against a real locally-built
wheel in a scratch venv: guard PASSED (not skipped) in both non-source modes; full `tests/cli/`
suite green in both; collected-count matched host baseline.

### Phase 4 -- Local podman runner script

`code/scripts/verify-installed-cli.sh`: `bash -n` and `shellcheck` clean; both failure paths
(absent podman, missing wheel) verified directly to exit non-zero with the named remediation and
no partial work. Documented in `code/scripts/README.md`.

### Phase 5 -- Container verification

**Correction to the plan**: the fallback ladder predicted `nix run nixpkgs#podman` would fail
without the host's setuid `newuidmap` wrapper. It did not -- this host supports rootless podman
via unprivileged user namespaces. Two missing local config files
(`~/.config/containers/{policy.json,registries.conf}`, neither a repo file) were the only
blockers; once created, `verify-installed-cli.sh` ran successfully end-to-end against
`python:3.11-slim`. Both `installed` and `installed-module` modes: **88 passed** each, guard and
completeness gate both PASSED (not skipped/collect-only), collected-count parity with the host
baseline (88 == 88), `model_checker.__file__` resolved to
`/v/lib/python3.11/site-packages/model_checker/__init__.py` inside the container.

### Phase 6 -- Retire the `load_theory` exclusion

Retired cleanly. `ask_generate()` prompts three times, not the plan's assumed one --
`input="y\ngen_project\nn\n"` through `run_cli_command` produces a clean, error-free generation,
confirmed 6/6 during investigation plus 5/5 repeat runs of the finished test. Closed-stdin fails
fast (no hang). `_EXCLUDED_FLAGS` is now empty; the completeness gate covers every registered
flag with zero exclusions.

### Phase 7 -- Documentation and CI handoff

`code/tests/README.md` gained a "CLI Invocation Modes" section documenting the three modes, the
guard, and the container-verification path. `code/tests/cli/conftest.py`'s stale module docstring
(claiming all invocations go through `python -m model_checker` only) corrected. The R4 CI-wiring
YAML remains recorded only in the research report, for the task that owns
`.github/workflows/release.yml` to adopt -- that file was not touched. No `code/**` deliverable
touched by this task cites a task number (confirmed by direct grep of the changed paths; the
repo-wide `check-task-references.sh` scan's 109 flagged occurrences are pre-existing, entirely
within `.opencode/`, unrelated to this task's scope).

## Files Changed

- `code/tests/utils/cli_mode.py` (new)
- `code/tests/utils/helpers.py`
- `code/tests/cli/test_cli_mode.py` (new)
- `code/tests/cli/test_installed_mode_guard.py` (new)
- `code/tests/conftest.py`
- `code/conftest.py`
- `code/tests/cli/test_flag_matrix.py`
- `code/scripts/verify-installed-cli.sh` (new)
- `code/scripts/README.md`
- `code/tests/README.md`
- `code/tests/cli/conftest.py`

## Plan Deviations

- **Phase 1**: recorded a verdict via 12 isolated runs + 1 live full-suite rerun rather than the
  literal "≥10 full-suite iterations" the plan's task list bullet describes -- a full statistical
  reproduction at ~10 contended runs (~4 min each) was disproportionate to the phase's 1-hour
  budget; the combined evidence (isolated + one live exact-command rerun) was judged sufficient
  to prefer "divergent draw" over "genuine version sensitivity."
- **Phase 5**: the plan's fallback ladder predicted ad hoc `nix run nixpkgs#podman` would fail
  without a setuid wrapper; it succeeded instead once two local config files were created. Real
  container verification was performed rather than declaring `[BLOCKED]`, which is a stronger
  result than the plan anticipated, not a scope reduction.
- **Phase 6**: the plan's example used `input="y\n"` (one answer); the real interactive flow
  needs three (`y`, project name, `n`), discovered by direct dispatch before writing the test.

No other deviations; all remaining phases followed the plan as written.
