# Implementation Summary: Eliminate Wall-Clock-Sensitive Test Flakes and Undiagnosable Hangs

**Plan**: `specs/169_eliminate_wall_clock_sensitive_test_flakes/plans/01_eliminate-wall-clock-test-flakes.md`
**Status**: All 8 phases [COMPLETED]

## What was built

Three defect families made the general CI suite non-deterministic across
`.github/workflows/tests.yml`'s Python 3.10-3.12 matrix and `flake.nix`'s `checks.default`, which
run the same pytest selection under the PyPI `z3-solver` toolchain and the nixpkgs-native Z3
toolchain respectively. All three are now fixed at their root, with executable guards preventing
regression:

1. **Solver-budget flakes** (Phases 1-3): a Z3 UNKNOWN is never reported as a plain
   `model_found=False` again. `BuildExample.get_result()`/`_get_model_structure_data()` and
   `utils/testing.py`'s `TestResultData` now always carry a `timeout` key, independently readable
   from `model_found`. `BuildExample.check_result()` and `ModelDefaults.check_result()` return a
   three-value `"match"`/`"mismatch"`/`"inconclusive"` instead of a boolean, checking timeout
   before the expectation comparison; all Jupyter and `utils/testing.py` call sites were
   migrated. A new, optional, default-off `max_rlimit` setting gives solves a deterministic,
   machine-load-independent Z3 resource-unit budget alongside the wall-clock `max_time`.
2. **Timing-assertion design flakes** (Phase 4): the unbounded `max_time / min_time` ratio
   assertion in `TestPerformanceAndScalabilityScenarios` (which had failed at ratio 17.4 against
   a 5.0 bound, and gets *worse* as the code gets faster) was replaced with a discarded warm-up
   iteration plus an absolute ceiling and a fixed median-plus-slack bound.
3. **Undiagnosable hangs** (Phase 6): both gating pytest invocations now pass
   `--timeout=300 --timeout-method=thread`, so a hang produces a named test and a full
   `faulthandler` stack dump instead of dying to a silent, opaque `timeout-minutes: 20` job
   cancellation (the motivating incident: CI run `32897405646`, 94% progress, 17 minutes of zero
   output, only orphaned workers in the cleanup log).

**Cross-cutting** (Phase 5, discovery continued into Phase 7): a new `xdist_serial` marker
(alongside the existing `performance` marker) removes every wall-clock-asserting test from the
contended `-n 6` xdist pool. Nine tests across six files now carry it and run instead in a new,
second, serial CI pass with no `-n` flag -- both `tests.yml` and `flake.nix` run the identical
two-pass structure, kept in sync by an executable test rather than a comment. Two of those nine
(`code/tests/integration/test_timeout_resources.py::test_z3_solver_timeout` and
`::test_cli_command_timeout`) were found and marked during Phase 7, correcting a gap in Phase 5's
own scope hypothesis, which had incorrectly claimed `code/tests/**` contributed no candidates.

Three regression guards make all three defect classes non-regressable:
`code/tests/ci/test_workflow_parity.py` (both CI files' marker expressions/`-n`/`--timeout`
values stay identical, and every named marker is registered), `code/tests/ci/test_timing_marker_coverage.py`
(an AST scan proving no wall-clock-asserting test is left unmarked), and the pre-existing
`TestTimeoutSurfacing`/`TestThreeWayCheckResult` classes in `builder/tests/unit/test_example.py`
(the timeout-key and three-way-result guards, already correct from Phase 1/2 and confirmed to
fail on a broken invariant during Phase 7).

`code/docs/core/TESTING_GUIDE.md` documents the fixed state: a new subsection under 8.5 for the
repeated-operation timing anti-pattern/fix, a revised 8.6 describing the timeout/rlimit
mechanisms, a new 8.11 for the `--timeout`/`--timeout-method=thread` CI convention, and a new
8.12 for the `xdist_serial` marker taxonomy.

## Verification

- PyPI toolchain, full gating parallel pass: 2292 passed, 1 skipped, 0 failed (168.93s).
- PyPI toolchain, serial (`xdist_serial`) pass: 9 passed, 0 failed (3.19s).
- Nix toolchain (`nix flake check -L`): "all checks passed!" (parallel: 2033 passed, 256
  skipped, 0 failed; serial: 9 passed, 1 skipped, 0 failed).
- `TestPerformanceAndScalabilityScenarios`: 10/10 consecutive runs green.
- All three regression guards confirmed to fail on a deliberately broken invariant, then restored
  clean (see the Phase 7 and Phase 8 handoffs for the exact break/observe/restore steps).
- No unregistered-marker warnings; `--collect-only` before/after counts reconcile exactly.

## Plan Deviations

1. **Phase 3**: `set_rlimit()` declared on `TrackedSolverProtocol` only, not the base
   `SolverProtocol` as the plan's literal text stated -- `set_timeout` (the pattern the plan cited
   as precedent) is in fact not declared on either Protocol class at all, and adding `set_rlimit`
   to the base `SolverProtocol` would have broken `test_z3_solver_matches_protocol`'s
   `isinstance` check against a raw `z3.Solver`.
2. **Phase 7**: `code/tests/ci/` was given an `__init__.py` despite the plan's literal
   "`__init__`-free" instruction, matching the actual, confirmed convention every existing
   `code/tests/**`/`code/src/model_checker/**/tests/**` subdirectory follows (including
   `code/tests/packaging/`, the plan's own named precedent).
3. **Phase 7**: `test_workflow_parity.py` parses both CI files via targeted regex rather than
   `yaml.safe_load` for `tests.yml`, since `PyYAML` is not an installed dependency of either CI
   toolchain and adding one was out of scope.
4. **Phase 7**: `code/tests/integration/test_timeout_resources.py` was marked (2 functions)
   outside the phase's literally-named file list, because the new AST guard's own operation
   surfaced a genuine gap in Phase 5's already-closed inventory (see item 5 below).
5. **Phase 5 (retroactive correction, applied in Phase 7)**: the phase's Scope Hypothesis claimed
   "exactly six files" carry wall-clock assertions and that `code/tests/**` contributed none;
   Phase 7's AST scan found two more, previously-unmarked cases in `code/tests/**`. Both were
   marked `xdist_serial` in Phase 7 rather than reopening the closed Phase 5.
6. **Phase 8**: `code/tests/ci/test_workflow_parity.py` needed a further bugfix (a clean skip
   when `.github/workflows/tests.yml`/`flake.nix` are absent) discovered during this phase's own
   Nix-toolchain verification -- `flake.nix`'s `checks.default` derivation's `src = ./code` means
   the sandboxed build never contains either file. Not itself a plan deviation in the phase it
   touches (Phase 7's file), but recorded here since it was applied during Phase 8.

None of these deviations changed the plan's Goals, Non-Goals, or Definition of Done; all are
scope-preserving corrections applied where the plan's literal premise did not hold up against the
actual codebase state.
