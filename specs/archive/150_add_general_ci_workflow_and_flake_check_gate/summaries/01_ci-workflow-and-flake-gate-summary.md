# Implementation Summary: Task #150

- **Task**: 150 - add_general_ci_workflow_and_flake_check_gate
- **Status**: [COMPLETED]
- **Started**: 2026-08-12T08:19:22Z
- **Completed**: 2026-08-12T09:50:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None (tasks 148 and 149 were COMPLETED)
- **Artifacts**: plans/01_ci-workflow-and-flake-gate.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Added `.github/workflows/tests.yml`, a push/PR-triggered general regression gate running
`code/tests/` and the full `code/src/model_checker` suite (`-m "not packaging"`, `-n 6`) across
Python 3.10/3.11/3.12, plus a `nix flake check` job. Broadened `flake.nix`'s `checks.default`
from a bimodal-only scope to the same broadened selection, correcting its now-false
"28 documented pre-existing failures" justification. Closed the two ROADMAP items this work
answers. All five phases verified by commands actually run on this host; nothing was pushed and
no PR was opened, per `.claude/rules/pr-prohibition.md`.

## What Changed

- `flake.nix` — added `ipywidgets`, `matplotlib`, and `typing-extensions` to `devPython`;
  rewrote `checks.default`'s `checkPhase` from `theory_lib/bimodal/tests`-only to
  `src/model_checker tests -m "not packaging" -n 6 -q`; replaced the false "28 documented
  pre-existing failures" justification comment with an accurate one; updated the `installPhase`
  message and the `doCheck = false` comment to match the new scope.
- `.github/workflows/tests.yml` — new file. `general-tests` job (matrix `ubuntu-latest` x Python
  3.10/3.11/3.12) runs `pytest tests/ src/model_checker -m "not packaging" -n 6 -q` from `code/`;
  `flake-check` job installs Nix (`cachix/install-nix-action`, `DeterminateSystems/magic-nix-cache-action`)
  and runs `nix flake check`. In-file comments state the `-m "not packaging"`, `-n 6`-never-auto,
  narrower-matrix, and cross-toolchain-bimodal rationales.
- `.github/workflows/README.md` — added a `tests.yml` bullet and a "Scoping rationale"
  subsection covering the same five rationale points, and noted `checks.default` is no longer
  bimodal-scoped.
- `specs/ROADMAP.md` — closed "Add `nix flake check` as a CI gate job" and "Follow-up task for
  the 28 documented 'everything-else' failures" (resolved, not reproducing); added a
  non-closing annotation to "Oracle differential-suite cadence decision" noting the exhaustive
  scan and `TestBimodalHarnessIntegration` were already designed as manual-only/self-skipping.

## Decisions

- Kept the plan's exact `checkPhase` target form (`pytest src/model_checker tests -m "not
  packaging" -n 6 -q`) rather than falling back to the `src/model_checker`-only scope — the
  broadened check reached green inside the Nix sandbox once one additional dependency was added
  (see Plan Deviations), so the documented fallback was never needed.
- Added `typing-extensions` to both `flake.nix`'s `devPython` and the workflow's `pip install`
  list: `code/src/model_checker/theory_lib/logos/protocols.py` imports it at module level but it
  is not declared in `code/pyproject.toml`'s dependencies. This pre-existing undeclared-dependency
  gap in the package itself was left unfixed (out of scope for this task); only the two CI-facing
  environments were given the dependency they need to import the package correctly.

## Plan Deviations

- **Phase 2, additive fix**: added `typing-extensions` to `flake.nix`'s `devPython`. The
  broadened `checkPhase` initially failed inside the Nix sandbox with
  `ModuleNotFoundError: No module named 'typing_extensions'` — a genuine missing runtime
  dependency, not a sandbox-hostility issue the plan's fallback was designed for. After the
  addition, `nix flake check` reported "all checks passed!" with 2002 passed / 254 skipped / 0
  failed / 0 errors (149.55s), exactly 1700 + 302 as the Scope Hypothesis anticipated.
- **Phase 3, additive fix**: added `typing-extensions` to the workflow's `pip install` line for
  the same reason, confirmed by reproducing the identical `ModuleNotFoundError` in a venv
  provisioned with the workflow's original (pre-fix) exact dependency list.
- **Phase 3, reworded comment**: one workflow comment originally contained the literal substring
  `-n auto` in prose explaining the prohibition; reworded to "xdist's auto worker-count mode" so
  the plan's own `grep -n "n auto"` verification (checking the file contains no live invocation of
  that flag) is not tripped by explanatory prose.
- Both deviations are additive dependency fixes, not weakened assertions or narrowed selectors;
  the documented `[COMPLETED WITH EXCLUSIONS]` fallback for Phase 2 was not needed.

## Verification

- Build: N/A (no package build step in this task)
- Tests:
  - Phase 1: `nix develop --command python -c "import ipywidgets, matplotlib"` -> `ok`;
    `jupyter/tests` -> 72 passed, 0 errors; `nix flake check` (no-regression) -> all checks passed.
  - Phase 2: `nix flake check` (broadened) -> all checks passed, 2002 passed / 254 skipped / 0
    failed / 0 errors in 149.55s.
  - Phase 3: exact YAML selectors run locally against a venv matching the workflow's `pip
    install` line — `tests/` (minus packaging): 354 passed, 0 failed, 16.6s;
    `src/model_checker` (minus packaging, bimodal included): 1648 passed, 254 skipped, 0 failed,
    102.5s. 1648 + 354 = 2002, matching Phase 2's sandbox total exactly.
  - `actionlint` is not installed on this host; stated explicitly and skipped, per the plan's
    local-only verification contract, rather than silently omitted.
- Files verified: Yes — all five phase headings read `[COMPLETED]` in the plan; all grep-based
  checks (`28 documented`, `n auto`, task-number citations, `theory_lib/bimodal/tests` inside
  `checkPhase`) pass.
- No push/PR: `git reflog | grep -i push` returns nothing; no `gh pr create` or `git push` was
  run at any point in this session.

## Impacts

- Every ordinary push/PR will now exercise `code/tests/` and the full `code/src/model_checker`
  suite (both toolchains: PyPI `z3-solver` via `general-tests`, nixpkgs-native `z3` via
  `flake-check`), closing a gap where the general suite ran only on developer machines.
- `flake.nix`'s `checks.default` is now a meaningful hermetic reproducibility gate covering
  ~2002 tests rather than the ~302-test bimodal-only subset it covered before.
- The workflow's cold-runner timing (GitHub Actions specifically) remains genuinely unverified —
  stated as such in-file per the plan's local-only verification contract; only local timings
  (149.55s / 102.5s / 16.6s) were actually observed.

## Follow-ups

- The `typing_extensions` undeclared-dependency gap in `code/pyproject.toml` (surfaced by this
  task but explicitly out of scope to fix) is a candidate for a small follow-up task: either add
  `typing_extensions` to `code/pyproject.toml`'s core `dependencies`, or replace the
  `typing_extensions.runtime_checkable` import in `logos/protocols.py` with `typing.runtime_checkable`
  if the project's Python floor (`>=3.10`, per `code/pyproject.toml`) already provides it natively.
- `.github/workflows/tests.yml`'s cold-runner timing (both jobs) has not been observed on an
  actual GitHub Actions runner; this can only be confirmed once a branch is pushed and CI runs,
  which is out of scope for this agent per `.claude/rules/pr-prohibition.md`.

## References

- `specs/150_add_general_ci_workflow_and_flake_check_gate/plans/01_ci-workflow-and-flake-gate.md`
- `specs/150_add_general_ci_workflow_and_flake_check_gate/reports/01_ci-workflow-and-flake-gate.md`
- `flake.nix`, `.github/workflows/tests.yml`, `.github/workflows/README.md`, `specs/ROADMAP.md`
