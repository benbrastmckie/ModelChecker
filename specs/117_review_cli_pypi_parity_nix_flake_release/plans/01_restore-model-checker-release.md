# Implementation Plan: Restore model-checker Identity and Prepare PyPI Release

- **Task**: 117 - review_cli_pypi_parity_nix_flake_release
- **Status**: [NOT STARTED]
- **Effort**: 30 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md (+ teammate a/b/c/d findings, same directory)
- **Artifacts**: plans/01_restore-model-checker-release.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/rules/pr-prohibition.md
- **Type**: python

## Overview

The repository has drifted into two incompatible product identities: the historic `model-checker`
multi-theory framework (published on PyPI at v1.2.12) and a narrower `bimodal-logic` Z3 oracle.
The current tree declares `bimodal-logic 0.1.0` in `pyproject.toml`, has a broken `model-checker`
CLI (`model_checker.builder`, `model_checker.iterate`, `model_checker.output.manager` were all
deleted), a half-resurrected unregistered `theory_lib/logos/`, and missing `exclusion`/
`imposition` theories. This plan restores the `model-checker` package identity and its deleted
general-purpose infrastructure from concrete git-history restore points, reconciles all restored
theories against the current solver-abstraction API, moves the bimodal-oracle/harness layer out of
the shipped package into a standalone top-level directory for independent development, rebuilds the
Nix flake into a real multi-system build/test gate, and prepares a rehearsed, high-quality release.
Definition of done: the full `model_checker` test suite collects and passes, `python -m
model_checker --help` works, `nix build`/`nix flake check` succeed, docs are honest, and a
TestPyPI-rehearsed release checklist is ready for the user to execute (the final PyPI publish and
any `git push` remain user-only actions).

### Research Integration

The team research report and four teammate findings supply verified facts used throughout this
plan: the broken `model-checker` CLI and canonical test command (teammates A/C), the
`bimodal-logic 0.1.0` identity in `pyproject.toml` (teammates B/C), the half-resurrected `logos/`
importing the deleted `model_checker.iterate` (teammate A), `testpaths` pinned to bimodal-only
(teammate C), the devShell-only flake hardcoded to `x86_64-linux` with a `../BimodalHarness`
dependency and no `packages`/`checks` output (teammates A/B), the `cd Code` casing bug in
`release.yml` and the long-lived `PYPI_API_TOKEN` (teammate B), stale docs/MANIFEST.in (all), the
un-root-caused `test_cross_oracle_differential.py` failures and 15-20+ min bimodal suite runtime
(teammate A). The user has resolved the report's decision gate authoritatively: restore the
`model-checker` identity; keep `bimodal` and `exclusion` (and `imposition`, `logos`) as theories;
move the oracle/harness layer out to develop independently.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` is an empty template (no items). No `--roadmap` flag was passed, so this plan
does not add or update roadmap phases. Seeding the roadmap with the identity decision is noted as a
non-blocking follow-up in the docs phase but is not a required deliverable here.

### Concrete Git Restore Points

Verified via `git log --diff-filter=D` and `git ls-tree`. Restore each deleted module from the
commit immediately preceding its deletion, using `git checkout <sha>^ -- <path>` (non-destructive
path checkout; do not use the pathspec-discard form `git checkout -- <path>`):

| Module | Deletion commit | Restore source | Solver-abstraction status |
|--------|-----------------|----------------|---------------------------|
| `model_checker/builder/` (67 files) | `013a486c` (task 104 ph1) | `013a486c^` | Post-migration — clean restore |
| `model_checker/iterate/` | `c21b3709` (task 100 ph3) | `c21b3709^` | Post-migration — clean restore |
| `model_checker/jupyter/` | `c21b3709` (task 100 ph3) | `c21b3709^` | Post-migration — clean restore |
| `model_checker/output/manager.py`, `output/progress/` | `71ef79a1` (task 104 ph2) | `71ef79a1^` | Post-migration — clean restore |
| `theory_lib/exclusion/` | `abb3bf7d` (task 30) | `abb3bf7d^` | PRE-migration — needs porting |
| `theory_lib/imposition/` | `abb3bf7d` (task 30) | `abb3bf7d^` | PRE-migration — needs porting |
| `theory_lib/logos/` | present in tree (via `feff3cbe`, first-order removed by `e9734a27`) | keep in-tree | Post-migration — fix imports + register |

Timeline confirmed by commit dates: the solver-abstraction migration (tasks 59-63, `cc0f54eb`,
2026-03-30) landed *after* `exclusion`/`imposition` were deleted (task 30, `abb3bf7d`, 2026-03-03)
but *before* `builder`/`iterate`/`jupyter`/`output` were deleted (2026-06-01). Consequently
`exclusion`/`imposition` restored from `abb3bf7d^` predate `z3_shim`, `model_checker.solver`, and
the modular `models.semantic`/`models.proposition`/`models.structure` package structure, and must
be ported; the other modules restore against an API that matches current HEAD.

## Goals & Non-Goals

**Goals**:
- Restore the `model-checker` package identity (name, version strategy, deps, single entry point)
  in `code/pyproject.toml` and `MANIFEST.in`.
- Restore and integrate the deleted general-purpose infrastructure (`builder/`, `iterate/`,
  `jupyter/`, `output/manager.py`, `output/progress/`) so `python -m model_checker` and
  `dev_cli.py` work.
- Restore `exclusion` and `imposition` theories, ported to the current solver-abstraction API, and
  reconcile `logos` (keeping the recent first-order removal); register all in `AVAILABLE_THEORIES`.
- Move the `bimodal_logic` oracle/harness layer and its BimodalHarness-facing entry points into a
  standalone top-level directory, excluded from the model-checker wheel/sdist, preserved for
  independent development.
- Repair test infrastructure so the full canonical suite collects and passes; root-cause the
  cross-oracle differential failures; add parallelization for the slow bimodal suite.
- Rewrite the Nix flake into a multi-system `packages.default` + `checks.default` build/test gate
  using nixpkgs-native `buildPythonPackage` and `python3Packages.z3`; retire `code/shell.nix`.
- Refresh all docs (root README, `code/README.md`, `CLAUDE.md`, `CHANGELOG.md`) honestly; fix dead
  links and directory casing.
- Fix and modernize release engineering (casing bug, Trusted Publishing/OIDC, TestPyPI rehearsal,
  wheel-content parity checks vs 1.2.12) and produce a user-gated publish checklist.

**Non-Goals**:
- Executing the actual PyPI publish or any `git push` / PR creation (user-only, per
  `pr-prohibition.md`).
- Restoring the first-order subtheory (its removal in `e9734a27` is intentional and preserved).
- Continued development of the oracle/harness beyond relocating and preserving it; integration back
  into the package happens later, only when ready.
- Rewriting theory semantics beyond what is required to make restored theories pass on the current
  API.

## Risks & Mitigations

- **Risk**: `exclusion`/`imposition` restored from a pre-solver-migration commit fail to import or
  run against the current `z3_shim`/`solver`/`models.semantic` API. **Impact**: H. **Likelihood**:
  H. **Mitigation**: Dedicate separate phases (5, 6) to each theory; port imports/APIs incrementally
  using `bimodal` and `logos` (already on the new API) as the reference; verify each theory's own
  test suite green before proceeding; commit per green sub-step.
- **Risk**: Restoring old `builder`/`iterate` reintroduces code that conflicts with post-strip
  improvements elsewhere. **Impact**: M. **Likelihood**: M. **Mitigation**: Restore from the
  freshest pre-deletion commit (post-migration), then run collection + import smoke tests
  immediately; fix-forward import breaks rather than reverting unrelated improvements.
- **Risk**: PyPI uploads are irreversible per filename; a wrong name/version/deps upload is
  permanent. **Impact**: H. **Likelihood**: L (mitigated). **Mitigation**: TestPyPI rehearsal +
  wheel-content parity diff vs 1.2.12 + `twine check --strict` before any real upload; publish step
  is user-gated and never automated by an agent.
- **Risk**: Full bimodal suite runtime (15-20+ min serial) makes iteration slow and can mask
  regressions. **Impact**: M. **Likelihood**: H. **Mitigation**: Capture a baseline early (Phase
  1), add `pytest-xdist`, run targeted subsets during development, reserve a full serial run for the
  green-gate phase.
- **Risk**: Moving the oracle out breaks `test_cross_oracle_differential.py` (which compares MC
  oracle vs BimodalHarness) or leaves it importing a moved module. **Impact**: M. **Likelihood**:
  M. **Mitigation**: Move the differential harness/tests with the oracle in Phase 2; ensure the
  in-package `bimodal` suite is independently green without the oracle; root-cause residual
  failures in Phase 9.
- **Risk**: `AVAILABLE_THEORIES` re-registration surfaces cross-theory coupling (e.g. `exclusion`
  importing `bimodal` witness modules). **Impact**: M. **Likelihood**: M. **Mitigation**: Verify
  registration incrementally per theory; keep witness/shared imports pointing at current module
  paths.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 3 |
| 4 | 6 | 5 |
| 5 | 7, 8 | 2, 4, 6 |
| 6 | 9 | 2, 8 |
| 7 | 10 | 7, 9 |
| 8 | 11, 12 | 10 |
| 9 | 13 | 11, 12 |

Phases within the same wave can execute in parallel.

### Phase 1: Branch, Inventory, and Baseline Capture [NOT STARTED]

- **Goal:** Create a working branch and record the pre-change state so regressions are detectable.
- **Tasks:**
  - [ ] Create a task branch (e.g. `task-117-restore-model-checker`) off `master`; do not push.
  - [ ] Run the current live bimodal suite once to record a pass/fail baseline and timing
        (`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q`,
        long-running; may run in background). Save output under the task dir for reference.
  - [ ] Snapshot the current failing state of the canonical command
        (`PYTHONPATH=code/src pytest code/tests/ --collect-only -q`) and
        `python -m model_checker --help` for before/after comparison.
  - [ ] Inventory the restore targets and their SHAs (table in this plan) and confirm each restore
        source path exists via `git ls-tree <sha>^ -- <path>`.
- **Timing:** 1 hour (plus background test time)
- **Depends on:** none

### Phase 2: Separate the Bimodal-Oracle/Harness Layer [NOT STARTED]

- **Goal:** Relocate the oracle/harness code out of the shipped package into a standalone top-level
  directory, preserved for independent development and excluded from the model-checker build.
- **Tasks:**
  - [ ] Move `code/src/bimodal_logic/` (cli.py, provider.py, serialization.py, translation.py,
        `__init__.py`, `tests/`) to a new top-level directory (e.g. `oracle/bimodal_logic/` at repo
        root); delete the stale `code/src/bimodal_logic.egg-info/`.
  - [ ] Move the cross-oracle differential harness/tests that depend on BimodalHarness
        (`theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` and any oracle-only
        helpers) alongside the oracle so the in-package suite does not depend on the external
        harness.
  - [ ] Give the oracle its own minimal dev setup (its own `pyproject.toml` or a README documenting
        `PYTHONPATH`-based standalone development and the `bimodal_harness.oracle_providers` entry
        point) so it builds/tests independently of the model-checker package.
  - [ ] Confirm nothing under `code/src/model_checker/` imports `bimodal_logic`; fix-forward any
        residual references.
  - [ ] Verify the oracle's own tests still collect from its new location.
- **Timing:** 2 hours
- **Depends on:** 1

### Phase 3: Restore Core Infrastructure (builder, iterate, jupyter, output) [NOT STARTED]

- **Goal:** Restore the deleted general-purpose modules so the `model-checker` CLI imports and runs.
- **Tasks:**
  - [ ] `git checkout 013a486c^ -- code/src/model_checker/builder`
  - [ ] `git checkout c21b3709^ -- code/src/model_checker/iterate code/src/model_checker/jupyter`
  - [ ] `git checkout 71ef79a1^ -- code/src/model_checker/output/manager.py code/src/model_checker/output/progress`
  - [ ] Reconcile imports: run import smoke tests for `model_checker.builder`, `model_checker.iterate`,
        `model_checker.output.manager`; fix any references to modules that changed since the restore
        point (these are post-solver-migration, so breakage should be minimal).
  - [ ] Verify `PYTHONPATH=code/src python -m model_checker --help` and `python code/dev_cli.py --help`
        both run without `ModuleNotFoundError`.
  - [ ] Commit per green sub-step (each module importing cleanly is a green milestone).
- **Timing:** 3 hours
- **Depends on:** 1

### Phase 4: Reconcile and Register the logos Theory [NOT STARTED]

- **Goal:** Make the in-tree `logos` theory functional and registered, keeping first-order removed.
- **Tasks:**
  - [ ] Confirm `theory_lib/logos/__init__.py`'s `from .iterate import ...` /
        `model_checker.iterate` imports now resolve (iterate restored in Phase 3); fix any residual
        import paths.
  - [ ] Verify the first-order subtheory removal (`e9734a27`) is intact and no dangling references
        to it remain.
  - [ ] Register `logos` (and its retained subtheories) in `theory_lib` `AVAILABLE_THEORIES`.
  - [ ] Get `theory_lib/logos/tests/` to collect and pass:
        `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q`.
- **Timing:** 1.5 hours
- **Depends on:** 3

### Phase 5: Restore and Port the exclusion Theory [NOT STARTED]

- **Goal:** Restore `exclusion` from history and port it to the current solver-abstraction API.
- **Tasks:**
  - [ ] `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/exclusion`
  - [ ] Port imports/APIs from the pre-migration form to current: `model_checker.z3_shim`,
        `model_checker.solver` (`is_true`/`is_false`), `models.semantic.SemanticDefaults`,
        `models.proposition.PropositionDefaults`, `models.structure.ModelDefaults`,
        `syntactic.atoms.get_atom_sort`, and bimodal witness modules — using `bimodal`/`logos`
        (already on the new API) as the reference pattern.
  - [ ] Register `exclusion` in `AVAILABLE_THEORIES`.
  - [ ] Get `theory_lib/exclusion/tests/` to collect and pass; commit per green sub-step.
- **Timing:** 3 hours
- **Depends on:** 3

### Phase 6: Restore and Port the imposition Theory [NOT STARTED]

- **Goal:** Restore `imposition` from history and port it to the current API, reusing the exclusion
  porting recipe.
- **Tasks:**
  - [ ] `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/imposition`
  - [ ] Apply the same import/API porting established in Phase 5 (solver abstraction, modular
        `models.*` structure, `z3_shim`).
  - [ ] Register `imposition` in `AVAILABLE_THEORIES`.
  - [ ] Get `theory_lib/imposition/tests/` to collect and pass; commit per green sub-step.
- **Timing:** 3 hours
- **Depends on:** 5

### Phase 7: Restore Package Identity (pyproject.toml, MANIFEST.in) [NOT STARTED]

- **Goal:** Return `code/pyproject.toml` and `MANIFEST.in` to the `model-checker` identity.
- **Tasks:**
  - [ ] Set `[project] name = "model-checker"`; choose the next version (recommend `1.3.0` given the
        restored theory set and first-order removal since 1.2.12 — final number confirmed in the
        release checklist, Phase 13); restore description/keywords/classifiers to the framework
        identity.
  - [ ] Restore dependencies to match PyPI 1.2.12 intent: `z3-solver>=4.8.0`, `networkx>=2.0`, and
        the `jupyter`/`all` optional-dependency extras (`ipywidgets`, `matplotlib`, `networkx`,
        `jupyter`, `ipython`).
  - [ ] Keep only the `model-checker = "model_checker.__main__:run"` console script; remove the
        `bimodal-logic` script and the `[project.entry-points."bimodal_harness.oracle_providers"]`
        table (moved to the oracle directory in Phase 2).
  - [ ] Ensure `[tool.setuptools.packages.find]` and package-data include `model_checker` (with
        restored `jupyter/` notebooks) and exclude the relocated oracle directory.
  - [ ] Reconcile version single-sourcing: `model_checker/__init__.py` uses
        `get_model_checker_version()` — ensure it reads the same source `pyproject.toml`'s `version`
        is validated against.
  - [ ] Update `MANIFEST.in`: keep `theory_lib/{logos,bimodal,exclusion,imposition}` and `jupyter/`
        includes now that those directories exist again; remove references to paths that no longer
        exist.
- **Timing:** 1.5 hours
- **Depends on:** 2, 4, 6

### Phase 8: Repair Test Infrastructure [NOT STARTED]

- **Goal:** Make the full canonical test suite collect and run, with the slow bimodal suite
  parallelizable.
- **Tasks:**
  - [ ] Widen `[tool.pytest.ini_options] testpaths` beyond bimodal-only to cover `code/tests/` and
        all registered theories (or remove the pin so `PYTHONPATH=code/src pytest code/tests/
        code/src/model_checker` works as CLAUDE.md prescribes).
  - [ ] Fix or delete stale top-level tests referencing formerly-deleted modules
        (`tests/e2e/test_simple_output_verify.py`, `tests/integration/test_model_building_sync.py`,
        `tests/integration/test_system_imports.py`, `tests/utils/helpers.py`) — repair them against
        the restored `builder`/`output` modules where meaningful, delete where obsolete.
  - [ ] Add `pytest-xdist` (dev dependency + `-n auto` usage documented) to parallelize the slow
        suite.
  - [ ] Confirm `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` reports zero collection
        errors.
- **Timing:** 2 hours
- **Depends on:** 4, 6

### Phase 9: Root-Cause Cross-Oracle Differential Failures [NOT STARTED]

- **Goal:** Resolve the un-root-caused differential failures and confirm the in-package bimodal
  suite is green independent of the external harness.
- **Tasks:**
  - [ ] With the oracle differential harness moved out (Phase 2), confirm the in-package
        `theory_lib/bimodal` suite passes without BimodalHarness present.
  - [ ] For the relocated `test_cross_oracle_differential.py`, run it in its new oracle context and
        root-cause the 2-4 consistent failures (regression vs. environment/xfail behavior); fix or
        correctly mark them, documenting the cause.
  - [ ] Record the definitive bimodal pass/fail tally against the Phase 1 baseline.
- **Timing:** 2 hours (plus Z3 solve wall-clock)
- **Depends on:** 2, 8

### Phase 10: Full Green Test Gate [NOT STARTED]

- **Goal:** Establish a clean, complete test baseline across the restored framework.
- **Tasks:**
  - [ ] Run the full `model_checker` suite to completion (all theories + top-level tests), using
        `pytest-xdist`; achieve green (or documented, justified skips/xfails only).
  - [ ] Run the relocated oracle suite separately to green.
  - [ ] Smoke-test the CLI end-to-end: `python -m model_checker --help`, a representative example
        run, and `--maximize`/`--save` paths if quick.
  - [ ] Record the final pass counts and runtimes as the release baseline.
- **Timing:** 2 hours (mostly wall-clock)
- **Depends on:** 7, 8, 9

### Phase 11: Nix Flake Rewrite [NOT STARTED]

- **Goal:** Provide a reproducible, multi-system Nix build and test gate; retire `code/shell.nix`.
- **Tasks:**
  - [ ] Rewrite root `flake.nix`: multi-system (flake-utils or explicit system list, replacing
        hardcoded `x86_64-linux`); `packages.default` via nixpkgs-native `buildPythonPackage {
        pyproject = true; }` against `python3Packages.z3` (NOT the PyPI `z3-solver` wheel), with
        `networkx` included.
  - [ ] Add `checks.default` running the canonical pytest suite so `nix flake check` is a real gate.
  - [ ] Provide a `devShell` that subsumes what `code/shell.nix` offered (z3, setuptools, pip,
        networkx, pytest); make the `../BimodalHarness` path strictly optional (no failure/warning
        path required for a standalone checkout).
  - [ ] Commit `flake.lock`; delete `code/shell.nix` (no backwards-compat layer).
  - [ ] Verify `nix build` and `nix flake check` succeed locally.
- **Timing:** 2.5 hours
- **Depends on:** 10

### Phase 12: Documentation Refresh [NOT STARTED]

- **Goal:** Make all user-facing docs honest about the restored framework and fix broken references.
- **Tasks:**
  - [ ] Root `README.md`: fix the `pip install model-checker[jupyter]` quick-start and the dead link
        to `jupyter/README.md`; ensure the four-theory framing matches the actual registered set.
  - [ ] `code/README.md`: fix `cd ModelChecker/Code` casing to `cd code`; update the component table
        to reflect restored `builder`/`iterate` and the relocated oracle.
  - [ ] `CLAUDE.md`: reconcile the canonical test command and architecture description with reality.
  - [ ] `code/CHANGELOG.md`: add an honest entry for this release (identity restore, theory set,
        first-order removal, oracle relocation).
  - [ ] Check `docs/usage/SEMANTICS.md` for stale first-order references and `code/scripts/README.md`
        for the dead link to the deleted `docs/theory/QUANTIFIER_SOLVERS.md`; fix.
  - [ ] Verify `MANIFEST.in` includes resolve against real paths (cross-check with Phase 7).
  - [ ] (Non-blocking) Seed `specs/ROADMAP.md` with the durable identity decision.
- **Timing:** 2 hours
- **Depends on:** 10

### Phase 13: Release Engineering and Rehearsal [NOT STARTED]

- **Goal:** Fix and modernize the release pipeline and produce a rehearsed, user-gated publish
  checklist. No agent publishes or pushes.
- **Tasks:**
  - [ ] Fix `.github/workflows/release.yml`: `cd Code` -> `cd code` (both jobs); reconcile
        `.github/RELEASE_SETUP.md` with the single actual workflow.
  - [ ] Migrate the publish job to PyPI Trusted Publishing (OIDC) via
        `pypa/gh-action-pypi-publish@release/v1` in a separate, environment-gated (`pypi`) job with
        `permissions: id-token: write`; drop the long-lived `PYPI_API_TOKEN`; add `twine check
        --strict`.
  - [ ] Add a TestPyPI rehearsal step and perform a local rehearsal: `python -m build`,
        `check-wheel-contents`, and a wheel-content/hash parity diff vs `pip download --no-deps
        model-checker==1.2.12` (NixOS-safe inside `nix develop`); confirm the built artifact is
        named `model_checker-<version>`, not `bimodal_logic`.
  - [ ] Confirm the final version number (Phase 7) and prepare a step-by-step publish checklist
        ending in the user-only actions: user pushes the branch/tag and either invokes `/merge` or
        triggers the release workflow. Explicitly mark publish + push as user-gated; the agent does
        neither.
- **Timing:** 2.5 hours
- **Depends on:** 11, 12

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` reports zero collection errors.
- [ ] `PYTHONPATH=code/src python -m model_checker --help` and `python code/dev_cli.py --help` run
      cleanly.
- [ ] Each restored theory's suite passes: `logos`, `exclusion`, `imposition` (plus existing
      `bimodal`).
- [ ] Full `model_checker` suite green (with `pytest-xdist`); oracle suite green separately.
- [ ] Cross-oracle differential failures root-caused and resolved/documented.
- [ ] `nix build` and `nix flake check` succeed.
- [ ] `python -m build` produces a `model_checker-<version>` wheel/sdist that excludes the oracle;
      `check-wheel-contents` clean; parity diff vs 1.2.12 reviewed.
- [ ] `twine check --strict dist/*` passes; TestPyPI rehearsal succeeds.

## Artifacts & Outputs

- plans/01_restore-model-checker-release.md (this file)
- summaries/01_restore-model-checker-release-summary.md (on completion)
- Restored source under `code/src/model_checker/` (`builder/`, `iterate/`, `jupyter/`,
  `output/manager.py`, `output/progress/`, `theory_lib/exclusion/`, `theory_lib/imposition/`).
- Relocated oracle directory (e.g. `oracle/bimodal_logic/`) with its own dev setup.
- Updated `code/pyproject.toml`, `code/MANIFEST.in`.
- Rewritten root `flake.nix` + committed `flake.lock`; deleted `code/shell.nix`.
- Updated `.github/workflows/release.yml`, `.github/RELEASE_SETUP.md`.
- Refreshed `README.md`, `code/README.md`, `CLAUDE.md`, `code/CHANGELOG.md`, and related docs.
- User-gated release/publish checklist.

## Rollback/Contingency

- All work occurs on a task branch off `master`; if the restore proves unworkable, the branch can
  be abandoned without touching `master`.
- Each phase commits per green sub-step, so any single failed phase can be reverted independently
  via `git revert` of its commits without losing earlier restored modules.
- If `exclusion`/`imposition` porting (Phases 5-6) exceeds budget, the framework can ship with
  `logos`+`bimodal` registered and the other two behind a follow-up task, rather than blocking the
  release — but this is a fallback, not the plan (the goal is full restoration).
- No PyPI upload or `git push` occurs during implementation; the irreversible publish is gated on
  explicit user action after TestPyPI rehearsal, so there is nothing to roll back on PyPI.
