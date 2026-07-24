# Implementation Plan: Restore Package Identity and Repair Test Infrastructure

- **Task**: 121 - restore_package_identity_and_repair_test_infrastru
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: 118, 119, 120 (all COMPLETED on branch task-117-restore-model-checker)
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md; parent plan specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md (phases 7-8)
- **Artifacts**: plans/01_restore-package-identity-test-infra.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: python

## Overview

The oracle relocation (task 118) and all theory registrations — logos (446 tests), exclusion
(143), imposition (110) — are complete, but `code/pyproject.toml` still declares the transient
`bimodal-logic` project identity: name `bimodal-logic`, version `0.1.0`, a `bimodal-logic` console
script, a `[project.entry-points."bimodal_harness.oracle_providers"]` table pointing at the
pre-move import path, and a `testpaths` pin restricted to the bimodal suite only. This task
restores the `model-checker` framework identity in `pyproject.toml` and `MANIFEST.in`, reconciles
version single-sourcing, and repairs the test infrastructure so the full canonical suite collects
with zero errors and the slow bimodal suite can be parallelized with `pytest-xdist`.

Definition of done: `pyproject.toml` declares the `model-checker` identity with restored
dependencies and the single `model-checker` console script (no bimodal artifacts);
`MANIFEST.in` resolves against real paths; `PYTHONPATH=code/src pytest code/tests/
code/src/model_checker --collect-only -q` reports zero collection errors; `pytest-xdist` is a
declared dev dependency with `-n auto` usage documented.

### Research Integration

The spawn analysis (report 02) confirms this task covers parent-plan phases 7-8 and that its
prerequisites (oracle relocation, logos/exclusion/imposition registration) are satisfied, so
package-data include/exclude and `testpaths` can now be finalized against the definitive layout.
Grounding against the live tree refined the parent plan's stale-test list: because tasks 118-120
already restored `builder`/`iterate`/`output`, the parent plan's pre-restoration list is partly
obsolete. A live `pytest --collect-only` run shows the **actual** current collection errors are a
different set (see Phase 3), so repair is driven by the live collection output rather than the
parent plan's hypothesized list.

### Prior Plan Reference

The parent plan (`plans/01_restore-model-checker-release.md`) phases 7-8 are the authoritative
detail for this work: Phase 7 (package identity, 1.5h, depends on plan-phases 2/4/6) and Phase 8
(test infrastructure, 2h, depends on plan-phases 4/6). Effort calibration (3.5h total) is taken
directly from that plan. The parent plan is reference only; its stale-test enumeration is treated
as a starting hypothesis and superseded by live collection output where they disagree.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set). This task advances the parent
task 117 release-restoration effort by finalizing the shippable package identity and test gate.

## Goals & Non-Goals

**Goals**:
- Restore `[project]` in `code/pyproject.toml` to the `model-checker` identity: name, next
  version (1.3.0 recommended; final number confirmed in the release task), description, keywords,
  classifiers.
- Restore dependencies to match PyPI 1.2.12 intent (`z3-solver>=4.8.0`, `networkx>=2.0`) plus the
  `jupyter`/`all` optional-dependency extras (`ipywidgets`, `matplotlib`, `networkx`, `jupyter`,
  `ipython`).
- Keep only `model-checker = "model_checker.__main__:run"`; remove the `bimodal-logic` script and
  the `[project.entry-points."bimodal_harness.oracle_providers"]` table.
- Ensure `[tool.setuptools.packages.find]` and package-data include `model_checker` (with restored
  `jupyter/` notebooks) and exclude the relocated oracle directory.
- Reconcile version single-sourcing in `model_checker/__init__.py`'s `get_model_checker_version()`.
- Update `MANIFEST.in` to keep `theory_lib/{logos,bimodal,exclusion,imposition}` and `jupyter/`
  includes and remove references to non-existent paths.
- Widen `[tool.pytest.ini_options] testpaths` to cover `code/tests/` and all registered theories.
- Repair or delete stale tests until `pytest --collect-only` reports zero collection errors.
- Add `pytest-xdist` as a dev dependency with `-n auto` usage documented.

**Non-Goals**:
- Do not finalize/publish the version number to PyPI (release task 8 owns the final version and
  publish; this task only sets the source-of-truth value).
- Do not fix runtime test *failures* beyond what is needed for zero *collection* errors (green-gate
  and differential-failure root-causing belong to the downstream green-gate task, plan phases
  9-10).
- Do not edit the relocated oracle package at `oracle/bimodal_logic/` (owned by task 118).
- Do not rewrite the Nix flake or documentation (downstream tasks).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deleting a test that has genuine, repairable value | M | M | Decide delete-vs-repair per file against live import errors; repair against restored modules where the referenced capability still exists, delete only when the referenced module/symbol is genuinely gone |
| Restoring a dependency the codebase no longer imports (e.g. `networkx`) as a hard requirement | M | L | Grep the source for actual imports before pinning; keep `networkx` as declared in PyPI 1.2.12 intent but verify it is imported; move to an extra if unused at import time |
| `testpaths` widening surfaces new collection errors from theory-internal test trees | M | H | Run `--collect-only` across the full widened scope and resolve every error before declaring done; the live run already shows 3 errors to fix |
| Version single-source drift (`__init__` reads installed metadata via `version('model-checker')`, not `pyproject`) | L | M | Confirm `get_model_checker_version()` resolves `model-checker` distribution metadata; ensure the `[project] name` matches the distribution name it queries so an editable/real install single-sources correctly |
| Editable-install metadata is stale (package still installed as `bimodal-logic`) causing `__version__` mismatch | L | M | Note in verification that a reinstall (`pip install -e code/`) may be needed for `__version__` to reflect the new identity; not required for collection/build correctness |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential because all
four phases edit the single file `code/pyproject.toml` (its `[project]`, `[tool.setuptools]`,
and `[tool.pytest.ini_options]`/dev-dependency sections respectively); serializing avoids
concurrent-write conflicts on that shared file.

### Phase 1: Restore [COMPLETED]

- **Goal:** Replace the `bimodal-logic` project identity with the `model-checker` framework
  identity, including dependencies and the single console script.
- **Tasks:**
  - [x] Set `[project] name = "model-checker"`.
  - [x] Set `version = "1.3.0"` (recommended given the restored theory set and first-order removal
        since 1.2.12; leave a comment noting the release task confirms the final number).
  - [x] Restore `description` to the framework identity (programmatic Z3-based modular semantic
        framework), and restore `keywords`/`classifiers` to the model-checker framing (modal logic,
        semantics, model checking, Z3, SMT) — drop the bimodal-oracle-specific wording.
  - [x] Set `dependencies = ["z3-solver>=4.8.0", "networkx>=2.0"]` after grepping the source to
        confirm `networkx` is imported at runtime; if it is only an optional/import-guarded use,
        record that and keep it per PyPI 1.2.12 intent. (Confirmed: `iterate/graph.py` imports
        `networkx` unconditionally at module scope, so it stays a hard dependency, not an extra.)
  - [x] Add `[project.optional-dependencies]` with `jupyter = [...]` and `all = [...]` extras
        containing `ipywidgets`, `matplotlib`, `networkx`, `jupyter`, `ipython`.
  - [x] In `[project.scripts]`, keep only `model-checker = "model_checker.__main__:run"`; remove the
        `bimodal-logic = "bimodal_logic.cli:run"` line.
  - [x] Remove the entire `[project.entry-points."bimodal_harness.oracle_providers"]` table.
- **Timing:** 1 hour
- **Depends on:** none
- **Files to modify:**
  - `code/pyproject.toml` — rewrite `[project]`, `[project.scripts]`; remove oracle entry-points
- **Verification:**
  - `grep -n "bimodal" code/pyproject.toml` returns nothing under `[project]`/scripts/entry-points.
  - `python -c "import tomllib; d=tomllib.load(open('code/pyproject.toml','rb')); print(d['project']['name'], d['project']['version'])"` prints `model-checker 1.3.0`.
  - `[project.scripts]` has exactly one entry (`model-checker`).

### Phase 2: Reconcile Packaging Config, MANIFEST.in, and Version Single-Sourcing [COMPLETED]

- **Goal:** Ensure the build includes `model_checker` (with `jupyter/` and all theory READMEs/
  notebooks), excludes the relocated oracle, and that `__init__.py`'s version resolution
  single-sources against the new distribution name.
- **Tasks:**
  - [x] Confirm `[tool.setuptools.packages.find] where = ["src"]` — the relocated oracle lives at
        repo-root `oracle/bimodal_logic/` (outside `code/src`), so it is already excluded by the
        `src`-rooted find; verify no stray `bimodal_logic` reference remains under `code/src` and
        add an explicit `exclude` guard only if a residual path is found. (Verified: `grep -rn
        bimodal_logic code/src/` returns nothing; no guard needed.)
  - [x] Confirm `[tool.setuptools.package-data]` globs (`README.md`, `*.md`, `*.ipynb`) include the
        restored `jupyter/` notebooks and theory README files; widen only if a needed asset type is
        missed. (Verified: globs unchanged and sufficient; sdist build below confirms inclusion.)
  - [x] Reconcile `MANIFEST.in`: keep `recursive-include` lines for
        `theory_lib/{logos,bimodal,exclusion,imposition}` READMEs and the `jupyter/` docs; verify
        each referenced path exists on disk (`jupyter/`, `jupyter/debug/`, all four theory dirs) and
        remove any line resolving to a non-existent path. (Verified: every path in `MANIFEST.in`
        resolves to an existing file; no edit needed, file left unchanged.)
  - [x] Verify `get_model_checker_version()` in `model_checker/utils/version.py` queries
        `version('model-checker')`; confirm the `[project] name` set in Phase 1 matches that
        distribution name so the version single-sources correctly. Note in the summary that an
        editable reinstall may be needed for the runtime `__version__` to reflect the new identity.
        (Confirmed: `version('model-checker')` matches `[project] name = "model-checker"`.)
  - [x] Confirm `model_checker/__init__.py` still imports `get_model_checker_version` and exposes
        `__version__` without change (no code edit expected unless a mismatch is found). (Confirmed
        unchanged; no mismatch found.)
- **Timing:** 45 minutes
- **Depends on:** 1
- **Files to modify:**
  - `code/pyproject.toml` — `[tool.setuptools]` packages/package-data (edit only if a gap found)
  - `code/MANIFEST.in` — remove dead paths, confirm real ones
  - `code/src/model_checker/__init__.py` — only if a version-sourcing mismatch is found
- **Verification:**
  - Every `recursive-include`/`include` path in `MANIFEST.in` resolves to an existing file/dir
    (a small check-loop over the paths reports no misses).
  - `python -m build --sdist code/` (or `python -m build code/`) succeeds and the built sdist/wheel
    contains `model_checker/jupyter/` and the four theory READMEs, and does NOT contain
    `bimodal_logic`/oracle files.

### Phase 3: Repair Test Collection [NOT STARTED]

- **Goal:** Widen `testpaths` and resolve every collection error so the full suite collects
  cleanly.
- **Tasks:**
  - [ ] Set `[tool.pytest.ini_options] testpaths` to cover both `code/tests` and the in-package
        theory/unit trees (e.g. `["tests", "src/model_checker"]`), or remove the pin so the
        CLAUDE.md-prescribed `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker`
        invocation drives collection. Keep `pythonpath = "src"`, `python_files`, markers, and
        `filterwarnings` intact.
  - [ ] Run `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker --collect-only -q` and
        repair each collection error against the live output. The current live errors are:
        - `code/tests/e2e/test_simple_output_verify.py` — imports
          `model_checker.output.collectors.ModelDataCollector`, which no longer exists (the
          `output/` module has no `collectors` submodule). Repair against the restored `output`
          module if an equivalent collector exists; otherwise delete the stale test.
        - `code/src/model_checker/builder/tests/integration/test_interactive.py` — imports
          `SequentialSaveManager` from `model_checker.output`, which is not exported (output exports
          `ANSIToMarkdown`, `JSONFormatter`, `MarkdownFormatter`, `formatters`). Repair against the
          current `output.manager` API or delete if the interactive save flow is gone.
        - `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` — imports
          `WitnessSemanticError` from `theory_lib.errors`, which does not exist (available:
          `WitnessError`, `SemanticError`, `WitnessConstraintError`, etc.). Repair to the correct
          exception name(s) or delete if the referenced behavior is gone.
  - [ ] Re-verify the parent plan's originally-flagged files against the live tree:
        `tests/integration/test_model_building_sync.py`, `tests/integration/test_system_imports.py`,
        and `tests/utils/helpers.py` currently collect cleanly (builder/iterate restored), so they
        need no change unless a widened `testpaths` surfaces a new error — do not delete files that
        collect.
  - [ ] For each delete-vs-repair decision, prefer repair when the referenced capability exists in a
        restored module under a new name; delete only when the referenced module/symbol is genuinely
        absent. Record the decision per file in the summary.
- **Timing:** 1 hour
- **Depends on:** 2
- **Files to modify:**
  - `code/pyproject.toml` — `[tool.pytest.ini_options] testpaths`
  - `code/tests/e2e/test_simple_output_verify.py` — repair or delete
  - `code/src/model_checker/builder/tests/integration/test_interactive.py` — repair or delete
  - `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` — repair or delete
- **Verification:**
  - `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker --collect-only -q` reports zero
    collection errors (exit status reflects collection success; the trailing summary shows
    `N tests collected` with no `errors`).

### Phase 4: Add pytest-xdist and Final Verification [NOT STARTED]

- **Goal:** Enable parallel execution of the slow suite and confirm the zero-collection-error gate
  end to end.
- **Tasks:**
  - [ ] Add `pytest-xdist` to the dev dependencies (e.g. a `[project.optional-dependencies] dev` or
        `test` extra, or the existing dev-dependency mechanism used by the repo) so
        `PYTHONPATH=code/src pytest -n auto code/tests/ code/src/model_checker` is available.
  - [ ] Document `-n auto` usage: add a short note in `code/tests/README.md` (and/or as a comment
        near the pytest config) describing parallel invocation for the slow bimodal suite. Keep the
        note inside `code/` (deliverable, no task-number references).
  - [ ] Run `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` and the widened
        `code/tests/ code/src/model_checker --collect-only -q` once more to confirm zero collection
        errors after all edits.
  - [ ] Smoke-check the console entry point resolves: `python -m model_checker --help` runs.
- **Timing:** 45 minutes
- **Depends on:** 3
- **Files to modify:**
  - `code/pyproject.toml` — add `pytest-xdist` dev/test dependency
  - `code/tests/README.md` — document `-n auto` usage
- **Verification:**
  - `python -c "import xdist"` (after install) or presence of `pytest-xdist` in the declared dev
    extra; `pytest -n auto --collect-only -q` is accepted by the config.
  - `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker --collect-only -q` — zero errors.
  - `PYTHONPATH=code/src python -m model_checker --help` exits 0.

## Testing & Validation

- [ ] `python -c "import tomllib; ..."` confirms `[project] name == "model-checker"` and version set.
- [ ] `grep -n "bimodal" code/pyproject.toml` shows no bimodal identity, script, or oracle
      entry-point remnants.
- [ ] All `MANIFEST.in` include paths resolve to existing files/directories.
- [ ] `python -m build code/` produces an sdist/wheel that contains `model_checker/jupyter/` and the
      four theory READMEs and excludes any oracle/`bimodal_logic` content.
- [ ] `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker --collect-only -q` reports zero
      collection errors.
- [ ] `pytest-xdist` is declared; `pytest -n auto --collect-only -q` is accepted.
- [ ] `PYTHONPATH=code/src python -m model_checker --help` runs.

## Artifacts & Outputs

- `code/pyproject.toml` — restored `model-checker` identity, dependencies, optional-dependency
  extras, single console script, no oracle entry-points, widened `testpaths`, `pytest-xdist` dev
  dependency.
- `code/MANIFEST.in` — reconciled include paths (theories + jupyter), no dead references.
- `code/src/model_checker/__init__.py` — version single-sourcing confirmed (edited only if needed).
- Repaired-or-deleted stale test files (final set determined by Phase 3 live output).
- `code/tests/README.md` — `-n auto` parallel-run note.
- `specs/121_restore_package_identity_and_repair_test_infrastru/summaries/01_*-summary.md`
  (implementation summary, created at implement time).

## Rollback/Contingency

All edits are confined to `code/pyproject.toml`, `code/MANIFEST.in`, `code/src/model_checker/`
test files, and `code/tests/`. To revert, `git checkout -- code/pyproject.toml code/MANIFEST.in`
and restore any deleted test files from git history on the `task-117-restore-model-checker`
branch. Because no source modules (only packaging metadata and test files) are changed, reverting
cannot regress the restored theory functionality delivered by tasks 118-120. If a stale-test
delete later proves wrong, the file is recoverable from git history and can be repaired instead.
