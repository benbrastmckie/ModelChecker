---
next_project_number: 127
---

# TODO

## Task Order

*Updated 2026-07-24. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 126 | -- | architecture |

**Grouped by Topic** (indented = depends on parent):

### Architecture

126 [IMPLEMENTING] — Systematically refactor the repo into: 1) the core codebase conta

## Tasks

### 126. Refactor repo core infrastructure theory lib
- **Status**: [IMPLEMENTING]
- **Task Type**: general
- **Topic**: architecture
- **Dependencies**: None
- **Research**: [126_refactor_repo_core_infrastructure_theory_lib/reports/01_team-research.md]
- **Plan**: [126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md]
- **Summary**:
  - [126_refactor_repo_core_infrastructure_theory_lib/summaries/01_phases-2-6-summary.md]
  - [126_refactor_repo_core_infrastructure_theory_lib/summaries/02_phases-1-9-summary.md]

**Description**: Systematically refactor the repo into: 1) the core codebase containing all appropriate utilities and resources (the model-checker infrastructure); 2) the theory_lib consisting of the bimodal, exclusion, imposition, and logos theories; and 3) remove the spatial subtheory from the logos theory. If it makes more sense, move theory_lib/ into src/, making any other natural restructuring as needed. Systematically review the modules throughout the codebase to design a full refactor improving organization, code quality, and uniformity, with a standardized set of modules for each theory/subtheory as appropriate, making systematic changes however improves the final state of the repo.

---

### 125. Release engineering and pypi rehearsal
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: packaging
- **Dependencies**: Task 123, Task 124
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [125_release_engineering_and_pypi_rehearsal/plans/01_release-engineering-pypi-rehearsal.md]
- **Summary**: [125_release_engineering_and_pypi_rehearsal/summaries/01_release-engineering-summary.md]

**Description**: Covers plan phase 13 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Release Engineering and Rehearsal'). Requires the Nix-verified build (flake task) as the ground-truth build target for parity checks, and the refreshed docs/CHANGELOG (documentation task) for the release checklist narrative. No agent publishes to PyPI or pushes to git in this task -- per .claude/rules/pr-prohibition.md, publish and push are strictly user-only actions. Goal: fix .github/workflows/release.yml (`cd Code` -> `cd code` in both jobs); reconcile .github/RELEASE_SETUP.md with the single actual workflow; migrate the publish job to PyPI Trusted Publishing (OIDC) via pypa/gh-action-pypi-publish@release/v1 in a separate, environment-gated (pypi) job with permissions: id-token: write, dropping the long-lived PYPI_API_TOKEN; add `twine check --strict`; add a TestPyPI rehearsal step and perform a local rehearsal (`python -m build`, `check-wheel-contents`, and a wheel-content/hash parity diff vs `pip download --no-deps model-checker==1.2.12`, run NixOS-safe inside `nix develop`); confirm the built artifact is named model_checker-<version>, not bimodal_logic; confirm the final version number (set provisionally in the package-identity task) and prepare a step-by-step publish checklist ending in the user-only actions -- user pushes the branch/tag and either invokes /merge or triggers the release workflow. Explicitly mark publish + push as user-gated in the checklist; the agent performs neither. Verification: release.yml casing fixed; OIDC Trusted Publishing configured; `python -m build` produces a model_checker-<version> wheel/sdist excluding the oracle directory; `check-wheel-contents` clean; wheel-content parity diff vs 1.2.12 reviewed and documented; `twine check --strict dist/*` passes; TestPyPI rehearsal succeeds; publish checklist handed to the user with publish/push explicitly marked user-only.

---

### 124. Documentation refresh for the restored framework
- **Effort**: 2 hours
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: packaging
- **Dependencies**: Task 122
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [124_documentation_refresh_for_the_restored_framework/plans/01_docs-refresh.md]
- **Summary**: [124_documentation_refresh_for_the_restored_framework/summaries/01_docs-refresh-summary.md]

**Description**: Covers plan phase 12 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Documentation Refresh'). Requires the full green test gate (prior wave) to be established so docs describe the definitive, working state rather than in-progress restoration. Goal: fix root README.md's `pip install model-checker[jupyter]` quick-start and the dead link to jupyter/README.md; ensure the four-theory framing (logos, bimodal, exclusion, imposition) matches the actual registered AVAILABLE_THEORIES set; fix code/README.md's `cd ModelChecker/Code` casing to `cd code` and update its component table to reflect restored builder/iterate and the relocated oracle directory; reconcile CLAUDE.md's canonical test command and architecture description with reality; add an honest code/CHANGELOG.md entry for this release (identity restore, theory set, first-order removal, oracle relocation); check docs/usage/SEMANTICS.md for stale first-order references and code/scripts/README.md for the dead link to the deleted docs/theory/QUANTIFIER_SOLVERS.md, fixing both; cross-check that code/MANIFEST.in (edited by the package-identity task) resolves against real paths -- read-only verification here, do not re-edit MANIFEST.in itself; as a non-blocking follow-up, seed specs/ROADMAP.md with the durable identity decision. Verification: no dead links in README.md/code/README.md/code/scripts/README.md; CLAUDE.md's test command matches the actual canonical command; CHANGELOG.md has an honest entry; no stale first-order or bimodal-logic references remain in user-facing docs.

---

### 123. Rewrite the nix flake for multisystem build and te
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Task Type**: nix
- **Topic**: packaging
- **Dependencies**: Task 122
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [123_rewrite_the_nix_flake_for_multisystem_build_and_te/plans/01_nix-flake-multisystem-rewrite.md]
- **Summary**: [123_rewrite_the_nix_flake_for_multisystem_build_and_te/summaries/01_nix-flake-multisystem-rewrite-summary.md]

**Description**: Covers plan phase 11 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Nix Flake Rewrite'). Requires the full test suite already green (prior task) so the flake's checks.default target validates a known-good state rather than surfacing unrelated failures, and the finalized package identity (pyproject.toml from the package-identity task) as the packages.default build target. Goal: rewrite root flake.nix to be multi-system (flake-utils or an explicit system list, replacing the hardcoded x86_64-linux); add packages.default via nixpkgs-native `buildPythonPackage { pyproject = true; }` against python3Packages.z3 (NOT the PyPI z3-solver wheel), with networkx included; add checks.default running the canonical pytest suite so `nix flake check` is a real gate; provide a devShell that subsumes what code/shell.nix offered (z3, setuptools, pip, networkx, pytest), making the ../BimodalHarness path strictly optional (no failure/warning path required for a standalone checkout); commit flake.lock; delete code/shell.nix (no backwards-compat layer); verify `nix build` and `nix flake check` succeed locally. This task exists specifically because pip install is impractical on NixOS -- the flake is the primary NixOS-native install/test path. Verification: `nix build` succeeds and produces a working model-checker package; `nix flake check` runs and passes the pytest suite; devShell provides a working development environment without requiring ../BimodalHarness; code/shell.nix removed.

---

### 122. Rootcause crossoracle differential and establish t
- **Effort**: 4 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118, Task 121
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [122_rootcause_crossoracle_differential_and_establish_t/plans/01_rootcause-differential-green-gate.md]
- **Summary**: [122_rootcause_crossoracle_differential_and_establish_t/summaries/01_rootcause-differential-green-gate-summary.md]

**Description**: Covers plan phases 9-10 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Root-Cause Cross-Oracle Differential Failures' and 'Full Green Test Gate'). Requires the oracle already relocated (bootstrap task) and the test suite widened/collectible (package identity + test infra task). Goal (differential): with the oracle differential harness moved to oracle/bimodal_logic/, confirm the in-package theory_lib/bimodal suite passes without BimodalHarness present; for the relocated test_cross_oracle_differential.py, run it in its new oracle context and root-cause the 2-4 consistent failures noted in research (regression vs. environment/xfail behavior), fixing or correctly marking and documenting them; record the definitive bimodal pass/fail tally against the Phase 1 baseline captured by the bootstrap task. Goal (green gate): run the full model_checker suite to completion (all theories + top-level tests) using pytest-xdist, achieving green or documented/justified skips/xfails only; run the relocated oracle suite separately to green; smoke-test the CLI end-to-end (`python -m model_checker --help`, a representative example run, and --maximize/--save paths if quick); record final pass counts and runtimes as the release baseline in the task directory. Verification: in-package bimodal suite green without BimodalHarness; differential failures root-caused and documented; full suite green (or documented skips/xfails) via pytest-xdist; oracle suite green; CLI smoke tests pass; release baseline recorded.

---

### 121. Restore package identity and repair test infrastru
- **Effort**: 3.5 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118, Task 119, Task 120
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [121_restore_package_identity_and_repair_test_infrastru/plans/01_restore-package-identity-test-infra.md]
- **Summary**: [121_restore_package_identity_and_repair_test_infrastru/summaries/01_restore-package-identity-test-infra-summary.md]

**Description**: Covers plan phases 7-8 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Restore Package Identity (pyproject.toml, MANIFEST.in)' and 'Repair Test Infrastructure'). Requires the oracle relocation and all theory registrations (logos, exclusion, imposition) to be complete so package-data include/exclude and testpaths can be finalized. Goal (identity): in code/pyproject.toml set [project] name = "model-checker"; choose next version (recommend 1.3.0 given the restored theory set and first-order removal since PyPI 1.2.12, final number confirmed in the release task); restore description/keywords/classifiers to the framework identity; restore dependencies to match PyPI 1.2.12 intent (z3-solver>=4.8.0, networkx>=2.0, jupyter/all optional-dependency extras: ipywidgets, matplotlib, networkx, jupyter, ipython); keep only the `model-checker = "model_checker.__main__:run"` console script, removing the bimodal-logic script and the [project.entry-points."bimodal_harness.oracle_providers"] table (already moved to oracle/ by the bootstrap task); ensure [tool.setuptools.packages.find] and package-data include model_checker (with restored jupyter/ notebooks) and exclude the relocated oracle directory; reconcile version single-sourcing in model_checker/__init__.py's get_model_checker_version(); update code/MANIFEST.in to keep theory_lib/{logos,bimodal,exclusion,imposition} and jupyter/ includes, removing references to paths that no longer exist. Goal (test infra): widen [tool.pytest.ini_options] testpaths beyond bimodal-only to cover code/tests/ and all registered theories (or remove the pin so `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker` works per CLAUDE.md); fix or delete stale top-level tests referencing formerly-deleted modules (tests/e2e/test_simple_output_verify.py, tests/integration/test_model_building_sync.py, tests/integration/test_system_imports.py, tests/utils/helpers.py) -- repair against restored builder/output modules where meaningful, delete where obsolete; add pytest-xdist (dev dependency + -n auto usage documented) to parallelize the slow bimodal suite; confirm `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` reports zero collection errors. Verification: pyproject.toml declares model-checker identity with restored deps/entry-point; MANIFEST.in resolves against real paths; zero pytest collection errors across code/tests/ and code/src/model_checker.

---

### 120. Restore and port the exclusion and imposition theo
- **Effort**: 6 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 119
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [120_restore_and_port_the_exclusion_and_imposition_theo/plans/02_port-exclusion-imposition.md]

**Description**: Covers plan phases 5-6 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Restore and Port the exclusion Theory' and 'Restore and Port the imposition Theory'). This is the highest-risk work in the plan: both theories restore from a PRE-solver-migration commit (abb3bf7d^), predating z3_shim, model_checker.solver, and the modular models.semantic/models.proposition/models.structure package structure, and must be ported to the current API. Use the already-current-API bimodal and logos theories (from the prior task) as the concrete reference pattern for the port. Goal (exclusion): `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/exclusion`; port imports/APIs from pre-migration to current: model_checker.z3_shim, model_checker.solver (is_true/is_false), models.semantic.SemanticDefaults, models.proposition.PropositionDefaults, models.structure.ModelDefaults, syntactic.atoms.get_atom_sort, and bimodal witness modules; register exclusion in AVAILABLE_THEORIES; get theory_lib/exclusion/tests/ to collect and pass; commit per green sub-step. Goal (imposition): `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/imposition`; apply the same import/API porting recipe established for exclusion; register imposition in AVAILABLE_THEORIES; get theory_lib/imposition/tests/ to collect and pass; commit per green sub-step. If porting exceeds budget, the plan's documented fallback is to ship with logos+bimodal registered and follow up on exclusion/imposition separately -- but the goal is full restoration; treat the fallback as a last resort. Verification: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion -q` and `.../imposition -q` both green; both registered in AVAILABLE_THEORIES; no import errors against current z3_shim/solver/models.* API.

---

### 119. Restore core infrastructure and reconcile the logo
- **Effort**: 4.5 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [119_restore_core_infrastructure_and_reconcile_the_logo/plans/01_restore-core-infra-logos.md]
- **Summary**: [119_restore_core_infrastructure_and_reconcile_the_logo/summaries/01_restore-core-infra-logos-summary.md]

**Description**: Covers plan phases 3-4 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Restore Core Infrastructure (builder, iterate, jupyter, output)' and 'Reconcile and Register the logos Theory'). Requires task branch and confirmed restore-point SHAs from the bootstrap task. Goal: restore deleted general-purpose infrastructure via `git checkout 013a486c^ -- code/src/model_checker/builder`, `git checkout c21b3709^ -- code/src/model_checker/iterate code/src/model_checker/jupyter`, and `git checkout 71ef79a1^ -- code/src/model_checker/output/manager.py code/src/model_checker/output/progress`; reconcile imports via smoke tests for model_checker.builder, model_checker.iterate, model_checker.output.manager, fixing any references broken since the (post-solver-migration) restore point; verify `PYTHONPATH=code/src python -m model_checker --help` and `python code/dev_cli.py --help` both run without ModuleNotFoundError; commit per green sub-step. Then reconcile theory_lib/logos/: confirm its `from .iterate import ...`/`model_checker.iterate` imports now resolve (iterate just restored), fix any residual import paths; verify the first-order subtheory removal (commit e9734a27) is intact with no dangling references; register logos (and its retained subtheories) in theory_lib's AVAILABLE_THEORIES; get theory_lib/logos/tests/ to collect and pass via `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q`. Verification: builder/iterate/jupyter/output.manager import cleanly; CLI --help commands work; logos registered in AVAILABLE_THEORIES; logos test suite green.

---

### 118. Bootstrap branch baseline capture and oracle reloc
- **Effort**: 3 hours
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md]
- **Plan**: [118_bootstrap_branch_baseline_capture_and_oracle_reloc/plans/01_branch-baseline-oracle-relocation.md]
- **Summary**: [118_bootstrap_branch_baseline_capture_and_oracle_reloc/summaries/01_branch-baseline-oracle-relocation-summary.md]

**Description**: Covers plan phases 1-2 of specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md ('Branch, Inventory, and Baseline Capture' and 'Separate the Bimodal-Oracle/Harness Layer'). Goal: create a task branch (e.g. task-117-restore-model-checker) off master (do not push); record a pre-change baseline (run the live bimodal suite once for pass/fail + timing, snapshot the currently-failing `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` and `python -m model_checker --help` output, both saved under the task directory); inventory the restore-point SHAs from the plan's git-restore table and confirm each restore source path exists via `git ls-tree <sha>^ -- <path>` (013a486c^ for builder/, c21b3709^ for iterate/jupyter, 71ef79a1^ for output/manager.py+progress/, abb3bf7d^ for exclusion/imposition). Then relocate the bimodal-oracle/harness layer: move code/src/bimodal_logic/ (cli.py, provider.py, serialization.py, translation.py, __init__.py, tests/) to a new top-level oracle/bimodal_logic/ directory at repo root; delete the stale code/src/bimodal_logic.egg-info/; move the cross-oracle differential harness/tests that depend on BimodalHarness (theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py and any oracle-only helpers) alongside the oracle; give the oracle its own minimal dev setup (own pyproject.toml or a README documenting PYTHONPATH-based standalone development and the bimodal_harness.oracle_providers entry point); confirm nothing under code/src/model_checker/ imports bimodal_logic (fix-forward any residual references); verify the oracle's own tests still collect from its new location. Verification: branch exists; baseline artifacts saved under the task directory; oracle/bimodal_logic/ exists with its own tests collecting; code/src/model_checker/ has zero references to bimodal_logic. This is the foundational task all others build on.

---

### 117. Review cli pypi parity nix flake release
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 118, Task 119, Task 120, Task 121, Task 122, Task 123, Task 124, Task 125
- **Research**:
  - [117_review_cli_pypi_parity_nix_flake_release/reports/01_team-research.md]
  - [117_review_cli_pypi_parity_nix_flake_release/reports/03_team-research.md]
- **Plan**: [117_review_cli_pypi_parity_nix_flake_release/plans/03_stabilize-and-release-closeout.md]
- **Summary**: [117_review_cli_pypi_parity_nix_flake_release/summaries/03_stabilize-and-release-closeout-summary.md]

**Description**: Review and stabilize the repo after recent revisions: verify the CLI works, audit discrepancies with the model-checker package on PyPI, build a Nix flake for testing on NixOS (pip install is impractical there), complete full testing, and prepare a top-quality release to push to PyPI

---

### 116. Draft email modelchecker architecture
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None

**Description**: Draft a brief email for a Python expert explaining how the ModelChecker supports modular extensions: each model structure is built over shared general infrastructure and supports a range of operators supplied semantic clauses using that model structure's resources. Explain the basic architecture and the pipeline by which logical claims are processed into SMTlib, solved, then passed back to print a model, where key methods are provided by each operator. Culminate with code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py as a worked example. Draw on docs/ and distributed README.md files as appropriate.
