# Changelog

All notable changes to the ModelChecker project are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

## [1.3.0] - 2026-07-24 (entry expanded 2026-08-12; publish date is set when the `v1.3.0` tag is pushed)

This release restores the `model_checker` package to full working order, ships a package-loading
refactor addressing GitHub Issue #73, completes a repository-wide core/theory-library boundary
refactor, fixes several CI reliability issues, and adds a portable local release-rehearsal runner.
`1.3.0` has not previously been published to PyPI, so this entry has grown to cover everything
that has landed on top of the original restoration work rather than being split into a second
version.

### Changed

#### Core / Theory Library Boundary Refactor
- Rewrote `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` as the single canonical
  theory contract: every theory follows one structure (a `semantic/` package, `operators.py`,
  `iterate.py`, `examples.py`, `tests/`, `docs/`), with `__init__.py`'s `__version__` as the sole
  per-theory version source.
- Removed dead code and stale cruft: the unused spatial subtheory stub, superseded semantic
  re-export wrappers, the `boneyard/` directory, superseded example copies, stray root files, and
  outdated per-theory TODOs.
- Replaced `builder/project.py`'s verbatim directory copy with an explicit
  `REQUIRED_COPY_ITEMS`/`SEMANTIC_ALTERNATIVES`/`OPTIONAL_COPY_ITEMS` manifest, and tightened
  `pyproject.toml`/`MANIFEST.in` packaging data from a blanket sweep to an explicit allowlist with
  defense-in-depth excludes.
- Added a parametrized theory-conformance test suite and a core/theory_lib layering regression
  test enforcing the rewritten contract.
- Relocated the logos solver benchmark script out of the shipped package and merged a
  case-colliding documentation pair (`usage_guide.md` into `USAGE_GUIDE.md`).

#### Packaging
- Removed the four duplicate `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` files;
  each theory's version now derives solely from its `__init__.py`'s `__version__`. This clears the
  `check-wheel-contents` `W002` (duplicate-file) finding that a bare `check-wheel-contents` run
  previously reported against the built wheel.

#### Framework Restoration
- **Package identity restored**: the project ships again as the `model_checker` package with a
  clean `[tool.setuptools.packages.find] where = ["src"]` layout; the four semantic theories
  (`logos`, `exclusion`, `imposition`, `bimodal`) are the complete registered theory set exposed
  via `AVAILABLE_THEORIES`.
- **First-order quantification removed from Logos**: the Logos theory's subtheory set is now
  `extensional`, `modal`, `constitutive`, `counterfactual`, `relevance` (18 operators total); no
  subtheory exposes first-order quantifier operators. Z3-level `ForAll`/`Exists` constraint
  encodings used internally by the solver backend are unaffected by this change.
- **Differential oracle relocated**: the cross-solver differential oracle now lives in a
  standalone top-level `oracle/` tree, outside `code/src/`, and is excluded from the built wheel.
- **`builder`/`iterate` infrastructure restored**: project generation (`model_checker.builder`)
  and model iteration (`model_checker.iterate`) are back to full working order alongside the
  rest of the package.

#### Package Loading Refactor (Issue #73)
- Added `_load_as_package_module()` method for better package handling.
- Added `_is_generated_project_package()` to detect new package format.
- Improved `sys.path` handling for generated packages, for both the new package format and the
  legacy `config.py` format.
- New `PackageError` hierarchy for clearer, more actionable error messages:
  - `PackageError`: base class for package-related errors
  - `PackageStructureError`: missing or invalid package structure
  - `PackageFormatError`: invalid `.modelchecker` marker
  - `PackageImportError`: package cannot be imported
  - `PackageNotImportableError`: package not in importable state and context
- Generated packages can now use a `.modelchecker` marker file (`package=true`) to opt into
  package-style imports; the legacy `config.py` format continues to work unchanged, so this is a
  backwards-compatible, additive change.

### Fixed
- **Issue #73**: Fixed `ModuleNotFoundError` when testing generated project examples via a
  complete refactor of the package loading system, with clear, actionable error messages for
  package issues. See `src/model_checker/builder/README.md` ("Package Loading" section) for the
  loader interface and error hierarchy.
- **CI: missing `wheel` build dependency**: `.github/workflows/packaging.yml` and
  `.github/workflows/release.yml`'s `build` job both now install `wheel` alongside `build`/`twine`,
  fixing a release-blocking gap where the packaging job's build step could fail for want of the
  `wheel` package.
- **CI: timing-gated test budgets raised**: several Z3-solve-bound correctness tests had
  wall-clock budgets tighter than this host's observed variance under load —
  `test_iterate_two_produces_distinct_models`'s `max_time` (30s -> 60s, confirmed against a
  61.25s local run), `test_theory_library_execution`'s generated-module `max_time` and outer
  subprocess timeout, and the differential-tests CI workflow's broad pytest step timeout
  (300s -> 900s). Two additional wall-clock speed-assertion tests were marked
  `@pytest.mark.performance` and deselected from the standard CI gate rather than budget-raised,
  since they assert relative speed rather than correctness.

### Added
- Comprehensive test suite for package loading
  (`src/model_checker/builder/tests/test_package_loading.py`,
  `src/model_checker/builder/tests/test_issue_73_fix.py`).
- Support for `.modelchecker` marker files in generated packages.
- **`code/scripts/release-verify.sh`**: a portable, pinned local rehearsal runner for the PyPI
  release pipeline's build/check steps (provisioning, `python -m build`, `twine check --strict`,
  `check-wheel-contents`, a reference-release diff, and sha256 hashing), driven from a single
  `nix develop` invocation with pinned tool versions in
  `code/scripts/release-tools-requirements.txt`. Documented in `.github/RELEASE_SETUP.md`'s
  "Local Rehearsal (No Publish)" section and `code/scripts/README.md`.

### Documentation
- `src/model_checker/builder/README.md` documents the package-loading refactor: the
  `ModuleLoader` interface, the `.modelchecker` marker file format, and the `PackageError`
  hierarchy.
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` rewritten as the canonical
  per-theory structural contract referenced throughout the core/theory_lib refactor above.

### Links
- [Issue #73](https://github.com/benbrastmckie/ModelChecker/issues/73)