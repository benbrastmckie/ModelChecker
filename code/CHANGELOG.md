# Changelog

All notable changes to the ModelChecker project are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

## [1.3.0] - 2026-07-24

This release restores the `model_checker` package to full working order and, alongside that
restoration, ships a package-loading refactor addressing GitHub Issue #73.

### Changed

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

### Added
- Comprehensive test suite for package loading
  (`src/model_checker/builder/tests/test_package_loading.py`,
  `src/model_checker/builder/tests/test_issue_73_fix.py`).
- Support for `.modelchecker` marker files in generated packages.

### Documentation
- `src/model_checker/builder/README.md` documents the package-loading refactor: the
  `ModuleLoader` interface, the `.modelchecker` marker file format, and the `PackageError`
  hierarchy.

### Links
- [Issue #73](https://github.com/benbrastmckie/ModelChecker/issues/73)