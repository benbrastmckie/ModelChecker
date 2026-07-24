# Changelog

All notable changes to the ModelChecker project are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

## [1.3.0] - 2026-07-24

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

#### Package Loading Improvements
- Added `_load_as_package_module()` method for better package handling
- Added `_is_generated_project_package()` to detect new package format
- Improved sys.path handling for generated packages
- Better error messages when packages cannot be imported

#### New Package Format Support
- Generated packages can now use `.modelchecker` marker file
- Marker file with `package=true` enables package-style imports
- Supports both new package format and legacy `config.py` format

#### Error Handling Improvements
- New `PackageError` hierarchy for clearer error messages:
  - `PackageError`: Base class for package-related errors
  - `PackageStructureError`: Missing or invalid package structure
  - `PackageFormatError`: Invalid .modelchecker marker
  - `PackageImportError`: Package cannot be imported
  - `PackageNotImportableError`: Package not in importable state and context

### Fixed
- **Issue #73**: Fixed ModuleNotFoundError when testing generated project examples
  - Complete refactor of package loading system
  - Clear, actionable error messages for package issues

### Added
- Comprehensive test suite for package loading (`test_package_loading.py`, `test_issue_73_fix.py`)
- API documentation for ModuleLoader (`docs/api/builder/loader.md`)
- Project creation guide (`docs/guides/project_creation.md`)
- Support for `.modelchecker` marker files in generated packages

### Documentation
- Updated builder package README with package loading improvements
- Created API documentation for loader module
- Updated error handling documentation with new error types
- Added project creation guide

### Internal
- Better sys.path handling for generated packages
- Support for both legacy and new package formats
- Improved error messages with context
- Backwards compatibility maintained

## Migration Optional

This update maintains backwards compatibility while adding new features:

1. Existing projects continue to work with `config.py`
2. New projects can use `.modelchecker` marker for cleaner imports
3. Both formats are supported simultaneously
4. Error handling improvements benefit all users

## Performance Impact

- No performance regression in module loading
- Test suite passes completely
- Better error messages aid debugging

## Links

- [Issue #73](https://github.com/benbrastmckie/ModelChecker/issues/73)
- [Implementation Plan](specs/plans/issue_73_package_loading_refactor.md)
- [Migration Guide](docs/migration/package_loading_v2.md)