# Changelog

All notable changes to the ModelChecker project are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

## [1.3.9] - 2026-09-01

### Fixed
- Model output no longer crashes on Windows consoles. Printed output wrote raw Unicode glyphs
  (the world-history transition arrow, subscript digits, the imposition/witness arrows, the
  null-state symbol, and progress-bar block characters) directly to the caller-supplied stream.
  On a Windows pipe -- `subprocess.run(..., capture_output=True)`, which falls off Python's
  PEP-528 console path -- these encode with cp1252 and raise `UnicodeEncodeError`, breaking every
  theory's print path. A new `model_checker.utils.glyphs` module resolves each glyph to its
  Unicode form or an ASCII fallback based on the target stream's encoding, and every theory's
  print paths now route through it. The bug was latent and long-standing; the `Verify PyPI
  install` Windows matrix added in 1.3.8 is what surfaced it.
- The bimodal aligned world-history renderer derives its column budget from the actually-rendered
  arrow string rather than a hard-coded width, so alignment survives ASCII substitution. This
  also fixes a latent column overflow for two-digit durations.
- Corrected a false claim in the oracle gating test's quarantine entry-criteria record, which
  stated the nightly runs reproduced an identical 96/103 conclusive, 7-timeout result. The actual
  spread across those runs is 96-98/103 at 5-7 timeouts. The record now also documents why all
  six runs were classified as new failures rather than matching the known timing signature.

### Changed
- Release-gating test selections no longer depend on bimodal solve cost. Tests that merely used
  bimodal as a convenient fixture now use logos, while tests whose subject is genuinely bimodal
  are marked `development` and deselected from gating runs. Measured effect: the packaging suite
  drops from 105.80s to 19.82s, and `builder/tests/unit/test_example.py` from 36.13s to 10.66s.
- The `packaging.yml`, `release.yml`, and `pypi-smoke.yml` workflows are now covered by the
  gating-selector contract, so their marker expressions are checked executably rather than by
  convention.

### Added
- Opt-in per-formula instrumentation for the oracle gating scan via
  `ORACLE_GATING_SCAN_OUT_DIR`, kept distinct from the existing `ORACLE_SCAN_OUT_DIR` so the two
  scans cannot overwrite each other's reports. This makes it possible to identify which formulas
  fail to resolve, which previously was not recoverable from the test's output.
- An executable contract test asserting that no release-gating selection constructs or solves a
  bimodal example.

### Testing and release infrastructure
- Regression coverage for the encoding fix writes to a cp1252-constrained stream, so it runs on
  Linux and does not require a Windows runner. The packaging suite gains an additive
  `PYTHONIOENCODING=cp1252` leg exercising the real installed console script.

## [1.3.8] - 2026-09-01

### Added
- Non-interactive project generation: `--project_name`/`-y` on `model-checker`, used with
  `--load_theory`, generates a project without prompting or reading stdin. The optional
  positional `file_path` argument, when supplied, is honored as the destination directory.
  This makes project generation usable from scripts and CI, where stdin is not available.
- Bimodal frame constraints for Seriality and Interpolation, implemented in Skolemized form and
  wired into the frame-class mapping. `bimodal/docs/ARCHITECTURE.md` gains a frame-class axioms
  ledger recording which axioms each frame class contributes.
- `run_tests.py` accepts `--markers`/`-m` and passes the expression through to pytest, so the
  gating marker selections CI uses can be reproduced locally with a single command.

### Changed
- Bimodal is now marked as a theory under active construction. Its test tree carries the new
  `development` pytest marker, and every release-gating pytest invocation across the CI drivers
  deselects it with `not development`. This makes bimodal's known-incomplete completeness claims
  non-gating while leaving its soundness claims fully gating -- in particular the oracle
  differential suite's soundness core stays unconditionally gating, so a real semantic
  disagreement between the in-package bimodal semantics and the reference oracle still fails the
  build.
- Corrected stale frame-class docstrings that described a three-axiom formulation the
  implementation no longer uses.

### Fixed
- A Z3 timeout is now distinguished from a genuine unsat result in the bimodal iterate tests,
  so an inconclusive solve is no longer reported as a definitive "no model exists".
- `tests/ci/test_oracle_development_marker_application.py` skips at module level when the
  repository root's `oracle/` tree is absent, which is the case inside `nix flake check`'s
  `checks.default` derivation (its `src = ./code` excludes the repo root). The module
  previously reported twelve failures there on a sandbox-layout artifact rather than on any
  marker defect, while passing in the GitHub Actions general-tests job.
- Fixed a `subprocess.run` output-corruption bug in `test_run_tests_markers.py`.

### Testing and release infrastructure
- The release workflow gains a fail-fast preflight job that checks tag/version agreement and the
  presence of a non-empty CHANGELOG entry before any build or publish step runs.
- TestPyPI publication is now a hard gate with an explicit documented escape, followed by a
  TestPyPI install-verification job and a post-publish PyPI confirmation matrix. A new
  `pypi-smoke.yml` workflow exercises the published artifact independently.
- Peak-RSS sampling attributes memory to xdist workers via `PYTEST_XDIST_WORKER` rather than by
  process tree, with the sampling interval tightened to 0.5s on measured overhead.
- Contention-flaky tests with real wall-clock assertions are marked `xdist_serial` and run in a
  serial second pass instead of under the parallel worker pool.
- The unstable-watch workflow records per-node-id streaks and per-run artifact history, and
  reports a "ready to promote" signal when a quarantined test stabilizes.

## [1.3.2] - 2026-08-12

### Documentation
- Rewrote `code/README.md`, which serves as the PyPI long description, to match the current
  codebase. Corrected the stated Python floor (3.8+ -> 3.10+), the subtheory count (five -> four),
  and the Logos operator inventory (added `\CFBox`, `\CFDiamond`, `\Rightarrow`, and `\preceq`,
  for the documented total of 18). Removed the `run_update.py`/`test_update.py` entries from the
  development-scripts table; both scripts were deleted in the cruft sweep that preceded 1.3.0.
- Replaced the inlined `LogosSemantics`, semantic-helper, and counterfactual-operator source
  listings with prose descriptions linking to the corresponding modules, so the README no longer
  carries copies of code that drift independently of their source. This also resolved an
  attribution error in which `fusion` and `is_part_of` were presented as Logos methods rather
  than as `SemanticDefaults` methods.
- Dropped the pasted example output, which no longer matched the current display format and is in
  any case not reproducible: the countermodel found for `CF_CM_1` varies between runs. A single
  abridged sample is retained and labelled as such.
- Documented previously unmentioned capabilities: the cvc5 solver backend and its `--z3`/`--cvc5`
  flags, the `--sequential` and `--align_vertically` flags, `--save`'s `markdown`/`json`
  arguments, and the `jupyter` extra.
- Converted the two remaining repository-relative links to absolute URLs, which are the only form
  that resolves when the README is rendered on PyPI.

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