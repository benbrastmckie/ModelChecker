# Changelog

All notable changes to the ModelChecker project are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [1.4.1] - 2026-09-30

A presentation-focused release. No semantic core, certificate search, or truth-value behavior
changed; the work is in what the printers emit, how color is gated, and what notation users may
type.

### Changed
- The bimodal countermodel block is rewritten around time-labelled arrow-chain histories. Each
  countermodel now prints a `Search bounds: back=B, mid=M, fwd=F (N lassos: 1 main + K reserved
  witnesses)` header in place of the meaningless `Atomic States: 0`, then a `Histories:` block
  with a one-line legend and one aligned row per lasso: every state renders as `(t:atoms)` with
  signed time, `⟹` joins adjacent states, `|` separates the back / mid / fwd segments, `…`
  brackets the periodic segments, and `[ ]` marks the evaluation point. Position columns are
  padded to their widest cell across lassos so times align vertically. A `Box guesses:` table
  reads its `falsified at L{i}, t=±t` witness from the certificate itself, and
  `-a`/`--align_vertically` switches the block to a time-aligned table view.
- Printed output is now held to an 80-column budget, codified as a rule in
  `code/docs/core/CODE_STANDARDS.md`. The `Verification:` label was a single unwrapped
  ~234-character sentence on every example and is now wrapped; the history role column is bounded
  to a three-value vocabulary (`main` / `witness` / `reserved, unused`) so one long role no longer
  shoves every row rightward, with formula provenance left recoverable from the `Box guesses:`
  table. Over-80-column lines in the default bimodal view dropped from 35 to 2.
- `BimodalProposition.__repr__` prints named lasso labels (`|A| = < {L0}, {L1} >`) instead of bare
  integers, which were indistinguishable from time indices on lines that also carry `t=-2`.
  Labels sort numerically rather than lexicographically.
- The terse one-line `Evaluation point: L0 at t=-2` is replaced by a four-line labelled block
  (`Lasso` / `History` / `Position` / `Label`), sharing a history-rendering helper with the
  `Histories:` block. The logos and exclusion printers gained a matching `Evaluation world:`
  heading-plus-value block so the four theories stay visually consistent; imposition inherits it.
- Color gating is unified on `model_checker.output.color.use_colors(output)`
  (`NO_COLOR` > `FORCE_COLOR` > `TERM=dumb` > `isatty()`), replacing every
  `output is sys.__stdout__` / `sys.stdout` test in the framework, in the four theory printers,
  and in the `--maximize` runner. Piped and redirected output now receives plain text instead of
  leaked escape sequences. Blue coloring additionally extends to block labels, within the
  already-declared palette; no new color meanings were introduced, and color never carries
  information on its own.

### Added
- Operators may declare user-facing Unicode glyphs. An optional `aliases: List[str]` class
  attribute on `syntactic.Operator` is registered alongside the canonical LaTeX `name` by
  `OperatorCollection.add_operator`, so `aliases = ["∧"]` on the class named `"\\wedge"` makes
  both spellings parse to the same operator. No parser changes were required. All seven shipped
  theory `operators.py` files now declare curated aliases for their arity-1 and arity-2
  operators; operators with no standard glyph carry an inline comment saying so instead. Alias
  collisions fail loudly via `DuplicateOperatorError`, and unregistered lookups now raise
  `UnknownOperatorError` with a suggestion list rather than a bare `KeyError`. Documented in
  `docs/usage/OPERATORS.md`.
- Transition arrows carry Unicode-subscripted step durations (`⟹₁`) via the existing
  `utils/glyphs.py::to_subscript`, with encoding-fallback coverage.
- A `THEORY-LIMITS` example group in the bimodal `examples.py`, recording permanent limits of this
  theory or of its verified Lean counterpart, seeded with the stability-of-since certificate-
  incompleteness result and two active countermodel entries (`TL_CM_1`, `TL_CM_2`). The header
  block states the inclusion criterion, separates the genuine ℤ-time non-validity from the
  verified side's provably-empty certificate class, and names the superseded temporal-asymmetry
  diagnosis as refuted rather than restating it.
- `ELLIPSIS` (`…`, which survives cp1252 as 0x85) added to the glyph table; the unused `OMEGA`
  entry and the `(back)^ω | mid | (fwd)^ω` one-liner it served are removed.

### Fixed
- The `Witness: L{i} at position {p}` line read `WitnessRegistry._witness_lassos` — a reserved
  index, not provenance — and so reported `L1 at position None` for `\Box A` on `MD_CM_1` where
  the only falsifier was `(L3, t=+2)`. `BimodalStructure.box_witness` now scans the certificate
  for the actual falsifying position.

### Documentation
- The A1 / A1-Γ / A3 adequacy-chain component rows are applied to the bimodal `ADEQUACY.md` and
  `TRUST_PIPELINE.md`. A live cross-document contradiction over A3's stated form (magnitude
  versus representability) is resolved in favor of representability, A1 is recorded as partially
  discharged at the empty-premise single-conclusion instance with the general form split out as
  its own open obligation (A1-Γ), and every `WitnessFamily`/`Compression`-subtree citation
  migrates from `file.lean:NNN` line anchors to the name-plus-manifest convention. Every cited
  declaration was re-verified against the live Lean tree.

### Testing
- Golden-output assertions for the history block's shape and joiner-column alignment, an
  end-to-end maximum-line-width gate over a full example run, a standing audit test asserting
  that the only remaining `sys.__stdout__` use is the `Total Run Time` footer, cp1252 / ascii /
  utf-8 encoding legs for each new glyph, and a characterization suite pinning the exact
  before/after accept-reject set of `is_syntactically_wff` across its structural tightening.

### Known limitation
- Two printed lines still exceed 80 columns, both originating in `models/structure.py`'s
  framework-shared recursive sentence printer, which all four theories use identically. Bringing
  those within budget requires an independent rework of that printer and was deliberately left
  out of this release.

## [1.4.0] - 2026-09-28

### Changed
- The bimodal theory's semantic core is redesigned around witness-family certificate search over
  discrete (ℤ) time, replacing the window-and-abundance Z3 encoding introduced in 1.3.8. The new
  encoding is quantifier-free (no `ForAll`/`Exists`, no frame-axiom ledger), independently
  re-checks every found countermodel with a pure-Python checker, and never reports validity. All
  nine previously-excluded examples (including the paper's own MF axiom) now decide correctly,
  and the theory's `development` pytest marker -- introduced in 1.3.8 to quarantine bimodal's
  then-incomplete completeness claims from release gating -- is removed: bimodal is a gating
  theory again. See `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` and
  `docs/ADEQUACY.md` for the design and its soundness proof.

### Fixed
- Live model iteration searched an **unconstrained** problem for every theory except bimodal.
  `ConstraintGenerator` populated its persistent search solver by copying `assertions()` off the
  original model structure's solver, but `ModelDefaults.solve()` assigns
  `stored_solver = solver` *before* `_setup_solver` reassigns `self.solver` to the freshly
  populated one, and then clears `self.solver` in its `finally` block -- so the copy yielded zero
  assertions. `ConstraintGenerator._ensure_original_constraints_in_solver` now re-asserts the four
  real constraint lists (frame/model/premise/conclusion) directly onto the search solver,
  generalizing what had been a bimodal-only workaround into the shared engine. Re-ordering the
  `stored_solver` assignment would not have fixed this: `assert_tracked` records constraints as
  `Implies(label, constraint)`, so copying a populated solver's assertions is vacuously
  satisfiable.
- The generic iterator's model-value pinning never reached bimodal, whose model content is not a
  bitvector state space with an `is_world` predicate. Pinned values now route into the constraint
  group that actually feeds the solver.
- `ModelConstraints.all_constraints` was a construction-time snapshot, so constraint lists that
  grow after construction -- bimodal's two-phase certificate encoding populates `frame_constraints`
  from `finalize_certificate()` -- were silently missing from it. It is now a read-only computed
  property (assignment raises `AttributeError`), and the three `inject_z3_model_values`
  implementations that appended to it (logos, exclusion, bimodal) append to the component list
  they actually mean.
- `\top` lost its derived structure during type assignment. `Sentence.update_types` keyed
  extremal-operator detection on `self.name`, which truncated `\top`'s
  `[NegationOperator, [BotOperator]]` expansion to a nullary shape; detection is now keyed on the
  shape of `derived_type`, so any defined nullary operator with a complex expansion is handled
  correctly.
- Bimodal iteration reported rotations and witness-lasso relabelings of an already-found
  certificate as fresh models. `_check_model_isomorphism` now compares an orbit-invariant
  canonical key, and `_create_non_isomorphic_constraint` excludes the whole orbit rather than a
  single certificate.

### Added
- Three documented theory-specific extension points on `BaseModelIterator` --
  `_pin_theory_specific_values`, `_create_difference_constraint`, and `_check_model_isomorphism` --
  for theories whose model content is not a bitvector state space with an `is_world` predicate.
  Each has a behavior-preserving base-class default, so a theory that overrides none of them keeps
  exactly its previous behavior; `_build_stronger_constraint` *composes* the generic escape
  constraint with any theory override rather than replacing it. Documented with a hook table in
  `src/model_checker/iterate/README.md`.
- `theory_lib/bimodal/semantic/symmetry.py`: the certificate rotation/permutation symmetry group
  `(Z/nb x Z/nf)^L (semidirect) S_{L-1}`, its action on decoded certificates and on raw witness
  registry keys, and the orbit-invariant canonical key -- one shared definition consumed by both
  the isomorphism detector and the orbit excluder so they cannot drift apart.

### Testing and release infrastructure
- Certificate fixture corpus differentialled against the Lean certificate checker, an A2-triangle
  encoding-completeness test, and a sentence-translation agreement channel between the Python
  translator and the Lean-mirroring `Formula` ADT.
- The differential oracle provider is rewritten for the new bimodal encoding; the abundance-era
  oracle tests and manifest are retired.
- Duplicate bimodal test helpers consolidated onto single definitions, and the timing-marker
  coverage scan extended through embedded source strings.
- The live bimodal iteration test that asserted a rotation/permutation duplicate is encountered
  (`isomorphic_model_count >= 1`) no longer depends on how a search draw falls. That assertion was
  a release-gating flake -- a `PYTHONHASHSEED` sweep showed zero duplicates is the *lucky* path
  (the runs that cleanly fill the whole request), and raising the drive did not close it. It is
  replaced by a deterministic assertion over the same solver-produced certificate: every image of
  it under the symmetry group is detected as a duplicate, and an out-of-orbit certificate is not.

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