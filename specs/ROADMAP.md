# Project Roadmap

## Durable Decisions

- **Package identity**: the framework ships as the `model_checker` package (four registered
  theories: `logos`, `exclusion`, `imposition`, `bimodal`) built from `code/` with
  `[tool.setuptools.packages.find] where = ["src"]`. The cross-solver differential oracle is
  kept as a standalone, unpacked top-level `oracle/` tree — outside `code/src/` and excluded
  from the wheel — rather than shipped as part of the installable package.
- **Enforced three-layer dependency model**: the codebase is organized into core
  (`models`, `syntactic`, `solver`, `utils`, `iterate`, `builder`, `settings`, `output`,
  `z3_shim`), `theory_lib` (may import core; never imported by core), and an upper layer
  (`model_checker/__init__.py`, `model_checker/api.py`, `__main__.py`, `jupyter/`) that may
  import both. This is not aspirational documentation: it is enforced by an executable test
  (`code/tests/test_layering.py`) that walks the AST of every core module and fails on any
  `theory_lib` import (including function-local imports and `importlib` string-literal
  references) or hardcoded theory-name literal. A single registration-based registry
  (`model_checker/registry.py`) replaced three previously drifting sources of "which theories
  exist" (a literal `AVAILABLE_THEORIES` list, `discover_theories()`'s filesystem scan, and
  `builder/loader.py`'s hardcoded dicts); `theory_lib` registers into it at import time and core
  queries it, never hardcoding theory names. Every theory is normalized onto one canonical
  module set (`semantic/` package, `operators.py`, `iterate.py`, `examples.py`, `tests/`,
  `docs/`) enforced by a parametrized conformance test
  (`theory_lib/tests/test_theory_conformance.py`) with a guard against any known gap being
  silently re-admitted. Directory position (where `theory_lib` physically sits) never created
  this modularity; dependency direction does, and the enforcement lives in these two test files,
  not in a folder layout.
- **Extract `theory_lib` into its own distribution — REJECTED (for now)**: directory position
  does not create modularity, dependency direction does — and the dependency graph is already
  one-way (`theory_lib` imports core in roughly 90 places; core imports `theory_lib` in zero,
  down from about 10 lazy call sites before the boundary work above). Moving `theory_lib` to a
  sibling `code/src/theory_lib/` package would not deliver a separate PyPI distribution by
  itself: `[tool.setuptools.packages.find] where = ["src"]` auto-discovers any `src/`-level
  package, so both `model_checker` and a hypothetical `theory_lib` would still ship in the same
  wheel — all of the breakage (renamed import paths, e.g. `model_checker.theory_lib.bimodal` ->
  `theory_lib.bimodal`, breaking every user notebook, script, and the `builder/serialize.py`
  module-string-based pickling contract) and none of the actual separate-distribution benefit.
  `theory_lib` is also too generic a name to safely claim in the public PyPI namespace.
  **Revisit trigger**: reconsider extraction when either (a) externally-authored third-party
  theories become a real, requested capability, or (b) `theory_lib`'s core-facing imports narrow
  to a small, stable, publishable surface rather than reaching into `solver`/`models` internals
  as they do today. At that point the correct mechanism is entry-point registration into the
  registry described above (the door is already left open for it — see `registry.py`'s
  `register_theory()` signature), not a directory move. The boundary work already done (one-way
  dependency, the enforced layering test, the single-source registry, the typed conformance
  contract) is a prerequisite for any clean extraction later, so choosing not to extract now
  forecloses nothing.

## Phase 1: Current Priorities (High Priority)

- [ ] **Merge and publish 1.3.0** [USER-ONLY]: **superseded by refactor-first sequencing.** A
  core/theory_lib boundary refactor landed first (one-way dependency enforced by an executable
  layering test, a single-source theory registry, a normalized per-theory module contract
  enforced by a conformance test with zero remaining known gaps, the spatial subtheory and the
  hollow relevance subtheory removed/folded, and bimodal's missing `iterate.py` restored — see
  the Durable Decisions entries above). The release rehearsal in
  `specs/125_release_engineering_and_pypi_rehearsal/` predates that refactor and should be
  redone once against the post-refactor tree (fresh wheel build, fresh `nix flake check`, fresh
  PUBLISH-CHECKLIST.md walkthrough) before a single 1.3.0 release follows. No agent performs any
  publish step — push, tag, `/merge`, and PyPI upload are all user-only per
  `.claude/rules/pr-prohibition.md`.
- [x] **Add `nix flake check` as a CI gate job** *(Completed: Task 150, 20260812)*:
  `.github/workflows/tests.yml`'s `flake-check` job now runs `nix flake check` on every push/PR.
  `flake.nix`'s `checks.default` derivation was also broadened from the bimodal-only suite
  (286/286) to the full in-package suite plus `code/tests/` (minus the `packaging` marker,
  2002 passed / 254 skipped / 0 failed at `-n 6`), so the gate is now both continuously enforced
  and meaningfully scoped.
- [ ] **Oracle differential-suite cadence decision**: `differential-tests.yml` is now correctly
  path-filtered to `oracle/bimodal_logic/**` and `code/src/model_checker/theory_lib/bimodal/**`
  and points at the live `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`. Decide
  whether push/PR-triggered (current behavior) is the right cadence long-term, or whether the
  suite's slower tests (full complexity-5 scans, `TestBimodalHarnessIntegration`) warrant a
  separate scheduled/nightly job instead of blocking every matching push. *(Note, Task 150,
  20260812: the exhaustive complexity-5 scan and `TestBimodalHarnessIntegration` were already
  deliberately designed as manual-only/self-skipping — `oracle/run-oracle-exhaustive-scan.sh`'s
  own header states it is never part of the gating path, and `TestBimodalHarnessIntegration`
  self-skips whenever the sibling `BimodalHarness` checkout is not importable, which it never is
  on a GitHub Actions runner. No new scheduled job is warranted; left open in case the cadence
  question is revisited for reasons other than these two already-answered sub-cases.)*
- [x] **Follow-up task for the 28 documented "everything-else" failures** *(Completed: Task 150,
  20260812)*: **resolved, not reproducing.** A measured re-run of the same selection
  (`code/tests/ code/src/model_checker --ignore=.../bimodal/tests -m "not packaging" -n 6`)
  produced 1700 passed / 254 skipped / 0 failed / 0 errors in 74.10s. All eight root-cause
  categories, including the Category B/G malformed `"A[]"` literal in
  `code/tests/utils/helpers.py`, were resolved as a side effect of the core/theory_lib boundary
  refactor and the CLI end-to-end suite's rewrite of `test_batch_output_real.py`. See
  `specs/150_add_general_ci_workflow_and_flake_check_gate/reports/01_ci-workflow-and-flake-gate.md`
  for the full measurement.

## Deferred Items

Surfaced during the core/theory_lib boundary refactor (see the Durable Decisions entries above)
but intentionally out of that refactor's scope:

- [ ] **Core-package internal reorganization**: `models/`, `solver/`, `syntactic/`, and `utils/`'s
  own internal structure was left as-is beyond the specific relocations the boundary refactor did
  make (moving the theory-aware `get_theory()` auto-load path out of `utils/api.py` into the new
  upper-layer `model_checker/api.py`, and relocating `builder/z3_utils.py` to
  `iterate/z3_utils.py`). A deeper internal reorganization of these packages was explicitly out of
  scope and remains open.
- [ ] **Fold `iterate/z3_utils.py` into `iterate/constraints.py`**: blocked on reconciling a
  `List[ExprRef]` vs `List[ModelRef]` signature mismatch between the two modules' overlapping
  helper functions. Not attempted as part of the boundary refactor.
- [ ] **Add `notebooks/` for bimodal and logos**: exclusion and imposition ship Jupyter
  demonstration notebooks; bimodal and logos do not. `THEORY_ARCHITECTURE.md` records this as
  optional and reported-but-not-enforced, so it is not a conformance defect, but a real content
  gap worth filling.
- [ ] **Revisit `builder/comparison.py`'s status as `--maximize`-only code**: a prior archived
  review proposed removing it as dead code specific to the `--maximize` CLI path. It has 15 live
  tests and its own blast radius; the boundary refactor left it untouched (distinct from the
  unrelated `logos/comparison.py` z3-vs-cvc5 benchmark script, which the refactor relocated out
  of the package entirely to `code/scripts/logos_solver_benchmark.py`).

## Success Metrics

- **Core/theory_lib boundary refactor** (see Durable Decisions above): `code/tests/test_layering.py`
  and `theory_lib/tests/test_theory_conformance.py` both pass with zero violations and zero
  `xfail` markers, guarded against silent re-admission by
  `TestZeroXfailGuard.test_no_xfail_reason_dicts_are_populated`; zero core-module imports of or
  string-literal references to `theory_lib`; zero core-module hardcoded theory-name literals; one
  registration-based registry (`model_checker/registry.py`) as the sole source of "which theories
  exist," with `discover_theories()`'s filesystem scan reporting zero drift against it.
- (Additional project-wide success metrics: define here as they arise)
