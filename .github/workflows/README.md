# GitHub Workflows

The release pipeline is documented in [RELEASE_SETUP.md](../RELEASE_SETUP.md).

## Workflows

- **`release.yml`** — the tag-triggered release pipeline (see `RELEASE_SETUP.md`). Its `build`
  job now also runs the packaging contract suite (`code/tests/packaging/`, `-m packaging`) as an
  additive check before the built artifact is uploaded, so a release build is contents-verified,
  not only metadata-checked by `twine check`.
- **`packaging.yml`** — push/PR-triggered. Runs only `code/tests/packaging/` (selected via the
  `packaging` pytest marker): builds a fresh wheel and sdist into a temp directory and asserts
  the exclusion/inclusion/parity/entry-point packaging contract that `code/pyproject.toml`'s
  `[tool.setuptools.package-data]` and `code/MANIFEST.in` otherwise only assert in comments.
  Deliberately narrow in scope -- it does not run the general test suite.
- **`differential-tests.yml`** — path-triggered on changes under `oracle/bimodal_logic/` or
  `code/src/model_checker/theory_lib/bimodal/`. Runs the bimodal cross-oracle differential test
  suite.
- **`tests.yml`** — push/PR-triggered (unfiltered, same trigger shape as `packaging.yml`). Two
  jobs:
  - `general-tests`: a `ubuntu-latest` x Python `['3.10', '3.11', '3.12']` matrix that installs
    the PyPI `z3-solver` toolchain and runs `code/tests/` plus the full `code/src/model_checker`
    suite (bimodal included), filtered by `-m "not packaging"`, at `-n 6`.
  - `flake-check`: a single job (no matrix -- the flake pins its own Python) that installs Nix and
    runs `nix flake check`, exercising `flake.nix`'s `checks.default` output, which itself now
    covers the same broadened scope (`src/model_checker tests -m "not packaging"`) inside the
    nixpkgs-packaged toolchain.

### Scoping rationale

- **Why packaging tests run serially, only in their own workflow**: `code/tests/packaging/`
  builds a fresh wheel and sdist per session via a session-scoped fixture in
  `code/tests/packaging/conftest.py`. Running that fixture under `pytest-xdist` parallelism is
  unsafe -- a measured `-n 6` run that included these tests alongside the rest of the suite
  reproduced 86 spurious `ERROR`s, all wheel/sdist build-race failures across concurrent xdist
  workers, none of them real defects. `packaging.yml` and `release.yml`'s `build` job both already
  run this suite serially (no `-n` flag), which is the only way it is currently safe to run.
- **Why `tests.yml`'s general gate excludes the `packaging` marker**: for the same reason above
  (the xdist build race) and because `packaging.yml` and `release.yml`'s `build` job already cover
  that suite on every relevant trigger -- including it again in `tests.yml` would be pure
  duplication as well as unsafe under `-n 6`.
- **Why the general gate uses a narrower matrix than the release pipeline**: `release.yml`'s
  9-combination `os x python-version` matrix answers "does the published wheel install and import
  on every platform we claim to support" -- a release-time concern. `tests.yml`'s `general-tests`
  job answers a different question -- fast, cheap behavioral regression detection on every push --
  so it runs `ubuntu-latest` only across the three supported Python versions. Cross-OS
  packaging/install breakage is caught at release time by `release.yml` and, more cheaply and on
  every push, by `packaging.yml`'s wheel/sdist contract checks.
- **Why `-n 6` and never xdist's auto worker-count mode**: the `theory_lib/bimodal` suite has a
  documented CPU-contention flake under that mode
  (`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]`), corroborated by a measured
  ~1.8x slowdown of the bimodal suite under concurrent host load. `-n 6` is used literally, in both
  `tests.yml` and `flake.nix`'s `checks.default`.
- **Why bimodal is covered by both the plain-Python job and the flake check (not redundant)**:
  `general-tests` exercises the PyPI `z3-solver` wheel that end users actually install via `pip`,
  while `flake-check` exercises the nixpkgs-packaged Z3/Python toolchain via `flake.nix`. These are
  two different toolchains; running the same bimodal tests against both is deliberate
  cross-toolchain coverage, not duplicated work.

`checks.default` in `flake.nix` is no longer bimodal-scoped: it now runs
`src/model_checker tests -m "not packaging" -n 6 -q`, the same broadened selection `tests.yml`'s
`general-tests` job runs (against the PyPI toolchain), matching this README.
