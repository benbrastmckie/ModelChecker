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
