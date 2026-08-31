# Phase 4 Handoff: Post-publish PyPI confirmation matrix in `release.yml`

**Status**: COMPLETED

## What was done

Added `verify-pypi` to `.github/workflows/release.yml`, between `publish-pypi` and
`github-release`:

- `needs: [publish-pypi]`, `runs-on: ${{ matrix.os }}`, `timeout-minutes: 20` (no
  `timeout-minutes` precedent exists elsewhere in `release.yml` itself; 20 mirrors the closest
  matrix-job precedent in `tests.yml`).
- `strategy: fail-fast: false`, matrix `os: [ubuntu-latest, macos-latest, windows-latest]` x
  `python-version: ['3.10', '3.11', '3.12']` -- the same 3x3 as `test-and-release`.
- Steps: checkout, `actions/setup-python@v5`, `pip install pytest build wheel`, then
  `cd code && python -m pytest tests/packaging/ -v -m "packaging and not unstable"` with
  `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE: pypi` (version left unset -> D2.1's exact pin to
  `code/pyproject.toml`, correct on this tag path).
- A comment block on the job recording why it exists (no prior post-publish PyPI verification),
  that it deliberately reuses the packaging suite instead of a fourth inline smoke script, and
  the 9-leg per-release cost.
- Extended `github-release`'s `needs:` from `publish-pypi` to `[publish-pypi, verify-pypi]`.
  `github-release` carries no explicit `if:` (confirmed by re-reading the file before editing),
  so the implicit `if: success()` default now covers both upstream jobs with no separate `if:`
  edit needed.

## Verification

- `python -c "import yaml; yaml.safe_load(open('.github/workflows/release.yml'))"` parses clean.
- `actionlint` is not installed on this host; YAML parse + structural assertions used as the
  documented fallback (per the plan's Phase 4 Verification and the Risks table's "Cannot verify
  workflow YAML without pushing" mitigation).
- Structural assertions (scripted, all passed): `verify-pypi.needs == ['publish-pypi']`; matrix
  is exactly the 3x3 OS/Python set; `fail-fast: false` present; `github-release.needs ==
  ['publish-pypi', 'verify-pypi']`; `github-release` gained no `if:`; the pytest invocation
  string contains `and not unstable`.
- `git diff .github/workflows/release.yml` filtered to `needs:`/`if:` lines shows exactly two
  changes: the new job's own `needs:` and `github-release`'s extended `needs:` -- no other job's
  `needs:` or `if:` was touched.

## Deviations

None from the plan's task list.

## Next phase

Phase 5 (parallel with this one, both depending only on Phase 3 -- already done): the new
`.github/workflows/pypi-smoke.yml`. Phase 6 (end-to-end verification + summary) depends on both.
