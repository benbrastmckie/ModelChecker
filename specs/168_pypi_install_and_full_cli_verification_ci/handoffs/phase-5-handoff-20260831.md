# Phase 5 Handoff: New `pypi-smoke.yml` workflow

**Status**: COMPLETED

## What was done

Created `.github/workflows/pypi-smoke.yml`:

- Header comment stating the non-gating contract (never in another workflow's `needs:`, never a
  required check), mirroring `unstable-watch.yml`'s precedent -- the repository's only other
  `schedule:`-triggered workflow, matched for the trigger block shape only.
- Triggers: `schedule: '0 7 * * *'` (offset from `unstable-watch.yml`'s `0 5 * * *`) plus
  `workflow_dispatch` with `version` (string, default `''`) and `debug_tmate` (boolean, default
  `false`).
- `permissions: contents: read`; job-level `timeout-minutes: 20`.
- Steps: checkout; `setup-python@v5` pinned to `3.12` (single version -- cross-platform breadth
  belongs to `release.yml`'s `verify-pypi` matrix); `pip install pytest build wheel`; a version
  echo step before the pytest step; the pytest step with
  `MODEL_CHECKER_PACKAGING_INSTALL_SOURCE: pypi` and
  `MODEL_CHECKER_PACKAGING_INSTALL_VERSION: ${{ inputs.version || 'latest' }}`; a `mxschmitt/action-tmate@v3`
  step gated on `if: ${{ failure() && inputs.debug_tmate }}` with its own `timeout-minutes: 15`.

## Verification

- YAML parses clean; `actionlint` not installed on this host (same as Phase 4), so the plan's
  documented fallback (YAML parse + structural assertions) was used.
- Structural assertions (scripted, all passed): both triggers present; `debug_tmate` defaults
  `false`; the tmate step's `if:` contains both `failure()` and `inputs.debug_tmate`; the tmate
  step carries `timeout-minutes`; the pytest invocation contains `and not unstable`.
- `grep -rn 'pypi-smoke' .github/workflows/` returns only the file's own job-name line inside
  itself -- no other workflow references it.

## Deviations

None from the plan's task list.

## Next phase

Phase 6: end-to-end verification from the NixOS host (default-path regression re-check,
`tests/ci/` run, both workflow files validated together) and the implementation summary. Both
Phases 4 and 5 are now done.
