# Phase 6 Handoff: End-to-end verification from the NixOS host

**Status**: COMPLETED (final phase -- all 6 phases of the plan are now complete)

## What was done

- Default-path regression re-check: `119 passed, 4 skipped` -- identical to Phase 3's result,
  no movement from the Phase 1 baseline plus the new helper tests.
- Real published-artifact run from this NixOS host, version unset (exact pin to
  `code/pyproject.toml`'s `1.3.7`): all 13 CLI tests across `test_entry_point.py`,
  `test_cli_console_script.py`, and `test_generate_then_execute.py` (every registered theory)
  passed, exercising `_add_cxx_runtime_to_env`'s repair, not the `libz3` skip backstop.
- `latest` path independently re-confirmed against the live PyPI JSON API; `testpypi` path
  independently re-confirmed (TestPyPI currently carries `1.3.7`).
- `pytest tests/ci/ -v`: `83 passed`.
- Both workflow files (`release.yml`, `pypi-smoke.yml`) validated together via YAML parse +
  scripted structural assertions (`actionlint` not installed on this host; documented as the
  plan's declared fallback).
- Wrote `summaries/01_pypi-install-verification-pipeline-summary.md` with the full verification
  table, resolved design decisions as implemented, the one documented deviation (Phase 3's
  collection-hook mechanism), and the three Non-Goal follow-ups.

## Verification

See the summary's verification table -- every claim there is backed by quoted command output
captured live during this phase and Phases 1-5.

## Deviations

None new in this phase. The one deviation across the whole task (Phase 3's
`pytest_collection_modifyitems` reading the raw env var instead of calling
`_resolve_install_source()`, to avoid a pytest `INTERNALERROR`) is documented in the summary and
in the Phase 3 handoff.

## Task status

All 6 phases of `plans/01_pypi-install-verification-pipeline.md` are COMPLETED. No publish,
push, tag, or PR step was performed at any point, per the delegation's non-negotiable
constraint. `.return-meta.json` and the orchestrator handoff at
`.orchestrator-handoff.json` (dispatch_seq 20) are written as the final step.
