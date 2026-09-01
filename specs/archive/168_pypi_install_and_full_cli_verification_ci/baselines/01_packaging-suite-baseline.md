# Packaging Suite Baseline (Pre-Change)

Recorded at Phase 1, before any fixture changes, per plan
`plans/01_pypi-install-verification-pipeline.md`.

## Command

```
cd code && PYTHONPATH=src python -m pytest tests/packaging/ -v -m packaging -rs
```

(`packaging.yml` runs the equivalent `cd code && python -m pytest tests/packaging/ -v -m packaging`
without an explicit `PYTHONPATH` since it runs against the installed package; both invocations
collect the same 110 items on this host — `PYTHONPATH=src` was added here only so the suite can
run without an editable/installed `model_checker` on this development host.)

## Result

```
106 passed, 4 skipped in 102.56s (0:01:42)
```

## Skip reasons (verbatim, via `-rs`)

```
SKIPPED [2] tests/packaging/test_inclusions.py:86: theory 'bimodal' has no on-disk notebooks/ directory
SKIPPED [2] tests/packaging/test_inclusions.py:86: theory 'logos' has no on-disk notebooks/ directory
```

These 4 skips are pre-existing and unrelated to this task (theories without an on-disk
`notebooks/` directory) — they are not part of the D4 not-applicable skip mechanism this task
adds.

## Non-regression contract

This 106-passed / 4-skipped result (with the exact skip reasons above) is the load-bearing
baseline for:

- Phase 2's verification (`installed_venv` env vars unset — helpers added but not yet wired in;
  must be untouched).
- Phase 3's default-path verification (env vars unset, `installed_venv` now parameterized but
  defaulting to `local`; must match this baseline exactly).
- Phase 6's final default-path regression check.

Any movement away from `106 passed, 4 skipped` with these exact skip reasons, under the default
(both env vars unset) invocation, is a defect to fix before continuing — not a result to accept.
