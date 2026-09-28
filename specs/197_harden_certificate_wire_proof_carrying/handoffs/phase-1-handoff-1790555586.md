# Phase 1 Handoff: Canonical wire bytes, in the protocol module

- **Status**: [COMPLETED]
- **Timestamp**: 1790555586

## What changed

- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`: added
  `canonical_wire_bytes(payload)` (compact separators, `ensure_ascii=False`, no `sort_keys`),
  with docstring rationale for each argument. Added to `__all__`.
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`: `run_check_certificate` now
  sends `canonical_wire_bytes(payload)` instead of `json.dumps(payload)`. No new export.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py`: new
  `TestCanonicalWireBytes` class (4 tests) asserting no separator whitespace, non-ASCII
  survival, canonical key order across every `formula.to_json` tag, and that `sort_keys=True`
  would break the order.

## Verification performed

- `PYTHONPATH=code/src python3 -c "... lc.SKIP_REASON ..."` now prints `None` (previously the
  `expected a decimal numeral` protocol error) — the differential tier is alive.
- `pytest .../tests/integration/test_certificate_lean_agreement.py -v`: 10 passed (previously
  all skipped).
- `pytest .../tests/unit/test_certificate.py -v`: 40 passed.
- `pytest .../bimodal/tests/ -q`: 598 passed, 1 failed
  (`test_iterate.py::TestLiveIteration::test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`).
  Re-ran in isolation: passed. Pre-existing flake in the iteration engine, unrelated to this
  phase's certificate/wire changes (confirmed by file scope: only `certificate.py`,
  `_lean_check.py`, `test_certificate.py` touched).

## Scope hypothesis outcome

Confirmed: exactly one call site fed the Lean binary a `json.dumps` payload
(`_lean_check.py:78`). `grep -rn "json.dumps" .../bimodal/` found two other unrelated sites
(`test_certificate.py:185`, `test_formula.py:252`, both self-contained round-trip tests, not
feeding the binary) — left alone as the scope hypothesis anticipated.

## Deviations from plan

None.

## Next phase

Phase 2: split `probe()`'s failure vocabulary in `_lean_check.py` so a protocol failure (binary
answers `"error"`) is a loud, non-skip condition, distinct from environment absence.
