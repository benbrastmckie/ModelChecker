# Phase 1 Handoff: Widen the primary timeout behind a named constant

- **Status**: COMPLETED
- **Files modified**: `oracle/bimodal_logic/tests/test_oracle_interface.py`

## What changed

Added two module-level constants adjacent to the existing shorthand-atom test data
(`oracle/bimodal_logic/tests/test_oracle_interface.py:110-116`):

```python
TEMPORAL_SOLVE_TIMEOUT_MS = 180000
ATEMPORAL_SOLVE_TIMEOUT_MS = 10000
```

Rewrote the depth>0 budget expression inside `test_all_sat_task_relation_ternary`
(`TestTernarySerializationAll`) from `timeout = 60000 if depth > 0 else 10000` to
`timeout = TEMPORAL_SOLVE_TIMEOUT_MS if depth > 0 else ATEMPORAL_SOLVE_TIMEOUT_MS`.

No other call site was touched in this phase.

## Verification

- `nix develop --command ... pytest oracle/bimodal_logic/tests/test_oracle_interface.py --collect-only -q`
  -> `108 tests collected` in 0.25s, no collection errors.
- `grep -n "TEMPORAL_SOLVE_TIMEOUT_MS\|ATEMPORAL_SOLVE_TIMEOUT_MS" ...` -> each constant defined
  once (lines 115-116) plus exactly one usage site (line 1056).

## Deviations from plan

None (implementation followed plan).

## Next

Proceed to Phase 2: confirm no competing pytest processes, run the target test 5x in isolation,
audit sibling boundary sites, and widen boundary-exposed cohort members.
