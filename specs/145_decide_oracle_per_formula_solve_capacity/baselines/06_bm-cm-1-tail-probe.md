# Witness-Candidate / BM_CM_4 Confirmation Probe Summary

Source: `06_bm-cm-1-tail-probe.json`

Seeds pinned via `z3.set_param('smt.random_seed'/'sat.random_seed')` in the
harness only; pipeline mirrors `Z3OracleProvider.find_countermodel`.

## bm_cm_1

- n = 1
- median(rlimit) = 930150200
- max(rlimit) = 930150200
- median(wall) = 600.68s
- max(wall) = 600.68s
- timeout seeds = [2]

| seed | repeat | rlimit | wall (s) |
|---|---|---|---|
| 2 | 0 | 930150200 | 600.68 |
