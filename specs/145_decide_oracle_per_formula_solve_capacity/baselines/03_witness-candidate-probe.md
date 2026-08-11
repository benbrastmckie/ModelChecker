# Witness-Candidate / BM_CM_4 Confirmation Probe Summary

Source: `03_witness-candidate-probe.json`

Seeds pinned via `z3.set_param('smt.random_seed'/'sat.random_seed')` in the
harness only; pipeline mirrors `Z3OracleProvider.find_countermodel`.

## bm_cm_4

- n = 7
- median(rlimit) = 6843909
- max(rlimit) = 32212711
- median(wall) = 6.88s
- max(wall) = 57.12s
- timeout seeds = none

| seed | repeat | rlimit | wall (s) |
|---|---|---|---|
| 1 | 0 | 32212711 | 57.12 |
| 2 | 0 | 14155554 | 22.06 |
| 3 | 0 | 1406881 | 1.26 |
| 4 | 0 | 13381655 | 17.37 |
| 5 | 0 | 698902 | 0.45 |
| 6 | 0 | 6843909 | 6.88 |
| 7 | 0 | 604443 | 0.52 |
