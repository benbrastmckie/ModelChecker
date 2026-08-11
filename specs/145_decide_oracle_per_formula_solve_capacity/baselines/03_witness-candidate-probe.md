# Witness-Candidate / BM_CM_4 Confirmation Probe Summary

Source: `03_witness-candidate-probe.json`

Seeds pinned via `z3.set_param('smt.random_seed'/'sat.random_seed')` in the
harness only; pipeline mirrors `Z3OracleProvider.find_countermodel`.

## bm_cm_1

- n = 7
- median(rlimit) = 14642280
- max(rlimit) = 203130883
- median(wall) = 7.17s
- max(wall) = 120.32s
- timeout seeds = [2]

| seed | repeat | rlimit | wall (s) |
|---|---|---|---|
| 1 | 0 | 5056481 | 1.72 |
| 2 | 0 | 203130883 | 120.32 |
| 3 | 0 | 7398857 | 3.44 |
| 4 | 0 | 24126440 | 9.95 |
| 5 | 0 | 14642280 | 7.17 |
| 6 | 0 | 22220097 | 7.30 |
| 7 | 0 | 4839810 | 1.44 |
