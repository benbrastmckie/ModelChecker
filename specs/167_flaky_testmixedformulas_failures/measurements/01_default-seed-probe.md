# Measurement Log: Default-Seed Solve-Cost Probe

Task 167 Phase 2. Determines whether the default-seed Z3 work quantity (measured via `rlimit`,
Z3's load-independent resource-unit counter) for the two flaky `TestMixedFormulas` formulas is
run-to-run deterministic. See the plan's Phase 2/3 for the campaign design and decision rule.

Tool: `oracle/probe_solve_cost.py` (built in Phase 1).

Hard ceiling: 45 minutes of campaign wall clock. A probe hitting its own `timeout` is a recorded
data point, not a blocker.

## Ambient conditions -- before first draw

- Timestamp (UTC): 2026-08-26T07:58:45Z
- `uptime`: `00:58:45 up 1 day 14:50, 1 user, load average: 4.25, 4.30, 5.64`
- `nproc`: 24
- `z3.get_version_string()`: 4.16.0
- `PYTHONHASHSEED`: unset (ambient shell default -- matches production, which never sets it)

## Draws 1-3: `and(neg(A), next(B))` (test_mixed_and_all_future_neg's formula)

`--formula-name mixed_and_all_future_neg --timeout-ms 180000`, default seed, each invocation
prefixed `timeout 240`, foreground, one at a time.

<!-- draws appended below as they complete -->

- Draw 1: `{"formula_name": "mixed_and_all_future_neg", "timeout_ms": 180000, "seed": "default", "wall_s": 105.8135, "decided": true, "rlimit": 363423989, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`
- Draw 2: `{"formula_name": "mixed_and_all_future_neg", "timeout_ms": 180000, "seed": "default", "wall_s": 105.4953, "decided": true, "rlimit": 363423989, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`
- Draw 3: `{"formula_name": "mixed_and_all_future_neg", "timeout_ms": 180000, "seed": "default", "wall_s": 104.6969, "decided": true, "rlimit": 363423989, "z3_version": "4.16.0", "pythonhashseed": null, "draw_index": 0}`

**Summary for `mixed_and_all_future_neg`**: rlimit = 363423989 on all 3 draws (0% spread, exact
match). wall_s = 105.81 / 105.50 / 104.70 (tight spread here, but that is host-load-dependent, not
Z3-dependent -- the rlimit identity is the signal that matters).

## Draws 4-6: `or(diamond(A), prev(B))` (test_mixed_or_diamond_prev's formula)

`--formula-name mixed_or_diamond_prev --timeout-ms 240000`, default seed, each invocation
prefixed `timeout 300`, foreground, one at a time.

