# Phase 2: Twenty-Plus-Seed Sweep of the Renamed Construction

- **Date**: 2026-09-25
- **Host**: single process, sequential runs (renamed arm, then baseline control arm, then
  counter-state check) -- no concurrent solver work, so timings are not distorted by CPU
  contention.
- **Harness**: `01_symbol-rename-harness.py`, `sweep` and `counter-states` subcommands.
- **Seeds**: 25 consecutive seeds (1-25), each pinned via `z3.set_param('smt.random_seed', N)`
  and `z3.set_param('sat.random_seed', N)` before the run -- exceeds the >= 20-seed requirement.
- **Probe budget**: 40s (deliberately below the 120s example budget, as the plan specifies, so a
  decided draw is decided with margin rather than scraping the ceiling).

## Decision gate (from the plan)

> if any seed produces an undecided draw, or any decided draw returns something other than
> `match`/`model_found: true`, STOP and route to Phase 7. Do not proceed to Phase 3.

**Result: GATE FAILED.**

## Renamed arm (both axioms alpha-renamed) -- the candidate fix

| Metric | Value |
|---|---|
| Seeds run | 25 (1-25) |
| Undecided (timeout) draws | **5** -- seeds 5, 7, 13, 15, 24 |
| Non-`match` decided draws | 0 |
| Decided-draw time: min / median / max | 0.24s / 3.65s / 37.66s |

5/25 = 20% of pinned-seed draws are undecided at a 40s budget under the renamed construction.
This alone fails the gate.

## Baseline arm (unmodified, committed construction) -- same-host, same-budget control

Run at the *same* 25 seeds and the *same* 40s budget, so this is a same-host, same-budget
contrast rather than a comparison against the report's earlier, differently-configured numbers.

| Metric | Value |
|---|---|
| Seeds run | 25 (1-25) |
| Undecided (timeout) draws | **2** -- seeds 7, 17 |
| Non-`match` decided draws | 0 |
| Decided-draw time: min / median / max | 0.24s / 0.97s / 26.46s |

**This is the decisive finding: under a genuine seed sweep, the unmodified (baseline)
construction is more reliable than the renamed one (2/25 undecided vs. 5/25 undecided), not
less.** The renamed construction is not a fix; it is a different, and on this evidence worse,
point in the same Z3 MBQI/E-matching sensitivity space the research report's 3-5-probe sample
did not surface. The research report's single-seed, default-parameter probes (3/3 renamed
`match` at ~2s, 3/3 baseline `inconclusive` at 120s) reflect the specific deterministic draw Z3's
*default* (unpinned) parameters happen to produce for each construction -- which is exactly the
draw the real, unseeded test suite hits every time (hence "BM_CM_4 fails deterministically") --
not the constructions' general reliability across the seed space. Both constructions have a
non-trivial undecided tail; the rename only moves which specific draws land in it, and this
sample places more of them there for `renamed` than for `baseline`.

## Renamed arm at the isolation test's exact counter states [0, 17, 30]

Run separately (not part of the 25-seed sweep; these use no `z3.set_param` seed pinning, matching
`test_bound_var_counter_isolation.py`'s own harness, and only poison
`bimodal.operators._bound_var_counter`):

| `poisoned_start` | `check_result` | `model_found` | `solving_time` |
|---|---|---|---|
| 0 | `match` | `True` | 2.18s |
| 17 | `match` | `True` | 2.17s |
| 30 | `match` | `True` | 2.13s |

This reproduces the research report's SS5 finding exactly (all three states decide fast under
the renamed construction) -- but per the seed sweep above, this reflects Z3's default parameter
draw for the renamed construction being fast, not that the renamed construction is reliable in
general. Z3's default (unpinned) draw is a single point in the seed space; a favorable single
point is exactly what the 25-seed sweep shows is not representative.

## Conclusion

The alpha-rename does **not** clear the plan's evidentiary bar for Acceptable Outcome 1 (a
`>= 20`-seed sweep with zero undecided draws). It also does not outperform the unmodified
construction under the same sweep, so there is no basis to prefer it as a "mitigation" either.
Per the plan's decision gate, this phase **stops here and routes directly to Phase 7**: Phase 3
(land the rename), Phase 4 (regression diff), and Phase 5 (suite verification) are not executed,
since they are conditioned on this gate passing. No file under `code/` or `oracle/` has been
modified by this phase.
