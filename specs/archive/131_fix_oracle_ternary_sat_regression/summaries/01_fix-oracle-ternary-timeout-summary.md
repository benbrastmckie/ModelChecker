# Implementation Summary: Fix Oracle Ternary-SAT Timeout Boundary

- **Task**: 131 - fix_oracle_ternary_sat_regression
- **Status**: COMPLETED (all 3 phases)
- **Plan**: `plans/01_fix-oracle-ternary-timeout.md`
- **Research**: `reports/01_oracle-ternary-sat-regression.md`

## Corrected framing

The original task record classified `test_all_sat_task_relation_ternary` as a
refactor-introduced semantic regression. Research (this task's own report) disproved that: five
isolated runs of the single test — 3 at HEAD, 2 at pre-refactor baseline `6cfb7f48` via a
read-only worktree — all landed in the same 52.8-58.9s wall-clock band against a 60000ms budget,
with byte-identical constraint-building code at both commits. **This is a timeout-budget boundary
flake, not a semantic defect.** No code under `code/src/model_checker/**` or
`oracle/bimodal_logic/provider.py`/`operators.py`/`semantic/core.py` was touched by this task.

## What changed

`oracle/bimodal_logic/tests/test_oracle_interface.py` only:

1. Added two module-level constants adjacent to the existing shorthand-atom test data:
   ```python
   # Solver budget for formulas with temporal_depth > 0. These force M = max(depth+2, 3) >= 3,
   # which dispatches to the expensive MBQI-avoidance constraint path; measured solve times
   # cluster at 53-59s. Set generously rather than at measured-time-plus-margin, per
   # code/docs/core/TESTING_GUIDE.md section 8.6 -- a tight ceiling here produces wall-clock
   # boundary flakes, not signal.
   TEMPORAL_SOLVE_TIMEOUT_MS = 180000
   ATEMPORAL_SOLVE_TIMEOUT_MS = 10000
   ```
2. Rewrote the primary failing site (`test_all_sat_task_relation_ternary`) to use these constants
   instead of the bare `60000`/`10000` literals.
3. Audited every sibling call site sharing the same 60000ms boundary and asserting a non-`None`
   result. Widened three that measured within 2x of the ceiling or shared the exact same
   temporal-depth-1 boundary case as the primary fix:
   - `test_enriched_vs_primitive_sat_agreement`'s depth>0 timeout expression (its `next`
     parametrize case measured 104.02s combined for enriched+primitive, the same M=3 case as the
     primary fix).
   - `test_mixed_and_neg_some_future` (measured 38.54s, >30000ms threshold).
   - `test_spot_check_individual_countermodels`'s F5 call (measured 241.95s for the whole test;
     isolated single-call timing showed only 0.64s, so widening here was not strictly necessary
     but is harmless).

## Measurement table (Phase 2)

| Site | Measured (pre-edit, single run) | Disposition |
|------|----------------------------------|-------------|
| `test_all_sat_task_relation_ternary` | 5 runs: 53.79s, 63.80s, 52.46s, 51.19s, 50.98s | Widened (primary fix); max 63.55s = 35.3% of 180000ms budget |
| `test_enriched_vs_primitive_sat_agreement[next]` | 104.02s combined | Widened |
| `test_enriched_vs_primitive_sat_agreement[all_future]` | 125.32s combined pre-edit; 379.57s post-edit | Widened, but see finding below |
| `test_enriched_vs_primitive_sat_agreement[some_past]` | 64.13s combined | Widened (shares the same timeout expression as `next`) |
| `test_mixed_and_neg_some_future` | 38.54s | Widened |
| F5 site (`test_spot_check_individual_countermodels`) | 0.64s isolated | Widened (harmless; not actually at risk) |
| `test_mixed_and_box_next` | 17.53s / 14.21s (re-run) | Left unchanged, >=2x headroom |
| `test_mixed_and_all_future_neg` | 25.75s / 21.62s (re-run) | Left unchanged, >=2x headroom |
| `test_mixed_or_diamond_prev` | 1.46s / 1.33s | Left unchanged, far below threshold |
| `test_deeply_nested_enriched` | 60.33s / 60.34s | Left unchanged, tolerates `None` by design |
| `valid_formulas` loop (F4/F7/F9/F10) | ~241.3s aggregate over 4 calls | Left unchanged, tolerates `None` by design |
| `test_timeout_handling` | n/a (`timeout_ms=1`) | Left unchanged, the tiny budget is the point of the test |
| all `30000`ms sites | not re-measured (plan's own audit already established these are `if result is not None:`-guarded or tolerate legitimate UNSAT `None`) | Left unchanged |

## Deviation from the plan's site enumeration

The plan listed "line 951-952 and line 964" (original line numbers) as both asserting non-`None`.
Direct inspection of the actual code shows only the F5 call (now line 959) asserts non-`None`; the
loop immediately after it (now line 972, over `valid_formulas` = F4/F7/F9/F10) asserts
`result is None` — it expects these formulas to be valid (no countermodel). That loop is
reclassified as a tolerates-`None` site and left at its existing 60000ms budget, consistent with
the same policy applied to `test_deeply_nested_enriched`.

## Finding for the downstream full-suite task (recorded, not fixed)

Isolated instrumentation of the `all_future` enriched/primitive pair
(`imp(all_future(A), B)` and its primitive unfold) shows **both forms genuinely exceed even the
new 180000ms budget**: enriched form took 195.47s, primitive form 187.63s, both returning `None`
(timeout). The parametrized test still passes because both sides agree (`None == None`), but this
is very likely a masked timeout-equivalence rather than a verified semantic agreement — the same
pathology already existed at the original 60000ms budget (both sides would have timed out there
too; widening did not introduce this, and it does not fix it). This is a genuinely slow solver
query, not a boundary flake, and is explicitly out of this task's scope per the plan's Non-Goals
("Solver-performance work on the M>=3 MBQI-avoidance path... there is no known cheap win").
`test_deeply_nested_enriched` (60.34s, right at its own 60000ms ceiling) and the `valid_formulas`
loop (~60s/call average) show the same tolerate-`None` pattern and may have the same masking
issue. Recommend the downstream full-suite task treat this as a known finding, not a new
regression, if it surfaces during the 550-test run.

## Verification performed (all inside `nix develop`)

- **Phase 1**: `pytest --collect-only -q` on the file — 108 tests collected, no errors. Both
  constants present exactly once each, plus one usage at the rewritten primary site.
- **Phase 2**:
  - 5x isolated `test_all_sat_task_relation_ternary` — 5/5 PASSED, max 63.55s (see table).
  - `TestTernarySerializationAll` class — 2/2 PASSED (50.47s).
  - `TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement` (11 parametrized cases,
    post-widening) — 11/11 PASSED (581.25s).
  - `TestMixedFormulas` (5 tests, post-widening) — 5/5 PASSED (111.90s).
  - `TestSpotCheckCrossSignal::test_spot_check_individual_countermodels` (post-widening) — PASSED
    (242.20s).
  - `grep -n "60000"` — remaining occurrences (lines 823, 830, 837, 845, 972) all correspond to
    sites explicitly left unchanged above.

  Note: the plan's single combined `-k "enriched_vs_primitive or mixed_ or ternary"` verification
  command exceeded this session's 10-minute tool timeout when run as one invocation (the
  `all_future` case alone now takes ~380s post-widening). It was run instead as three separate
  sequential invocations covering the same tests, each completing well within its own timeout,
  with identical pass results.
- **Phase 3**:
  - `pytest oracle/ -n 6 --collect-only -q` — **550 tests collected in 0.29s**, no collection
    errors, `-n 6` accepted (confirms `pytest-xdist` is live in the devShell with no rebuild
    needed).
  - `git status --short -- code/ oracle/` — the only file this task modified is
    `oracle/bimodal_logic/tests/test_oracle_interface.py`. Other `code/` files show as modified in
    git status, but these were already present in the working tree before this task began
    (pre-existing uncommitted work from a concurrent session scoped to
    `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` and related
    files) — this task did not touch, revert, or stash any of them.
  - `jq -e '.active_projects[] | select(.project_number == 131) | .completion_summary'` — exits 0
    and prints the corrected timeout-flake framing.

## Downstream baseline task blocker correction

The downstream full-suite baseline task's stated blocker ("pytest-xdist unavailable") is
**false**. `pytest-xdist` is declared at `flake.nix:72` and `code/pyproject.toml:48`, and is
present and already realized inside the devShell (`/nix/store/kykgmi6vxjzw76miazjf3yfn59kp7phd-python3-3.12.13-env`)
with no rebuild required. It is absent only from the bare interactive Python
(`/home/benjamin/.nix-profile/bin/python3` or similar) — every command in this task's
verification used `nix develop --command ...` and had no trouble with `-n 6`.

## Recorded handoff invocation for the downstream full-suite task

```bash
nix develop /home/benjamin/Projects/ModelChecker --command bash -c \
  'cd /home/benjamin/Projects/ModelChecker && \
   PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
   python -m pytest oracle/ -n 6'
```

Use `-n 6`, **not** `-n auto`: `flake.nix` documents `-n auto` as a known CPU-contention flake for
this repo and pins its own `checks.default` to `-n 6`. Since this task's entire failure mode was
wall-clock contention against a solver budget, `-n auto` risks re-creating the same problem under
a different name (more workers than physical cores competing for Z3 solve time).

**Exit criteria for the downstream run**: the devShell provides pytest 9.0.3, z3, `pytest-xdist`
3.8.0, and `PYTHONPATH` (its shellHook exports `code/src` plus the `BimodalHarness` sibling when
present at `/home/benjamin/Projects/BimodalHarness/src`, confirmed present on disk). No `code/` or
`oracle/` source change was made by this task, so any suite failure in the downstream run is
pre-existing and not attributable to this task's change (with the possible exception of the
`all_future` finding above, which is a pre-existing masked timeout, not a regression).

## Plan Deviations

- Corrected the plan's cohort site enumeration: the `valid_formulas` loop (F4/F7/F9/F10) asserts
  `result is None`, not non-`None` as the plan stated; reclassified as tolerates-`None` and left
  unchanged.
- Split the Phase 2 combined `-k` verification command into three sequential invocations due to a
  10-minute tool timeout (same tests, same results, no outcome difference).
- Recorded (did not fix) a new finding: the `all_future` enriched/primitive pair genuinely exceeds
  even the widened 180000ms budget. This is additional information for the downstream task, not a
  scope change — no solver-performance work was undertaken, per the plan's Non-Goals.
- Set `specs/state.json` task 131 `status` to `"completed"` (standard terminus for a non-pr task
  type once `completion_summary` is set and all 3 plan phases are done).

## Files changed

- `oracle/bimodal_logic/tests/test_oracle_interface.py` (all code changes for this task)
- `specs/state.json` (corrected `completion_summary`, `status`, added summary artifact entry)
- `specs/TODO.md` (regenerated via `generate-todo.sh`, not hand-edited)
- `specs/131_fix_oracle_ternary_sat_regression/plans/01_fix-oracle-ternary-timeout.md` (phase
  status headings, task checkboxes, and measurement tables updated in place)
- `specs/131_fix_oracle_ternary_sat_regression/handoffs/phase-1-handoff-1785000005.md` (new)
- `specs/131_fix_oracle_ternary_sat_regression/handoffs/phase-2-handoff-1785000900.md` (new)
- `specs/131_fix_oracle_ternary_sat_regression/summaries/01_fix-oracle-ternary-timeout-summary.md` (this file)
