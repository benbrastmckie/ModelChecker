# Research Report: Per-Formula Solve Capacity Decision (Oracle Gating Suite)

- **Task**: 145 - decide_oracle_per_formula_solve_capacity
- **Date**: 2026-08-11
- **Session**: sess_1786456768_0d5e0f
- **Scope**: the PER-SOLVE budgets governing individual oracle formula solves (60000 ms /
  180000 ms / `SELF_SCAN_SOLVE_TIMEOUT_MS`-adjacent margins), one layer below the already-settled
  pass-level `ORACLE_PASS2_TIMEOUT` decision. The pass-level decision is NOT revisited here.
- **Sources/Inputs**:
  - `specs/144_fix_oracle_per_formula_solve_timeouts/reports/01_oracle-solve-cost-reduction.md`
    (root-cause chain, dead ends 1-6)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/summaries/01_oracle-solve-cost-reduction-summary.md`
    (dead ends 7-11, headroom table, twice-run gate outcome)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/01_solve-cost-baseline.json` and
    `05_final-solve-cost.json` (21-run paired-seed rlimit/wall data, reanalyzed here)
  - `specs/143_decide_oracle_serial_pass_timeout_capacity/reports/01_serial-pass-capacity.md`
    (the discipline template for a recorded capacity decision) and
    `summaries/01_phase4-triage-record.md` (the two full-gate failure inventories)
  - `oracle/run-oracle-suite.sh`, `oracle/conftest.py`, `code/scripts/verify-refactor.sh`
  - `oracle/bimodal_logic/tests/test_oracle_interface.py`, `test_boundary_regression.py`,
    `test_cross_oracle_differential.py`, `test_oracle_provider.py`
  - `code/src/model_checker/theory_lib/bimodal/examples.py`
  - `code/docs/core/TESTING_GUIDE.md` sections 8.6 and 8.8
  - Fresh uncensored-tail probe measurements taken in this dispatch (section 5), using a
    scratch copy of `specs/144_.../bench_solve_cost.py` with raised probe budgets
  - Live red-run transcript `/tmp/verify-refactor-oracle.txt` (the phase-5 full-gate Step 6
    failure, still on disk; failure identities confirmed from it directly)

## Executive Summary

- **Recommendation: a three-part remedy matched to three measured mechanisms** — (b) per-solve
  budget recalibration with a recorded measurement basis where the cost distribution is bounded
  but exceeds the budget (`and_box_next`, BM_CM_4, the gating-scan re-check margin); a narrow,
  genuine application of (a) serial-pass relocation for the one pure contention victim still in
  the parallel pass (`and_all_future_neg`); and a witness-formula substitution for the one
  formula whose bad tail is measured DIVERGENT and therefore fixable by neither budget nor
  scheduling (the ternary test's `next_A` leg — section 7.2). Option (a) alone cannot fix the
  observed failures: every observed pass-2 failure occurred in a pass that is already
  contention-free by construction (zero xdist workers), and the decisive triage evidence shows
  the failures are load-INDEPENDENT — the quiet-machine gate attempt (load 1.57) failed *more*
  tests than the contended one (load 5.4-7.5). Option (c) is rejected: with the measured failure
  probabilities, "monitor" means a mostly-red gate blocking every future wave boundary, and the
  blocked pass-level task stays blocked.
- **The recorded-argument standard the task demands is met by direct measurement, not by
  assertion.** Reanalysis of the 21-run paired-seed baselines shows `test_mixed_and_box_next`
  exceeded its 60000 ms budget on **3 of 7 isolated, contention-free seeded runs in both
  measurement rounds** (6 of 14 draws censored at the budget), and the ternary test's `next_A`
  leg exceeded its 180000 ms budget on 1 of 7 in both rounds. A budget that fails ~43% of
  contention-free draws is not being "papered over" by widening — it sits **below the genuine
  cost distribution** of the workload, which grew for a documented, accepted, correctness-required
  reason (the bound-variable aliasing soundness fix; see section 4).
- **A fresh uncensored-tail probe (this dispatch) measured what the censored 60.4s "max" values
  hid**: with the probe budget raised to 300 s, the previously-timing-out seeds of
  `and_box_next` cost **94.3 s / 92.8 s / 104.2 s** — all three decided — with rlimit 222M /
  236M / 338M vs. the ~130M of a good draw: the real bad-draw cost is ~1.5-1.7x the 60 s budget
  in wall terms and up to 2.6x in load-independent solver work. The sibling precedent
  (`test_mixed_or_diamond_prev`, widened 60000 -> 150000 at ~2.07x measured worst after the same
  soundness fix) applied to the 104.2 s worst gives **240000 ms** (2.3x worst, rounded to a
  clean generous value per the pass-level decision's own rounding convention) for
  `and_box_next`. **The `next_A` probe produced the opposite result**: its bad-draw seed did NOT
  decide even at a 600 s probe budget (3.3x the current 180 s budget), consuming rlimit 1.026B —
  7.5x a good draw's ~137M — and still running. `next_A`'s bad tail is effectively divergent,
  so NO practical budget widening fixes it; the remedy for that one witness formula is
  different (section 7.2) and budget recalibration is explicitly NOT recommended there.
- **The 60000 ms budget was never calibrated.** It dates to the test's original authoring
  (2026-06-01, commit `ea516a4b`, pre-dating the oracle tree itself), written for a pre-fix
  encoding in which this solve was fast. The one recorded characterization since ("~44-45s,
  ~25% headroom", commit `7f7269d6`) was a 2-sample observation that the 21-run paired data
  supersedes: the median is 46.5-49.9 s and ≥43% of seeds exceed 60 s entirely. No commit ever
  recorded a measurement basis for 60000 itself. The 180000 ms constant DID have a basis
  ("measured solve times cluster at 53-59s", ~3x margin) — but it was recorded on 2026-07-25,
  13 days BEFORE the soundness fix that permanently raised the cost; post-fix `next_A` medians
  are ~90 s with a divergent bad-draw tail, so its basis is stale in exactly the way the task's
  "workload legitimately grew" clause anticipates — though for that particular formula the
  growth outran what any budget can absorb (section 5).
- **The `TestGatingConclusiveScan` 99-of-103 floor miss is a distinct sub-problem** and gets a
  distinct remedy: its marginal manifest formulas cost up to 10.094 s against a 10000 ms
  per-solve budget — ~1.0x headroom BY CONSTRUCTION, since the manifest is defined as "conclusive
  at 10000 ms" and the gating run re-checks at exactly the derivation budget. Recommended:
  decouple the gating RE-CHECK budget (new constant, 20000 ms, ~2x the slowest known-conclusive
  member) from the manifest DERIVATION budget (`SELF_SCAN_SOLVE_TIMEOUT_MS`, unchanged at 10000,
  keeping 8.8's re-derivation trigger and the exhaustive scan's wall-clock ceiling untouched).
  Membership is monotone in budget, so no manifest re-derivation is required. The floor stays at
  100. Trade-off recorded in section 7.3.
- **Nothing recommended here lowers a floor, xfails/skips a test, revisits
  `ORACLE_PASS2_TIMEOUT`, or touches `disagreements == 0`.** Both verify-refactor Step 5c pins
  and the Step 3 collection pins are strengthened or re-pinned per their own documented
  procedure, never weakened.

## 1. Layer Under Decision (and what is settled)

The pass-level budget (`ORACLE_PASS2_TIMEOUT`, 900 -> 1800 s in commit `e3b09d4e`) is settled,
measured, and confirmed: pass 2 wall clock came in at 958.58 s and 847.38 s against 1800 s in the
two full-gate runs — never approached. That layer is out of scope.

The unresolved layer is the per-formula solve budgets:

| Budget | Where defined | Governs |
|---|---|---|
| 60000 ms | `test_oracle_interface.py:963` (inline `timeout_ms=60000`) | `TestMixedFormulas::test_mixed_and_box_next` (pass 2) |
| 60000 ms | `test_oracle_interface.py:1000` | `test_mixed_and_all_future_neg` (pass 1) |
| 180000 ms | `TEMPORAL_SOLVE_TIMEOUT_MS`, `test_oracle_interface.py:116` | temporal-depth>0 solves incl. the ternary test's `next_A` leg (`test_oracle_interface.py:1343`, pass 1) and the spot-check F5/F4 solves (pass 2) |
| 150000 ms | `test_oracle_interface.py:993` | `test_mixed_or_diamond_prev` (pass 2) — already recalibrated, healthy |
| `max_time: 30` s | `examples.py` `BM_CM_4_settings` + inline at `test_boundary_regression.py:386` | the three BM_CM_4 tests (pass 2) |
| `max_time: 15` s | `examples.py` `BM_CM_1_settings` | `test_regression_all_active_examples[BM_CM_1]` (pass 2) |
| `SELF_SCAN_SOLVE_TIMEOUT_MS` = 10000 | `test_cross_oracle_differential.py:93` | every solve in `TestGatingConclusiveScan` (pass 2) and the exhaustive scan; pinned by verify-refactor Step 5c |

Floors (hard-constrained, untouched): `MIN_CONCLUSIVE_GATING_FORMULAS = 100`
(`test_cross_oracle_differential.py:162`; 103 manifest entries, so 3 formulas of slack) and
`MIN_CONCLUSIVE_SCAN_FORMULAS = 90` (line 123). The 99-of-103 outcome arises when 4+ of the 103
known-conclusive manifest formulas time out at 10000 ms in a single gating re-check
(`timeout_count=4` in both observed misses).

## 2. Mechanism Map (verified, with citations)

**Two-pass structure** (`oracle/run-oracle-suite.sh`): pass 1 runs
`pytest oracle -n 6 -m "not xdist_serial and not slow"` (line 160-162; hard-coded `-n 6`, not
`-n auto`, per the inline rationale at lines 153-159). Pass 2 runs
`pytest oracle -m "xdist_serial and not slow"` with **no `-n` flag at all** (lines 167-169) —
genuinely serial, confirmed in the live red-run transcript (`14 selected`, no xdist worker
banner). The passes run sequentially, never concurrently. There is no CPU pinning, `taskset`,
or `nice` anywhere in the runner or in `verify-refactor.sh`, and `verify-refactor.sh` runs its
steps strictly sequentially — the gate never contends with itself (the one historical
self-contention incident was operator-launched, not gate-structural; see section 6).

**Serial-pass membership mechanism**: `@pytest.mark.xdist_serial` at the test/class definition
site, plus `oracle/conftest.py:27-30`'s `_XDIST_SERIAL_NODEID_FRAGMENTS` for two parametrized
cases that cannot carry source marks (`[some_past]`, `[BM_CM_1...]`). Current population: 14
tests (enumerated via `pytest oracle --collect-only -q -m "xdist_serial and not slow"`),
exact-pinned by verify-refactor Step 3 (`BASELINE_ORACLE_SERIAL_COUNT=14`,
`verify-refactor.sh:67`) with a documented all-four-together re-pin procedure
(`verify-refactor.sh:57-64`) that has been exercised twice (606/594/10/2 -> 627/611/14/2).

**Failure identities in the phase-5 red run** (from `/tmp/verify-refactor-oracle.txt`, still on
disk and re-read for this report): pass 1 green (605 passed, 2 [KNOWN] timeout-skips, 4 xfail,
706.49 s). Pass 2: 3 failed, 11 passed, 1030.74 s (vs. 1800 s budget):

1. `TestBoundaryDocumentation::test_countermodel_bm_cm4_at_example_settings`
   (`test_boundary_regression.py:359`) — `assert False` after a blown 30 s `max_time`.
2. `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
   (`test_cross_oracle_differential.py:2303`) — "Only 99 of 103 formulas were conclusive
   (floor=100)", `disagreements=0`.
3. `TestMixedFormulas::test_mixed_and_box_next` (`test_oracle_interface.py:951`) —
   `OracleTimeoutError: Z3 solver did not decide the formula within 60000 ms`.

**Where the failing formulas live**: `and(box(A), next(B))` at `test_oracle_interface.py:962`;
BM_CM_4 (`Diamond A ⊢ past A`, N=2, M=2, contingent) at `examples.py:377-399` and inline at
`test_boundary_regression.py:380-388`; the gating-scan population in
`oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json` (103 entries), solved via
`_generate_differential_report(..., timeout_ms=SELF_SCAN_SOLVE_TIMEOUT_MS)` at
`test_cross_oracle_differential.py:2319-2330`.

## 3. The Evidence: These Failures Are Load-Independent, Not Contention

The task instructs that option (a) "most directly matches the measured failure mode (quiet run
vs loaded run)". The verified record shows the opposite — the quiet/loaded framing does not
survive contact with the triage data
(`specs/143_.../summaries/01_phase4-triage-record.md`):

| Full-gate attempt | Load avg | Pass 1 | Pass 2 | Failures |
|---|---|---|---|---|
| Contended (2026-08-10 16:23) | 5.36-7.47 | PASSED | FAILED | `and_box_next` (60 s), scan floor 99/103 |
| Quiet (2026-08-10 22:46) | **1.57-2.25** | **FAILED** | FAILED | pass 1: `and_all_future_neg` (60 s), ternary `next_A` (180 s); pass 2: `and_box_next` (60 s) |
| Phase-5 re-run (2026-08-11, load ~3.95) | ~3.14-3.95 | PASSED | FAILED | BM_CM_4-at-example-settings (30 s), scan floor 99/103, `and_box_next` (60 s) |

The quiet attempt failed MORE tests than the contended one, and `test_mixed_and_box_next` failed
in all three attempts — including at load 1.57, a level at which no plausible contention
mechanism operates on a serial pass. The triage record itself classified this as its branch
(iii): "a varying set of per-formula solve timeouts, load-independent, with `disagreements=0`
throughout — a genuine budget/performance condition in the oracle's Z3 solves, not a
machine-contention artifact."

The paired-seed baselines make the same point quantitatively. Reanalysis of
`baselines/01_solve-cost-baseline.json` and `05_final-solve-cost.json` (7 runs per formula per
round, isolated, serial, seeded):

| Formula (budget) | Round | median wall | max wall | runs OVER budget |
|---|---|---|---|---|
| `and_box_next` (60 s) | baseline | 46.54 s | 60.37 s (censored) | **3 of 7** |
| `and_box_next` (60 s) | final | 49.89 s | 60.39 s (censored) | **3 of 7** |
| ternary `next_A` (180 s) | baseline | 94.36 s | 180.47 s (censored) | 1 of 7 |
| ternary `next_A` (180 s) | final | 89.69 s | 180.39 s (censored) | 1 of 7 |
| `and_all_future_neg` (60 s) | both | 18.6-20.1 s | 23.6-25.2 s | 0 of 14 |

A formula that blows its budget on 3 of 7 isolated, contention-free, seeded draws — identically
in two independent measurement rounds — does not have a contention problem. It has a budget that
sits inside its genuine cost distribution. Ambient load only shifts WHICH marginal draws land
over the line, which is why the failing set "moves" between runs while `and_box_next` (the worst
margin) recurs in all of them.

## 4. Why the Workload Legitimately Grew (the recorded argument option (b) requires)

The task forbids selecting (b) without an explicit argument distinguishing "budgets never
calibrated against measured cost + workload legitimately grew" from "papering over contention".
That argument, with provenance:

1. **The cost increase is real, permanent, and correctness-required.** Commit `3c0cf210`
   (2026-08-07) replaced fixed-name Z3 bound variables with per-call-unique names in all 14
   quantified temporal/modal operator sites, eliminating a proven term-aliasing UNSOUNDNESS
   (concrete casualty: F4 `p U q -> q U p` was mis-documented VALID because sibling Until
   instances aliased). The fix removed an accidental term-sharing shortcut that had kept several
   formulas artificially fast. This mechanism, its casualties, and its costs are documented in
   the prior research report's root-cause chain (section 3) and in three inline records written
   at the time: `test_mixed_or_diamond_prev`'s docstring (~1.5 s -> ~73 s), `BM_CM_4_settings`'
   `max_time` comment (~3 s -> ~15-24 s), and the archived soundness-fix summary.
2. **The 60000 ms budget predates all of it and was never calibrated.** `git blame` places
   `timeout_ms=60000` at commit `ea516a4b` (2026-06-01) — written for the pre-fix encoding, in
   the original in-package test file, before the oracle tree existed. No commit since has
   recorded a measurement basis for it. The only post-fix characterization ("~44-45s, ~25%
   headroom... confirmed by repeated serial timing", commit `7f7269d6`, 2026-08-10) was a
   2-sample serial observation made while relocating the test to the serial pass "with no budget
   change"; the 21-run paired data now shows that characterization sampled the lucky side of a
   distribution whose median is 46.5-49.9 s and whose bad-draw tail (~43% of seeds) exceeds the
   budget entirely (uncensored bad-draw cost: 66.6-100.7 s, section 5).
3. **The 180000 ms budget had a basis, but it is 13 days older than the cost increase.**
   `TEMPORAL_SOLVE_TIMEOUT_MS`'s comment ("measured solve times cluster at 53-59s", i.e. ~3x
   margin) was committed 2026-07-25 (`a4f99f5e`); the soundness fix landed 2026-08-07. Post-fix,
   `next_A` medians are ~90 s and the measured bad-draw tail does not decide at 600 s
   (section 5) — the recorded ~3x margin has silently become a margin against a distribution
   whose tail no budget covers.
4. **The codebase has already adjudicated this exact situation twice, in option (b)'s favor,
   with recorded reasoning**: `test_mixed_or_diamond_prev` 60000 -> 150000 (~2x its measured
   post-fix 72.6 s, plus `xdist_serial`), and `BM_CM_4` `max_time` 15 -> 30 (task-139 summary:
   "genuine solve-time cost, term-identity-shortcut-loss mechanism, not a soundness issue").
   Both were accepted as calibration, not papering. The formulas at issue here are the same
   operator family hit by the same mechanism — they were simply not recalibrated at the time.
5. **The distinguishing test applied**: "papering over contention" = widening a budget that
   suffices on an idle machine so that loaded runs stop failing. That is NOT this case: the
   budgets fail on isolated, contention-free, seeded measurement (3/7 and 1/7), and on a
   quiet-machine gate run (load 1.57). Conversely, `and_all_future_neg`'s single observed
   failure WAS pure contention (0/14 isolated draws over budget, 2.4x isolated headroom, failed
   only in the `-n 6` parallel pass) — and accordingly this report recommends relocation (a),
   NOT a budget change, for it. The two remedies are matched to the two measured mechanisms.

This is the same standard the pass-level decision met: a real measurement basis, a documented
"workload grew" causal chain, the ~2x-of-measured convention, and inline recording at the
constant.

**Where TESTING_GUIDE 8.6/8.8 land on this.** 8.8's "a skip/timeout is a budget/performance
outcome, never cleared by widening a solve budget" forbids REACTIVE widening — widening as the
response to a red run, without measurement, to force green. 8.6 simultaneously mandates that
budgets be set "generously, not tightly", far above measured solve time, precisely because a
tight budget "silently inverts its semantic conclusion" (and documents a ~6x margin that still
failed once). The two are reconciled by the measurement basis: a budget at ≤1.0-1.3x the
measured contention-free cost distribution is a miscalibrated budget under 8.6, and correcting
it with a recorded ~2x-of-measured basis is calibration; a budget already at ~2x+ of measured
cost that fails only under load is a contention problem, and widening it would be the move 8.8
forbids. Every widening recommended here is in the first category, and the one formula in the
second category (`and_all_future_neg`) gets scheduling, not widening. The implementation should
also update the stale "~44-45s / ~25% headroom" docstring so the inline record matches the
21-run data — TESTING_GUIDE 8.6 itself needs no text change.

## 5. Fresh Probe: the Uncensored Bad-Draw Costs (measured in this dispatch)

The 21-run baselines' "max" values are censored — a 60.39 s entry with `timeout: true` means
"the budget fired at 60 s; true cost unknown". Calibrating a new budget from censored maxima
would under-set it, so this dispatch ran a short uncensored-tail probe: a scratch copy of
`bench_solve_cost.py` (methodology unchanged: same pipeline, same pinned seeds, rlimit primary /
wall secondary) with probe budgets raised to 300 s (`and_box_next`) and 600 s (`next_A`),
re-running exactly the seeds that timed out in the final baseline round (seeds 1, 2, 3 for
`and_box_next`; seed 3 for `next_A`). Probe artifacts:
`specs/145_decide_oracle_per_formula_solve_capacity/baselines/01_uncensored-tail-probe.json`
(+ `.md` summary) for `and_box_next`, and `baselines/02_next-a-divergence-probe.json` for the
`next_A` divergence probe.

| Formula / seed | Censored (final round, at old budget) | Uncensored probe | rlimit (probe vs. good-draw ~130M) |
|---|---|---|---|
| `and_box_next` seed 1 | 60.25 s, rlimit 140M, timeout | **94.28 s**, decided | 222M (1.71x) |
| `and_box_next` seed 2 | 60.39 s, rlimit 163M, timeout | **92.79 s**, decided | 236M (1.81x) |
| `and_box_next` seed 3 | 60.36 s, rlimit 156M, timeout | **104.24 s**, decided | 338M (2.60x) |
| ternary `next_A` seed 3 | 180.39 s, timeout | **UNDECIDED at 601.0 s** (600 s probe budget) | 1026M vs. good-draw median 137M (**7.5x, still running**) |

Ambient load during the probe was ~2-4.4 (not idle), so the wall figures are mildly inflated;
the rlimit ratios — load-independent by construction, the same reason the prior task chose
rlimit as primary metric — corroborate the shape. The two formulas measured OPPOSITE tail
behaviors:

- **`and_box_next`: bounded bad tail.** All three previously-censored seeds DECIDE (countermodel
  found) at 92.8-104.2 s, 1.7-2.6x a good draw's solver work. This is a budget-boundary failure:
  a recalibrated budget deterministically fixes it.
- **`next_A`: divergent bad tail.** The bad seed consumed 3.3x the current budget and 7.5x a
  good draw's rlimit without deciding. Its good draws (6 of 7 seeds) cost 26-100 s wall
  (median ~50 s, rlimit median 137M, max 239M); the bad draw is not "slightly over" — it is in a
  different regime, consistent with the encoding's known property that many bare temporal
  formulas are simply inconclusive at any practical budget (60-65% of the exhaustive-scan
  population). No observed draw lies in the 180-600 s band, so widening the budget into that
  band buys nothing measurable: budget recalibration CANNOT fix this leg, and neither can
  scheduling (the draws are isolated and contention-free already). See section 7.2.

**Derived budget recommendations (the ~2x-of-measured-worst convention, matching both the
pass-level decision and the `or_diamond_prev` precedent at 150000 ≈ 2.07x of 72.6 s):**

| Constant / site | Current | Measured worst (uncensored) | Recommended | Margin vs. worst / vs. median |
|---|---|---|---|---|
| `test_mixed_and_box_next` `timeout_ms` | 60000 | 104.24 s | **240000** | 2.3x / 4.8x |
| ternary `next_A` witness | 180000 | divergent (>601 s, undecided) | **no budget fix possible — substitute the witness formula (7.2)** | — |
| `BM_CM_4` `max_time` (examples.py + inline test) | 30 | ~24 s (prior task's record; not re-probed) | **60** | 2.5x / ~3x |
| Gating-scan RE-CHECK budget (new constant; see 7.3) | 10000 (shared) | 10.094 s (slowest known-conclusive member, manifest derivation record) | **20000** | ~2x |

Notes: (i) `TEMPORAL_SOLVE_TIMEOUT_MS` itself (180000) is NOT changed: its other users either
pass with real margin or intentionally EXPECT `OracleTimeoutError` (`validate_self` tests),
and raising it would multiply the wall cost of every expected-timeout solve. `and_box_next`'s
240000 is an inline per-site value, matching how that test's budget is already expressed.
(ii) BM_CM_4 was not re-probed here (three tests share it and its prior 15-24 s record is
uncensored and recent); the plan phase may optionally probe it with the same harness before
finalizing 60.

## 6. Is Pass 2 Actually Contention-Free? (task question, answered)

Verified affirmative for everything the gate controls:

- Pass 2 runs with no `-n` flag — a single pytest process, zero xdist workers
  (`run-oracle-suite.sh:167-169`; transcript confirms no worker banner).
- Pass 1 and pass 2 are strictly sequential in the runner; `verify-refactor.sh`'s steps are
  strictly sequential; nothing in the gate runs concurrently with pass 2.
- There is no CPU pinning/affinity anywhere; adding it would not help, because pinning cannot
  reserve cores against OTHER processes without privileged cgroup control.
- The residual contention source is EXTERNAL to the gate: this is a continuously-active shared
  development machine (concurrent agent sessions, `lean build`, `latexmk -pvc` watchers —
  inventoried in the pass-level report's appendix), and a genuinely idle window "is not
  obtainable on demand". The one recorded 99/103 floor miss outside a full gate was
  self-inflicted by an operator-launched concurrent `verify-refactor.sh --skip-oracle` — an
  operational hazard, not a gate-structural one.

Consequence: for tests ALREADY in pass 2, option (a) has no remaining mechanism — there is no
"more machine" the gate can grant them, and the quiet-run failure evidence (section 3) shows
machine capacity was not the binding constraint anyway. Option (a) remains genuinely applicable
only to marginal tests still in the `-n 6` parallel pass, where six sibling workers are a real,
gate-controlled contention source. Two tests qualify (section 7.2).

## 7. The Decision, Component by Component

### 7.1 Option (b) — recalibrate the never-calibrated / stale-calibrated bounded budgets. SELECTED (primary).

Per sections 3-5: `and_box_next` 60000 -> 240000 (inline at `test_oracle_interface.py:963`);
BM_CM_4 `max_time` 30 -> 60 at both definition sites (`examples.py` `BM_CM_4_settings` and the
inline `test_boundary_regression.py:386`), keeping the two in sync. Each change carries the
measurement basis inline at the constant (probe figures + convention + the soundness-fix causal
chain), mirroring how `or_diamond_prev`'s and `BM_CM_4`'s existing recalibrations are recorded.
The stale "~44-45s / ~25% headroom" docstring in `test_mixed_and_box_next` is corrected by the
same edit.

Explicitly NOT widened: `TEMPORAL_SOLVE_TIMEOUT_MS` (see section 5 note (i)),
`and_all_future_neg` (60000 stands; 2.4x isolated headroom is within convention; its one
failure was parallel-pass contention -> relocation below), `or_diamond_prev` (150000 stands,
~2x, healthy), BM_CM_1 (15 s vs. ~8 s measured — thin-ish but zero observed failures; watch
item), spot-check F5/F4 (180000; documented session-order sensitivity but zero observed gate
failures; watch item), and the ternary `next_A` witness (budget widening measurably buys
nothing against a divergent tail — next subsection).

### 7.2 The ternary `next_A` witness — substitution, because neither budget nor scheduling can fix a divergent tail. SELECTED, flagged for plan-phase adjudication.

`TestTernarySerializationAll::test_all_sat_task_relation_ternary` asserts the ternary
`{source, duration, target}` serialization shape of `task_relation` across five witness
formulas; `next_A` (`_next(A)`) is there to exercise the temporal-depth>0 / M=3 serialization
path. The probe shows `next_A`'s bad draws do not decide at 3.3x the current budget (7.5x a good
draw's solver work, still running) — the same known encoding property that leaves 60-65% of the
exhaustive-scan population inconclusive at any practical budget. Consequences: (i) widening the
budget cannot fix it (no observed draw lies in the band a wider budget would rescue);
(ii) relocation cannot fix it (the divergent draws occur in isolated, contention-free
measurement); (iii) accepting it means a ~1-in-7 hard gate failure from this one leg forever.

Recommended remedy: **substitute a measured-reliable depth-1 SAT witness for `_next(A)` in this
test's `sat_formulas` list**, preserving the test's actual assertion (temporal-model
serialization shape) with a formula that reliably reaches it. Two already-measured candidates:
`_some_future(A)` (`\Future p` measured ~3 s — 60x headroom at the existing budget) and
`_and(_neg(A), _next(B))` (median 18.6-20.1 s, max 25.2 s across 14 contention-free draws — the
latter still exercises `next`'s serialization, inside a conjunction). The plan phase must
confirm the chosen witness across the 5-seed harness (cheap: minutes) and record the basis at
the list entry.

Adjudication against the no-weakening constraints, recorded honestly: this is NOT an xfail,
skip, or disable — the test keeps all five legs hard-asserting. What changes is WHICH temporal
formula witnesses the serialization path. Bare `next(A)`'s own solve coverage is retained
elsewhere: the enriched-pair `[next]` case solves `_next(A)` vs. `untl(A, bot)` in
`test_enriched_vs_primitive_sat_agreement`, and `next`-exercising conjunctions are solved in
`test_mixed_and_box_next` / `test_mixed_and_all_future_neg`. What IS lost: a hard-asserting
solve of bare `next(A)` specifically. If the plan phase judges that loss unacceptable, the
recorded fallback is relocation + a 480000 ms budget with an explicitly-accepted residual
~1-in-7 divergent-draw failure rate — but the measurement says that fallback does not actually
make the gate reliable, which is why substitution is the recommendation.

### 7.2b Option (a) — relocate the one pure contention victim. SELECTED (secondary).

`TestMixedFormulas::test_mixed_and_all_future_neg` gains `@pytest.mark.xdist_serial`: pure
contention victim (section 4, point 5 — 0 of 14 isolated draws over budget, failed only under
`-n 6`); relocation is the complete fix, budget untouched — the same reasoning that moved the
four previous `xdist_serial` relocations. With the 7.2 substitution in place, the ternary test
no longer needs relocation (a 20-60x-headroom witness tolerates `-n 6` contention comfortably).

Consequences handled: verify-refactor Step 3 re-pin 611 -> 610 parallel, 14 -> 15 serial, total
627 unchanged, all four together with a provenance comment — the exact procedure already
exercised twice (`verify-refactor.sh:57-81`).

### 7.3 The gating-scan margin — decouple re-check budget from derivation budget. SELECTED, with trade-off recorded.

Mechanism: `TestGatingConclusiveScan` currently re-solves the 103 known-conclusive formulas at
`SELF_SCAN_SOLVE_TIMEOUT_MS` = 10000 — the same budget the manifest was DERIVED at. The slowest
member entered the manifest at 10.094 s, so the re-check runs at ~1.0x headroom by construction
and a 4-formula flip (99/103 < 100) is an ordinary-variance outcome, exactly as observed twice.

Fix: introduce `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` used ONLY at the two call sites inside
`TestGatingConclusiveScan` (`test_cross_oracle_differential.py:2321,2329`).
`SELF_SCAN_SOLVE_TIMEOUT_MS` stays 10000 everywhere else (exhaustive scan, scan_runner default,
manifest derivation). Soundness of the decoupling: conclusiveness is monotone in budget, so
every formula conclusive at 10000 in derivation remains a legitimate member at 20000; the
`disagreements == 0` tooth now checks MORE decided results, never fewer; the floor (100) and
manifest are untouched; 8.8's "budget change requires re-derivation" trigger remains tied to
the derivation budget, which does not change — so no 60-90-minute re-derivation is needed and
the exhaustive scan's wall-clock ceiling analysis is unaffected.

Trade-off (recorded, per the task's honesty requirement): per-formula cost-regression detection
at the 10 s threshold moves from every gating run to the scheduled exhaustive scan (which keeps
10000 and its freshness check). A formula whose cost regresses 9 s -> 19 s would pass the gating
re-check until the next exhaustive run. This is the correct trade: the gating scan's teeth are
the soundness claim and the gross-starvation floor, not per-formula performance tracking — and
the alternative (widening `SELF_SCAN_SOLVE_TIMEOUT_MS` itself) costs a ~76-minute re-derivation,
pushes the exhaustive sweep's extrapolated wall toward its 90-minute abort ceiling, and was
already shown to buy almost nothing (doubling 5000 -> 10000 gained 5 conclusive formulas).

Enforcement: ADD `GATING_RECHECK_SOLVE_TIMEOUT_MS=20000` to verify-refactor Step 5c's pinned
constants (a strengthening — one more constant that cannot drift silently);
`SELF_SCAN_SOLVE_TIMEOUT_MS=10000` stays pinned unchanged.

### 7.4 Pass-wall arithmetic (does any of this threaten the pass budgets?)

Pass 2, worst-case bound after all changes: current measured band 800-1030 s; add
`all_future_neg` (~20-25 s typical, 60 s budget-bound), add `and_box_next`'s widened bad-draw
bound (+180 s over the current 60 s bound in the worst draw, though its measured worst is
104 s), BM_CM_4 (+30 s x 3 tests in the worst draw), scan re-check (+~40 s if 4 marginal
formulas run to the new 20 s budget). Typical-case: ~850-1100 s (headroom ~700-950 s under
1800 s). Simultaneous-worst-case (every widened budget drawn to its maximum in the same run):
~1450-1550 s — under the budget with margin, and that scenario requires 5+ independent
worst-draws to coincide. The plan phase should record this arithmetic at
`ORACLE_PASS2_TIMEOUT`'s comment as a headroom note WITHOUT changing the 1800 s value (the
pass-level decision is not implicated; if a future measured pass-2 run actually approaches
1800 s, that is a new pass-level measurement to take to that layer's own procedure). Pass 1
loses ~20 s of typical work (one relocation) and sheds its two observed flake sources (the
relocated `all_future_neg` and the substituted `next_A` witness), gaining reliability at
roughly neutral wall cost.

### 7.5 Option (c) — accept and monitor. REJECTED.

Honestly evaluated: (i) the gate is the wave-boundary regression gate for the refactor line and
is currently red in 3 of 3 full-gate attempts — "monitor" means every future wave boundary
adjudicates the same known failure signatures by hand; (ii) the pass-level task is blocked
pending a green Step 6, so acceptance perpetuates a blocked dependency; (iii) the failure
distribution is now measured (43% per-run failure probability for `and_box_next` alone across
seeds — the compound probability of a green gate is well under 50%), so "accept" is
statistically "accept a mostly-red gate"; (iv) nothing about monitoring generates new
information the 21-run baselines + probe have not already provided. Rejected.

## 8. Hard-Constraint Compliance Check

- `MIN_CONCLUSIVE_GATING_FORMULAS` / `MIN_CONCLUSIVE_SCAN_FORMULAS`: untouched (100 / 90).
- No xfail/skip/disable of any failing test; all three failing tests remain fully asserting.
- `ORACLE_PASS2_TIMEOUT`: untouched at 1800 (7.4 records headroom arithmetic only).
- `disagreements == 0`: untouched; strengthened in practice (more conclusive results checked).
- All measurement/adjudication inside `nix develop` (probe runs used
  `nix develop --command python ...`).
- No encoding-level changes proposed (dead ends 1-11 stand; `bench_solve_cost.py` reused for
  measurement only).
- No test is xfailed, skipped, or disabled by the 7.2 substitution: all five ternary legs stay
  hard-asserting; the coverage delta (bare `next(A)`'s hard-asserted solve) is enumerated in
  7.2 together with where `next` coverage is retained, and the fallback is recorded.
- Verify-refactor Step 5c: constants pinned there keep their values; one NEW pin added (7.3).
- Verify-refactor Step 3: re-pinned via its own documented all-four-together procedure (7.2b).

## 9. Recommended Plan Shape (for the plan phase)

1. **Phase 0 — cheap confirmation probes** (minutes each, harness reuse): 5-seed run of the
   chosen substitute witness for the ternary test (7.2); optional BM_CM_4 re-probe before
   finalizing 60 s.
2. **Phase 1 — bounded-budget recalibration + inline records** (option b): `and_box_next`
   240000; BM_CM_4 `max_time` 60 in `examples.py` + `test_boundary_regression.py` inline;
   correct the stale "~44-45s" docstring; each with the measurement basis inline.
3. **Phase 2 — witness substitution** (7.2): replace `_next(A)` in
   `test_all_sat_task_relation_ternary`'s `sat_formulas` with the Phase-0-confirmed witness,
   basis recorded at the list entry.
4. **Phase 3 — relocation + re-pin** (option a): `xdist_serial` on
   `test_mixed_and_all_future_neg`; re-pin Step 3 to 627/610/15/2 with provenance comment.
5. **Phase 4 — scan re-check decoupling**: `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` +
   comment block recording basis and trade-off; swap the two call sites; add the new Step 5c pin;
   note the two-budget contract in TESTING_GUIDE 8.8's known-conclusive subsection.
6. **Phase 5 — gate confirmation**: full `verify-refactor.sh` (no `--skip-oracle`) inside
   `nix develop` to "All checks passed"; ideally a second run to sample variance. If red
   recurs, triage against the new margins before touching anything (the probe harness is the
   tool); do not iterate budgets reactively.

## 10. Watch Items (recorded, no action)

- `BM_CM_1` `max_time: 15` vs. ~8 s measured (~1.9x): within convention but the thinnest
  untouched margin in pass 2; zero observed failures.
- `test_spot_check_individual_countermodels` F5 at 180000: documented session-order
  sensitivity; zero observed gate failures.
- The operational hazard of launching concurrent gate/suite runs on this shared machine
  (self-inflicted 99/103 incident) — a process gap flagged by the pass-level report's
  recommendations, not a code defect; unchanged here.
