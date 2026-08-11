# Capacity Decision Record: Oracle Per-Formula Solve Budgets

- **Date**: 2026-08-11
- **Task**: 145 - decide_oracle_per_formula_solve_capacity
- **Measurement inputs**:
  - `baselines/01_uncensored-tail-probe.md` (and_box_next uncensored tail, seeds 1-3)
  - `baselines/02_next-a-divergence-probe.json` (next_A divergence, seed 3, 600 s budget)
  - `baselines/03_witness-candidate-probe.{json,md}` (witness candidates + BM_CM_4, seeds 1-7)
  - 21-run gating history + 14 isolated seeded draws
    (specs/144_fix_oracle_per_formula_solve_timeouts, reports/01 of this task)
- **Method**: seeded, uncensored probes via `bench_witness_probe.py` /
  `bench_solve_cost.py` (pipeline mirrors `Z3OracleProvider.find_countermodel`; seeds pinned
  via `z3.set_param` in the harness only; rlimit primary metric, wall secondary)

This record is written BEFORE the code changes land; the code changes implement this record.

## 1. Per-mechanism decision table

| Mechanism | Site | Decision | Basis |
|---|---|---|---|
| `and_box_next` bounded tail | `test_oracle_interface.py` `test_mixed_and_box_next`, `timeout_ms` | 60000 → **240000 ms** | Uncensored probe: 3 previously-censored seeds DECIDE at 92.8-104.2 s (rlimit 222M/236M/338M vs ~130M good draw) — bounded, not divergent. 240000 = 2.3x measured worst per sibling convention (`or_diamond_prev` 150000 ≈ 2.07x of 72.6 s). Cost grew permanently with the 2026-08-07 bound-variable-aliasing soundness fix (`3c0cf210`); the 60000 figure (`ea516a4b`, 2026-06-01) predates it and was never recalibrated, while both siblings were. |
| BM_CM_4 bounded tail | `bimodal/examples.py` `BM_CM_4_settings` + inline copy in `test_boundary_regression.py` | `max_time` 30 → **120 s** (NOT the provisionally-planned 60) | Fresh 7-seed probe at a 120 s budget: all decide, median 6.88 s, **max 57.12 s** (seed 1, rlimit 32.2M). The prior "15-24 s" record under-sampled the tail: 60 s would cover the measured worst at only 1.05x — exactly the boundary-sitting this recalibration exists to remove. 120 = 2.1x measured worst, same convention as the other two recalibrated siblings. Raising `max_time` is monotone-safe for the countermodel assertion. |
| Ternary `next_A` divergent tail | `test_oracle_interface.py` `test_all_sat_task_relation_ternary` | **Recorded fallback**: relocate test to `xdist_serial` + `next_A` leg budget 180000 → **480000 ms**, accepted residual ~1-in-7 | Divergence probe: bad seed UNDECIDED at 601.0 s (600 s budget), rlimit 1.026B = 7.5x a good draw — no budget fixes a divergent draw. Substitution (the preferred remedy) is unavailable: BOTH candidates failed the 7-seed confirmation probe (section 3). Relocation removes the −n 6 contention adder; 480000 ms covers every measured *decided* draw with wide margin; the divergent draw remains a hard failure and its ~1-in-7 rate is explicitly accepted and recorded. |
| Gating-scan re-check headroom | `test_cross_oracle_differential.py` `TestGatingConclusiveScan` call sites | New **`GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000`**, decoupled from `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` (unchanged) | Slowest known-conclusive manifest member entered the manifest at 10.094 s against the 10000 ms derivation budget — the re-check runs at ~1.0x headroom BY CONSTRUCTION. 20000 = ~2x. Decoupling is sound because conclusiveness is monotone in budget: every derivation-time member remains legitimately conclusive at 20000; the floor (100) and the manifest are untouched; `disagreements == 0` now checks MORE decided results, a strengthening. |
| `all_future_neg` contention victim | `test_oracle_interface.py` `test_mixed_and_all_future_neg` | Add `@pytest.mark.xdist_serial`, budget UNCHANGED at 60000 | 0/14 isolated draws over budget in the two prior measurement rounds; its sole gate failure occurred under the parallel pass's six-way CPU contention (−n 6) — a scheduling problem, not a budget problem. See section 6 watch item for the fresh-tail caveat. |

Step 3 collection re-pin bound to the two relocations: 627 total / **609** parallel / **16**
serial / 2 slow (was 627/611/14/2; both relocations move parallel → serial, total unchanged).

## 2. Option (c) accept-and-monitor: REJECTED

- 3 of 3 recent full-gate runs were red on these mechanisms; `and_box_next` alone carries a
  ~43% per-run failure probability (3 of 7 isolated seeded draws over its old budget in both
  measurement rounds).
- The pass-level task is blocked on a green Step 6; monitoring keeps it blocked indefinitely.
- The 21-run history plus the seeded probes already characterize the distributions; further
  monitoring generates no new information — the mechanisms are measured, not mysterious.

## 3. Witness adjudication (updated with Phase 1 measurements)

The plan's adjudication concluded substitution would preserve the test's semantic intent
(the test asserts ternary serialization shape via an existential temporal-depth>0 witness at
M=3, not bare `next(A)` specifically), CONDITIONAL on a candidate measuring reliable across
the 7-seed harness (all decide, max wall ≤ 60 s, no rlimit outlier > 3x own median).

**Both candidates failed that confirmation** (`baselines/03_witness-candidate-probe.md`):

| Candidate | Result | Failure |
|---|---|---|
| `_and(_neg(A), _next(B))` (primary) | 7/7 decide; median 13.86 s; max **107.40 s** (seed 5), 80.65 s (seed 7); rlimit max 238.3M = **4.4x median** | > 60 s criterion; > 3x-median outlier criterion |
| `_some_future(A)` (secondary) | 6/7 decide; seed 7 **UNDECIDED at 180.85 s** (rlimit 337.5M); seed 2 at 85.75 s | fails "decides on all 7 seeds" |

The prior favorable figures (primary: median 18.6-20.1 s, max 25.2 s over 14 draws;
secondary: ~3 s) were drawn from seeds 0-4 (+ repeats) and single draws; seeds 5-7 expose
heavy tails both bases missed. A substitute that merely *moves* the unreliable tail to a
different formula would not make the gate reliable — the adjudicated ground for substitution
(measured reliability) does not exist for either candidate.

**Fallback invoked as recorded in the plan**: keep `_next(A)` (no coverage change at all —
strictly stronger on the no-disable constraint than substitution), relocate the ternary test
to `xdist_serial`, raise the `next_A` leg to 480000 ms via a per-leg override
(`TEMPORAL_SOLVE_TIMEOUT_MS` itself is untouched at 180000 for all other users), and accept
the explicitly recorded residual: a divergent draw (measured ~1-in-7 across the pinned-seed
distribution) remains a hard test failure. This fallback is inferior to a reliable
substitution (it does not make the gate fully deterministic), which is why substitution was
preferred — but no reliable substitute exists on current measurement, and xfail/skip/disable
is forbidden. The residual is a known, bounded, recorded operational hazard, and the test
keeps all five hard-asserting legs unchanged.

## 4. Gating re-check trade-off (recorded)

Widening the re-check budget to 20000 ms means a formula whose solve cost regresses from
<10 s into the 10-20 s band no longer trips the gating floor. That per-formula
cost-regression detection at the 10 s threshold moves to the scheduled exhaustive scan,
which keeps `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` and its manifest-freshness re-derivation
trigger unchanged. Accepted: the gating suite's teeth are soundness (`disagreements == 0`)
and the conclusiveness floor, both of which are strengthened, not weakened, by more decided
results.

## 5. Pass-2 worst-case arithmetic (ORACLE_PASS2_TIMEOUT stays 1800 s)

Recomputed for the fallback branch and the revised BM_CM_4 value. Simultaneous-worst-case
requires 6+ independent worst draws to coincide in one run:

| Component | Delta vs current worst band |
|---|---|
| Current measured pass-2 band (3 full-gate runs) | 800-1030 s |
| `and_box_next` worst-draw bound 60 → 240 s | +180 s |
| BM_CM_4 `max_time` 30 → 120 s, 3 tests | +270 s |
| Gating re-check: 4 marginal formulas x (20-10 s) | +40 s |
| Relocated `all_future_neg` (60 s budget bound; ~20-25 s typical) | +60 s |
| Relocated ternary test (typical 5-leg total ~5-110 s; worst measured decided draw ~110 s) | +110 s |
| **Simultaneous worst-case total (all draws decided)** | **~1450-1690 s** |

Even at the pessimistic top (~1690 s), pass 2 stays under 1800 s with ~110 s margin; the
typical case is ~850-1150 s (650-950 s headroom). The one scenario that could push past
1800 s — a divergent `next_A` draw consuming its full 480 s bound — is a scenario in which
the gate is ALREADY red from that leg's own hard failure (the accepted ~1-in-7 residual),
so the pass-level budget is not the binding constraint there and widening it would rescue
nothing. `ORACLE_PASS2_TIMEOUT` is therefore calibrated, not implicated, and stays 1800 s.

## 6. Explicit non-changes and watch items

- `TEMPORAL_SOLVE_TIMEOUT_MS = 180000`: unchanged (other users pass with margin or
  intentionally expect timeout); the ternary `next_A` leg gets a per-leg override instead.
- `ATEMPORAL_SOLVE_TIMEOUT_MS = 10000`: unchanged.
- `ORACLE_PASS2_TIMEOUT = 1800`: unchanged (section 5); a headroom note is added at its
  comment site.
- `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000`: unchanged everywhere (exhaustive scan, scan_runner
  default, manifest derivation).
- Floors unchanged: `MIN_CONCLUSIVE_GATING_FORMULAS = 100`,
  `MIN_CONCLUSIVE_SCAN_FORMULAS = 90`.
- `or_diamond_prev` (150000, xdist_serial): unchanged — already recalibrated with recorded
  reasoning.
- BM_CM_1 and spot-check F5/F4: watch items only, no change.
- **Watch item (new, from Phase 1)**: `test_mixed_and_all_future_neg`'s formula
  (`and(neg(A), next(B))`) measured 107.4 s / 80.6 s on probe seeds 5/7 — a heavier
  isolated tail than the "0/14 draws over 60 s" (seeds 0-4) basis for keeping its 60000 ms
  budget. The relocation still lands as planned (its observed gate failure WAS contention),
  and no reactive budget change is made; if a future gate reds on this test serially, treat
  that as new measurement contradicting the 60000 figure and re-adjudicate — do not tweak
  reactively.
- No encoding-level speedup attempts: the nine-plus recorded dead ends stand; out of scope.

## 7. Gate outcome appendix

### 7.1 Full-gate runs 1 and 2 (2026-08-11): red on non-remedied mechanisms

Two full `verify-refactor.sh` runs (transcripts: `baselines/04_full-gate-transcript.txt`,
`baselines/05_full-gate-transcript-run2.txt`):

| | Run 1 | Run 2 |
|---|---|---|
| Wall | 31m18s | 35m37s |
| Steps 1-5 | ALL GREEN (new pins 627/609/16/2 and 5-constant set verified) | ALL GREEN |
| Pass 1 | PASSED (602 passed, 3 skipped, 4 xfailed, 562.7 s) | PASSED (602/3/4, 555.1 s) |
| Pass 2 | 1 failed / 15 passed, 1066.98 s | 1 failed / 15 passed, 1321.31 s |
| Pass 2 failure | `test_temporal_propositional_interleaving` (some_future(p) draw blew its 5000 ms provider default on 1 of 50 iterations) | `TestGatingConclusiveScan`: 98/103 conclusive vs floor 100 (5 re-check timeouts; disagreements = 0) |
| Step 7 | FAIL: BM_CM_1 (42/43) | FAIL: BM_CM_1 (42/43) |
| disagreements | 0 throughout | 0 throughout |

**Every remedied mechanism was green in both runs**: and_box_next, BM_CM_4 (all sites),
the relocated ternary test (next_A leg decided), the relocated all_future_neg, and the
gating re-check's soundness tooth. Pass-2 wall stayed inside the recomputed arithmetic
band both times.

### 7.2 BM_CM_1 diagnosis (Step 7, failed both runs): PRE-EXISTING, not change-induced

Hypothesis tested (cheaply, without full gate runs): that the Phase 3 edit to BM_CM_4's
`max_time` in the same examples.py induced the adjacent BM_CM_1 failure. REFUTED by direct
isolated measurement of `test_example_cases[BM_CM_1-example_case7]` (the exact Step 7
selection, `--timeout=120`, one test alone per process):

| Commit | Isolated runs | Walls |
|---|---|---|
| HEAD (all task changes) | PASS, FAIL, PASS | 15.12 s / 15.20 s / 13.09 s |
| Pre-task commit `8bcff93d` (no task changes) | PASS, PASS, FAIL, FAIL | 14.23 s / 13.71 s / 15.32 s / 15.25 s |

BM_CM_1 straddles its own `max_time: 15` boundary in ISOLATION at BOTH commits — the
failure reproduces with no task changes present and cannot be an induced regression. Its
recorded basis ("~8s with isolated Z3 context") is stale: genuine isolated cost now
measures ~13.7-15.3+ s, i.e. the budget sits at ~1.0x the real cost. This is the same
never-recalibrated-boundary family as the mechanisms this record remedies (`\Future A`
involves the all_future operator family whose cost grew with the 2026-08-07
bound-variable-aliasing fix). Seeded 7-seed probe (120 s budget): median 7.17 s walls,
but seed 2 CENSORED at 120.3 s (rlimit 203.1M = ~14x median). A 600 s uncensored
re-probe of seed 2 (`baselines/06_bm-cm-1-tail-probe.json`) is UNDECIDED at 600.7 s,
rlimit 930.2M = ~64x median — BM_CM_1's tail is DIVERGENT (same class as next_A), so no
budget fully closes it; the operative in-suite failure mode, however, is the BOUNDED
unseeded ~13-15 s draw against the 15 s budget, which a measured recalibration does fix.

**Remedy applied (recorded deviation from this plan's original non-goals, on measured
grounds after both gate runs failed Step 7 on it)**: `max_time` 15 → 60 at its single
definition site, = ~4x the measured operative worst decided draw (~15.1 s), chosen above
strict 2x because the thin decided sample (7 seeded + 7 isolated draws) demonstrably
under-represents the mid-tail (the same lesson BM_CM_4's fresh probe taught about its
"15-24 s" record), with the divergent seeded residual explicitly accepted and recorded —
exactly the next_A treatment. Verified post-change in section 7.6.

It is unknown whether the three pre-task red full-gate runs also failed Step 7 (their
recorded triage focused on pass-2 per-formula timeouts); what is established is that the
failure exists at the pre-task commit under isolated re-measurement today.

### 7.3 Load-independence reconciliation (correcting an earlier over-claim)

An earlier interim status grouped all run-1/run-2 failures as "contention-class". That
grouping is WRONG and is corrected here, reconciled against this task's own
load-independence finding (quiet-machine run at load 1.57 failed MORE tests than the
contended 5.4-7.5 run; and_box_next blew budget on isolated contention-free seeds):

- **BM_CM_1**: NOT contention. Deterministic-ish boundary-straddling at ~1.0x budget,
  reproduced in isolation on a quiet machine at both commits (section 7.2).
- **Interleaving some_future flake (run 1)**: NOT primarily contention. The 7-seed
  some_future probe shows genuine heavy-tail draws (85.7 s; one censored at 180 s) — 50
  sequential draws at a 5000 ms budget sample that tail. Load-independent mechanism;
  pre-existing exposure outside this task's remedied set.
- **Gating floor 98/103 (run 2)**: the ONE leg plausibly contention-driven — it matches
  the recorded "concurrent operator-launched run caused the one non-gate 99/103 incident"
  signature, and run 2 executed while a separate repository's lean/lake build held
  ~6.5 cores (25% RAM); run 2's pass 2 also ran 24% slower than run 1's. This attribution
  is one-leg-specific and does NOT generalize; the load-independence finding for the
  per-formula mechanisms stands unmodified.

### 7.4 Enriched-pair [next] coverage erosion (recorded; Phase 4 fallback reassessed)

Both runs' pass 1 timeout-skip inventory flags
`[NEW] test_enriched_vs_primitive_sat_agreement[next]`: at least one side did not decide
within 180000 ms (skip-on-timeout mechanism, pre-dating this task). The Phase 4
adjudication's point 3 cited that test as retaining bare next(A) solve coverage
"elsewhere, hard-asserting" — a premise that supported SUBSTITUTION. That premise is now
eroded: the divergent next-class tail also surfaces there, where it produces a skip, not
an assert.

Reassessment: this erosion REINFORCES rather than undermines the fallback actually taken.
The fallback kept `_next(A)` in the ternary test, hard-asserting at 480000 ms — currently
the strongest bare-next(A) solve gate in the suite (substitution would have removed it
while the "retained elsewhere" coverage was itself timeout-skipping). The [NEW] inventory
line's own demand (adjudicate the enriched pair's expected_sat against ground truth)
belongs to the timeout-skip inventory process, outside this task's mandate; recorded here
so it is not lost.

### 7.5 Remaining exposures for a green gate

1. ~~BM_CM_1 `max_time` at ~1.0x measured genuine cost~~ — REMEDIED (sections 7.2, 7.6):
   measured recalibration 15 → 60 with recorded basis and accepted divergent residual.
2. The interleaving test's 50-draw some_future exposure at 5000 ms fails a run with
   nontrivial per-run probability (observed 1 of 2 runs). Pre-existing; outside mandate;
   NOT remedied by this task.
3. A contention-free window is needed for the gating re-check floor (98/103 under heavy
   external load; 103/103 in run 1 and in the Phase 6 targeted run).

### 7.6 BM_CM_1 post-recalibration verification

At `max_time: 60`, `test_example_cases[BM_CM_1-example_case7]` in the exact Step 7
invocation, isolated, 3 consecutive runs on a quiet machine: PASS 9.65 s, PASS 10.65 s,
PASS 11.13 s — the operative draw sits at ~6x headroom against the new budget. Full-gate
confirmation is the Phase 7 run-3 transcript (below), not these isolated runs.

### 7.7 The divergent-tail pattern: what this task does NOT resolve

Stated plainly, so it cannot be papered over: this task's remedy is **capacity
recalibration for BOUNDED tails** (and scheduling for contention victims). It does not —
and cannot — resolve **divergent tails**, of which there are now THREE measured or
surfaced instances in the same encoding family:

1. The ternary test's `next_A` leg: undecided at 601.0 s, rlimit 1.026B = 7.5x good draw
   (`baselines/02_next-a-divergence-probe.json`). Residual ~1-in-7 accepted at 480000 ms.
2. BM_CM_1's seed-2 draw: undecided at 600.7 s, rlimit 930.2M = ~64x median
   (`baselines/06_bm-cm-1-tail-probe.json`). Residual accepted at 60 s.
3. `test_enriched_vs_primitive_sat_agreement[next]`: [NEW] timeout-skip at 180000 ms in
   both gate runs' pass 1 — the same next-class divergence surfacing through the
   skip-on-timeout mechanism.

Three instances is a pattern, not three coincidences: the post-soundness-fix encoding has
a population of formula/draw combinations that Z3 does not decide at ANY practical budget
(consistent with the known 60-65% inconclusive-at-any-budget scan population). Budget
recalibration converts bounded-tail failures into reliable passes; it converts divergent
tails only into bounded, recorded residual risk. Resolving the divergent class would
require encoding-level work, which is explicitly out of scope here (nine-plus recorded
dead ends; constraint 7) and remains an open, honestly-scoped limitation. Any future
recurrence of a divergent draw in a gate is a manifestation of this recorded residual —
triage it against this section before treating it as a new regression.
