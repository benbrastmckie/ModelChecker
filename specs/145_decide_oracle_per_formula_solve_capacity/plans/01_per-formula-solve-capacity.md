# Implementation Plan: Per-Formula Solve-Capacity Decision (Oracle Gating Suite)

- **Task**: 145 - decide_oracle_per_formula_solve_capacity
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None (this task unblocks the pass-level task currently blocked on a green Step 6)
- **Research Inputs**: specs/145_decide_oracle_per_formula_solve_capacity/reports/01_per-formula-solve-capacity.md
- **Artifacts**: plans/01_per-formula-solve-capacity.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Produce a recorded, implemented per-formula solve-capacity decision for the oracle gating
suite, ending in a full `code/scripts/verify-refactor.sh` run that prints
"[verify-refactor] All checks passed" with `disagreements == 0`. The remedy is composite,
matched per measured mechanism: (b) budget recalibration with inline measurement basis for
the BOUNDED tails (`and_box_next` 60000 -> 240000 ms; BM_CM_4 `max_time` 30 -> 60 s); witness
substitution for the one DIVERGENT tail (the ternary test's `next_A` leg, undecided at 600 s /
rlimit 7.5x a good draw — fixable by neither budget nor scheduling); a new decoupled
`GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` for the gating-scan re-check; and a narrow (a)
relocation for the one genuine `-n 6` contention victim (`test_mixed_and_all_future_neg`).
Option (c) accept-and-monitor is rejected and the rejection is recorded. The recorded decision
(inline bases at every changed constant + a standalone decision record) is a first-class
deliverable, not an afterthought to the code change.

### Research Integration

Key findings integrated from `reports/01_per-formula-solve-capacity.md`:
- The 60000 ms `and_box_next` budget dates to 2026-06-01 (commit `ea516a4b`), pre-dates the
  2026-08-07 bound-variable-aliasing soundness fix (`3c0cf210`) that permanently raised genuine
  solve cost, and was never recalibrated — while two siblings (`or_diamond_prev` 60000 -> 150000,
  BM_CM_4 15 -> 30) already were, with recorded reasoning.
- Fresh uncensored probe (`baselines/01_uncensored-tail-probe.md`): all three previously
  censored `and_box_next` seeds DECIDE at 92.8-104.2 s (rlimit 222M/236M/338M vs ~130M good
  draw). Bounded tail -> 240000 ms = 2.3x measured worst, per the sibling ~2x convention.
- `next_A` divergence probe (`baselines/02_next-a-divergence-probe.json`): the bad seed is
  UNDECIDED at 601.0 s (600 s probe budget), rlimit 1.026B = 7.5x a good draw. Divergent tail —
  no budget or scheduling fix exists.
- Failures are load-INDEPENDENT (quiet-machine run at load 1.57 failed MORE tests than the
  contended run at 5.4-7.5); `and_box_next` blew budget on 3 of 7 isolated seeded draws in both
  measurement rounds. Only `and_all_future_neg` (0/14 isolated draws over budget) is a genuine
  contention victim.
- Gating-scan re-check runs at ~1.0x headroom BY CONSTRUCTION (slowest manifest member 10.094 s
  vs 10000 ms budget); membership is monotone in budget, so decoupling the re-check budget
  requires no manifest re-derivation.

### Prior Plan Reference

No prior plan for this task. Calibration reference: the sibling tasks' recorded recalibrations
(`or_diamond_prev`, BM_CM_4 15 -> 30) and the pass-level `ORACLE_PASS2_TIMEOUT` decision provide
the ~2x-of-measured-worst convention and the inline-record discipline this plan follows.

### Roadmap Alignment

No roadmap_path provided; ROADMAP.md not consulted.

## Goals & Non-Goals

**Goals**:
- A green full gate: `code/scripts/verify-refactor.sh` (no `--skip-oracle`) inside `nix develop`
  prints "[verify-refactor] All checks passed" with `disagreements == 0`.
- Every changed budget constant carries an inline comment recording its measurement basis
  (probe figures, convention, causal chain) — not just a new number.
- A standalone decision record artifact capturing the per-mechanism decision, the witness
  adjudication, the option (c) rejection, and the pass-2 arithmetic.
- Verify-refactor pins strengthened per their own procedures: Step 3 re-pin to 627/610/15/2;
  Step 5c gains a `GATING_RECHECK_SOLVE_TIMEOUT_MS=20000` pin.

**Non-Goals**:
- No change to `ORACLE_PASS2_TIMEOUT` (1800 s — calibrated, not implicated; arithmetic below).
- No change to `TEMPORAL_SOLVE_TIMEOUT_MS` (180000 — other users pass with margin or
  intentionally expect timeout).
- No change to `SELF_SCAN_SOLVE_TIMEOUT_MS` (10000 — manifest derivation budget stays; no
  re-derivation triggered).
- No encoding-level speedup attempts (eleven dead ends already recorded in the prior task's
  report and summary; do not re-attempt).
- No change to floors, no xfail/skip/disable, no `BM_CM_1` or spot-check F5/F4 changes (watch
  items only).

## Hard Constraint Gates

These are gates on every phase, carried verbatim from the task. Any phase that would violate
one MUST stop and report instead of proceeding:

1. Do NOT lower `MIN_CONCLUSIVE_GATING_FORMULAS` or `MIN_CONCLUSIVE_SCAN_FORMULAS`.
2. Do NOT xfail, skip, or otherwise disable any failing test.
3. Do NOT revisit `ORACLE_PASS2_TIMEOUT` (calibrated, not implicated). The plan's worst-case
   pass-2 arithmetic (below) fits under 1800 s and is shown explicitly.
4. `disagreements` must remain 0 throughout.
5. All verification runs inside `nix develop` only (`nix develop --command ...`).
6. Every budget constant changed MUST carry an inline comment recording its measurement basis,
   not just a new number.
7. Do NOT re-attempt encoding-level speedups (nine-plus dead ends already recorded).
8. Files outside `specs/**` (test sources, `examples.py`, `verify-refactor.sh`,
   TESTING_GUIDE.md) MUST NOT cite task numbers; inline records cite measurements, dates,
   commits, and sibling constants instead (per no-task-references-in-deliverables.md).

## Witness Substitution Adjudication (decided here, not deferred)

**Question**: Does substituting a different witness formula for `_next(A)` in
`TestTernarySerializationAll::test_all_sat_task_relation_ternary`'s `sat_formulas` list
(`test_oracle_interface.py:1343`) preserve the test's semantic intent, or does it weaken
coverage in a way the no-disable constraints forbid?

**Decision: substitution PRESERVES the test's semantic intent. Substitute.** Reasoning:

1. **What the test asserts** is the ternary `{source, duration, target}` serialization shape of
   `task_relation` in models found across five witness formulas. Its semantic target is "for a
   spread of formula classes — including a temporal-depth>0 witness at M=3 — the found model's
   task relation serializes in ternary form." The witness formulas are existential vehicles for
   reaching that assertion; the test is "there EXISTS a witness of this shape that reaches the
   temporal serialization path," not "bare `next(A)` specifically must solve here." Nothing in
   the test's name, docstring, or assertions pins `next_A` as the semantic subject.
2. **The substitute preserves the exercised path.** The primary candidate
   `_and(_neg(A), _next(B))` is temporal-depth-1 at M=3 and still contains a `next` operator,
   so the temporal-depth>0 / M=3 serialization path — the thing `next_A` was there to exercise —
   remains exercised, and specifically through `next`'s own serialization. All five legs remain
   hard-asserting; nothing is xfailed, skipped, or disabled.
3. **Bare `next(A)` solve coverage is retained elsewhere, hard-asserting**: the enriched-pair
   `[next]` case solves `_next(A)` vs `untl(A, bot)` in
   `test_enriched_vs_primitive_sat_agreement`, and `next`-exercising conjunctions are solved in
   `test_mixed_and_box_next` and `test_mixed_and_all_future_neg`. The only delta is losing bare
   `next(A)` as a solo solve in THIS particular test — a duplicate of coverage that survives
   elsewhere, not a coverage hole.
4. **The alternative is not more coverage — it is a permanently unreliable gate.** The bad draw
   is measured DIVERGENT (undecided at 600 s, 7.5x good-draw rlimit, consistent with the
   encoding's known 60-65% inconclusive-at-any-budget population). Keeping `next_A` means a
   ~1-in-7 hard gate failure from this leg forever; a test that red-fails on a known-divergent
   draw asserts nothing extra — it just fails.
5. **This is not the forbidden move.** The constraint forbids xfail/skip/disable of a failing
   test. The test keeps five hard-asserting legs and its full assertion body. Changing which
   formula witnesses an existential claim is a workload correction matched to a measured
   divergence, with the reasoning recorded inline — the same category of recorded calibration
   the codebase has already accepted twice.

**Requirements bound to this decision**:
- The chosen witness must first be confirmed across the pinned-seed harness (Phase 1); the
  decision above is conditional on the substitute measuring reliable (all seeds decide, >= 3x
  headroom against 180000 ms).
- The adjudication reasoning (points 1-4, condensed) MUST be recorded inline in the test source
  at the `sat_formulas` list entry — not only in this plan and the decision record.
- **Candidate order**: primary `_and(_neg(A), _next(B))` (median 18.6-20.1 s, max 25.2 s across
  14 contention-free draws; retains a `next` operator); secondary `_some_future(A)` (~3 s, 60x
  headroom) if the primary fails Phase 1 confirmation.
- **Recorded fallback** (only if BOTH candidates fail Phase 1 confirmation — not expected given
  existing measurements): relocate the ternary test to `xdist_serial` and raise the leg's budget
  to 480000 ms with an explicitly recorded, accepted residual ~1-in-7 divergent-draw failure
  rate. This fallback is recorded as inferior (it does not actually make the gate reliable),
  which is why substitution is the decision.

## Pass-2 Worst-Case Arithmetic (constraint 3 evidence)

`ORACLE_PASS2_TIMEOUT` stays 1800 s. Simultaneous-worst-case bound after all changes (every
widened budget drawn to its maximum in the same run — requires 5+ independent worst-draws to
coincide):

| Component | Delta vs current worst band |
|---|---|
| Current measured pass-2 band (3 full-gate runs) | 800-1030 s |
| `and_box_next` worst-draw bound 60 -> 240 s | +180 s |
| BM_CM_4 `max_time` 30 -> 60 s, 3 tests | +90 s |
| Gating re-check: 4 marginal formulas x (20-10 s) | +40 s |
| Relocated `all_future_neg` (60 s budget bound; ~20-25 s typical) | +60 s |
| **Simultaneous worst-case total** | **~1170-1400 s** |

Even padding the current band's top (1030 s) with every worst-draw delta simultaneously
(~1400 s; the research report's more conservative accounting reaches ~1450-1550 s), pass 2
stays under 1800 s with >= 250 s margin. Typical case: ~850-1100 s (700-950 s headroom). Phase 3
records this arithmetic as a headroom note at `ORACLE_PASS2_TIMEOUT`'s comment WITHOUT changing
the value. Pass 1 sheds both observed flake sources at roughly neutral wall cost.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `and_box_next` exceeds even 240000 ms in the gate (contradicting probe) | H | L | Do NOT iterate budgets reactively; re-probe uncensored with the harness; treat as new measurement requiring a revised decision record |
| Chosen witness candidate fails Phase 1 confirmation | M | L | Candidate order + recorded fallback (see Adjudication); both candidates already have favorable measurements |
| BM_CM_4 at 60 s still misses a bad draw (not re-probed by default) | M | M | Phase 1 includes an optional cheap re-probe; prior uncensored record is 15-24 s (2.5x margin at 60); if gate still red here, probe before touching the number again |
| Full gate red from an UNRELATED step/test | M | M | Phase 7 requires triage against the new margins using the probe harness before changing anything; no reactive budget edits |
| Ambient machine load inflates the gate's wall clock | L | M | Failures were measured load-independent; avoid launching concurrent suite runs (recorded operational hazard); rely on rlimit-backed margins |
| Step 3 re-pin drifts from actual collection counts | M | L | Re-pin all four numbers together per the documented procedure (`verify-refactor.sh:57-64`), verified by a `--collect-only` run in Phase 5 |
| Widened gating re-check masks per-formula cost regressions at the 10 s threshold | L | H (accepted) | Recorded trade-off: regression detection at 10 s moves to the scheduled exhaustive scan, which keeps `SELF_SCAN_SOLVE_TIMEOUT_MS=10000` and its freshness check |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |

Phases are sequential: the decision record precedes code changes; Phases 3-5 all touch
`oracle/bimodal_logic/tests/test_oracle_interface.py` and Phases 5-6 both touch
`code/scripts/verify-refactor.sh`, so they must not run in parallel. Cheap, deterministic,
individually-verified changes (Phases 3-6) land before the expensive full-gate run (Phase 7).

### Phase 1: Confirmation probes for witness candidate and BM_CM_4 [COMPLETED]

**Goal**: Measure the substitute-witness candidate across the pinned-seed harness (and
optionally re-probe BM_CM_4) so Phases 2-4 rest on fresh, uncensored measurement — never on
assumption.

**Tasks**:
- [x] Reuse the scratch probe harness (copy of
      `specs/144_fix_oracle_per_formula_solve_timeouts/.../bench_solve_cost.py` methodology:
      same pipeline, pinned seeds 1-7, rlimit primary / wall secondary), run inside
      `nix develop --command python ...`.
      (`specs/145_decide_oracle_per_formula_solve_capacity/bench_witness_probe.py`)
- [x] Probe primary candidate `_and(_neg(A), _next(B))` in the ternary-test context (M=3,
      temporal-depth-1) across all 7 pinned seeds at a 180 s probe budget.
      **RESULT: FAILS criteria** — all 7 seeds decide (no timeout), but max wall 107.40 s
      (seed 5; seed 7 at 80.65 s) > 60 s criterion, and max rlimit 238.3M = 4.4x median
      (54.6M) > 3x criterion. The prior "median 18.6-20.1 s, max 25.2 s across 14 draws"
      basis (seeds 0-4 + repeats) under-sampled the tail; seeds 5 and 7 expose it.
- [x] If primary fails criteria, probe secondary candidate `_some_future(A)` identically.
      **RESULT: FAILS criteria** — seed 7 UNDECIDED at the 180 s probe budget (censored,
      rlimit 337.5M); seed 2 at 85.75 s. Fails "decides on all 7 seeds". The "~3 s, 60x
      headroom" basis was a single-draw figure, not a distribution.
- [x] Optional (cheap, recommended): re-probe the BM_CM_4 solve (N=2, M=2, contingent) across
      the pinned seeds at a 120 s probe budget to confirm 60 s covers the worst draw at ~2x;
      if skipped, record reliance on the prior uncensored 15-24 s record.
      **RESULT: 60 s NOT confirmed** — all 7 seeds decide, median 6.88 s, but max wall
      57.12 s (seed 1, rlimit 32.2M). 60 s would cover the measured worst at only 1.05x,
      not ~2x; the prior 15-24 s record under-sampled the tail. Phase 3 revised:
      `max_time` 30 -> 120 (= 2.1x measured worst, sibling convention), NOT 30 -> 60.
- [x] Write probe results to
      `specs/145_decide_oracle_per_formula_solve_capacity/baselines/03_witness-candidate-probe.json`
      and a `.md` summary table (same format as `01_uncensored-tail-probe.md`).

**PHASE 1 GATE OUTCOME — RECORDED FALLBACK BRANCH TAKEN**: Both substitute-witness candidates
failed confirmation, so per the Adjudication section's recorded fallback, Phase 4 becomes:
keep `_next(A)`, relocate `TestTernarySerializationAll::test_all_sat_task_relation_ternary`
to `xdist_serial`, and raise the `next_A` leg's budget to 480000 ms with an explicitly
recorded, accepted residual ~1-in-7 divergent-draw failure rate. Phase 5's Step 3 re-pin
becomes 627/609/16/2 (two tests relocate: `all_future_neg` + the ternary test), and its
"ternary NOT relocated" check is inverted by this branch. Phase 3's BM_CM_4 value becomes
120 (fresh probe superseded the 15-24 s record). Substitution remains recorded as the
preferred remedy in principle; it is unavailable because no measured-reliable witness exists.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `specs/145_decide_oracle_per_formula_solve_capacity/baselines/03_witness-candidate-probe.json` - new probe data
- `specs/145_decide_oracle_per_formula_solve_capacity/baselines/03_witness-candidate-probe.md` - summary table

**Verification** (success criterion — explicit green milestone):
- Chosen candidate DECIDES on all 7 seeds with max wall <= 60 s (>= 3x headroom vs the
  180000 ms leg budget) and no rlimit outlier > 3x the candidate's own median.
- Probe artifacts exist and are non-empty.
- If BOTH candidates fail: STOP; invoke the recorded fallback path (Adjudication section) and
  revise Phases 2 and 4 accordingly before proceeding.

---

### Phase 2: Decision record artifact [COMPLETED]

**Goal**: Write the standalone capacity-decision record — half the point of this task — before
any code changes land, so the code changes implement a recorded decision rather than the record
post-hoc rationalizing the changes.

**Tasks**:
- [x] Write `specs/145_decide_oracle_per_formula_solve_capacity/reports/02_capacity-decision-record.md`
      containing (DEVIATIONS per Phase 1 gate: BM_CM_4 recorded as 30 -> 120, not 30 -> 60;
      ternary mechanism recorded as the fallback — relocation + 480000 ms leg override +
      accepted ~1-in-7 residual — not substitution; Step 3 re-pin recorded as 627/609/16/2;
      pass-2 arithmetic recomputed to ~1450-1690 s simultaneous-worst, still < 1800 s):
  - Per-mechanism decision table: `and_box_next` 60000 -> 240000 ms (bounded tail, probe
    92.8-104.2 s uncensored, 2.3x-worst convention, never-calibrated provenance `ea516a4b`);
    BM_CM_4 `max_time` 30 -> 60 s (bounded, 15-24 s prior record + Phase 1 probe if taken);
    ternary `next_A` -> substituted witness (divergent tail, undecided at 601 s, rlimit 7.5x);
    `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` new constant decoupled from
    `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` (monotone membership, no re-derivation);
    `test_mixed_and_all_future_neg` -> `xdist_serial` relocation (pure `-n 6` contention,
    0/14 isolated draws over budget).
  - The witness adjudication (this plan's Adjudication section, updated with Phase 1 numbers)
    including the recorded fallback.
  - The explicit option (c) rejection: 3-of-3 red full gates, ~43% per-run failure probability
    for `and_box_next` alone, blocked pass-level dependency, monitoring generates no new
    information beyond the 21-run + probe data.
  - The gating re-check trade-off (10 s regression detection moves to the exhaustive scan).
  - The pass-2 worst-case arithmetic table (from this plan, with any Phase 1 updates).
  - Explicit non-changes: `TEMPORAL_SOLVE_TIMEOUT_MS`, `ORACLE_PASS2_TIMEOUT`, floors,
    `or_diamond_prev`, BM_CM_1 and F5/F4 watch items.

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `specs/145_decide_oracle_per_formula_solve_capacity/reports/02_capacity-decision-record.md` - new decision record

**Verification** (success criterion):
- Decision record exists, covers all five mechanisms + option (c) rejection + adjudication +
  arithmetic, and every recommended constant in it matches a Phase 1/prior measurement citation.

---

### Phase 3: Bounded-budget recalibration with inline measurement bases [COMPLETED]

**Goal**: Land option (b) — the two bounded-tail budget recalibrations — each carrying its
measurement basis inline at the constant.

**Tasks**:
- [x] `oracle/bimodal_logic/tests/test_oracle_interface.py:963`: `timeout_ms=60000` ->
      `timeout_ms=240000` with inline comment recording: uncensored probe 92.8-104.2 s across
      the three previously-censored seeds (rlimit 222M/236M/338M vs ~130M good draw); ~2.3x
      measured worst per the sibling convention (`or_diamond_prev` 150000 ~= 2.07x of 72.6 s);
      cost grew permanently with the 2026-08-07 bound-variable-aliasing soundness fix
      (`3c0cf210`); original 60000 (`ea516a4b`, 2026-06-01) predated that fix and was never
      calibrated.
- [x] Same file, `test_mixed_and_box_next` docstring: replace the stale "~44-45s, ~25%
      headroom" characterization with the 21-run figures (median 46.5-49.9 s, ~43% of isolated
      seeded draws exceeded 60 s; uncensored bad-draw cost 92.8-104.2 s).
- [x] `code/src/model_checker/theory_lib/bimodal/examples.py` (`BM_CM_4_settings`):
      DEVIATION per Phase 1 gate — `max_time: 30` -> `max_time: 120` (NOT 60): the fresh
      7-seed probe measured a 57.12 s worst draw, so 60 would sit at 1.05x the measured
      worst; 120 = 2.1x per convention. Inline basis records the probe figures.
- [x] `oracle/bimodal_logic/tests/test_boundary_regression.py` (inline copy): `30` -> `120`
      with matching comment — both definition sites in sync (also refreshed the stale
      "~15-24s" characterizations in the two BM_CM_4 docstrings there).
- [x] Add the pass-2 headroom arithmetic note at `ORACLE_PASS2_TIMEOUT`'s comment
      (value UNCHANGED at 1800) — `oracle/run-oracle-suite.sh`.
- [x] No task numbers added in any of these files (constraint 8; pre-existing citations in
      untouched text left as-is).

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - and_box_next budget + docstring
- `code/src/model_checker/theory_lib/bimodal/examples.py` - BM_CM_4 max_time
- `oracle/bimodal_logic/tests/test_boundary_regression.py` - inline BM_CM_4 max_time
- `oracle/run-oracle-suite.sh` or wherever `ORACLE_PASS2_TIMEOUT`'s comment lives - headroom note only

**Verification** (success criterion — targeted, inside `nix develop`):
- `nix develop --command pytest oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_box_next -v`
  passes (allow up to ~4 min).
- `nix develop --command pytest oracle/bimodal_logic/tests/test_boundary_regression.py -k bm_cm4 -v`
  passes all BM_CM_4 tests.
- `grep` confirms both `max_time` sites read 60 and both carry a measurement-basis comment;
  the 240000 site carries its basis; no `task 1` / `task-` citations added outside `specs/**`.

---

### Phase 4: Ternary witness substitution [COMPLETED]

**Goal**: Replace the divergent `_next(A)` leg with the Phase-1-confirmed witness, with the
adjudication recorded inline in the test source.

**Tasks** (EXECUTED AS THE RECORDED FALLBACK — no substitution; both candidates failed the
Phase 1 confirmation probe, see Phase 1 gate outcome):
- [x] Keep `_next(A)`; add `@pytest.mark.xdist_serial` to the ternary test and a per-leg
      480000 ms override for the `next_A` entry (`sat_formulas` entries now carry an optional
      timeout override; `TEMPORAL_SOLVE_TIMEOUT_MS` itself untouched at 180000).
- [x] Record inline (docstring + list-entry comment): divergence measurement (undecided at
      601.0 s, rlimit 1.026B = 7.5x good draw), the adjudication outcome, BOTH failed
      candidate probes (primary max 107.4 s / 4.4x-median outlier; secondary undecided at
      180 s on one seed), and the explicitly accepted ~1-in-7 residual.
- [x] Confirm all five legs remain hard-asserting; no xfail/skip added (the xdist_serial
      marker is a scheduling routing, not a disable).

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - sat_formulas entry + inline record

**Verification** (success criterion — inside `nix develop`):
- `nix develop --command pytest "oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary" -v`
  passes in wall time consistent with the Phase 1 measurement (minutes, not >180 s).
- Inline adjudication comment present at the list entry; the test carries no new skip/xfail.

---

### Phase 5: Relocate the contention victim + Step 3 re-pin [COMPLETED]

**Goal**: Land the narrow option (a): move `test_mixed_and_all_future_neg` to the serial pass
(budget untouched at 60000 — 2.4x isolated headroom is within convention) and re-pin the
verify-refactor Step 3 collection counts by their documented procedure.

**Tasks**:
- [x] Add `@pytest.mark.xdist_serial` to
      `TestMixedFormulas::test_mixed_and_all_future_neg` with a basis comment (0/14 isolated
      draws over budget; sole failure occurred under `-n 6` parallel contention -> scheduling
      fix, not budget) plus the Phase-1 heavier-tail watch item recorded inline.
- [x] Re-pin verify-refactor Step 3 counts all-four-together per the documented procedure:
      DEVIATION per Phase 1 fallback branch — total 627 (unchanged), parallel 611 -> 609,
      serial 14 -> 16, slow 2 (unchanged), with a provenance comment naming BOTH relocations
      (all_future_neg + the ternary test).
- [x] Ternary test IS relocated on this branch (fallback; the substitute's assumed 7x+
      headroom did not survive the Phase 1 probe) — plan text inverted by the Phase 1 gate.
      Verified by `--collect-only`: 627 / 609 / 16 / 2 exactly.

**Timing**: 30 minutes

**Depends on**: 4

**Files to modify**:
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - xdist_serial mark
- `code/scripts/verify-refactor.sh` - Step 3 re-pin (627/610/15/2) + provenance comment

**Verification** (success criterion — inside `nix develop`):
- `nix develop --command pytest oracle --collect-only -q -m "not xdist_serial and not slow" | tail -1`
  reports 610 selected; the `xdist_serial and not slow` collection reports 15; totals match
  627/610/15/2 exactly as pinned.
- `nix develop --command pytest "oracle/bimodal_logic/tests/test_oracle_interface.py::TestMixedFormulas::test_mixed_and_all_future_neg" -v`
  passes serially (~20-25 s).

---

### Phase 6: Gating re-check budget decoupling + Step 5c pin + TESTING_GUIDE note [COMPLETED]

**Goal**: Introduce `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000`, decoupled from the manifest
derivation budget, with the trade-off recorded and the new constant pinned so it cannot drift.

**Tasks**:
- [x] `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (line 114): added
      `GATING_RECHECK_SOLVE_TIMEOUT_MS = 20000` with the full basis/decoupling/trade-off
      comment block.
- [x] Swapped ONLY the two `TestGatingConclusiveScan` call sites (now lines 2342/2350) to the
      new constant. `SELF_SCAN_SOLVE_TIMEOUT_MS` remains 10000 everywhere else (verified by
      grep: definition + comments + exhaustive/scan_runner/manifest sites only).
- [x] `code/scripts/verify-refactor.sh` Step 5c: added pin
      `GATING_RECHECK_SOLVE_TIMEOUT_MS=20000` alongside the unchanged
      `SELF_SCAN_SOLVE_TIMEOUT_MS=10000` pin ("four" -> "five" wording updated).
- [x] `code/docs/core/TESTING_GUIDE.md` section 8.8: two-budget contract note added
      (derivation vs gating re-check, monotone-membership rationale, where regression
      detection now lives). No task-number citations.

**Timing**: 45 minutes

**Depends on**: 5

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - new constant + two call sites
- `code/scripts/verify-refactor.sh` - Step 5c new pin
- `code/docs/core/TESTING_GUIDE.md` - 8.8 two-budget contract note

**Verification** (success criterion — inside `nix develop`):
- `nix develop --command pytest "oracle/bimodal_logic/tests/test_cross_oracle_differential.py" -k "TestGatingConclusiveScan" -v`
  passes: >= 100 of 103 conclusive (floor intact at 100) and `disagreements == 0`.
- `grep` confirms: floors unchanged (100/90); `SELF_SCAN_SOLVE_TIMEOUT_MS = 10000` unchanged;
  exactly the two gating call sites use the new constant; Step 5c pins both constants.

---

### Phase 7: Full-gate confirmation run [COMPLETED]

**Goal**: The task's terminal deliverable — a full `verify-refactor.sh` run (no
`--skip-oracle`) inside `nix develop` ending in "[verify-refactor] All checks passed" with
`disagreements == 0`, confirming the composite decision green end-to-end.

**Tasks** (three runs were required; runs 1-2 red on NON-remedied mechanisms, triaged per
the recorded procedure before any further change):
- [x] Run `nix develop --command bash code/scripts/verify-refactor.sh` (full, no skip flags),
      transcripts captured: `baselines/04_full-gate-transcript.txt` (run 1, red),
      `05_full-gate-transcript-run2.txt` (run 2, red), `07_full-gate-transcript-run3.txt`
      (run 3, GREEN, with load-average evidence).
- [x] Run 3 transcript contains "[verify-refactor] All checks passed"; `disagreements == 0`
      throughout (gating-scan tooth asserted and passed).
- [x] No concurrent runs launched by this task; runs 1-2 were contended by ANOTHER session's
      lean/lake build (650% CPU) — evidence and one-leg-specific attribution in decision
      record section 7.3; run 3 executed in a confirmed-quiet window.
- [x] Red-run triage performed per procedure (no reactive budget edits; probe-first):
      run-1/run-2 failures were all OUTSIDE the remedied set — (a) interleaving
      some_future draw at 5000 ms (pre-existing heavy tail, recorded, NOT remedied);
      (b) gating floor 98/103 under external contention (one-leg attribution);
      (c) BM_CM_1 Step 7 failure — diagnosed as PRE-EXISTING boundary-straddling
      (~13-15 s vs stale 15 s budget, reproduced at the pre-task commit), probed 7-seed
      uncensored (divergent seed-2 tail), and recalibrated 15 -> 60 with inline basis —
      a recorded, measured deviation from the original "BM_CM_1 watch item only"
      non-goal, forced by the gate and verified 3/3 isolated + in run 3.
- [x] Second and third full-gate runs performed (variance sampled: red/red/green with
      causes recorded per run).
- [x] Gate outcome appended to the decision record (sections 7.1-7.8; pass-2 wall 1315.36 s
      recorded against the recomputed arithmetic).
- [x] Summary notes that the green Step 6 unblocks the pass-level task currently blocked
      on it.

**Timing**: 1.5 hours (gate runtime ~30-45 min per run + triage margin + record update)

**Depends on**: 6

**Files to modify**:
- `specs/145_decide_oracle_per_formula_solve_capacity/baselines/04_full-gate-transcript.txt` - gate transcript
- `specs/145_decide_oracle_per_formula_solve_capacity/reports/02_capacity-decision-record.md` - outcome appendix

**Verification** (success criterion — the task's definition of done):
- Transcript contains the literal line "[verify-refactor] All checks passed".
- `disagreements == 0` throughout.
- Pass 2 wall clock recorded and confirmed under 1800 s (expected ~850-1100 s typical).

## Testing & Validation

- [x] Phase 1 probe executed: NO witness candidate met the criteria (both failed) — the
      recorded fallback branch was taken instead of substitution.
- [x] Per-phase targeted pytest runs (Phases 3-6), all inside `nix develop`, all passing.
- [x] Collection pins verified by `--collect-only`: 627 total / 609 parallel / 16 serial /
      2 slow (fallback-branch values; the planned 610/15 assumed substitution).
- [x] Floors verified unchanged: `MIN_CONCLUSIVE_GATING_FORMULAS = 100`,
      `MIN_CONCLUSIVE_SCAN_FORMULAS = 90`.
- [x] No xfail/skip/disable added anywhere; all previously failing tests remain hard-asserting.
- [x] Grep audit: every changed constant carries an inline measurement-basis comment; no
      task-number citations added outside `specs/**`.
- [x] Full gate (run 3): "[verify-refactor] All checks passed", `disagreements == 0`,
      pass 2 = 1315.36 s < 1800 s.

## Artifacts & Outputs

- `plans/01_per-formula-solve-capacity.md` (this file)
- `baselines/03_witness-candidate-probe.json` + `.md` (Phase 1)
- `reports/02_capacity-decision-record.md` (Phase 2, appended Phase 7) — the recorded decision
- Modified sources: `oracle/bimodal_logic/tests/test_oracle_interface.py`,
  `oracle/bimodal_logic/tests/test_boundary_regression.py`,
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`,
  `code/src/model_checker/theory_lib/bimodal/examples.py`,
  `code/scripts/verify-refactor.sh`, `code/docs/core/TESTING_GUIDE.md`,
  plus the `ORACLE_PASS2_TIMEOUT` headroom comment site
- `baselines/04_full-gate-transcript.txt` (Phase 7)
- `summaries/01_per-formula-solve-capacity-summary.md` (written at implementation completion)

## Rollback/Contingency

All code changes are small, independent text edits committed per-phase — each is revertible in
isolation via `git revert` of its phase commit without disturbing the others. Per change:

- **`and_box_next` 240000**: revert to 60000 restores the exact prior (red-gate) state. If the
  gate is red HERE despite the probe, do not pick an intermediate number — re-probe uncensored
  and re-adjudicate (a measurement contradiction, not a tuning knob).
- **BM_CM_4 `max_time` 60**: revert both sites together (they must stay in sync). Raising
  `max_time` is monotone-safe for the countermodel assertions (more solver time can only help
  find the asserted countermodel); no semantic risk.
- **Witness substitution**: revert restores `_next(A)` and its ~1-in-7 divergent failure; the
  in-plan fallback (relocation + 480000 ms, accepted residual) is the recorded intermediate
  option. Never resolve a red leg here by xfail/skip.
- **Relocation + Step 3 re-pin**: revert the mark and the four pinned counts together
  (627/611/14/2) — the pins and the mark are one atomic unit; reverting one without the other
  turns Step 3 red by construction.
- **Gating re-check decoupling**: revert the constant, the two call sites, and the Step 5c pin
  together. `SELF_SCAN_SOLVE_TIMEOUT_MS` was never changed, so no manifest re-derivation is
  needed in either direction.
- **Contingency on persistent red gate**: keep all recorded artifacts (decision record, probes,
  transcript), mark the implementation [PARTIAL] at the failing phase, and surface the failing
  mechanism + fresh measurement for re-adjudication. Do not un-land the green phases.
