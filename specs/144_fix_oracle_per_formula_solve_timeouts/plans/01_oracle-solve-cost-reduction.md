# Implementation Plan: Reduce Oracle Per-Formula Z3 Solve Cost

- **Task**: 144 - fix_oracle_per_formula_solve_timeouts
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours (excluding unattended measurement wall-clock; see "Measurement Wall-Clock Budget")
- **Dependencies**: None
- **Research Inputs**: `specs/144_fix_oracle_per_formula_solve_timeouts/reports/01_oracle-solve-cost-reduction.md`
- **Artifacts**: plans/01_oracle-solve-cost-reduction.md (this file)
- **Standards**: `.claude/context/formats/plan-format.md`; `.claude/rules/plan-format-enforcement.md`; `.claude/rules/artifact-formats.md`; `.claude/rules/state-management.md`; `.claude/rules/git-workflow.md`
- **Type**: python

## Overview

The gating oracle suite cannot reach a green Step 6 in `code/scripts/verify-refactor.sh` because a
varying set of per-formula Z3 solves fails to decide within its budget. The research report
establishes that this is not a new regression: the necessary term-aliasing soundness fix (commit
`3c0cf210`) permanently raised solve cost for the `\Box`/`\Future`/`\Past`/`\Until`/`\Since`
operator family by removing accidental Z3 term sharing, leaving several formulas at 20-95s against
60000/180000 ms budgets — thin enough that Z3's documented ~20x run-to-run variance can tip any one
of them over. `disagreements=0` everywhere: this is purely a cost outcome, not a semantic one.

This plan reduces genuine encoding-level solve cost by extending the codebase's own existing
E-matching trigger-pattern precedent (`build_forward_comp_constraint`) to the still-unpatterned
quantifiers, and by partially grounding the small, depth-bounded *shift* dimension of
`depth_bounded_skolem_abundance_constraint`. Because the underlying signal is noisy, every phase is
gated on a **repeated, paired, seed-controlled measurement** rather than a single timing sample,
and any change that does not measurably reduce cost is reverted rather than kept. Definition of
done: the Step 6 gating oracle path runs green end to end inside `nix develop`, with measured
per-formula headroom reported against budgets and floors that were never touched.

### Research Integration

Integrated from `reports/01_oracle-solve-cost-reduction.md`:

- **Root cause is settled**: cost did not silently regress; the entire quantified-operator family
  picked up a permanent, already-accepted cost from the task 139 soundness fix. No further
  root-cause investigation is in scope, and the aliasing fix must not be weakened or reverted.
- **Highest-leverage lever (report 5.1)**: `build_forward_comp_constraint` is the *only* quantifier
  in the entire frame-constraint/operator encoding supplying an explicit `patterns=` argument.
  `NecessityOperator`, `ForAllTime`/`ExistsTime`, both Skolem abundance constraints, and
  `matching_states_when_shifted_var` have none. Phases 2 and 4 extend that precedent.
- **Second lever (report 5.2)**: `depth_bounded_skolem_abundance_constraint` jointly quantifies
  `[source_world, shift_amount]` where `shift_amount` ranges over exactly `{-1, 1}` for all three
  failing tests (`max_shift == temporal_depth == 1`). Grounding only that dimension is Phase 3.
- **Measurement hygiene (report 5.3)**: no `smt.random_seed` is pinned anywhere. Phase 1 pins seeds
  **inside the measurement harness only** so before/after comparisons are paired and reproducible.
- **Confirmed pattern-eligibility caveat**: `is_valid_time` is `z3.And(t > -M, t < M)` — arithmetic,
  **not** a function application, therefore **not** a legal trigger as written. `is_world` *is* a
  genuine `z3.Function` (core.py:201) and *is* eligible. This is why the `ForAllTime`/`ExistsTime`
  work is isolated into its own later, gated phase rather than bundled with the easy sites.
- **Plan-time correction to report 5.1**: a Z3 pattern set must cover **every** bound variable of
  its quantifier. `is_world(source_world)` alone therefore cannot serve as the trigger for the
  abundance axioms, which bind `[source_world, shift_amount]`. The covering candidate is the Skolem
  application `shift_of_bounded(source_world, shift_amount)` (or a `MultiPattern` including it).
  Phase 2 must verify this before writing code.
- **Established dead ends carried forward verbatim** — see "Established Dead Ends" below.

### Prior Plan Reference

No prior plan for this task.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context; no ROADMAP.md consultation performed.

## Hard Constraints (Non-Negotiable)

These are carried verbatim from the task definition. Any phase that violates one is a failed phase,
not a trade-off.

- **MUST NOT widen any budget**: do not raise `SELF_SCAN_SOLVE_TIMEOUT_MS` or the 60000/180000 ms
  per-solve budgets.
- **MUST NOT lower any floor**: do not lower `MIN_CONCLUSIVE_GATING_FORMULAS` or
  `MIN_CONCLUSIVE_SCAN_FORMULAS`.
- **MUST NOT xfail, skip, or otherwise disable the failing tests.**
- The pass-level `ORACLE_PASS2_TIMEOUT` is **NOT** implicated (measured 958.58s / 847.38s against
  1800s) — leave it alone.
- All work must be adjudicated inside `nix develop` only.
- Every change must be semantics-preserving: the oracle is a differential correctness reference, so
  `disagreements` must remain 0 after every phase.

Concretely, the following files/constants are **read-only** for this task:
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py:93` (`SELF_SCAN_SOLVE_TIMEOUT_MS`),
`:123` (`MIN_CONCLUSIVE_SCAN_FORMULAS`), `:162` (`MIN_CONCLUSIVE_GATING_FORMULAS`),
`oracle/run-oracle-suite.sh:123` (`pass2_timeout`), and the `timeout_ms=` arguments in
`oracle/bimodal_logic/tests/test_oracle_interface.py`.

## Established Dead Ends — Do Not Re-Propose

Already benchmarked and rejected in this codebase (research report section 6). Re-proposing any of
these is out of scope:

1. **Full grounding of the abundance constraint** (`build_grounded_abundance_constraints`, task 98):
   regressed both SAT and UNSAT (`BM_CM_1` 9s -> 15s timeout; `BM_TH_1`/`BM_TH_2` 30s -> 75s+).
   Phase 3 deliberately grounds only the *shift* dimension, never the *world*/target dimension.
2. **Array-disequality grounding of `world_uniqueness`** (task 97 phase 2): reverted, 8 test
   failures, conflicts with `valid_array_domain`.
3. **Enabling `task_restriction`** (disabled by design, core.py:700-754): nested
   `ForAll/Exists` alternation MBQI handles poorly; confirmed timeouts at >3 worlds, M>=3.
4. **`z3.FreshInt`** instead of counter-suffixed `z3.Int` (task 139): severe MBQI cliff.
5. **`smt.mbqi.max_cexs=50`** (task 98): no measurable benefit.
6. **`qi.max_instances`**: causes `unknown` on `BM_CM_2`/`BM_CM_4`.

## Goals & Non-Goals

**Goals**:

- Establish a reproducible, noise-aware per-formula cost baseline for
  `test_mixed_and_box_next`, `test_mixed_and_all_future_neg`, and
  `test_all_sat_task_relation_ternary`.
- Reduce genuine Z3 solve cost for those formulas via semantics-preserving encoding changes only
  (explicit E-matching triggers; finite-domain shift grounding).
- Keep `disagreements=0` and every guard test green after each encoding change.
- Reach a green Step 6 gating oracle run and report measured per-formula headroom against the
  unchanged budgets.
- Record any candidate that fails to measurably reduce cost as a new dead end, in the same place
  and style the codebase already records the six above.

**Non-Goals**:

- Any budget widening, floor lowering, xfail, skip, or test disablement (see Hard Constraints).
- Reverting or weakening the task 139 term-aliasing soundness fix.
- Re-attempting any of the six established dead ends.
- Pinning `smt.random_seed`/`sat.random_seed` in **production** (`z3_adapter.py`). Seeds are pinned
  in the measurement harness only. A pinned production seed does not reduce cost — it only fixes
  which draw is taken — and locking in a draw is a separate decision this task does not make.
- Changing `ORACLE_PASS1_TIMEOUT`/`ORACLE_PASS2_TIMEOUT` or the two-pass suite structure.
- Broad refactoring of `core.py`/`operators.py` beyond the specific quantifier sites named here.

## Measurement Methodology (Binding for All Phases)

Every acceptance decision in this plan is made against this methodology. A single timing run is
never evidence, in either direction.

### Environment

- All runs inside `nix develop --command ...`. No exceptions.
- Machine otherwise idle: no other pytest session, no parallel agent build, load average checked
  and recorded before each measurement round.
- Serial only during measurement (no `-n`), matching the research report's section 4 method.

### Primary metric: Z3 `rlimit count`

Wall-clock is the *budgeted* quantity but the *noisiest* one. `solver.statistics()`'s
`rlimit count` (research report section 4 measured `130120807` for `and_box_next`) counts internal
resource units and is essentially deterministic for a fixed (formula, seed, encoding) triple, and is
independent of machine load. Therefore:

- **Primary metric**: `rlimit count`, read from `structure.stored_solver.statistics()` after the
  solve.
- **Secondary metric**: wall-clock seconds for the same solve.
- Both are recorded for every run. A change is only accepted when both move in the same direction
  (see acceptance rule C below) — this guards against an rlimit reduction that does not translate
  into real time.

### Sampling design (paired, seed-controlled)

For each of the three target formulas, one **measurement round** is:

- A fixed seed set `S = {0, 1, 2, 3, 4}`, with `smt.random_seed` and `sat.random_seed` set to the
  same value `s` for each run. Seeds are set **by the harness only**, never in `z3_adapter.py`.
- One run per seed (5 runs), plus 2 additional runs at seed `0` to quantify residual within-seed
  variability (7 runs total per formula per round).
- Results appended to a JSON results file so a round can be resumed after interruption rather than
  restarted.

Before/after comparisons are **paired by seed**: run `i` at seed `s` after a change is compared
against run `i` at seed `s` before it. Unpaired mean comparison is not acceptable evidence.

### Statistics reported

Per formula per round: `median(rlimit)`, `max(rlimit)`, `median(wall)`, `max(wall)`, and the
per-seed paired deltas. `max` matters as much as `median`: the budget must survive the worst draw,
not the typical one.

### Acceptance rule: what counts as evidence of a real cost reduction

A candidate optimization is **accepted** only if ALL of the following hold on the target formulas:

- **A. Median improvement**: `median(rlimit)` reduced by **>= 20%** versus the paired baseline.
- **B. Worst case not worsened**: `max(rlimit)` not increased versus the paired baseline.
- **C. Direction agreement**: `median(wall)` also decreases (any amount). An rlimit drop with flat
  or rising wall-clock is not accepted.
- **D. Consistency, not luck**: the paired per-seed `rlimit` delta is negative on **>= 4 of the 5
  seeds**. Improvement on one or two seeds is sampling luck, not a cost reduction.
- **E. Semantics preserved**: the semantics-preservation gate below passes.

A candidate is **neutral** if `|median(rlimit) delta| < 10%`. A neutral candidate is **reverted**
(see Rollback/Contingency) — a neutral-but-complicating change is a net negative.

A candidate is **regressive** if `median(rlimit)` increases at all, or if B fails. Regressive
candidates are reverted immediately and recorded as dead ends.

### Semantics-preservation gate (run in every phase that touches the encoding)

Run inside `nix develop`, all must be green, and `disagreements` must be `0` everywhere:

- `pytest oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` — the permanent aliasing-
  regression guard installed by task 139.
- `pytest oracle/bimodal_logic/tests/test_soundness_regression.py`.
- `pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — grep the output for any
  non-zero `disagreements` value; a non-zero count means a pattern suppressed a needed
  instantiation and changed a verdict, and is an immediate revert.

A pattern that is too restrictive can suppress a required quantifier instantiation and silently
convert a `sat` into an `unknown`/`unsat`. This gate is the detector for that failure mode, and it
is mandatory, not optional, on every encoding-touching phase.

### Measurement Wall-Clock Budget

Each measurement round is roughly `(45 + 25 + 95) s x 7 runs ~= 20 minutes` of pure solve time per
round, before overhead. Budget ~30-45 minutes of unattended wall clock per round, and expect 4-5
rounds across the plan (baseline plus one per candidate). This is measurement time, not agent
reasoning time, and is excluded from the per-phase effort estimates below.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A trigger pattern is too restrictive and suppresses a needed instantiation, flipping a verdict | H | M | Mandatory semantics-preservation gate every phase; any non-zero `disagreements` is an immediate revert |
| A pattern set fails to cover all bound variables and Z3 silently rejects/ignores it, producing an apparent "neutral" result | M | M | Phase 2 verifies pattern legality explicitly (all bound vars covered) before benchmarking; a rejected pattern must be distinguishable from an ineffective one |
| Z3's ~20x variance makes a lucky run look like a fix | H | H | Paired, seed-controlled, 7-run rounds; `rlimit` as primary metric; >= 4-of-5 seed consistency rule (acceptance rule D) |
| `is_valid_time` proves unusable as a trigger, stalling the `ForAllTime` work | M | H (already confirmed arithmetic-only) | Isolated into Phase 4, gated on Phases 2-3 outcome; explicit time-box and revert path |
| Grounding the shift dimension increases ground-term count and regresses (the task 98 failure mode) | M | M | Phase 3 grounds only the 2-element shift domain, never the world dimension; measured against acceptance rules; reverted on regression |
| Phases 2-4 all land neutral and headroom is unchanged | H | M | Phase 5 still runs the gate and reports measured headroom; outcome is escalated with data rather than papered over by touching a budget |
| Measurement contaminated by machine load | M | M | Load average recorded per round; `rlimit` primary metric is load-independent; contaminated rounds re-run |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential by design:
Phases 2, 3, and 4 all mutate the same encoding (`core.py`, `operators.py`) and each is accepted or
reverted on a **paired** measurement against the immediately preceding accepted state. Running two
encoding changes concurrently would make the measurement unattributable, which is precisely the
failure mode this plan exists to avoid.

---

### Phase 1: Measurement harness and seeded baseline [COMPLETED]

- **Goal:** Build a reproducible, seed-controlled measurement harness and record the paired
  baseline for all three target formulas, so every later phase has something legitimate to compare
  against.
- **Tasks:**
  - [x] Create `specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py`: drives
        `BimodalSemantics`/`ModelConstraints`/`BimodalStructure` directly, exactly as
        `provider.find_countermodel` does (mirroring the research report's section 4 direct pipeline
        reproduction), bypassing pytest so solver parameters are controllable.
  - [x] Support `--formula {and_box_next,and_all_future_neg,all_sat_task_relation_ternary}`,
        `--seeds 0,1,2,3,4`, `--repeats-at-seed0 2`, `--out <json>`, with append/resume semantics so
        an interrupted round is resumed, not restarted.
  - [x] Determine and document the seed injection point (candidates: `z3.set_param('smt.random_seed',
        s)` / `'sat.random_seed'` before construction, or a harness-local override of the adapter's
        parameter set). **Do not modify `code/src/model_checker/solver/z3_adapter.py`.** Verify the
        seed actually takes effect by confirming two different seeds yield different `rlimit count`
        values and the same seed reproduces its own `rlimit count`. DEVIATION: `structure.stored_solver`
        is a `Z3SolverAdapter` wrapper, not a raw `z3.Solver` -- statistics are read via its
        `.raw_solver` property (`structure.stored_solver.raw_solver.statistics()`), not directly.
        Seed injection point confirmed: `z3.set_param('smt.random_seed', s)` /
        `z3.set_param('sat.random_seed', s)` called immediately before `isolated_z3_context()`,
        which is a process-global Z3 parameter table entry (not tied to the C-level Context), so
        ordering relative to context creation does not matter.
  - [x] Record per run: seed, `rlimit count` from `structure.stored_solver.statistics()`, wall-clock
        seconds, `temporal_depth`, `M`, and the solve verdict. Assert `temporal_depth=1, M=3` for the
        three targets (matches the baseline transcripts and `provider.py:213-222`).
  - [x] Emit a summary table: per formula, `median`/`max` of `rlimit` and wall, plus each per-seed
        value.
  - [x] Run the full baseline round inside `nix develop` on an idle machine; record load average.
        Load average before the round was 1.37/1.43/2.22 (idle).
  - [x] Write the baseline to `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/01_solve-cost-baseline.json`
        plus a short human-readable `01_solve-cost-baseline.md` alongside it.
- **Timing:** ~2 hours agent time, plus ~30-45 min unattended measurement.
- **Depends on:** none
- **Files to modify:**
  - `specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py` - new harness
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/01_solve-cost-baseline.json` - new
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/01_solve-cost-baseline.md` - new
  - No production source files are modified in this phase.
- **Verification:**
  - [x] Harness runs to completion inside `nix develop` for all three formulas.
  - [x] Seed control is demonstrated: seed 0 reproduces `rlimit=130120807` on the initial run and
        both repeats for `and_box_next`; seed 1 (`140250670`) differs from seed 0.
  - [x] Baseline JSON contains 7 runs per formula with all required fields (21 total).
  - [x] Baseline `median`/`max` for `and_box_next` (median 130120807 rlimit, median wall 46.54s,
        seed-0 wall 45.50/44.83/46.54s) are in the neighbourhood of the research report's
        44.33s/46.75s and its `rlimit count: 130120807` figure -- harness confirmed to reproduce the
        real solve.
  - [x] No production file appears in `git status`.

---

### Phase 2: Explicit E-matching triggers on the function-application quantifier sites [COMPLETED]

- **Goal:** Extend the codebase's own `build_forward_comp_constraint` trigger precedent to every
  quantifier whose bound variables are already covered by a genuine function application, and
  measure the effect.
- **Outcome: candidate tested and REJECTED (neutral/regressive); all changes reverted to comment-only
  dead-end records.** See "New Dead Ends" in the phase-2 handoff and the implementation summary.
- **Tasks:**
  - [x] Confirm Z3 pattern legality rules before writing code: a pattern set must cover **all**
        bound variables of its quantifier; patterns must be (multi-)applications, not arithmetic
        comparisons. Confirm whether `patterns=` on `z3.Exists` is meaningful in this encoding
        (top-level existentials are skolemized, so a pattern there may be inert) and record the
        finding — if inert, do not spend effort on the `false_at`/`Exists` sites. DEVIATION: none of
        the three Phase 1 target formulas exercise `NecessityOperator.false_at` (none negate `\Box`),
        so inertness could not be measured against this benchmark; left unpatterned and unmeasured
        rather than guessing, per "do not spend effort" guidance.
  - [x] `NecessityOperator.true_at` (`operators.py` ~507): added
        `patterns=[semantics.is_world(other_world)]` to the `z3.ForAll`. Z3 accepted the pattern
        (legal: single bound var covered). Measured neutral (see below); reverted -- dead end 9.
  - [x] `depth_bounded_skolem_abundance_constraint` (`core.py:1456-1499`): added
        `patterns=[shift_of_bounded(source_world, shift_amount)]`, the covering Skolem application.
        Z3 accepted the pattern. Measured: helped `and_box_next` at some seeds but **regressed**
        `\Future p` (F(p)) from ~3s to a 5000ms timeout in
        `test_soundness_regression.py::TestBoundaryVacuity::test_depth1_boundary_safe_is_true` --
        this constraint is shared by every depth-1, M=3 formula via `build_frame_constraints`, not
        only the three named targets. Reverted -- dead end 8.
  - [x] `capped_skolem_abundance_constraint`: applied the same treatment with `shift_of_capped`. Z3
        accepted the pattern. Not measurable against the 3 target formulas (none reach M<=2 or
        unset-temporal_depth, the only paths that dispatch to this constraint instead of
        `depth_bounded_...`). Reverted alongside its sibling for encoding symmetry.
  - [x] `matching_states_when_shifted_var` (`core.py:1232-1265`): added
        `patterns=[z3.Select(source_array, time)]`. Z3 accepted the pattern (legal: single bound var
        `time` covered by a genuine array-select application). Measured: this was the specific
        culprit reproduced in isolation for the F(p) regression above (bisected independently of the
        `depth_bounded` pattern -- either one alone reproduces the regression). Reverted -- dead
        end 7.
  - [x] Run the semantics-preservation gate. `test_encoding_nondegeneracy.py`: green (4 passed).
        `test_soundness_regression.py`: FAILED with 8-9 tests red while any subset of the abundance-
        constraint patterns (depth_bounded and/or matching_states_when_shifted_var) was applied;
        this is what triggered the bisection and revert. All 30 tests pass once those two patterns
        are reverted (confirmed by a full run with only `NecessityOperator`+`capped` applied).
        `test_cross_oracle_differential.py` (`disagreements=0` check): not re-run against the final
        comment-only (functionally-identical-to-baseline) diff -- deferred to Phase 3's gate run,
        since the current diff has zero behavioral effect on any code path (net revert) and would be
        redundant with the already-passing pre-task-144 baseline.
  - [x] Run a full measurement round with the Phase 1 harness; wrote
        `baselines/02_phase2-patterns.json` (re-measured `and_box_next` only, under the
        `NecessityOperator`+`capped`-only interim state, since `and_all_future_neg` and
        `all_sat_task_relation_ternary` exercise neither of those two sites and are therefore
        byte-identical to their Phase 1 baseline under that interim state -- reused rather than
        re-run). `and_box_next`: median rlimit 130120813 vs. baseline 130120807 (~0.00% change,
        neutral), max rlimit 192875085 (improved vs. baseline max 213334140), median wall 42.13s vs.
        baseline 46.54s (~9.5% faster), but per-seed rlimit delta was negative on only 2 of 5 seeds
        (1, 3) -- failing the >=4-of-5 consistency rule (D).
  - [x] Apply the acceptance rules. **Rejected** (neutral: |median rlimit delta| = 0.00% < 10%, and
        rule D fails at 2/5 not >=4/5). Reverted per Rollback/Contingency; recorded as dead ends 7,
        8, 9 (inline comments at each site) plus the "New Dead Ends" summary section.
- **Timing:** ~2 hours agent time, plus ~30-45 min unattended measurement.
- **Depends on:** 1
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/operators.py` - `patterns=` on `NecessityOperator.true_at`
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - `patterns=` on
    `depth_bounded_skolem_abundance_constraint`, `capped_skolem_abundance_constraint`,
    `matching_states_when_shifted_var`
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/02_phase2-patterns.json` - new
- **Verification:**
  - Every added pattern is confirmed accepted by Z3 (all bound variables covered; no silent
    discard) — an inert pattern must be distinguishable from an ineffective one.
  - Semantics-preservation gate green, `disagreements=0`.
  - Paired measurement round recorded; accept/neutral/regressive verdict stated explicitly against
    acceptance rules A-E.
  - Working tree contains only accepted changes (neutral/regressive edits reverted).

---

### Phase 3: Ground the depth-bounded abundance axiom's shift dimension [NOT STARTED]

- **Goal:** Remove the `shift_amount` quantifier dimension from
  `depth_bounded_skolem_abundance_constraint` by unrolling its provably tiny, construction-time-known
  finite domain, leaving the world dimension fully quantified.
- **Tasks:**
  - [ ] Confirm at construction time that `max_shift` is a concrete Python `int` and that the
        eligible shift set is `{-max_shift..max_shift} \ {0}` — for all three target formulas
        `max_shift == 1`, so the set is exactly `{-1, 1}`.
  - [ ] Replace the single `ForAll([source_world, shift_amount], ...)` with a conjunction of
        `2*max_shift` constraints, one per concrete shift value `k`, each of the form
        `ForAll([source_world], Implies(guard_k, body_k))` with `k` substituted as a `z3.IntVal`
        everywhere `shift_amount` appeared — including in the `shift_of_bounded(source_world, k)`
        applications and in the `matching_states_when_shifted_var(source_world, k, ...)` call.
  - [ ] Attach the now-single-variable trigger `patterns=[shift_of_bounded(source_world, k)]` (or
        `is_world(source_world)`, whichever benchmarks better — both legally cover the sole
        remaining bound variable).
  - [ ] **Do not** touch the world/target dimension. Grounding it is established dead end 1.
  - [ ] Assert logical equivalence explicitly in a code comment: the unrolled conjunction is
        equivalent to the joint quantifier precisely because `shift_amount`'s range is a
        construction-time-known finite set, bounded by temporal depth by design.
  - [ ] Sanity-check behaviour at larger `max_shift` (the constraint is used beyond depth 1):
        confirm the unroll count stays bounded by temporal depth and does not reintroduce the task
        98 ground-term blowup. If unroll count grows unacceptably, gate the unroll behind a small
        `max_shift` threshold and keep the quantified form above it.
  - [ ] Run the semantics-preservation gate (`disagreements=0`).
  - [ ] Run a full measurement round; write `baselines/03_phase3-shift-grounding.json`; compare
        paired-by-seed against the Phase 2 accepted state.
  - [ ] Apply the acceptance rules. Accept, or revert and record as a dead end.
- **Timing:** ~2 hours agent time, plus ~30-45 min unattended measurement.
- **Depends on:** 2
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` -
    `depth_bounded_skolem_abundance_constraint` unrolled over the shift dimension
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/03_phase3-shift-grounding.json` - new
- **Verification:**
  - Frame constraint list still assembles for M=2 and M>=3 paths (`*skolem_abundance` splat at
    `core.py:808` still receives a well-formed list).
  - Semantics-preservation gate green, `disagreements=0`.
  - Paired measurement round recorded; explicit accept/neutral/regressive verdict.
  - No world-dimension grounding introduced (explicit check against dead end 1).

---

### Phase 4: Trigger patterns for `ForAllTime`/`ExistsTime` (gated) [NOT STARTED]

- **Goal:** Address the one remaining unpatterned quantifier family — the helper every
  `\Future`/`\Past`/`\Until`/`\Since` truth method routes through — whose guard is arithmetic and
  therefore not directly pattern-eligible.
- **Gate:** Execute this phase only if, after Phases 2-3, the measured `max(wall)` headroom for any
  target formula is still below **2x** its budget. If all three formulas already clear 2x headroom,
  skip this phase, mark it `[NOT STARTED]` with a one-line note recording the measured headroom that
  justified skipping, and proceed to Phase 5. Do not spend effort on a lever that is no longer needed.
- **Tasks:**
  - [ ] Confirm the blocking fact from the research: `is_valid_time` is
        `z3.And(given_time > -M + offset, given_time < M + offset)` (`core.py` ~841) — arithmetic,
        **not** a function application, therefore illegal as a trigger as written.
  - [ ] Identify a legal covering trigger from the quantifier body instead. The natural candidates
        are the `world_function`/`z3.Select` applications at `time_var` that the recursive truth
        predicate already generates. Determine whether a body-derived pattern is available at the
        point `ForAllTime` is constructed, given that `body` arrives as an opaque Z3 expression.
  - [ ] If no legal body-derived trigger is reachable without restructuring `ForAllTime`'s API,
        stop and record this as a dead end with the specific reason. Do **not** introduce an
        auxiliary axiomatized `valid_time` predicate solely to create a trigger: that adds a new
        quantified iff-axiom to the encoding, which is a cost increase of unknown sign and outside
        this task's measured-improvement-only discipline.
  - [ ] If a legal trigger is reachable, apply it to `ForAllTime` (the universal case). Evaluate
        whether `ExistsTime` benefits at all given the Phase 2 finding on patterns under `Exists`.
  - [ ] Run the semantics-preservation gate (`disagreements=0`). This phase carries the highest
        instantiation-suppression risk of the plan: a too-narrow time trigger can starve a temporal
        operator of the instantiation it needs and flip a verdict.
  - [ ] Run a full measurement round; write `baselines/04_phase4-time-patterns.json`; compare paired
        against the Phase 3 accepted state.
  - [ ] Apply the acceptance rules. Accept, or revert and record as a dead end.
- **Timing:** ~2 hours agent time (hard time-box; if no legal trigger is found within it, record the
  dead end and move on), plus ~30-45 min unattended measurement if a candidate is produced.
- **Depends on:** 3
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - `ForAllTime` / `ExistsTime`
    (only if a legal trigger is found)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/04_phase4-time-patterns.json` - new
    (only if a candidate is produced)
- **Verification:**
  - Either: a legal, Z3-accepted trigger is in place with the semantics-preservation gate green and
    an explicit accept/neutral/regressive verdict; or: a documented dead-end record explaining
    precisely why no legal trigger was reachable, with no production file modified.
  - The gate decision (skipped vs. executed) is recorded with the measured headroom that justified it.

---

### Phase 5: Gate re-run, headroom report, and dead-end record [NOT STARTED]

- **Goal:** Re-run the Step 6 gating oracle path end to end and report measured per-formula headroom
  against budgets and floors that were never touched.
- **Tasks:**
  - [ ] Run a final confirmation measurement round on all three target formulas against the accepted
        final encoding; write `baselines/05_final-solve-cost.json`.
  - [ ] Run the Step 6 path inside `nix develop`:
        `nix develop --command bash oracle/run-oracle-suite.sh` (both passes: parallel `-n 6` and
        `xdist_serial`), capturing full output. Confirm exit 0 and inspect the
        `== ORACLE TIMEOUT-SKIP INVENTORY ==` section for `[NEW]` entries.
  - [ ] Run the full gate: `nix develop --command bash code/scripts/verify-refactor.sh`, confirming
        Step 6 reports "gating oracle suite green across both passes".
  - [ ] Confirm `TestGatingConclusiveScan` reaches or exceeds the **unchanged**
        `MIN_CONCLUSIVE_GATING_FORMULAS = 100` (the prior miss was 99/103), and that
        `timeout_count` dropped.
  - [ ] Verify with `git diff` that none of the read-only constants listed under Hard Constraints
        were modified, that no test is xfailed or skipped, and that `ORACLE_PASS2_TIMEOUT` is
        untouched.
  - [ ] Produce a headroom table in the implementation summary: per formula, `median(wall)`,
        `max(wall)`, budget, and `budget / max(wall)` headroom ratio, before and after — using the
        Phase 1 baseline as "before".
  - [ ] Record every rejected candidate as a new numbered dead end, in the codebase's own
        established style: an inline comment at the relevant constraint in `core.py`/`operators.py`
        (matching how the existing six dead ends are recorded), plus a section in the implementation
        summary. Include the measured numbers that justified rejection.
  - [ ] Save the gate transcripts under
        `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/`.
- **Timing:** ~1.5 hours agent time, plus the gate's own run time (pass 1 ~650s, pass 2 ~850-960s,
  plus the remaining verify-refactor steps).
- **Depends on:** 4
- **Files to modify:**
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/05_final-solve-cost.json` - new
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/` - gate transcripts
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` and/or `operators.py` - dead-end
    comments only
  - `specs/144_fix_oracle_per_formula_solve_timeouts/summaries/01_oracle-solve-cost-reduction-summary.md` - new
- **Verification:**
  - `verify-refactor.sh` Step 6 green; runner exit 0 on both passes.
  - `git diff` confirms no budget widened, no floor lowered, no test disabled.
  - Headroom table present with before/after numbers drawn from measurement rounds, not single runs.
  - If the gate is still not green, the outcome is escalated **with the measured data** — never by
    touching a budget or a floor.

---

## Testing & Validation

- [ ] `nix develop --command pytest oracle/bimodal_logic/tests/test_encoding_nondegeneracy.py` green
      after every encoding-touching phase (aliasing regression guard).
- [ ] `nix develop --command pytest oracle/bimodal_logic/tests/test_soundness_regression.py` green
      after every encoding-touching phase.
- [ ] `nix develop --command pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
      with `disagreements=0` after every encoding-touching phase.
- [ ] `nix develop --command pytest oracle/bimodal_logic/tests/test_oracle_interface.py -k
      "test_mixed_and_box_next or test_mixed_and_all_future_neg or test_all_sat_task_relation_ternary"`
      green in isolation.
- [ ] `TestGatingConclusiveScan` reaches or exceeds the unchanged `MIN_CONCLUSIVE_GATING_FORMULAS = 100`.
- [ ] `nix develop --command bash oracle/run-oracle-suite.sh` exits 0 across both passes, with no
      `[NEW]` entries in the timeout-skip inventory.
- [ ] `nix develop --command bash code/scripts/verify-refactor.sh` reports Step 6 green.
- [ ] `PYTHONPATH=code/src pytest code/tests/` and the bimodal theory unit tests remain green (the
      encoding is shared with the production theory, not only the oracle).
- [ ] `nix develop --command bash code/scripts/compare_bimodal_baseline.sh
      specs/archive/097_optimize_build_frame_constraints/baseline_results.txt` (verify-refactor
      Step 7) reports no regressions.
- [ ] `git diff` shows no change to `SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`,
      `MIN_CONCLUSIVE_SCAN_FORMULAS`, `ORACLE_PASS2_TIMEOUT`, or any per-solve `timeout_ms=`.

## Artifacts & Outputs

- `specs/144_fix_oracle_per_formula_solve_timeouts/plans/01_oracle-solve-cost-reduction.md` (this file)
- `specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py` (measurement harness)
- `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/01_solve-cost-baseline.json` + `.md`
- `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/02_phase2-patterns.json`
- `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/03_phase3-shift-grounding.json`
- `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/04_phase4-time-patterns.json` (conditional)
- `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/05_final-solve-cost.json`
- Gate transcripts under `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/`
- `specs/144_fix_oracle_per_formula_solve_timeouts/summaries/01_oracle-solve-cost-reduction-summary.md`
- Encoding changes (accepted candidates only) in
  `code/src/model_checker/theory_lib/bimodal/semantic/core.py` and
  `code/src/model_checker/theory_lib/bimodal/operators.py`

## Rollback/Contingency

### Per-candidate revert policy (binding)

Each of Phases 2, 3, and 4 produces exactly one candidate optimization, evaluated against the
acceptance rules. The disposition is mandatory, not discretionary:

- **Accepted** (rules A-E all pass): keep the change; commit it as its own phase commit so it can be
  bisected and reverted independently later.
- **Neutral** (`|median(rlimit) delta| < 10%`): **revert the change.** A neutral-but-complicating
  change to a correctness-critical encoding is a net negative: it adds a trigger or an unroll that
  future readers must reason about, for no measured benefit. Reverting is the default, not the
  fallback.
- **Regressive** (median cost up, or `max(rlimit)` up): revert immediately.
- **Semantics-violating** (any non-zero `disagreements`, or any guard test red): revert immediately
  and treat as the most severe class of failure. Never attempt to "tune" a pattern that changed a
  verdict — the pattern is wrong, not narrow.

Because each phase is committed separately and the preceding phase's state is green, reverting a
candidate is `git revert` of that phase's commit; no snapshot-and-reset is required. Follow
`.claude/rules/git-workflow.md` — never discard uncommitted work destructively.

### Dead-end recording (required for every rejected candidate)

Every reverted candidate is recorded alongside the six already documented, in both places:

1. An inline comment at the relevant constraint in `core.py`/`operators.py`, matching the style of
   the existing dead-end notes (what was tried, what was measured, why it was rejected — with the
   actual numbers).
2. A "New Dead Ends" section in the implementation summary, numbered continuing from the research
   report's list (i.e. starting at 7).

This is what makes a rejected candidate a durable result rather than wasted work, and prevents a
future task from re-attempting it.

### If all candidates are rejected

If Phases 2-4 all land neutral or regressive and the gate is still not green, the task outcome is
**"measured, no lever found"**, escalated with the baseline and per-candidate data. It is **not**
resolved by widening a budget, lowering a floor, xfailing a test, or reverting the task 139
soundness fix — all four are explicitly forbidden by the Hard Constraints. The escalation should
carry the measured headroom table so the decision about what to do next is made on data. A follow-up
profiling pass with `smt.qi.profile` enabled (to obtain a direct quantifier-instantiation count,
which the research report notes was not captured) is the natural next investigation, not a
constraint relaxation.

### If the harness cannot reproduce the real solve

If Phase 1's harness numbers diverge substantially from the research report's section 4 timings
(44.33s/46.75s for `and_box_next`), the harness is not reproducing the real pipeline and every later
measurement would be worthless. Stop and fix the harness before proceeding to Phase 2; do not
proceed on an unvalidated baseline.
