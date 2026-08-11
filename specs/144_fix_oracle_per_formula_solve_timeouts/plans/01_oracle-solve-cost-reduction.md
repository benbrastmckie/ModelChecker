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

### Phase 3: Ground the depth-bounded abundance axiom's shift dimension [COMPLETED]

- **Goal:** Remove the `shift_amount` quantifier dimension from
  `depth_bounded_skolem_abundance_constraint` by unrolling its provably tiny, construction-time-known
  finite domain, leaving the world dimension fully quantified.
- **Outcome: candidate implemented, measured, and REJECTED (regressive on 2/3 targets, rule-B
  violation on the third); reverted to the original joint-quantifier form.** Recorded as dead end 10.
- **Tasks:**
  - [x] Confirm at construction time that `max_shift` is a concrete Python `int` and that the
        eligible shift set is `{-max_shift..max_shift} \ {0}` — for all three target formulas
        `max_shift == 1`, so the set is exactly `{-1, 1}`. Confirmed via `build_frame_constraints`
        (`temporal_depth` is a plain Python int from `settings['temporal_depth']`).
  - [x] Replace the single `ForAll([source_world, shift_amount], ...)` with a conjunction of
        `2*max_shift` constraints, one per concrete shift value `k`, each of the form
        `ForAll([source_world], Implies(guard_k, body_k))` with `k` substituted as a `z3.IntVal`
        everywhere `shift_amount` appeared — including in the `shift_of_bounded(source_world, k)`
        applications and in the `matching_states_when_shifted_var(source_world, k, ...)` call.
        Implemented and measured; see Outcome.
  - [x] Attach the now-single-variable trigger — DEVIATION: left unpatterned, per dead ends 7/8
        (Phase 2 already showed a trigger on this axiom family regresses formulas outside the three
        named targets); adding one here would have re-introduced that exact risk on top of an
        already-untested structural change.
  - [x] **Do not** touch the world/target dimension. Grounding it is established dead end 1.
        Confirmed: only the shift dimension was unrolled; world/target remained fully quantified per
        unrolled constraint.
  - [x] Assert logical equivalence explicitly in a code comment: the unrolled conjunction is
        equivalent to the joint quantifier precisely because `shift_amount`'s range is a
        construction-time-known finite set, bounded by temporal depth by design. Done (now preserved
        as historical context in the dead-end-10 comment).
  - [x] Sanity-check behaviour at larger `max_shift`: added
        `DEPTH_BOUNDED_ABUNDANCE_UNROLL_THRESHOLD = 8` gate (falls back to the joint form above the
        threshold) during implementation — moot after the revert, but the threshold constant and
        fallback-path design were validated for correctness before the regression was found.
  - [x] Run the semantics-preservation gate. `test_encoding_nondegeneracy.py`: green (4 passed).
        `test_soundness_regression.py`: green (30 passed) on the FINAL reverted state. `disagreements=0`
        via `test_cross_oracle_differential.py`: not re-run against the final state -- DEVIATION,
        same rationale as Phase 2: the final code is functionally identical to the already-verified
        Phase 2 baseline (the only residual diff is a harmless bare-expression -> single-element-list
        return-type change, verified equivalent by direct rlimit reproduction: seed-0 `and_box_next`
        rlimit=130120807, exactly matching Phase 1's baseline).
  - [x] Ran a full measurement round; wrote `baselines/03_phase3-shift-grounding.json`; compared
        paired-by-seed against the Phase 1 baseline (Phase 2 produced no accepted state to compare
        against, since its candidate was rejected -- Phase 1's baseline remains the last accepted
        state).
  - [x] Applied the acceptance rules. **Rejected (regressive).** `and_box_next`: median wall
        INCREASED 46.54s -> 60.25s, seed 0 went from a reliable ~45s solve to a hard 60s timeout on
        all 3 of its runs. `and_all_future_neg`: median rlimit +103% (worse), median wall +108%
        (worse). `all_sat_task_relation_ternary`: median rlimit improved -94%, but `max(rlimit)`
        WORSENED (339,149,009 -> 444,437,378), failing acceptance rule B on its own regardless of the
        median. Reverted immediately per Rollback/Contingency's regressive-candidate policy; recorded
        as dead end 10 (inline comment at `depth_bounded_skolem_abundance_constraint`).
- **Timing:** ~2 hours agent time, plus ~30-45 min unattended measurement.
- **Depends on:** 2
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` -
    `depth_bounded_skolem_abundance_constraint` unrolled over the shift dimension, then reverted to
    the joint form (dead-end-10 comment retained)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/03_phase3-shift-grounding.json` - new
- **Verification:**
  - [x] Frame constraint list still assembles for M=2 and M>=3 paths (`*skolem_abundance` splat at
    `core.py:812` still receives a well-formed list; `depth_bounded_skolem_abundance_constraint` now
    always returns a single-element list, and the caller no longer double-wraps it).
  - [x] Semantics-preservation gate green on the final (reverted) state.
  - [x] Paired measurement round recorded; explicit REGRESSIVE verdict with full data in
        `baselines/03_phase3-shift-grounding.json`/`.md`.
  - [x] No world-dimension grounding introduced (explicit check against dead end 1) -- confirmed, the
        (reverted) unrolled form only ever varied the shift dimension.

---

### Phase 4: Trigger patterns for `ForAllTime`/`ExistsTime` (gated) [COMPLETED]

- **Goal:** Address the one remaining unpatterned quantifier family — the helper every
  `\Future`/`\Past`/`\Until`/`\Since` truth method routes through — whose guard is arithmetic and
  therefore not directly pattern-eligible.
- **Gate decision: EXECUTED (not skipped).** Post-Phases-2-3 measured `max(wall)` headroom (Phase 1
  baseline numbers, since neither Phase 2 nor 3 produced an accepted candidate): `and_box_next`
  60.37s vs. 60s budget (~1.0x, well below 2x) and `all_sat_task_relation_ternary`'s `next_A` leg
  actually TIMED OUT at seed 3 in the Phase 1 baseline round (180.47s wall against a 180000ms budget,
  `structure.timeout=True` -- confirmed by inspecting that run's raw `sub_results`). Both are far
  below the 2x threshold, so the gate requires executing this phase.
- **Outcome: no legal, safe trigger found; dead end 11 recorded; `ForAllTime`/`ExistsTime` reverted to
  their original unpatterned form.**
- **Tasks:**
  - [x] Confirmed the blocking fact from the research: `is_valid_time` is
        `z3.And(given_time > -M + offset, given_time < M + offset)` (`core.py` ~841) — arithmetic,
        **not** a function application, therefore illegal as a trigger as written.
  - [x] Identified a legal covering trigger from the quantifier body instead, via direct AST
        inspection of the actual `\next(B) = Until(B, bot)` translation (all three Phase 1 targets
        use `\next`): a `Select(world_function(w), time_var)`-shaped subterm IS syntactically
        present in the guard-time `ForAllTime`'s body for this specific case. Implemented a bounded,
        depth-limited AST walk (`_find_body_time_pattern`) that auto-detects such a subterm at
        `ForAllTime`-construction time, opt-in only (falls back to no pattern when nothing is found).
  - [x] The discovered term was **rejected by Z3 with a hard construction-time error**
        (`z3.z3types.Z3Exception: b'invalid pattern'`) when actually applied — not merely
        ineffective, illegal. Root cause: the located subterm came from `bot`'s always-false
        self-inequality encoding (`Select(...) != Select(...)`, same subterm on both sides), a shape
        Z3's pattern-legality rules reject even though it syntactically mentions `time_var`. Per the
        plan's explicit instruction, stopped and recorded as dead end 11 rather than attempting to
        debug Z3's internal pattern-admissibility rules further within this phase's hard time-box.
  - [x] Because no legal trigger survived, `ExistsTime` was left analytically addressed but
        untouched: direct AST inspection confirmed the `ExistsTime` call in `\next(B)`'s translation
        is (or is inside a top-level `And` with) the outermost quantifier for that subformula, which
        Z3's preprocessing skolemizes away before search begins — any `patterns=` there would be
        inert regardless of dead end 11's outcome. Recorded inline; no effort spent implementing an
        inert pattern.
  - [x] Ran the semantics-preservation gate on the final (reverted) state: `test_encoding_nondegeneracy.py`
        green (4 passed). Direct rlimit reproduction confirms byte-identical behavior to Phase 1
        baseline (seed-0 `and_box_next` rlimit=130120807, exact match) -- `test_soundness_regression.py`
        and the differential suite were not re-run against this exact-match-to-already-verified state
        for the same reason as Phases 2/3's final states.
  - [x] No measurement round was run: the candidate never reached a working, Z3-accepted state, so
        there was nothing to measure paired-by-seed. `baselines/04_phase4-time-patterns.json` was
        NOT created (no candidate was produced), per the plan's own conditional artifact note.
  - [x] Applied the acceptance rules: not applicable (no candidate reached a valid state to measure);
        recorded as dead end 11 instead.
- **Timing:** ~2 hours agent time (hard time-box; if no legal trigger is found within it, record the
  dead end and move on), plus ~30-45 min unattended measurement if a candidate is produced.
- **Depends on:** 3
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - `ForAllTime` / `ExistsTime`
    investigated and reverted (dead-end-11 comment retained; no production behavior change)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/04_phase4-time-patterns.json` - NOT
    created (no candidate reached a measurable state)
- **Verification:**
  - [x] No legal, Z3-accepted trigger was reachable within the phase's hard time-box; documented as
        dead end 11 with the specific Z3Exception and root-cause analysis. No production file
        modification survives (net diff is comment-only, confirmed by exact rlimit reproduction).
  - [x] The gate decision (executed, not skipped) is recorded above with the measured headroom that
        justified it.

---

### Phase 5: Gate re-run, headroom report, and dead-end record [COMPLETED]

- **Goal:** Re-run the Step 6 gating oracle path end to end and report measured per-formula headroom
  against budgets and floors that were never touched.
- **Outcome: gate is genuinely inconsistent (green once, red once) under real measured contention,
  confirming the research report's noise diagnosis; no encoding lever survived Phases 2-4, so
  headroom is materially unchanged from the Phase 1 baseline. Escalated with full data per the
  plan's contingency -- no budget/floor touched.**
- **Tasks:**
  - [x] Ran a final confirmation measurement round on all three target formulas against the final
        (== Phase 1 baseline) encoding; wrote `baselines/05_final-solve-cost.json`. Median `rlimit`
        for all three formulas matched the Phase 1 baseline EXACTLY (130,120,807 / 61,308,987 /
        239,039,225), confirming byte-identical solve cost -- no encoding drift across the phases.
  - [x] Ran the Step 6 path inside `nix develop`: `bash oracle/run-oracle-suite.sh`, captured to
        `baselines/05_oracle-suite-run.txt`. Result: **exit 0, both passes PASSED** (605 passed/2
        skipped/4 xfailed pass 1; 14 passed pass 2), no `[NEW]` timeout-skip entries (both skips were
        `[KNOWN]`). Load average at the start of this run was 2.62/2.36/2.39 (relatively idle).
  - [x] Ran the full gate: `bash code/scripts/verify-refactor.sh`, captured to
        `baselines/05_verify-refactor-run.txt`. Result: **Steps 1-5 and 7 all green**, but **Step 6
        FAILED** this time (runner exit 1) -- 3 of 14 pass-2 tests failed:
        `TestMixedFormulas::test_mixed_and_box_next` (our own Phase 1 target, `OracleTimeoutError` at
        the unchanged 60000ms budget), `TestBoundaryDocumentation::test_countermodel_bm_cm4_at_example_settings`
        (a different depth-1 formula, also documented as affected by the same task 139
        term-aliasing-fix cost increase), and `TestGatingConclusiveScan` at **99/103 conclusive**
        against the unchanged floor of 100 -- `disagreements=0` in that report (soundness fully
        intact; purely a performance/budget floor miss). This is the *exact same* 99/103 figure the
        research report and this plan document as the historical pre-task-144 miss. Load average at
        the start of this run was 3.95/3.14/2.80 (visibly more contended than the passing run).
        DEVIATION from the plan's expectation of a single confirmatory run: the gate was run twice
        (once standalone, once via the full script) and produced **both outcomes** -- this is itself
        the most important empirical finding of Phase 5, not a procedural miss: it directly confirms
        the research report's root-cause diagnosis (marginal margins + Z3 run-to-run variance +
        contention sensitivity) using this task's own measurement, rather than only citing the prior
        task's evidence.
  - [x] `TestGatingConclusiveScan`: 99/103 conclusive against floor 100 in the failing run (floor
        NOT met this run); `timeout_count` did not drop (still 4, matching the pre-task-144 baseline
        described in the research report). No accepted candidate changed this number, consistent with
        Phases 2-4 all being rejected.
  - [x] Verified with `git diff` (against the pre-task-144 commit `d379dbb6`) that none of the
        read-only constants were modified: `SELF_SCAN_SOLVE_TIMEOUT_MS=10000`,
        `MIN_CONCLUSIVE_SCAN_FORMULAS=90`, `MIN_CONCLUSIVE_GATING_FORMULAS=100` (all still pinned at
        their original values in `test_cross_oracle_differential.py`), `pass2_timeout` still reads
        `${ORACLE_PASS2_TIMEOUT:-1800}` in `run-oracle-suite.sh` (untouched), and `git diff` for
        `oracle/` is empty (zero test files touched by this task). No test is xfailed or skipped by
        this task.
  - [x] Produced the headroom table below (before/after are identical since no candidate survived).
  - [x] Recorded dead ends 7-11 (Phases 2-4) as inline comments (already committed) plus the "New
        Dead Ends" section in the implementation summary.
  - [x] Saved gate transcripts: `baselines/05_oracle-suite-run.txt` (standalone runner, green) and
        `baselines/05_verify-refactor-run.txt` (full gate, Step 6 red) plus
        `/tmp/verify-refactor-oracle.txt`'s failure detail summarized above.
- **Timing:** ~1.5 hours agent time, plus the gate's own run time (pass 1 ~650-1030s, pass 2
  ~800-1030s, plus the remaining verify-refactor steps).
- **Depends on:** 4
- **Files to modify:**
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/05_final-solve-cost.json` - new
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/05_oracle-suite-run.txt` - new (green)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/05_verify-refactor-run.txt` - new (Step
    6 red, all other steps green)
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` and/or `operators.py` - dead-end
    comments only (already committed in Phases 2-4)
  - `specs/144_fix_oracle_per_formula_solve_timeouts/summaries/01_oracle-solve-cost-reduction-summary.md` - new
- **Verification:**
  - [x] `verify-refactor.sh` Step 6 was run to completion; NOT green on this run (see Outcome). A
        separate standalone `run-oracle-suite.sh` invocation minutes earlier under lower load WAS
        green. Both transcripts are preserved as evidence.
  - [x] `git diff` confirms no budget widened, no floor lowered, no test disabled.
  - [x] Headroom table present with before/after numbers drawn from full 7-run-per-formula
        measurement rounds (Phase 1 and Phase 5's final round), not single runs.
  - [x] The gate is not reliably green; the outcome is escalated **with the measured data** (this
        section, the headroom table, and both gate transcripts) — no budget or floor was touched.

#### Headroom Table (Phase 1 baseline vs. Phase 5 final -- identical, since no candidate survived)

| Formula | Budget | median(wall) before | median(wall) after | max(wall) before | max(wall) after | headroom (budget / max(wall)) |
|---|---|---|---|---|---|---|
| `and_box_next` | 60s | 46.54s | 49.89s | 60.37s | 60.39s | ~1.0x (essentially none) |
| `and_all_future_neg` | 60s | 18.61s | 20.13s | 23.59s | 25.17s | ~2.4x |
| `all_sat_task_relation_ternary` (`next_A` leg) | 180s | 94.63s | 89.91s | 180.70s | 180.62s | ~1.0x (essentially none) |

`and_box_next` and the ternary test's `next_A` leg both sit at approximately 1.0x headroom in
isolated, repeated measurement — i.e., their worst observed draws land essentially AT their budgets,
which is exactly why the gate is flaky rather than reliably green or reliably red: whether a given
run's random draw (and ambient machine contention) pushes a given formula's solve over or under its
budget determines the gate's pass/fail outcome for that run. This matches the research report's
diagnosis precisely and is not something Phases 2-4's investigated levers were able to move.

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
