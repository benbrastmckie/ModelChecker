# Implementation Summary: Reduce Oracle Per-Formula Z3 Solve Cost

- **Task**: 144 - fix_oracle_per_formula_solve_timeouts
- **Plan**: `plans/01_oracle-solve-cost-reduction.md`
- **Status**: All 5 phases completed. Outcome is **"measured, no lever found"** — the plan's own
  explicitly-anticipated contingency, not a process failure. Every candidate encoding change was
  implemented, measured against a rigorous paired-seed methodology, and honestly rejected when it
  failed the binding acceptance rules. No budget was widened, no floor was lowered, no test was
  xfailed or skipped, and the task 139 soundness fix was not touched.

## What Was Built

- `specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py`: a standalone, seeded
  measurement harness that drives `BimodalSemantics`/`ModelConstraints`/`BimodalStructure` directly
  (the same pipeline `Z3OracleProvider.find_countermodel` uses), with `z3.set_param`-pinned
  `smt.random_seed`/`sat.random_seed` so before/after comparisons are paired and reproducible. Seeds
  are pinned in the harness only; `z3_adapter.py` is untouched. Verified: same seed reproduces
  identical `rlimit count` across repeated runs; different seeds diverge.
- Five measurement rounds (`baselines/01_solve-cost-baseline.json` through `05_final-solve-cost.json`,
  plus two gate transcripts), each 7 runs x 3 formulas = 21 Z3 solves, `rlimit count` as primary
  metric and wall-clock as a secondary direction check, per the plan's binding measurement
  methodology.

## What Was Tried and Rejected

Three distinct encoding-level candidates were implemented, each measured against the plan's binding
acceptance rules (>=20% median `rlimit` reduction, no worsened `max(rlimit)`, wall-clock agreement,
negative delta on >=4 of 5 seeds), and each rejected:

1. **Phase 2 — explicit E-matching `patterns=` triggers** on the four remaining unpatterned
   quantifier sites (`NecessityOperator.true_at`, `depth_bounded_skolem_abundance_constraint`,
   `capped_skolem_abundance_constraint`, `matching_states_when_shifted_var`), extending the
   codebase's own `build_forward_comp_constraint` precedent. All four patterns were legal (Z3
   accepted them). Bisection found that a trigger on the shared abundance-axiom infrastructure
   regressed `\Future p` (F(p)) from ~3s to a 5000ms timeout — a formula outside the three named
   targets that shares the same frame constraint. The remaining non-regressive candidate
   (`NecessityOperator`'s pattern) measured **neutral** (median `rlimit` unchanged, ~0.00%, and
   per-seed sign inconsistent). All four reverted.
2. **Phase 3 — grounding the shift dimension** of `depth_bounded_skolem_abundance_constraint` by
   unrolling its provably 2-element `shift_amount` domain into `2*max_shift` separate
   single-variable `ForAll`s, a sound finite-domain elimination distinct from established dead end 1
   (which grounds the much larger world/target dimension). Measured **regressive**: `and_box_next`'s
   median wall increased 46.54s -> 60.25s (seed 0 went from a reliable solve to a hard timeout on all
   3 runs), `and_all_future_neg`'s median rlimit/wall roughly doubled, and even
   `all_sat_task_relation_ternary`'s dramatically-improved median (-94%) failed acceptance rule B
   because its `max(rlimit)` got worse. Reverted.
3. **Phase 4 — a body-derived trigger for `ForAllTime`/`ExistsTime`**, the one remaining unpatterned
   quantifier family every `\Future`/`\Past`/`\Until`/`\Since` truth method routes through. Direct AST
   inspection of the actual `\next(B)` translation located a structurally-present, syntactically-legal
   candidate term. Z3 **rejected it outright** with `invalid pattern` when actually constructed
   against the real quantifier — a stronger negative than Phases 2/3, since the candidate never even
   reached a measurable state. `ExistsTime` was separately confirmed inert for all three targets
   (its quantifier is skolemized away by Z3 preprocessing before the main search begins). Reverted.

All three rejections are recorded both as inline dead-end comments in `core.py`/`operators.py`
(matching the codebase's existing six-dead-end style) and in the "New Dead Ends" section below.

## Gate Outcome (Phase 5)

The Step 6 gate was run twice under this task, producing **both a pass and a failure**:

- A standalone `oracle/run-oracle-suite.sh` invocation (load average 2.62/2.36/2.39, relatively idle)
  passed cleanly: both passes green, no `[NEW]` timeout-skip entries.
- The full `code/scripts/verify-refactor.sh` gate, run minutes later (load average 3.95/3.14/2.80,
  visibly more contended), failed at Step 6: 3 of 14 pass-2 tests failed, including this task's own
  `test_mixed_and_box_next` target, a different depth-1 formula (`BM_CM_4`, also documented as
  affected by the same task 139 term-aliasing cost increase), and `TestGatingConclusiveScan` landing
  at 99/103 conclusive against the unchanged floor of 100 — **the exact same figure documented as the
  historical pre-task-144 miss** in the research report. `disagreements=0` in every run: soundness
  was never at risk, only budget/performance.

This inconsistency is not a bug in this task's work — the encoding is byte-identical to the Phase 1
baseline throughout (confirmed by exact `rlimit` reproduction after every phase), so both gate runs
exercised the same code. It is direct, first-hand confirmation of the research report's root-cause
diagnosis: `and_box_next` and the ternary test's `next_A` leg both measure at essentially **1.0x
headroom** (their worst observed draws land at or past their budgets even in isolated, contention-free
measurement), so whether a given gate run's random draw and ambient machine load happen to land under
or over budget determines pass/fail for that run.

## Headroom Table

| Formula | Budget | median(wall) before | median(wall) after | max(wall) before | max(wall) after | headroom |
|---|---|---|---|---|---|---|
| `and_box_next` | 60s | 46.54s | 49.89s | 60.37s | 60.39s | ~1.0x |
| `and_all_future_neg` | 60s | 18.61s | 20.13s | 23.59s | 25.17s | ~2.4x |
| `all_sat_task_relation_ternary` (`next_A`) | 180s | 94.63s | 89.91s | 180.70s | 180.62s | ~1.0x |

Before/after are identical because no candidate encoding change survived Phases 2-4; the "after"
column is drawn from a full independent 21-run remeasurement (Phase 5), not a copy of Phase 1's data,
and its median `rlimit` values match Phase 1's exactly for all three formulas.

## New Dead Ends (continuing the research report's numbering from 6)

7. **`patterns=[z3.Select(source_array, time)]` on `matching_states_when_shifted_var`'s inner
   `ForAll([time], ...)`** (Task 144, Phase 2): legal, Z3-accepted, but regressed `\Future p` (F(p))
   from ~3s to a 5000ms timeout by starving this shared axiom's instantiation for formulas whose
   ground term set doesn't yet contain the needed application. Reverted; recorded inline at
   `matching_states_when_shifted_var` in `core.py`.
8. **`patterns=[shift_of_bounded(source_world, shift_amount)]` on
   `depth_bounded_skolem_abundance_constraint`** (Task 144, Phase 2): legal, Z3-accepted, and the
   plan's highest-leverage candidate (active for all three Phase 1 targets), but independently
   reproduces the same F(p) regression as dead end 7. Reverted; recorded inline at
   `depth_bounded_skolem_abundance_constraint` in `core.py`.
9. **`patterns=[is_world(other_world)]` on `NecessityOperator.true_at`** (Task 144, Phase 2): legal,
   does not break any test, but measured neutral (median rlimit unchanged, inconsistent per-seed
   sign). Rejected under the neutral-candidates-are-reverted policy. Recorded inline in
   `operators.py`.
10. **Unrolling `depth_bounded_skolem_abundance_constraint`'s `shift_amount` dimension into
    `2*max_shift` separate single-variable `ForAll`s** (Task 144, Phase 3): sound, logically-
    equivalent finite-domain elimination, distinct from established dead end 1 (which grounds the
    world dimension). Measured regressive on 2 of 3 target formulas and rule-B-violating on the
    third — likely because splitting one joint quantifier into many independent top-level
    quantifiers increases Z3 MBQI scheduling overhead across the whole frame-constraint set. Reverted;
    recorded inline at `depth_bounded_skolem_abundance_constraint` in `core.py`.
11. **A body-derived E-matching trigger for the guard-time `ForAllTime` inside `\next`'s
    `Until(arg, bot)` translation** (Task 144, Phase 4): a candidate term
    (`Select(world_function(w), time_var)`) was structurally located via direct AST inspection and is
    syntactically legal, but Z3 rejected it outright with `invalid pattern` when actually constructed
    — Z3's pattern admissibility rules are stricter than syntactic bound-variable coverage; the
    specific subterm (from `bot`'s always-false self-inequality encoding) does not qualify. No legal
    alternative was found within the phase's hard time-box. Reverted; recorded inline at
    `ForAllTime` in `core.py`.

## Plan Deviations

- **Phase 2**: `NecessityOperator.false_at`'s `Exists` was left unpatterned and unmeasured (rather
  than tested for inertness) because none of the three Phase 1 target formulas exercise it (none
  negate `\Box`), per the plan's "do not spend effort" guidance for an untestable site.
- **Phases 2-4 final states**: the full `test_cross_oracle_differential.py` (`disagreements=0`) gate
  was not re-run against each phase's final (fully-reverted, comment-only) diff, since each was
  confirmed functionally identical to the last already-differential-verified state via exact `rlimit`
  reproduction; the full differential suite (and the fuller gate) WAS run at the end of Phase 5
  against the actual final code.
- **Phase 5**: the gate was run twice (once standalone, once via the full `verify-refactor.sh`
  script) rather than once, because the two runs produced different outcomes (green, then red) —
  this divergence is itself the phase's most important finding, documented in full above rather than
  treated as a re-run-until-green loop.
- **`depth_bounded_skolem_abundance_constraint`'s return type**: now returns a single-element list
  (was a bare Z3 expression) even in its final, fully-reverted state, with `build_frame_constraints`'
  caller updated to match. This is a harmless, verified-equivalent refactor left over from the Phase
  3 experiment (whose accepted form would have needed a list return); reverting the return-type
  change back to a bare expression was not necessary since the caller already tolerates a list
  (confirmed by the `*skolem_abundance` splat's own pre-existing comment anticipating "multiple for
  M>=3").

## Files Modified

- `specs/144_fix_oracle_per_formula_solve_timeouts/bench_solve_cost.py` (new)
- `specs/144_fix_oracle_per_formula_solve_timeouts/baselines/*.json`, `*.md`, `*.txt` (new,
  measurement data and gate transcripts)
- `code/src/model_checker/theory_lib/bimodal/operators.py` (dead-end 9 comment only; no behavior
  change)
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (dead-end 7/8/10/11 comments;
  `depth_bounded_skolem_abundance_constraint` return-type refactor, verified behavior-equivalent; no
  other behavior change)
- `.gitignore` (excluded the bench harness's `__pycache__/`)

## Recommendation for Future Work

Per the plan's own contingency: this outcome is not resolved by widening a budget, lowering a floor,
xfailing a test, or reverting the task 139 soundness fix — all four are explicitly forbidden. The
plan's own suggested next step is a follow-up profiling pass with `smt.qi.profile` enabled to obtain
a direct quantifier-instantiation count (not captured by this task, since `rlimit count` was used as
the primary metric per the binding methodology). That direct instantiation count could help identify
whether the cost is dominated by a specific quantifier's instantiation volume in a way this task's
three encoding-level candidates did not reach.
