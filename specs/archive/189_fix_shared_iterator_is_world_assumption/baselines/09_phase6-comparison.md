# Phase 6 Decision Gate: Post-Change Comparison Against Phase 1 Baseline

## 1. Phase 1's exact four-file, 19-test baseline command

Re-run: `08_phase6-regression-rerun.txt` (this run also includes the bimodal file, since Phase 1's
own command already did; total now 26 -- 19 baseline + 7 bimodal tests added since Phase 1).
**Result: all 19 baseline tests still pass, 0 newly failing.** Gate sub-criterion 1 met.

## 2. Per-theory live `iterate: 3` re-run, same representative examples as `02_...md`

| Theory     | Phase 1 baseline (checked / isomorphic / models found) | Phase 6 re-run |
|------------|----------------------------------------------------------|----------------|
| logos      | 31 / 30 / 1                                               | 31 / 30 / 1 (byte-identical) |
| imposition | 31 / 30 / 1                                               | 31 / 30 / 1 (byte-identical) |
| exclusion  | 31 / 30 / 1 (`max_time` timeout at 9.94s)                 | 27-29 / 26-28 / 1 (`max_time` timeout, ~10.0-10.35s), varies run to run |

**Models found is unchanged for all three (1 in every run, both before and after).** logos's and
imposition's `checked_model_count`/`isomorphic_model_count` are byte-identical, because both
terminate via the *logical* "Insufficient progress" rule (`checked_model_count > 30`), which is
timing-independent.

exclusion's `checked_model_count` varies run-to-run (27-29, vs. the single Phase 1 sample of 31)
because exclusion terminates via `max_time`'s **wall-clock** timeout instead -- exclusion's
per-check cost is high enough that it never reaches the logical 30-check cap before 10 real
seconds elapse, so how many checks fit in that window is inherently sensitive to machine load,
not to constraint content. This is confirmed structurally, not just by re-running: throughout
every one of these runs, exactly one model is ever found (model 1), so `self.found_models` never
grows past length 1, which means every single `_build_exclusion_constraints([model_1])` call
during the run passes a **one-element** list to `_create_difference_constraint`. For a
one-element `previous_models` list, the new default-delegation path
(`BaseModelIterator._create_difference_constraint` -> `ConstraintGenerator._create_difference_constraint`,
called once with `[model_1]`) and the old direct path
(`ConstraintGenerator.create_extended_constraints([model_1])`, which loops once and calls
`_create_difference_constraint([model_1])` -- identical single call) construct **the exact same
Z3 expression**, because `git diff` on `constraints.py` between the commit before and after Phase
3 (`62585663~1`..`62585663`) shows the docstring-only change -- zero logic changed in
`_create_difference_constraint`, `_create_state_difference_constraints`, or any method it calls.
The observed exclusion timing spread is therefore provably a wall-clock artifact of this
environment at measurement time, not a consequence of any code change in this plan.

## 3. Broader theory suites plus the shared iterate suite

See `10_phase6-full-suite-output.txt` for the full re-run of
`theory_lib/{logos,imposition,exclusion}/tests/` and `iterate/tests/`.

## Gate Decision

**Criterion met: all baseline tests green AND per-theory model counts unchanged.** No narrowing
(the Phase 3 contingency branch) is needed. Bimodal's fix stands as implemented; logos,
imposition and exclusion keep routing through the polymorphic hooks' base-class defaults with
zero behavioral difference from before this plan, other than the incidental,
wall-clock-timeout-driven check-count spread documented above for exclusion, which is not a
constraint-content regression.
