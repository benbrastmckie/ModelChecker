# Phase 4 Handoff (plan 02): task 185

## Immediate Next Action

Open Phase 5: add `\boxrightILC`, `\boxrightILMC`, `\boxrightMC` (+ might variants) to `candidates.py` via `il_clause` / `minimal_clause` over concrete states, extend `test_candidate_operators.py`'s roster, run the nesting-cost probe at N=3/N=4 and write `baselines/08_nesting-cost.json`.

## Current State

Phase 4 [COMPLETED]. `frame_oracle.py` gained `LOGIC_PRINCIPLES`, `logic_failures`, `logic_sweep`, `hyperintensionality_sweep`. `tests/test_candidate_logic_oracle.py` (26 tests, ~3 s) pins the F7 nested-logic profile for `I, ILC, ILMC, W, L, MC, SRC, XPa, XS` on the seed-23 sample, the F8 same-truth-set counts on the seed-37 sample (723 pairs), the strict-collapse mechanism (`ILC`'s verifiers contain every true world; `X □→ C` and `□(X → C)` agree at every world of every sampled model; `ILMC` has a sampled counterexample, saved in `06_logic-matrix.json`), and Frame G2 (shared truth-set; `L`/`MC`/`W` identical propositions; `IL`/`ILC`/`ILMC` distinct with `x'` vs `a'`,`y`; `ILMC`'s nested truth values differ). Baselines `06_logic-matrix.json` and `07_hyperintensionality.json` written.

## Key Decisions Made

- Report correction: `SR`/`SRC` same-truth-set distinct count on the seed-37 sample is 403, not the 428 quoted in F8's prose; the test pins the mechanical value and the recommendation document must cite 403.
- The Frame G2 `ILC` nested-truth agreement is asserted alongside `ILMC`'s disagreement, to show the difference is visible only through `\equiv`-style operators under `ILC`.

## Deviations from Plan

- None beyond the pin correction recorded inline.

## What NOT to Try

- Do not pin the hyperintensionality counts from the report's prose; the archived table and the sweep agree with each other.

## References

- Plan: `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/plans/02_ilmc-settled-imposition-verifiers.md`, Phase 4 of 7.
