# Phase 6 Handoff (plan 02): task 185

## Immediate Next Action

Open Phase 7: write `counterfactual/report/verifier_clauses.md` (the recommendation), update `counterfactual/README.md` and `tests/README.md`, run `check-task-references.sh` over `code/`, complete gate, drop the stash on a clean tree, write the summary.

## Current State

Phase 6 [COMPLETED]. `candidate_examples.py` (`nested_examples`, `constitutive_example(s)`, `regression_examples`, curated `counterfactual_candidate_examples`, runnable module); `tests/test_candidate_logic.py` (76 tests: 36 nested schemata at N=3 all matching the oracle profile; constitutive comparison N=3/N=4; oracle confirmation of the Z3 countermodel; regression guard 4 x 6); `examples.py` registers the collection additively. Baselines: `05_regression-matrix.json` (identical across candidates), `09_constitutive-countermodels.json`, `10_possible-state-separation-n4.json`; `tests/n4_separation_witnesses.json` with oracle pins (`test_candidate_logic_oracle.py`, now 31 tests). Suites: logos 747, `code/tests` 680, counterfactual dir green.

## Key Decisions Made

- Hyperintensionality at N=4 is established, correcting the research's small-frame-coincidence reading: Z3 finds constitutive (`\equiv`) countermodels for `ILC`/`ILMC` at N=4 (valid for `W`/`L`/`MC`); large oracle samples give possible-state separations at n=4 (ILMC witness: worlds `a.b, b.c, a.d, b.d`, `V ∩ possible = {a.b, c}` vs `{a.b, b.c}`; `MC` gives `{a.b, c}` for both). This is a direct `ILMC` vs `MC` separation at 4 atoms, the "further test" the research asked for.
- The Z3 countermodels' possible-state separation is seed-dependent, so the Z3 test pins only that the pair is separated; the possible-state pin lives in the oracle test on the saved witness.
- `\equiv` compares whole sets, so impossible members of `ILMC` matter to it (as they do for letters); recorded as a concession item for the report.

## Deviations from Plan

- Two extra baselines (09, 10) and one extra test-data file beyond the plan's list; the constitutive hypothesis recorded as overturned inline.

## What NOT to Try

- Do not pin the Z3 constitutive countermodel's world set; it varies with the Z3 seed.

## References

- Plan: `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/plans/02_ilmc-settled-imposition-verifiers.md`, Phase 6 of 7.
