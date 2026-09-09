# Phase 3 Handoff (plan 02): task 185

## Immediate Next Action

Open Phase 4: `tests/test_candidate_logic_oracle.py` -- port `logic_sweep` / `hyper_sweep` over the seeded n=3 samples (seeds 23 and 37, 1,500 models), pin the F7/F8 counts, add the Frame G2 tests and the strict-collapse mechanism test, and write `baselines/06_logic-matrix.json`, `07_hyperintensionality.json`.

## Current State

Phase 3 [COMPLETED]. `tests/test_candidate_structure.py` (39 tests, ~19 s) pins for `I, ILC, ILMC, W, L, MC, SRC, XPe, XPa, XS`: the n=3 exhaustive failure counts (3,204 models, 24 contingent), the n=4 seeded-sample counts (seed 11, 300 models, 11 contingent), the proper-verifier/falsifier tallies per population, the F4 exact-sufficiency characterization (3,228 true worlds, 0 mismatches), the F3 `ILMC` proper verifiers and `IL` closure witness, Frame G (`y`, `a'` settle but survive no imposition; `IL != L`; `ILMC ∩ possible = {c, b, c.b}` vs `MC ∋ a', y`), Frame F3z (`SR`/`SRC` have neither verifier nor falsifier below `w4`; `ILMC` verifies via `p'.z`, `b.z`, `p'.b.z`) and the SRC null-remainder model. `baselines/04_structure-matrix.json` holds both sweeps with population sizes and first witnesses. Every research count matched.

## Key Decisions Made

- Sweep helpers (`structure_sweep`, `SWEEP_PROPERTIES`, `exact_sufficiency_mismatches`) are in `frame_oracle.py` so the baseline writer and the tests share one implementation.
- The seeded n=4 sample is reproducible from the research script's `seed=11`; the n=4 counts are pinned, not left unpinned.

## Deviations from Plan

- None.

## What NOT to Try

- Do not lower the sweep key list to speed the tests; the 10 keys cover every column the recommendation cites.

## References

- Plan: `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/plans/02_ilmc-settled-imposition-verifiers.md`, Phase 3 of 7.
