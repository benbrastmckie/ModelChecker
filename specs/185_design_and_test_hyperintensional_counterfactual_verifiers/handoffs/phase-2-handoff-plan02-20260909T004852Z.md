# Phase 2 Handoff (plan 02): task 185

## Immediate Next Action

Open Phase 3: `tests/test_candidate_structure.py` -- exhaustive n=3 sweep pinning the F4/F5/F6 counts per candidate, the proper-verifier desideratum, the F4 exact-sufficiency characterization, Frame G / F3z / SRC-null separations, and `baselines/04_structure-matrix.json`.

## Current State

Phase 2 [COMPLETED]. `frame_oracle.py` now states every clause key of the research (`ILC ILM ILMC SR SRC XS XSr XPe XPer XPa XPar XSx SB SAB SX SXr SXC`, plus the context-dependent `XE`) as `Evaluator` methods (`composed_at`, `exact_proposition`, `remainder_proposition`, `context_dependent_proposition`) with module-level `composable`/`composable_subset`, key groups (`IMPOSITION_KEYS`, `BASELINE_KEYS`, `REMAINDER_KEYS`, `EXACT_KEYS`, `SETTLED_EXACT_KEYS`, `CONTEXT_DEPENDENT_KEYS`), `closure_or_empty`, and `Evaluator.identical_proposition`. `tests/witness_frames.py` builds F3, G, G2, F3z and the SRC null-remainder model. `tests/test_frame_oracle.py`: 58 green, including per-key F3 pins from `tests/f3_candidate_sets.json` (generated pre-port). Research script `03_research-exploration.py` imports the ported clauses; its `f3` output is byte-identical to the pre-port capture.

## Key Decisions Made

- Pins are a JSON data file next to the test rather than inline literals: the archived text output truncates long set lines, so it could not serve as the full pin; the JSON was produced from the unported script.
- Frame G carries only `A`, `B`: its research-script `C` letter is not letter-constraint compliant. Every F5 claim about Frame G concerns `A []-> B`; the F8 same-truth-set comparison uses G2, whose four letters are compliant (test-pinned).
- `XE` is grouped with `SQ` as context-dependent (raises without an evaluation world); `ALL_KEYS` = `SQ, SQpy, XE` + 23 candidate keys; `CANDIDATE_KEYS` now has 23 entries, all measured on every n=2 model by the existing enumerator test.

## Deviations from Plan

- Pin format (JSON file) and Frame G letter set, both recorded inline in the plan's Phase 2 tasks.

## What NOT to Try

- Do not regenerate `f3_candidate_sets.json` from the ported oracle; its value is that it predates the port.

## References

- Plan: `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/plans/02_ilmc-settled-imposition-verifiers.md`, Phase 2 of 7.
