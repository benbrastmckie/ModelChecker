# Phase 5 Handoff (plan 02): task 185

## Immediate Next Action

Open Phase 6: `candidate_examples.py` (nested schemata, constitutive comparison, regression substitution per candidate), `tests/test_candidate_logic.py` (Z3 outcomes vs the oracle profile), the once-run regression matrix (`baselines/05_regression-matrix.json`), and the additive `counterfactual_candidate_examples` collection in `examples.py`.

## Current State

Phase 5 [COMPLETED]. `candidates.py` implements `\boxrightILC` (`SettlingImpositionClosureCounterfactual`), `\boxrightILMC` (`ExactSettlingImpositionCounterfactual`) and `\boxrightMC` (`GeneratedSettlerCounterfactual`) plus might variants, via `il_verifier_at` / `il_falsifier_at` (truth clause at the state and settling by imposition), `settler_at` (memoized per concrete state), and `minimal_clause` (concrete-state iteration). `CANDIDATE_OPERATORS` has six keys, `CANDIDATE_ROLES` names each role, `__init__.py` exports them. `test_candidate_operators.py` (86 tests) cross-validates every candidate: Python side == oracle == Z3 side at every evaluation world (context-freedom), truth/falsity complementary at worlds, predicate == direct encoding on the nested example. Cost probe recorded in `baselines/08_nesting-cost.json`: direct encoding retained. Full logos suite 666, counterfactual dir 251, all green.

## Key Decisions Made

- `I(t)` for a concrete state is the memoized `truth_at_world(t)` term (the truth clause reads its world slot as a plain state), so `IL(t)` shares subterms with the settler clause; that sharing is what keeps ILMC's four quantifier layers at ~1 s for N=4.
- `settler_at` memoization added after `MC-CF_CM_1` took 27 s unmemoized (now 2.4 s).
- Minimality over a symbolic state is encoded as `Implies(And(is_part_of(t, s), t != s), Not(member(t)))` over concrete `t`; over a concrete state the proper parts are selected in Python.

## Deviations from Plan

- None (the plan's `il_clause`/`minimal_clause` names became `il_verifier_at`/`il_falsifier_at`/`minimal_clause`).

## What NOT to Try

- Do not evaluate `extended_verify` under the predicate encoding after solving (phase-3 handoff rule still binding); tests pass `DIRECT` explicitly.

## References

- Plan: `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/plans/02_ilmc-settled-imposition-verifiers.md`, Phase 5 of 7.
