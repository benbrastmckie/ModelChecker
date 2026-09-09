# Implementation Summary: ILMC settled-imposition verifiers (plan 02)

- **Task**: 185 - Design and test hyperintensional counterfactual verifiers
- **Plan**: `plans/02_ilmc-settled-imposition-verifiers.md` (7 phases, all `[COMPLETED]`)
- **Status**: [COMPLETED]
- **Branch**: `counterfactual-verifier-semantics`
- **Session**: sess_1788911899_64b5b6
- **Deliverable**: `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_clauses.md` — recommends `ILMC` (`\boxrightILMC`), with the discriminating evidence, an explicit Concessions section, and Further Tests per undiscriminated pair.

## What was built

| Phase | Commit | Outcome |
|-------|--------|---------|
| 1 Recover the stashed Z3 substrate | `64eb483b` | `candidates.py` (I, W, L), 44 cross-validation tests and the `get_operators()` merge restored from `stash@{0}` by explicit path. The full-suite run exposed a pre-existing bound-variable capture in `CounterfactualOperator.true_at`/`false_at` (fixed name `t_cf_u` reused at every nesting level; a consequent-position counterfactual lost its evaluation world). Fixed with per-call fresh names; semantics verbatim; regression test added. |
| 2 Port research clauses and witness frames | `fa13209d` | `frame_oracle.py` states all 24 keys (exact family, settled-exact, `SR`/`SRC`, `ILC`/`ILM`/`ILMC`, `XE`); `tests/witness_frames.py` (F3, G, G2, F3z, SRC-null); per-key F3 pins from a pre-port capture; research script rewired, `f3` output byte-identical. |
| 3 Oracle structure characterization | `90b3fda9` | `tests/test_candidate_structure.py` (39): n=3 exhaustive and n=4 seeded counts, proper-verifier tallies, F4 characterization (0 mismatches / 3,228 true worlds), Frame G / F3z / SRC-null separations; `baselines/04_structure-matrix.json`. Every research count matched. |
| 4 Oracle nested logic and hyperintensionality | `e62aa784` | `tests/test_candidate_logic_oracle.py`: F7 profile and F8 counts pinned on the research seeds; strict-collapse mechanism; Frame G2; baselines 06, 07. One report figure corrected (`SR`/`SRC` 403, not 428). |
| 5 Z3 operators ILC, ILMC, MC | `08cb3076` | `\boxrightILC`, `\boxrightILMC`, `\boxrightMC` + might variants via `il_verifier_at`/`il_falsifier_at`, `settler_at`, `minimal_clause`, `closure_clause`; 86 cross-validation tests (Python side == oracle == Z3 side at every world; predicate == direct encoding). Cost gate: direct encoding retained (`ILMC` nested at N=4 in 1.1 s; `baselines/08_nesting-cost.json`). |
| 6 Discriminating examples and Z3 matrices | `5806c5e9` | `candidate_examples.py` (nested schemata, constitutive comparison, regression substitution, curated runnable collection); `tests/test_candidate_logic.py` (76): all 36 nested cells match the oracle profile at N=3; constitutive comparison at N=3/N=4; regression identical across candidates (`baselines/05_regression-matrix.json`). New evidence: Z3 finds `\equiv` countermodels for `ILC`/`ILMC` at N=4 (none for `W`/`L`/`MC`), and 20,000-model oracle samples at n=4 hold possible-state separations for `ILMC`/`ILC` and none for `L`/`MC` (baselines 09, 10; `tests/n4_separation_witnesses.json`). |
| 7 Recommendation, docs, cleanup | this commit | `report/verifier_clauses.md`; `README.md` and `tests/README.md` updated (directory structure, candidate operator table, corrected verification-semantics section, example collections, test methodology); stash dropped; snapshot marker and patch removed. |

## Recommendation (from the report)

`ILMC`: `s` verifies `A □→ B` iff `s` is a fusion of parthood-minimal states `t` such that imposing any `A`-verifier on `t`, or on any world containing `t`, reaches only `B`-worlds; falsifiers dually. It is the only clause measured that is context-free, built from the imposition machinery, sound/sufficient/exclusive/exhaustive/fusion-closed on every population, hyperintensional on possible states at four atoms (Z3-confirmed at N=4 via `\equiv`), non-strict at nested antecedents with the base counterfactual profile, and supplied with possible proper verifiers in most contingent models from n=4 on. `ILC` is the fully mechanical control (same structure; strict collapse under nesting). Concessions: every possible verifier is a settler; V3 is a minimality step (admitted by the prior user decision); at n=3 nothing proper verifies; impossible members are visible to `\equiv`; nested truth values do not separate `ILMC` from `MC` on any sampled population (the separation is in the proposition); tensed generalization not addressed; the existing `\boxright` is untouched.

## Verification

- Counterfactual test directory: 251 tests (before Phase 6) and the Phase 6/7 additions all green; full logos suite 747 passed (baseline 452 + 295 new); `code/tests/` 680 passed, 5 skipped.
- `./dev_cli.py candidate_examples.py` runs the curated collection with the pinned outcomes.
- Task-number references in `code/`: manual grep clean (`check-task-references.sh` rejects `code/` as a scope, so the mechanical lint could not be run there).

## Plan Deviations

- Phase 1: `operators.py`'s operator classes are not byte-identical to HEAD — `true_at`/`false_at` draw fresh bound-variable names per call to fix a capture defect exposed by the recovered tests. Semantics and the 37 examples' expectations unchanged; pinned by `test_status_quo_audit.py::test_nested_consequent_keeps_its_evaluation_world`.
- Phase 2: F3 pins are a JSON data file (`tests/f3_candidate_sets.json`) generated before the port, because the archived text output truncates long set lines; `frame_g()` carries only `A`, `B` because the research script's `C = ({c},{y})` violates the letter constraints on that frame (caught by the RED constraint test).
- Phase 4: the `SR`/`SRC` same-truth-set count is pinned at 403 (mechanical), correcting the research report's prose figure 428.
- Phase 6: the small-frame-coincidence hypothesis for the constitutive comparison was overturned (Z3 countermodels at N=4 for `ILC`/`ILMC`); two extra baselines (09, 10) and one test-data file record it.
- Phase 7: `check-task-references.sh` does not accept `code/` as a scope; a manual grep was used instead.

## Findings for follow-up (not in scope)

- `imposition/operators.py` uses the same fixed bound-variable names (`t_imp_x`/`t_imp_u`) and is exposed to the same nested-consequent capture; worth its own task.
- The research report's F8 prose figure (428) and its small-frame-coincidence reading are superseded by the pinned tests; the report itself was left as the historical record.
