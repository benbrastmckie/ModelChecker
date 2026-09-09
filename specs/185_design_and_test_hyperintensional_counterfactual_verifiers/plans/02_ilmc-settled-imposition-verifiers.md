# Implementation Plan: Task #185

- **Task**: 185 - Design and test hyperintensional counterfactual verifiers
- **Status**: [NOT STARTED]
- **Effort**: 12 hours
- **Dependencies**: None (phases 1-2 of the superseded plan `plans/01_counterfactual-verifier-candidates.md` are committed at `24998369` and `9a706717` and are inherited as prerequisites, not repeated)
- **Research Inputs**: specs/185_design_and_test_hyperintensional_counterfactual_verifiers/reports/01_exact-imposition-verifier-clauses.md; prior decision (`.decisions.json`, cycle 2): admit the minimality step, plan around ILMC as primary with ILC as control
- **Artifacts**: plans/02_ilmc-settled-imposition-verifiers.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The research round characterized the whole design space the task opened and settled the candidate roster: the exact-imposition family (consequent *verified* by a designated part, verifier composed from those parts) cannot verify any genuinely counterfactual truth under the fixed truth clause (report F4), while settler-selection by imposition -- `IL` = Reading I at `s` AND settling by imposition -- yields the two live candidates `ILC` (fusion closure of `IL`) and `ILMC` (fusion closure of the parthood-minimal `IL` members), both sound, sufficient, exclusive, exhaustive, fusion-closed, context-free, hyperintensional, and with possible verifiers properly below world states in most contingent models from n=4 on (F5, F8). The user admitted the minimality step (V3); `ILMC` is the primary candidate, `ILC` the fully mechanical control. This plan turns that oracle-based evidence into repository-tracked, reproducible measurement: it ports the research clauses and witness frames into the committed oracle with characterization tests; recovers the stashed Z3 substrate and adds `ILC`, `ILMC`, `MC` as Z3 operators alongside `I`, `W`, `L` (six candidates plus might variants, cross-validated Python side == oracle == Z3 side); adds the nested-antecedent and constitutive example collections the existing 37 examples cannot supply (F10); and writes the recommendation naming `ILMC`, its discriminating evidence, its concessions, and the further tests where the evidence does not separate candidates. Definition of done: every claim in the recommendation is backed by a test in `counterfactual/tests/` or a saved baseline; the existing operator, its 37 examples, and their expectations are untouched.

### Research Integration

Findings carried into the plan from `reports/01_exact-imposition-verifier-clauses.md`:

- **F1**: phases 1-2 of the earlier plan are green (24 oracle/audit tests); the earlier phase 3 (`candidates.py`, 44 cross-validation tests, `get_operators()` merge, phase-3 handoff) sits in `git stash@{0}` (`stash@{0}^3` holds the untracked files). Phase 1 below recovers it rather than rewriting it.
- **F2**: report 02's F3 refutation of Reading I is CONFIRMED on all four counts and strengthened (null state is an `I`-falsifier). `I` is the refuted control, kept for the tables.
- **F3 / F4**: the exact family (`XS`, `XSr`, `XPe`, `XPer`, `XPa`, `XPar`, `XSx`, `SB`, `SAB`, `SX*`) is out: a true world contains an exact verifier iff every alternative carries a `B`-verifier already part of that world (0 mismatches over 3,515 true worlds), so the family gives up sufficiency and exhaustivity, and its self-based members soundness. Retained oracle-only for the comparison tables and the F4 characterization test.
- **F5**: `IL` differs from `L` on Frame G (7 atoms); `ILMC` differs from `MC` there (`ILMC` excludes antecedent-incompatible settlers `a'`, `y`). At n <= 4 the sets coincide on possible states -- Z3 tests at N <= 4 must not be read as showing coincidence.
- **F6**: the remainder clause `SR`/`SRC` (task item (c)) is the best clause without minimality but is insufficient at holistic worlds (Frame F3z) and antecedent-incompatible worlds (null remainder); recorded, not recommended.
- **F7**: nested-antecedent profile -- `ILMC`/`MC`: identity and MP valid, antecedent strengthening invalid, `[](X -> C) |- X []-> C` valid, converse invalid (base counterfactual profile); `ILC`/`W`/`L`: strict collapse both directions; `I`: identity fails.
- **F8**: Frame G2 (8 atoms) separates `ILC`/`ILMC` propositions from `L`/`MC` for two counterfactuals with the same truth-set; for `ILMC` the difference shows in nested truth values as well.
- **F9**: report 02's F4 impossibility claim is refuted by `IL*`; what survives is that possible verifiers are settlers and that keeping every true world as a verifier collapses nested antecedents.
- **F10**: regression over the 37 existing examples is provably identical across candidates; run once as a sanity check, not as evidence.
- **F11**: Z3 notes -- concrete-state iteration instead of `utils.ForAll`, memoized per-world truth subterms, `settler_clause`/`closure_clause` already in the stash, minimality as `IL(s) ∧ ∀t ⊏ s. ¬IL(t)`, predicate encoding (`cf_true(w)`, `il(s)`) as the cost mitigation.

### Prior Plan Reference

`plans/01_counterfactual-verifier-candidates.md` (status `[IMPLEMENTING]`, phases 1-2 `[COMPLETED]`) is superseded by this file: its candidate roster (`I, W, L, M, MC, IL`) predates the re-scoping and the research, and its phases 3-8 are replaced. Lessons carried over: the oracle-first / Z3-confirm split was the right instrument choice (every research result came from the oracle in seconds); the 1-2 h phase sizing held for phases 1-2 (handoffs record no overrun); the cost risk for nested Z3 searches was over-estimated (1.2 s at N=4 with concrete-state iteration) but `ILMC` adds two quantifier layers, so the cost gate is kept. The stashed phase-3 handoff's "What NOT to Try" (never evaluate a fresh truth predicate after solving) is binding on Phase 5.

### Roadmap Alignment

No ROADMAP.md was provided for this task.

## Candidate Roster

Notation as in the research report F3: `W` worlds; `|A|± = (V_A, F_A)`; `[s]_a` = `max_compatible_part`; `Alt(s, a)` = `is_alternative(u, a, s)` with `s` in the world slot; `T(w)` the fixed truth clause; settler: `∀w ∈ W. s ⊑ w -> T(w)`.

| Key | Z3 operator | Role | Verifiers `V` | Falsifiers `F` |
|-----|-------------|------|---------------|----------------|
| SQ | `\boxright` (untouched) | status quo | `{w}` at eval world `w` (Z3 side); all true worlds (Python side) | dual |
| I | `\boxrightI` | refuted control | `{s : ∀a ∈ V_A ∀u ∈ Alt(s,a). B true at u}` | `{s : ∃a ∃u ∈ Alt(s,a). B false at u}` |
| ILC | `\boxrightILC` | mechanical control (D2) | fusion closure of `V_I ∩ settlers` | closure of `F_I ∩ co-settlers` |
| ILMC | `\boxrightILMC` | **primary (D1)** | closure of minimal elements of `V_I ∩ settlers` | closure of minimal `F_I ∩ co-settlers` |
| W | `\boxrightW` | disqualified baseline | closure of true worlds | closure of false worlds |
| L | `\boxrightL` | disqualified baseline | settlers | co-settlers |
| MC | `\boxrightMC` | disqualified baseline | closure of minimal settlers | closure of minimal co-settlers |
| IL, ILM, M, SR, SRC, exact family | oracle only | tables | as in report F3 | as in report F3 |

`ILMC` stated as an exact clause (report D1): `s` verifies `A []-> B` iff `s` is a fusion of one or more states `t` with (V1) every alternative to `t` under any `A`-verifier makes `B` true; (V2) every alternative, under any `A`-verifier, to any world containing `t` makes `B` true; (V3) no proper part of `t` satisfies V1 and V2. Falsifiers dually. Every might variant is a `DefinedOperator` with `derived_definition = ¬(A \boxrightK ¬B)`.

## Goals & Non-Goals

**Goals**:
- Make the research evidence reproducible in the repository: oracle clauses for every key in the report's F3 table, the witness frames G, G2, F3z and the SRC null-remainder model, and characterization tests pinning F4 (exact-family characterization), F5 (structural profile and Frame G separations), F6 (SRC insufficiency), F7 (nested logic), F8 (hyperintensionality on G2).
- Implement `ILC`, `ILMC`, `MC` as Z3 operators next to the recovered `I`, `W`, `L`, each cross-validated (Python side == oracle == Z3 side at every world) on solved models, with the nesting-cost gate decided on measurement.
- Add discriminating example collections (nested-antecedent schemata, constitutive comparison) and the once-run regression matrix, keeping the 37-example baseline untouched.
- Deliver the recommendation document naming `ILMC`, the model-based evidence separating it from `ILC`, `I`, `W`, `L`, `MC`, `SRC` and the exact family, its explicit concessions, and the further test for each undiscriminated pair.

**Non-Goals**:
- Modifying `CounterfactualOperator`, `MightCounterfactualOperator`, `LogosSemantics.true_at`/`is_alternative`, any frame constraint, or the 37 examples' expectations.
- Re-running the design-space exploration (the exact family and `SR`/`SRC` are measured, not redesigned).
- Tensed generalization; any change to `~/Projects/Logos/**`.
- Z3 reproduction of the 7-9 atom witness frames (oracle-only by design).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Small-frame coincidence (`IL = L`, `ILMC = MC` on possible states at N <= 4) is read as evidence that the mechanism constraint is idle | H | M | Frame G/G2 separations are pinned as oracle tests (Phase 3, 4); the recommendation cites them, and every Z3 table carries a note that N <= 4 cannot separate `ILMC` from `MC` |
| `ILMC` Z3 clause (closure, minimality, settling, imposition around the truth clause) is too slow at N=4 for nested examples | M | M | Phase 5 cost probe with a 60 s budget; on overrun, switch to the stashed predicate encoding extended with an `il(s)` predicate (report F11); N=3 remains the floor for every characterization test |
| Stash recovery reapplies stale edits (old plan, `.lock/holder.json`, `events.jsonl`) | M | M | Phase 1 restores only the four source/test paths and the handoff by explicit path (`git checkout 'stash@{0}' -- <paths>` and `git checkout 'stash@{0}^3' -- <paths>`), never `git stash pop`; the stash is dropped only in Phase 7 on a clean tree |
| Constitutive `\equiv` search with candidate `extended_verify` on both sides is expensive | M | M | N=3 first, `max_time` bounded; a timeout is recorded as inconclusive and Frame G2 (oracle) remains the evidence of record for hyperintensionality |
| Registering six more operators in `get_operators()` changes what every logos consumer loads | M | L | Already exercised by the stashed phase 3 (full logos suite green per its handoff); full suite is the gate in Phases 1, 5, 6, 7; collision check against `imposition/operators.py` aliases retained |
| Regression run (37 examples x 6 candidates) is slow in pytest | L | M | Run once as a recorded script (`baselines/05_regression-matrix.json`); pytest keeps a 4-example guard per candidate |
| Deliverable under `code/` cites task numbers | M | L | Phase 7 runs `bash .claude/scripts/check-task-references.sh`; cite filenames and section headings only |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4, 5 | 1, 2 |
| 3 | 6 | 4, 5 |
| 4 | 7 | 3, 4, 6 |

Phases within the same wave can execute in parallel. Phases 3 and 4 depend on 2 only; Phase 5 depends on 1 and 2.

### Phase 1: Recover the stashed Z3 substrate [NOT STARTED]

**Goal**: Bring the earlier phase-3 work (`candidates.py`, cross-validation tests, `get_operators()` merge) back from `git stash@{0}` by explicit path, confirm it green on the current tree, and commit it so Phase 5 builds on a committed base.

**Tasks**:
- [ ] Verify `git stash list` shows `stash@{0}: On counterfactual-verifier-semantics: git-snapshot-1788911805` and `git show --stat 'stash@{0}^3'` lists `candidates.py`, `tests/test_candidate_operators.py`, `handoffs/phase-3-handoff-20260908T235211Z.md`; abort with a recorded finding if the stash is absent
- [ ] Restore tracked edits by path only: `git checkout 'stash@{0}' -- code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py code/src/model_checker/theory_lib/logos/subtheories/counterfactual/__init__.py`; confirm the diff against `HEAD` touches only `get_operators()` (merge of `candidates.get_candidate_operators()`) and the `__init__.py` exports -- the two operator classes must be byte-identical to `HEAD`
- [ ] Restore untracked files by path: `git checkout 'stash@{0}^3' -- code/.../counterfactual/candidates.py code/.../counterfactual/tests/test_candidate_operators.py specs/185_.../handoffs/phase-3-handoff-20260908T235211Z.md`
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/ -q`; expected 24 (oracle/audit) + 37 (examples) + 44 (candidate cross-validation) green
- [ ] Run the full logos suite `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -q` and compare with `baselines/01_logos-suite-baseline.txt` (452 passed); the new count must be the baseline plus the recovered tests
- [ ] Add a module-docstring note to `candidates.py` naming the roster this plan implements (`I`, `W`, `L` now; `ILC`, `ILMC`, `MC` in Phase 5) and that `IL`, `ILM`, `M`, `SR`, `SRC` are oracle-only
- [ ] Do NOT `git stash pop` or `git stash drop` in this phase

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: The stash holds exactly two tracked source edits (`operators.py`, `__init__.py`) and two untracked source files (440-line `candidates.py`, 207-line `test_candidate_operators.py`, 44 tests) plus the handoff; confirm with `git show --stat 'stash@{0}'` / `'stash@{0}^3'` before restoring. If the stash also holds edits the research did not list, record them in the phase handoff and restore only the paths above.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` - restored from stash, docstring note
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` - `get_operators()` merge only
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/__init__.py` - exports
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_operators.py` - restored
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/handoffs/phase-3-handoff-20260908T235211Z.md` - restored record

**Verification**:
- `git diff HEAD -- .../operators.py` shows changes inside `get_operators()` only
- Counterfactual tests directory green; full logos suite green at baseline + recovered count
- `git status` shows no stray restored files (old plan, `.lock`, `events.jsonl` untouched)

---

### Phase 2: Port the research clauses and witness frames into the oracle [NOT STARTED]

**Goal**: Move every candidate clause and every witness frame the research defined out of `baselines/03_research-exploration.py` / `03_research-witnesses.py` and into the committed oracle, so later phases and the recommendation cite tracked code rather than a task-directory script.

**Tasks**:
- [ ] RED: extend `tests/test_frame_oracle.py` with a test asserting `Evaluator.counterfactual_proposition` accepts every key in `("SQpy","I","W","L","M","MC","IL","ILC","ILM","ILMC","SR","SRC","XS","XSr","XPe","XPer","XPa","XPar","XSx","SB","SAB","SX","SXr","SXC")` on the F3 frame and, for each key, returns the exact sets recorded in `baselines/03_research-exploration-output.txt` (`f3` mode) -- transcribe the F3-frame verifier/falsifier sets per key into the test as the pinned expectation
- [ ] Port `composable`, `composable_subset` and the `XEvaluator` clause bodies (`pairs`, `b_options`, `br_options`, `comp_at`, the per-key branches) into `frame_oracle.py`'s `Evaluator` as methods, keeping the committed keys' behavior unchanged; delete `XEvaluator` from the baselines script by replacing it with an import of the ported `Evaluator` (the script remains runnable for reproduction)
- [ ] Create `tests/witness_frames.py` with builders `frame_f3()`, `frame_g()`, `frame_g2()`, `frame_f3z()`, `src_null_remainder_model()` transcribed from `03_research-witnesses.py` and the `g` mode, each returning `(Frame, Interpretation)` with atom names and the letters' propositions as in the report Appendix; move the existing F3 fixture in `test_frame_oracle.py` to use `frame_f3()`
- [ ] RED tests for the witness builders: each frame's computed `worlds` equals the declared world list; each letter proposition satisfies `letter_constraints_hold`
- [ ] Add `Evaluator.identical_proposition(phi, psi)` (the `\equiv` truth: same verifier and falsifier sets) so hyperintensionality can be measured in the oracle without Z3
- [ ] Re-run `python baselines/03_research-exploration.py f3` after the port and diff against the archived output to prove the port is behavior-preserving

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: 17 new clause keys (`ILC ILM ILMC SR SRC XS XSr XPe XPer XPa XPar XSx SB SAB SX SXr SXC`) and 5 witness builders are ported; confirm by the key-coverage test enumerating exactly the 24-key tuple above and by the `f3`-mode diff being empty.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py` - clause port, `identical_proposition`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/witness_frames.py` - new fixture module
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_frame_oracle.py` - key coverage, F3 per-key pins, witness-frame sanity
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/03_research-exploration.py` - imports the ported clauses

**Verification**:
- `pytest .../tests/test_frame_oracle.py -q` green (existing 20 + new)
- `python baselines/03_research-exploration.py f3` output identical to the archived `f3` section

---

### Phase 3: Oracle characterization: structure, F4, and the Frame G / F3z separations [NOT STARTED]

**Goal**: Pin the research's structural findings as characterization tests so the recommendation's soundness/sufficiency/closure/proper-verifier claims and the mechanism-constraint separations are reproducible from `pytest` alone.

**Tasks**:
- [ ] RED: `tests/test_candidate_structure.py` -- exhaustive n=3 sweep (`enumerate_models(3)`, 3,204 models, 24 contingent) parametrized over `I, ILC, ILMC, W, L, MC, SRC, XPe, XPa, XS`: per candidate, count models failing each `measure` property (closure V/F, `exclusive_compat`, `exhaustive`, bridge soundness both polarities, sufficiency both polarities, `impossible_harmless_*`) and pin the counts from report F4/F5/F6 tables (`ILC`/`ILMC`/`W`/`L`/`MC`: 0 everywhere; `XS`: sound 6, sufficient 1554/1644, exhaustive 3192; `XPe`: closure 3/18; `SRC`: closure 0/0; `I`: the F3-style failures) -- if a count differs, the test fails and the report is corrected, not the test
- [ ] Proper-verifier desideratum: pin per candidate the count of contingent models with a possible verifier properly below a world at n=3 exhaustive (`ILMC`: 0/24 V, 24/24 F) and on the seeded n=4 sample (`enumerate_models(4, limit=300, seed=...)` -- use the seed the research script uses; `ILMC`: 6/11), and pin the F3-frame `ILMC` proper verifiers `{a.p', a.q', a.b, a.p'.b, a.q'.b}` and `IL`'s closure witness `a.p.p' ⊔ a.q.q'`
- [ ] F4 characterization test: over n=3 exhaustive models, assert `XPe` has a verifier below true world `w` iff every `(a,u) ∈ P(w)` has some `b ∈ V_B` with `b ⊑ u` and `b ⊑ w` (port `characterize_exact_sufficiency`); 0 mismatches
- [ ] Frame G tests: `y` and `a'` are settlers but not `I`-verifiers (`Alt(y, a)` contains `u = a.x.b'`); `IL ≠ L` and `ILMC ∩ possible = {c, b, c.b}` versus `MC`'s set containing `a'`, `y`
- [ ] Frame F3z tests: `T(w4)` true; `SR`/`SRC` have no verifier and no falsifier at `w4` (exhaustivity fails); `ILMC` verifies `w4` via `p'.z`, `b.z`, `p'.b.z`
- [ ] SRC null-remainder tests: at world `d` the counterfactual is false, `[d]_b = {null}`, `SRC` has no falsifier below `d`, `ILMC`/`MC` give `d`
- [ ] Write the property matrix to `baselines/04_structure-matrix.json` (candidate x property -> count or witness) from the test run (a small writer in the test module gated on an env var, or a `python -m` entry in `frame_oracle.py`)

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: 3,204 models at n=3 with 24 contingent, 300 sampled at n=4 with 11 contingent (report F5); confirm by asserting the population sizes in the sweep test before pinning any count. If the enumerator's sample seed is not recoverable from the research script, pin n=3 exhaustive counts only and record the n=4 figures as unpinned.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_structure.py` - new
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py` - sweep/serialization helpers as needed
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/04_structure-matrix.json` - results

**Verification**:
- Every (candidate, property) cell in the matrix is a count with its population size or a named witness; no cell is inherited from another candidate
- Sweep runtime under 60 s so the tests stay in the default run

---

### Phase 4: Oracle characterization: nested logic and hyperintensionality [NOT STARTED]

**Goal**: Pin the nested-antecedent logic profile per candidate (F7) and the same-truth-set/distinct-proposition results (F8), including the Frame G2 separation that Z3 at N <= 4 cannot show.

**Tasks**:
- [ ] RED: `tests/test_candidate_logic_oracle.py` -- port `logic_sweep` (identity `X []-> X`, MP `X, X []-> C |- C`, AS `X []-> C |- (X ∧ D) []-> C`, `[](X -> C) |- X []-> C`, converse, might-identity; `X := A []-> B` under the candidate) over the seeded n=3 sample (1,500 models) and pin the F7 counts: `ILC`/`W`/`L`: 0 everywhere; `ILMC`/`MC`: identity 0, MP 0, AS 361, strict->cf 0, cf->strict 700; `SRC`: AS 200, cf->strict 372; `I`: identity 22; `XPa`: MP 389
- [ ] RED: port `hyper_sweep` (same truth-set, distinct proposition, `A []-> B` vs `C []-> D`) over the same sample and pin: `I` 1, settler-based keys 0, `SR` 428, `XS` 482
- [ ] Frame G2 tests: `A []-> B` and `C []-> D` have the same truth-set; `L`/`MC` give identical propositions; `ILC` and `ILMC` give distinct ones (`x'` verifies the first only; `a'`, `y` the second only); under `ILMC`, `(A []-> B) []-> C` is false at every world while `(C []-> D) []-> C` is true at three of four; `identical_proposition` returns False for `ILC`/`ILMC` and True for `L`/`MC`
- [ ] The strict-collapse mechanism test: on any model, `ILC`'s verifier set contains every true world, and `X []-> C` under `ILC` is true at `w` iff `[](X -> C)` is (pin on the n=3 sample); under `ILMC` exhibit one sampled model where they differ and save it to `baselines/06_logic-matrix.json`
- [ ] Write the logic and hyperintensionality matrices (`baselines/06_logic-matrix.json`, `baselines/07_hyperintensionality.json`) with every countermodel's frame/interpretation serialized via `model_to_dict`

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: the seeded sample is 1,500 models at n=3 and 723 same-truth-set pairs; confirm the sizes before pinning counts. If the seed cannot reproduce the research sample, pin the qualitative profile (0 vs nonzero) and record the counts as unpinned.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_logic_oracle.py` - new
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/06_logic-matrix.json`, `07_hyperintensionality.json` - results

**Verification**:
- Per candidate, each of the six principles has a pinned outcome; `ILMC`'s profile equals the base counterfactual profile of `examples.py` (identity/MP valid; strengthening, `cf -> strict` invalid)
- Frame G2 tests pass and are cited by name in the recommendation

---

### Phase 5: Z3 operators ILC, ILMC, MC with cross-validation and the cost gate [NOT STARTED]

**Goal**: Add the primary candidate, its control, and the remaining baseline as Z3 operators sharing `true_at`/`false_at` verbatim, prove on solved models that each operator's Python side equals the oracle and its own Z3 clause at every world, and decide the encoding on measured cost.

**Tasks**:
- [ ] RED: extend `test_candidate_operators.py` `KEYS` with `ILC`, `ILMC`, `MC`: registration of `\boxrightILC`, `\boxrightILMC`, `\boxrightMC` and `\diamondright*`, parsing inside nested formulas, no collision with `imposition/operators.py` aliases, and the three existing cross-validation tests (Python side == oracle; Z3 side == Python side at every world; truth/falsity complementary at worlds) on `CF_CM_1` (N=4), `CF_CM_7`, `CF_CM_19`, `NESTED_ANTECEDENT` (N=3)
- [ ] `candidates.py`: add `il_clause(state, leftarg, rightarg, eval_point)` = `ImpositionLocalCounterfactual.verifier_clause` ∧ `settler_clause`; `minimal_clause(state, member)` = `member(state) ∧ ⋀_{t ⊏ state} ¬member(t)` iterating concrete states (per the phase-3 handoff, never `utils.ForAll`); dual falsifier clauses via `falsifier_clause` ∧ co-settling
- [ ] Implement `SettlingImpositionClosureCounterfactual` (`\boxrightILC`: `closure_clause(state, il_clause)`), `ExactSettlingImpositionCounterfactual` (`\boxrightILMC`: `closure_clause(state, lambda t: minimal_clause(t, il_clause))`), `GeneratedSettlerCounterfactual` (`\boxrightMC`: `closure_clause(state, lambda t: minimal_clause(t, settler_clause))`); Python sides via `SolvedModelView` + `fusion_closure`/`minimal_elements`, mirroring the oracle keys exactly
- [ ] Register the three primitives and factory-built might variants in `CANDIDATE_OPERATORS`/`MIGHT_OPERATORS`; `get_operators()` needs no further change
- [ ] Cost probe (recorded, not a test): time `((A \boxrightK B) \boxrightK C)` with premise `\neg (A \boxrightK B)` for `K ∈ {ILC, ILMC, MC}` at N=3 and N=4, `max_time=60`, both encodings where available; write `baselines/08_nesting-cost.json`
- [ ] Decision gate: if `ILMC` exceeds 60 s at N=4, extend the stashed `truth_predicate` pattern with an `il_<n>(s)` predicate (2^N defining constraints appended to `semantics.frame_constraints` before solving) and rewrite `ILC`/`ILMC` over it; re-run the probe and the cross-validation tests; otherwise record "direct encoding retained" in the JSON header
- [ ] Full logos suite green; counterfactual test directory green

**Timing**: 2 hours

**Depends on**: 1, 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: three primitive classes and three might variants complete the six-candidate roster; confirm by the registration test enumerating exactly twelve candidate operator names. The N=4 nested cost for `ILMC` is hypothesized under 60 s with the direct encoding given the 1.2 s single-layer measurement; the probe decides.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` - three operators, `il_clause`, `minimal_clause`, optional `il` predicate
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_operators.py` - extended `KEYS` and coverage
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/__init__.py` - exports
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/08_nesting-cost.json` - timings and the decision

**Verification**:
- All six candidates pass the three cross-validation tests on the four examples; context-freedom holds (Z3-side set identical at every evaluation world)
- `baselines/08_nesting-cost.json` records N=3/N=4 times per candidate and the encoding decision

---

### Phase 6: Discriminating example collections and the Z3 logic and regression matrices [NOT STARTED]

**Goal**: Give the theory the examples it lacks (F10) -- nested-antecedent schemata and the constitutive comparison per candidate -- confirm the oracle's F7/F8 profile through Z3 at N <= 4, and record the once-run regression matrix.

**Tasks**:
- [ ] Create `counterfactual/candidate_examples.py`: `nested_examples(key)` building, per candidate key, the six schemata of Phase 4 as `(premises, conclusions, settings)` triples at N=3 (N=4 where Phase 5 cleared it) with `expectation` set from the oracle profile (`ILMC`/`MC`: identity and MP theorems, AS and `cf -> strict` countermodels, `strict -> cf` theorem; `ILC`/`W`/`L`: all four collapse-related schemata theorems; `I`: identity countermodel); `constitutive_examples(key)` with registry `['extensional','modal','constitutive','counterfactual']`: premise `\Box ((A \boxrightK B) \leftrightarrow (C \boxrightK D))`, conclusion `((A \boxrightK B) \equiv (C \boxrightK D))`, N=3 and N=4; `regression_examples(key)` substituting `\boxright`/`\diamondright` in `examples.unit_tests` via `substitute_candidate`
- [ ] RED: `tests/test_candidate_logic.py` characterization tests over `nested_examples` for the six candidates via `harness.outcome`, asserting the oracle-pinned outcome; a timeout is recorded as inconclusive with N and `max_time` and fails only if the oracle test of Phase 4 is also absent
- [ ] Constitutive comparison per candidate: record found/none/timeout; hypothesis (F8, small-frame coincidence): a countermodel for `I` only, none for the settler-based keys at N <= 4; the test asserts the recorded outcome and its docstring points to the Frame G2 oracle test as the evidence that `ILC`/`ILMC` are nonetheless hyperintensional
- [ ] Regression matrix: run `regression_examples(key)` for all six candidates once (script or env-gated test), diff against `baselines/01_counterfactual-examples-baseline.txt`, and write `baselines/05_regression-matrix.json`; expected identical for every candidate (F10) -- state this explicitly in the file rather than reporting an empty diff silently; keep a 4-example pytest guard per candidate (`CF_CM_1`, `CF_CM_7`, `CF_TH_2`, `CF_TH_11`)
- [ ] Register `counterfactual_candidate_examples` in `examples.py` as a separate collection (curated subset: `ILMC` identity, MP, AS, `cf -> strict`; `ILC` collapse; constitutive comparison for `ILMC`) that is NOT merged into `unit_tests`, with the `example_range`/collections comment block extended; run `cd code && ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py` once for the dual-methodology check
- [ ] Full logos suite green; `PYTHONPATH=code/src pytest code/tests/ -q` green

**Timing**: 2 hours

**Depends on**: 4, 5

**Verification Tier**: full

**Scope Hypothesis**: 6 schemata x 6 candidates = 36 nested examples plus 6 constitutive examples and 37 x 6 = 222 regression runs; confirm the counts by `len()` assertions in the generator tests. If N=4 nested runs exceed the budget for `ILMC`, the nested collection runs at N=3 and the matrix records the N used per cell.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py` - new
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_logic.py` - new
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py` - additive collection only
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/05_regression-matrix.json` - results

**Verification**:
- Every (candidate, schema) cell has an outcome (theorem / countermodel / inconclusive with N, `max_time`); the `ILMC` and `ILC` rows match Phase 4's oracle profile
- `test_counterfactual_examples.py` (37 examples) unchanged and green; regression diff recorded per candidate

---

### Phase 7: Recommendation document, documentation, cleanup, and summary [NOT STARTED]

**Goal**: Deliver the recommendation naming `ILMC`, the discriminating evidence, its explicit concessions, and the further tests, with the subtheory documentation updated and the stash retired.

**Tasks**:
- [ ] Write `counterfactual/report/verifier_clauses.md` (no task-number references; cite filenames, test names, and section headings): the governing criterion and mechanism constraint; the roster with each clause stated; the F3 verdict (confirmed, strengthened); the exact family's characterization and what it gives up; the structure matrix; the nested-logic matrix; the hyperintensionality results with Frame G2; the regression result; the verdict on the settler argument (impossibility refuted by `IL*`; what survives); the recommendation `ILMC` with a dedicated "Concessions" section (every possible verifier is a settler; V3 is a minimality operation of the same kind as `max_compatible_part`'s maximality; in some contingent models -- all at n=3 -- nothing proper verifies, only proper falsifiers exist; the tensed generalization is not addressed); `ILC` as the mechanical control and what choosing it would concede (strict collapse); `SRC` recorded with its two insufficiency modes; and a "Further Tests" section naming, for `ILMC` vs `MC` (constitutive comparison on a Frame-G-type model; conceptual grounds) and `ILC` vs `L`/`W` (`\equiv` on Frame G2, oracle-only), the test that would separate them
- [ ] Update `counterfactual/README.md`: Directory Structure (add `candidates.py`, `candidate_examples.py`, `frame_oracle.py`, `report/verifier_clauses.md`, the new test modules), Operator Reference (candidate operators marked as exploratory alternatives to `\boxright`, with the roster table), Example Collections (the candidate collection), and a pointer from the Verification Semantics section to the report
- [ ] Update `counterfactual/tests/README.md` to describe the oracle, the witness frames, and the characterization-test methodology (pinned oracle outcomes, Z3 confirmation at N <= 4, small-frame coincidence caveat)
- [ ] Run `bash .claude/scripts/check-task-references.sh` over `code/`; fix any hit
- [ ] Complete gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -q` and `PYTHONPATH=code/src pytest code/tests/ -q`; compare against `baselines/01_logos-suite-baseline.txt`
- [ ] After the phase commit, with `git status --porcelain` empty, run `git stash drop 'stash@{0}'` (allowed only on a clean tree per `.claude/rules/git-workflow.md`) and remove `.git-snapshot-marker` and `working-progress-1788911805.patch` from the task directory
- [ ] Write `specs/185_.../summaries/02_ilmc-settled-imposition-verifiers-summary.md` per summary-format.md, pointing at the report, the tests, and baselines `04`-`08`

**Timing**: 1.5 hours

**Depends on**: 3, 4, 6

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_clauses.md` - new (the recommendation)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md` - documentation
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/README.md` - test methodology
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/summaries/02_ilmc-settled-imposition-verifiers-summary.md` - summary

**Verification**:
- The report names exactly one recommended clause, has a "Concessions" section and a "Further Tests" section, and every table cell cites the test or baseline that produced it
- `check-task-references.sh` clean under `code/`; full logos suite and `code/tests/` at or above baseline; stash list empty

## Testing & Validation

- [ ] Phase 1: recovered `test_candidate_operators.py` (44 tests) green with `I`, `W`, `L`; full logos suite at baseline + recovered count
- [ ] Phase 2: every clause key returns the archived F3-frame sets; `f3`-mode output diff empty; witness frames' worlds and letter constraints verified
- [ ] Phase 3: `test_candidate_structure.py` pins the n=3 exhaustive counts, the F4 characterization, Frame G, F3z and null-remainder separations
- [ ] Phase 4: `test_candidate_logic_oracle.py` pins the F7 profile and the Frame G2 hyperintensionality results
- [ ] Phase 5: six candidates pass Python == oracle == Z3 cross-validation at every world; cost decision recorded
- [ ] Phase 6: `test_candidate_logic.py` outcomes match the oracle profile; regression matrix identical across candidates; 37-example baseline untouched and green
- [ ] Phase 7: `check-task-references.sh` clean; `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -q` and `pytest code/tests/ -q` green

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` (recovered, extended with `ILC`, `ILMC`, `MC`)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py` (all research clauses, `identical_proposition`)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/witness_frames.py`, `test_candidate_operators.py`, `test_candidate_structure.py`, `test_candidate_logic_oracle.py`, `test_candidate_logic.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_clauses.md` (the recommendation)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md`, `tests/README.md` (updated)
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/04_structure-matrix.json`, `05_regression-matrix.json`, `06_logic-matrix.json`, `07_hyperintensionality.json`, `08_nesting-cost.json`
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/summaries/02_ilmc-settled-imposition-verifiers-summary.md`

## Rollback/Contingency

All changes are additive on the `counterfactual-verifier-semantics` branch: new modules, new tests, a merged dictionary in `get_operators()`, an additive example collection, and documentation; `CounterfactualOperator`, `MightCounterfactualOperator`, and the 37 baseline examples are never edited, so `git revert` of the phase commits cannot regress them. If the `ILMC` Z3 clause proves infeasible even at N=3 after the predicate encoding, Phases 3-4 (oracle) still carry every structural, logical, and hyperintensionality claim, Phase 6 records the Z3 cells as inconclusive with the encoding tried, and the recommendation stands on the oracle evidence with the Z3 confirmation named as the further test. If the stash is missing, Phase 1 rewrites `candidates.py` from the phase-3 handoff's description (the design is fully recorded there and in report F11) at roughly +1.5 hours.
