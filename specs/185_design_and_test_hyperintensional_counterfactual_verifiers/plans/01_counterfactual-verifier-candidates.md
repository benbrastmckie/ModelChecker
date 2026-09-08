# Implementation Plan: Task #185

- **Task**: 185 - Design and test hyperintensional counterfactual verifiers
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours
- **Dependencies**: None
- **Research Inputs**: None in this repository (no `reports/` artifact this round). Provenance reports read at plan time: `~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/01_counterfactual-null-state-verification.md` and `.../02_context-free-counterfactual-verifiers.md`
- **Artifacts**: plans/01_counterfactual-verifier-candidates.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The logos counterfactual operator (`code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`) currently gives `A \boxright B` the context-dependent verifier set `{w}` at evaluation world `w` (`extended_verify` :74-90), which the governing criterion rejects. This plan adds, alongside the existing operator and without modifying it, one Z3 operator per candidate verification clause (I, W, L, M, MC, IL -- defined under "Candidate Clauses" below) that shares the existing *truth* clause verbatim and varies only `extended_verify` / `extended_falsify` / `find_verifiers_and_falsifiers`. A pure-Python exhaustive frame oracle is the primary measurement instrument (it reproduces report 02's 8-atom refutation frame, which is too large for the Z3 layer because `model_checker.utils.ForAll`/`Exists` expand quantifiers finitely); the Z3 operators are the instrument for logic-level searches (nested-antecedent axioms, strict-conditional collapse, hyperintensionality via `\equiv`) at small `N`. Definition of done: every candidate is measured on every discriminating property listed in the task, the F3 refutation is mechanically confirmed or overturned, an explicit attempt is made to refute report 02's F4 argument, and a recommendation naming one clause with its evidence and concessions is written to the subtheory's `report/` directory.

### Research Integration

No research report exists in this repository for this round; the two provenance reports were read directly. Key inputs carried into the plan:

- Report 02 F2: Reading I's imposition of `a` on an arbitrary state `s` is `{a ⊔ r : r ∈ [s]_a}`; both quantifiers universal for the would-counterfactual. In this codebase that is exactly `semantics.is_alternative(u, a, s)` with `s` in the world slot, so Reading I's verification clause is literally the existing `true_at` evaluated with `s` substituted for the evaluation world.
- Report 02 F3.1: the refutation frame (atoms `{a,a',p,p',q,q',b,b'}`, worlds `w0..w3`, `|A|+={{a}}`, `|A|-={{a'}}`, `|B|+={{b}}`, `|B|-={{b'}}`), and the claimed facts F3.2/F3.3 (verifiers `{p,p'}`, `{q,q'}`; falsifier `{q}`; `T(w0)` false, `T(w1)`, `T(w2)` true, `T(w3)` false).
- Report 02 F4: the settler argument (sound + sufficient + context-free implies verifiers are settlers, and settler-hood is a function of the truth-set). To be tested, not assumed.
- Report 02 F5/F6: Reading W's expected properties (closed, exclusive, exhaustive, bridge biconditional, strict-conditional collapse `X \boxright C <-> \Box(X -> C)` at nested antecedents).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Candidate Clauses

All clauses are stated over states of an untensed logos model. `W` is the set of world states; `T(w)` abbreviates "`A \boxright B` is true at `w`" as computed by the unchanged `CounterfactualOperator.true_at`; `[s]_a` is the set of maximal `a`-compatible parts of `s` (`semantics.max_compatible_part`); `Alt(s, a) = {u ∈ W : ∃r ∈ [s]_a. a ⊔ r ⊑ u}` (`semantics.is_alternative(u, a, s)`). Falsifier sets `F` are the polarity duals stated per candidate. Operator names are hypotheses to be confirmed against the parser (the `\boxrightlogos` alias in `theory_lib/imposition/operators.py` shows alphanumeric suffixes parse).

| Key | Name | Verifiers `V` | Falsifiers `F` | Context-free? |
|-----|------|---------------|----------------|---------------|
| SQ | `\boxright` (status quo, untouched) | `{w}` when `T(w)`, relative to eval world `w` | `{w}` when not `T(w)` | no |
| I | `\boxrightI` (imposition-local) | `{s : ∀a ⊩ A. ∀u ∈ Alt(s, a). B true at u}` | `{s : ∃a ⊩ A. ∃u ∈ Alt(s, a). B false at u}` | yes |
| W | `\boxrightW` (world-state) | fusion closure of `{w ∈ W : T(w)}` | fusion closure of `{w ∈ W : ¬T(w)}` | yes |
| L | `\boxrightL` (settlers) | `{s : ∀w ∈ W. s ⊑ w → T(w)}` | `{s : ∀w ∈ W. s ⊑ w → ¬T(w)}` | yes |
| M | `\boxrightM` (minimal settlers) | parthood-minimal elements of `V_L` | parthood-minimal elements of `F_L` | yes |
| MC | `\boxrightMC` (generated settlers) | fusion closure of `V_M` | fusion closure of `F_M` | yes |
| IL | `\boxrightIL` (settling imposition-local) | `V_I ∩ V_L` | `F_I ∩ F_L` | yes |

Notes the implementer must carry, each a hypothesis for Phase 2/5 to confirm mechanically:
- `V_L` and `F_L` both contain every impossible state (vacuously). Exclusivity is measured over possible states only; the "harmlessness" claim is that impossible members are part of no world.
- `V_M` cannot be closed under fusion unless it is a singleton (the fusion of two distinct minimal elements of an upward-closed set is not minimal). MC is the repair the task names; its soundness (every member a settler) follows from upward-closure of `V_L`. Both facts are to be confirmed by the oracle, not assumed.
- IL is sound (subset of settlers), sufficient (every `T`-world `w` satisfies I at `s = w`, since I at a world is the truth clause), context-free, and mentions `A`'s and `B`'s verifiers, so it is hyperintensional by construction. It is the concrete candidate (6) this plan puts forward against F4. Its open questions are fusion closure and whether it ever admits a *possible, proper* part of a world as verifier in a contingent case.
- Every might-counterfactual variant (`\diamondrightI`, ..., `\diamondrightIL`) is a `syntactic.DefinedOperator` whose `derived_definition` is `¬(A \boxrightK ¬B)`; no hand-written clauses.
- Fusion closure of a set `S` of states in the bitvector lattice: `s` is a fusion of a nonempty subset of `S` iff `∃t ∈ S. t ⊑ s` and every atomic (single-bit) part `x ⊑ s` has some `t ∈ S` with `x ⊑ t ⊑ s`. This is the Z3 encoding for W and MC; Python-side it is a direct closure computation.

## Goals & Non-Goals

**Goals**:
- Reproduce report 02's F3 refutation frame mechanically and confirm or overturn each of its four failure claims for Reading I.
- Implement candidates I, W, L, M, MC, IL as Z3 operators alongside the untouched status-quo operator, each with a Python-side `find_verifiers_and_falsifiers` that is cross-validated against the Z3-side `extended_verify` on the same model.
- Measure, per candidate: fusion closure of `V` and `F`; harmlessness of impossible members; exclusivity; exhaustivity; bridge soundness; existence of possible proper-part verifiers; hyperintensionality at nested position; the nested-antecedent axioms (identity, modus ponens rule, antecedent strengthening, strict-conditional collapse); and the regression matrix over the existing 37 counterfactual examples.
- Attempt explicitly to refute F4 with a sound, sufficient, context-free, hyperintensional clause (IL and its fusion closure are the seeded candidates).
- Deliver a recommendation naming one clause, its discriminating evidence, and what it concedes, with the further test named wherever evidence does not discriminate.

**Non-Goals**:
- Modifying or deleting `CounterfactualOperator`, `MightCounterfactualOperator`, or the existing examples' expectations.
- Changing `LogosSemantics.true_at`, `is_alternative`, or any frame constraint.
- Any change to the Logos manual or Lean tree (`~/Projects/Logos/**`).
- Tensed/temporal generalization of the clauses.
- Performance work on the Z3 quantifier expansion beyond what the measurements need.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `utils.ForAll`/`Exists` expand quantifiers by substituting all `2^N` values, so a settler clause nested in an antecedent costs roughly `(2^N)^7` leaf terms; N=4 nested searches may be infeasible | H | H | Primary structural measurements run in the pure-Python oracle (no Z3). Z3 nested-antecedent measurements start at N=3; Phase 4 probes cost at N=3/N=4 and, if N=4 exceeds 60 s per example, introduces a definitional predicate `cf_true_<id>(w)` with `2^N` defining constraints appended to `semantics.frame_constraints` (precedent: `theory_lib/exclusion/semantic/registry.py` registers auxiliary Z3 functions with generated constraints) so the truth-set is computed once per formula rather than re-expanded per quantifier instance |
| Report 02's 8-atom frame needs N=8 (256 states); infeasible through the Z3 operator layer | M | H | Encode it in the oracle only; additionally search (oracle, small-N enumeration) for a smaller frame exhibiting the same four failures so the Z3 layer can confirm at least one of them independently |
| Status-quo `find_verifiers_and_falsifiers` (:117-148) already returns *all* `T`-worlds (context-free, Reading W minus closure) while its Z3 `extended_verify` returns `{eval world}`; the two disagree, and truth-bridge measurements on SQ must say which side they measured | M | H | Phase 1 writes a test recording the disagreement as a finding; every measurement table labels SQ's Z3-side and Python-side results separately |
| Registering candidate operators in `get_operators()` changes the operator collection every logos consumer loads (iterate, printing, `validate_operator_compatibility`) | M | M | Candidates ship in a separate module and are merged into `get_operators()`; full logos test suite is the gate in Phases 3, 4 and 8; name-collision check against `imposition/operators.py` aliases |
| Z3 model search over `\equiv` (constitutive subtheory) with candidate `extended_verify` on both sides is expensive | M | M | Restrict to N=3, `max_time` bounded, and treat a timeout as "inconclusive, further test named" rather than as evidence |
| Candidate M/MC nested logic may be sensitive to `Alt` at non-world verifiers in ways no report analysed; results could be hard to interpret | M | M | Every countermodel found is printed and saved under `specs/185_.../baselines/`; the recommendation cites concrete models, not summaries |
| Parser rejects suffixed names like `\boxrightIL` | L | L | Phase 3 first test asserts each name parses; fallback is a distinct LaTeX-style stem per candidate |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 3 |
| 5 | 5, 6 | 4 |
| 6 | 7 | 5 |
| 7 | 8 | 5, 6, 7 |

Phases within the same wave can execute in parallel.

### Phase 1: Baseline, branch check, and status-quo audit [COMPLETED]

**Goal**: Freeze the regression baseline, confirm the working branch, and record on disk the one fact about the status quo that every later measurement must be labelled against: its Z3-side and Python-side verifier sets disagree.

**Tasks**:
- [x] Confirm the current branch is the dedicated `counterfactual-verifier-semantics` branch (task requires a dedicated branch); do not create a new one if it is
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/ -v` and save the per-example pass/fail list to `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/01_counterfactual-examples-baseline.txt`
- [x] Run the full logos suite `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -q` and record the summary line in the same baselines directory
- [x] Write `tests/test_status_quo_audit.py` (RED first): on a solved model for `CF_CM_1`, compare, per world `w`, `z3_model.evaluate(op.extended_verify(s, A, B, {"world": w}))` for all states `s` against `op.find_verifiers_and_falsifiers(...)`; the test asserts the documented disagreement (Z3 side is `{w}`, Python side is all `T`-worlds) so that it fails if someone later silently changes either side *(altered: solved `\Box (A \boxright C)` at N=3 instead of `CF_CM_1`, because CF_CM_1 does not guarantee two true worlds and so cannot guarantee the two clauses differ; CF_CM_1 is used by the Phase 3 cross-validation instead)*
- [x] Add a short module docstring note in the new test naming the two clauses and their line ranges in `operators.py`

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_status_quo_audit.py` - new audit test
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/` - baseline captures

**Verification**:
- Baseline file lists all 37 existing examples with their pass status
- Audit test passes against the unmodified operator and documents the disagreement

---

### Phase 2: Pure-Python frame oracle and F3 reproduction [COMPLETED]

**Goal**: Build the exhaustive measurement instrument -- an explicit-finite-frame evaluator independent of Z3 -- and use it to reproduce report 02's F3 refutation of Reading I.

**Tasks**:
- [x] Create `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py` with a `Frame` (states as bitmasks over named atoms; `possible` as an explicit downward-closed set; worlds computed as maximal possible states, asserted equal to the declared worlds) and an `Interpretation` (verifier/falsifier bitmask sets per sentence letter)
- [x] Implement the shared primitives over bitmasks: `is_part_of`, `fusion`, `compatible`, `max_compatible_parts(s, a)`, `alternatives(s, a)`, and the counterfactual truth clause `T(w)` transcribed from `CounterfactualOperator.true_at` (universal over `A`-verifiers and alternatives)
- [x] Implement `verifiers_falsifiers(candidate, frame, interp, A, B)` for every key in the Candidate Clauses table (I, W, L, M, MC, IL; SQ takes an explicit world argument), plus `fusion_closure(S)` and `minimal_elements(S)` helpers
- [x] Implement `measure(candidate, ...)` returning a record with: closure of `V` and `F` under fusion (with a witness pair on failure); impossible members and whether each is part of some world; exclusivity over possible states (witness on failure); exhaustivity over worlds; bridge soundness (a verifier part of a world where `T` is false, and dually) ; existence of a possible verifier that is a proper part of some world
- [x] Encode the F3.1 frame verbatim (8 atoms, `w0..w3`, `|A|+ = {{a}}` etc.) as a test fixture; RED tests first asserting report 02's F3.2 facts (`T(w0)` false, `T(w1)`/`T(w2)` true, `T(w3)` false; `[w0]_{a} = {{p,p',b},{q,q',b},{p,q}}`), then the four F3.3 claims for I: closure fails at `{p,p'} ⊔ {q,q'}`, exclusivity fails at `{p,p'}`/`{q}`, bridge fails at `{p,p'} ⊑ w0`, and the identity instance `(A \boxright B) \boxright (A \boxright B)` fails at `w0` when the antecedent's verifiers are `V_I`
- [x] On the same frame, run `measure` for W, L, M, MC, IL and record the results table (this is the first cross-candidate datum; report 02's F5 sanity check `V_W = {w1, w2, w1 ⊔ w2}` is a RED assertion)
- [x] Add a small-N (N ≤ 4 atoms) exhaustive frame enumerator restricted to frames satisfying the logos frame constraints and the classical/exclusivity/exhaustivity constraints on sentence letters, used by later phases to search for witnesses without Z3

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: The F3.1 frame has 256 states and exactly 4 worlds after computing maximal possible states; confirm by asserting `frame.worlds == {w0, w1, w2, w3}` in the fixture test. If the computed world set differs, the report's frame description is wrong and the finding is recorded before any measurement is trusted.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py` - new module
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_frame_oracle.py` - primitives, fixture, F3 reproduction, cross-candidate table

**Verification**:
- `pytest .../tests/test_frame_oracle.py -v` green; each of the four F3.3 claims has its own test whose docstring states confirm/overturn
- The cross-candidate table for the F3 frame is written to `specs/185_.../baselines/02_f3-frame-candidate-table.json`

---

### Phase 3: Z3 candidate operators I, W, L with cross-validation [NOT STARTED]

**Goal**: Add the first three candidate operators as Z3 operators alongside the status quo, sharing its truth clause, and prove on solved models that each operator's Python-side sets equal both the oracle's sets and its own Z3-side clause.

**Tasks**:
- [ ] RED: `tests/test_candidate_operators.py` asserting that `get_operators()` exposes `\boxrightI`, `\boxrightW`, `\boxrightL` and `\diamondrightI/W/L`, that each name parses inside a formula via `Syntax`, and that no name collides with `imposition/operators.py`'s `\boxrightlogos`/`\diamondrightlogos`
- [ ] Create `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` with a base `_CandidateCounterfactual(CounterfactualOperator)` that inherits `true_at`/`false_at`/`print_method` unchanged and declares the shared helper `truth_set(model_structure, leftarg, rightarg)` (Python-side: evaluate `true_at` at every `z3_world_state`)
- [ ] Implement `ImpositionLocalCounterfactual` (`\boxrightI`): `extended_verify(s, A, B, ep) = self.true_at(A, B, semantics.with_world(ep, s))`, `extended_falsify` dually via `false_at`; `find_verifiers_and_falsifiers` evaluates those clauses at every state of the solved model
- [ ] Implement `WorldStateCounterfactual` (`\boxrightW`): Z3 clause via the fusion-closure encoding in "Candidate Clauses" over `is_world(w) ∧ T(w)`; Python side closes the truth-set under fusion
- [ ] Implement `SettlerCounterfactual` (`\boxrightL`): Z3 clause `ForAll w. (is_world(w) ∧ s ⊑ w) → true_at(A, B, w)` and its dual; Python side filters all states
- [ ] Implement the three `DefinedOperator` might-variants with `derived_definition` only
- [ ] Merge the candidate dictionary into `operators.get_operators()` and export the classes from `__init__.py`
- [ ] Cross-validation tests, parametrized over the three candidates and over `CF_CM_1`, `CF_CM_7`, `CF_TH_2` at N=3: (a) `find_verifiers_and_falsifiers` equals the oracle's sets on the frame extracted from the solved model (`z3_possible_states`, `z3_world_states`, verify/falsify tables); (b) for every state `s` and every world `w`, `z3_model.evaluate(extended_verify(s, ..., {"world": w}))` equals membership in the Python-side set (context-freedom and Z3/Python agreement in one assertion)
- [ ] Run the full logos suite to confirm the enlarged operator collection breaks nothing

**Timing**: 2 hours

**Depends on**: 1, 2

**Verification Tier**: full

**Scope Hypothesis**: Three primitive operator classes plus three defined might-variants suffice for this phase; confirm by the operator-availability test enumerating exactly six new names.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` - new module
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` - `get_operators()` merges candidates (no change to existing classes)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/__init__.py` - exports
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_operators.py` - availability, parsing, cross-validation

**Verification**:
- `pytest .../counterfactual/tests/ -v` green, including Phase 1's audit and the untouched 37 examples
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -q` matches the Phase 1 baseline summary

---

### Phase 4: Z3 candidate operators M, MC, IL and the nesting-cost decision [NOT STARTED]

**Goal**: Add the three remaining candidates, cross-validate them the same way, and decide on evidence whether nested-antecedent Z3 searches need the definitional-predicate encoding.

**Tasks**:
- [ ] RED: extend `test_candidate_operators.py` with availability/parsing/cross-validation for `\boxrightM`, `\boxrightMC`, `\boxrightIL` and might-variants
- [ ] Implement `MinimalSettlerCounterfactual` (`\boxrightM`): Z3 clause `L(s) ∧ ForAll t. (t ⊏ s) → ¬L(t)` (reuse `SettlerCounterfactual`'s clause builder); Python side takes minimal elements of the settler set
- [ ] Implement `GeneratedSettlerCounterfactual` (`\boxrightMC`): fusion-closure encoding over `M`'s clause; Python side closes `V_M` under fusion
- [ ] Implement `SettlingImpositionLocalCounterfactual` (`\boxrightIL`): conjunction of I's and L's clauses; Python side intersects the two sets
- [ ] Cost probe (not a test): time one nested-antecedent example `((A \boxrightK B) \boxrightK C)` per candidate at N=3 and N=4 with `max_time=60`; record times in `specs/185_.../baselines/03_nesting-cost.json`
- [ ] Decision gate: if any candidate exceeds 60 s at N=4, implement a `cf_truth_predicate(leftarg, rightarg)` helper that allocates `z3.Function("cf_true_<n>", BitVecSort(N), BoolSort())` once per (operator, argument pair), appends its `2^N` defining constraints `cf_true(w) == true_at(A, B, {"world": w})` to `semantics.frame_constraints` (which `ModelConstraints.__init__` concatenates into `all_constraints` after premise/conclusion construction), and rewrites the W/L/M/MC/IL clauses over the predicate; re-run the probe and the cross-validation tests. If no candidate exceeds the budget, record that fact and skip the helper
- [ ] Full logos suite green

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: Nested-antecedent searches are feasible at N=3 for every candidate without the definitional predicate and infeasible at N=4 for at least L/M/MC/IL; the cost probe confirms or refutes this and the decision gate acts on the measurement, not on this guess.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` - three more operators, optional predicate helper
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_operators.py` - extended coverage
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/03_nesting-cost.json` - timings

**Verification**:
- All six candidates pass cross-validation (oracle equality, Z3/Python agreement, context-freedom) on the same three examples
- Cost probe recorded; the decision taken is written in the file's header comment

---

### Phase 5: Structural measurements per candidate over searched models [NOT STARTED]

**Goal**: For every candidate, search small models for violations of each structural property and record witnesses, so each property is confirmed by exhaustive small-N enumeration or refuted by a concrete model.

**Tasks**:
- [ ] RED: `tests/test_candidate_structure.py` parametrized over candidates and over the properties: fusion closure of `V` and of `F`; impossible-member harmlessness; exclusivity over possible states; exhaustivity over worlds; bridge soundness in both polarities; possible proper-part verifier existence
- [ ] Oracle route: run the Phase 2 small-N enumerator (N ≤ 4 atoms, letters A, B) and, per candidate and property, report either "holds on all enumerated frames" or the first witness frame (serialized)
- [ ] Z3 route (independent confirmation on searched rather than enumerated models): for each candidate at N=3, run `iterate` over `CF_CM_1`-style examples with `\boxrightK` and re-measure the same properties on each found model via the oracle's `measure`
- [ ] Hyperintensionality at nested position via the constitutive identity operator: registry `['extensional','modal','constitutive','counterfactual']`; example premises `\Box((A \boxrightK B) \leftrightarrow (C \boxrightK D))`, conclusion `((A \boxrightK B) \equiv (C \boxrightK D))`, N=3, `expectation=True` means a countermodel (same truth-set, distinct propositions) exists; record found/none/timeout per candidate. Expected (hypothesis): none for W, L, M, MC; a countermodel for I and IL
- [ ] Record the full property matrix to `specs/185_.../baselines/04_structure-matrix.json` and the human-readable table in the Phase 8 report draft

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_structure.py` - new
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py` - enumerator/serialization helpers as needed
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/04_structure-matrix.json` - results

**Verification**:
- Every (candidate, property) cell is filled with `holds (n frames)`, a witness, or `timeout`; no cell is inferred from another candidate
- The M-closure result and the MC-soundness result are each backed by an explicit witness or an exhaustive count

---

### Phase 6: Nested-antecedent logic and regression matrix [NOT STARTED]

**Goal**: Measure, per candidate, the counterfactual axioms and rules at nested counterfactual antecedents, the strict-conditional collapse, and the regression matrix over the existing examples.

**Tasks**:
- [ ] Create `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py` with a generator `examples_for(candidate_key)` that substitutes `\boxright` -> `\boxrightK` and `\diamondright` -> `\diamondrightK` in premises/conclusions of `examples.unit_tests`, and a fixed set of nested-antecedent examples (N=3 unless the Phase 4 probe cleared N=4): identity `((A \boxrightK B) \boxrightK (A \boxrightK B))`; modus ponens rule `(A \boxrightK B), ((A \boxrightK B) \boxrightK C) ⊢ C`; antecedent strengthening `((A \boxrightK B) \boxrightK C) ⊢ (((A \boxrightK B) \wedge D) \boxrightK C)`; strict collapse both directions `((A \boxrightK B) \boxrightK C)` vs `\Box((A \boxrightK B) \rightarrow C)`; and the same four with a might-counterfactual antecedent
- [ ] RED: `tests/test_candidate_logic.py` parametrized over candidates and nested examples; each test records the outcome (valid / countermodel found / inconclusive) rather than asserting a prior expectation, then a second assertion layer pins the recorded outcomes once measured (characterization tests)
- [ ] Regression matrix: run all 37 substituted examples per candidate and diff against the Phase 1 baseline; record which currently-valid theorems break and which currently-invalid ones become valid
- [ ] Record hypotheses in the test docstrings before running: (a) the regression matrix is identical across candidates because no existing example places a counterfactual in a verifier-consuming position (antecedent of `\boxright`, or under `\equiv`); (b) W and L collapse to the strict conditional at nested antecedents; (c) M/MC/IL do not collapse, because a minimal or settling verifier imposed on `w` need not reach every `T`-world; confirm or refute each
- [ ] Save the two matrices to `specs/185_.../baselines/05_logic-matrix.json` and `06_regression-matrix.json`, including every countermodel's printed model

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: 37 existing examples (23 countermodels, 14 theorems, per `examples.py`'s collections) are substituted per candidate; confirm by asserting `len(examples_for(k)) == len(unit_tests)` in the generator test. If hypothesis (a) above holds, say so explicitly in the matrix file rather than reporting an empty diff silently.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py` - new
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_logic.py` - new
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/05_logic-matrix.json`, `06_regression-matrix.json` - results

**Verification**:
- Every (candidate, nested example) cell is filled; timeouts are labelled inconclusive with the `N`/`max_time` used
- Regression diff per candidate is recorded even when empty

---

### Phase 7: F4 refutation attempt and further candidates [NOT STARTED]

**Goal**: Look explicitly for a sound, sufficient, context-free clause that is hyperintensional, using the Phase 5/6 harness, rather than treating report 02's F4 as settled.

**Tasks**:
- [ ] From the Phase 5 hyperintensionality search, take IL's outcome: if a countermodel (same truth-set, distinct `V_IL`) was found, verify with the oracle that on that model IL is sound (every verifier a settler), sufficient (every `T`-world contains a verifier) and exclusive/exhaustive; if all hold, F4's "except by fiat" claim is refuted by a clause whose selection criterion is Reading I's own imposition condition -- record the model verbatim
- [ ] Measure IL's fusion closure; if it fails, add `\boxrightILC` (fusion closure of `V_IL`) as a further candidate through the Phase 3/4 pattern and re-run the Phase 5 structure and hyperintensionality measurements for it
- [ ] Measure whether IL (or ILC) ever has a possible verifier that is a proper part of a world in a model where the counterfactual is contingent (the desideratum); search with the small-N enumerator and record the first witness or the exhaustive negative
- [ ] If IL/ILC fail the desideratum, test the one further variant the harness makes cheap: "settling possible imposition-local" (`V_IL` restricted to possible states, then closed under fusion), and record
- [ ] Write the F4 verdict paragraph (refuted / not refuted at N ≤ 4 / inconclusive) with the exact models, for the Phase 8 report

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` - optional ILC and variant operators
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_candidate_structure.py` - extended coverage
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/07_f4-attempt.json` - models and verdict

**Verification**:
- The F4 verdict is one of three labelled outcomes and each is backed by a saved model or an exhaustive count with its `N`
- Any operator added here passes the Phase 3 cross-validation tests

---

### Phase 8: Recommendation report, documentation, and summary [NOT STARTED]

**Goal**: Turn the measurements into the deliverable: one recommended clause, the evidence discriminating it, its concessions, and the further tests where evidence does not discriminate.

**Tasks**:
- [ ] Write `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_candidates.md` (no task-number references; cite filenames and section headings): candidate definitions; the F3 reproduction verdict; the structure matrix; the nested-logic matrix; the regression diff; the F4 verdict; the recommendation with its explicit concessions; and, for every pair of candidates the evidence does not separate, the named further test
- [ ] Update `counterfactual/README.md` (Operator Reference and Directory Structure sections) to list the candidate operators, `candidates.py`, `frame_oracle.py`, `candidate_examples.py`, and the new report, marking the candidates as exploratory alternatives to `\boxright`
- [ ] Register a curated subset of nested-antecedent examples in `examples.py` under a new `counterfactual_candidate_examples` collection that is *not* merged into `unit_tests` (so the existing example test and its baseline stay untouched), with the `example_range` comment block extended
- [ ] Run the complete gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -v` and `PYTHONPATH=code/src pytest code/tests/ -q`; compare against the Phase 1 baseline; run `cd code && ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py` once for the dual-methodology check in `code/docs/core/TESTING_GUIDE.md` section 4.1
- [ ] Write `specs/185_.../summaries/01_counterfactual-verifier-candidates-summary.md` per summary-format.md, pointing at the report and the baselines

**Timing**: 1.5 hours

**Depends on**: 5, 6, 7

**Verification Tier**: full

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_candidates.md` - new
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md` - operator/directory documentation
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py` - candidate example collection (additive)
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/summaries/01_counterfactual-verifier-candidates-summary.md` - summary

**Verification**:
- `bash .claude/scripts/check-task-references.sh` (or the equivalent lint named in `.claude/rules/no-task-references-in-deliverables.md`) reports no task-number references under `code/`
- Full logos suite and `code/tests/` match or exceed the Phase 1 baseline
- The report names exactly one recommended clause and lists its concessions in a dedicated section

## Testing & Validation

- [ ] Phase 1 audit test documents the SQ Z3/Python disagreement and passes unchanged through Phase 8
- [ ] `test_frame_oracle.py` reproduces every F3.2 fact and gives a confirm/overturn verdict on each F3.3 claim
- [ ] `test_candidate_operators.py` cross-validates all six (or more) candidates: oracle equality, Z3/Python agreement, context-freedom across evaluation worlds
- [ ] `test_candidate_structure.py` fills every (candidate, property) cell with an exhaustive count or a witness
- [ ] `test_candidate_logic.py` pins the nested-antecedent outcomes and the regression diff per candidate
- [ ] Existing `test_counterfactual_examples.py` (37 examples) unchanged and green
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ -v` and `PYTHONPATH=code/src pytest code/tests/ -q` green; `./dev_cli.py` run of the candidate examples completes

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/frame_oracle.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidate_examples.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_status_quo_audit.py`, `test_frame_oracle.py`, `test_candidate_operators.py`, `test_candidate_structure.py`, `test_candidate_logic.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_candidates.md` (the recommendation)
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/01`-`07` result files
- `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/summaries/01_counterfactual-verifier-candidates-summary.md`

## Rollback/Contingency

All changes are additive: new modules, new tests, a merged dictionary in `get_operators()`, an additive collection in `examples.py`, and documentation. Rollback is `git revert` of the phase commits on the `counterfactual-verifier-semantics` branch; the existing `CounterfactualOperator`, `MightCounterfactualOperator`, and the 37 baseline examples are never edited, so reverting cannot regress them. If the Z3 layer proves infeasible for nested antecedents even at N=3, the oracle-route measurements (Phases 2, 5) and the regression matrix still complete, and the report records the nested-logic cells as inconclusive with the further test (definitional predicate or hand-built frames) named.
