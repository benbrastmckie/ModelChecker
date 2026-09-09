# Research Report: Exact-imposition verifier clauses for the counterfactual

- **Task**: 185 - Design and test hyperintensional counterfactual verifiers
- **Started**: 2026-09-08T23:58:36Z
- **Completed**: 2026-09-09T00:25:00Z
- **Effort**: 1 research dispatch (oracle-based exploration; no source files under `code/` modified)
- **Dependencies**: None (plan `01_counterfactual-verifier-candidates.md` phases 1-2 are committed and green; see F1 for the stashed phase 3)
- **Sources/Inputs**:
  - Dispatch: `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/.dispatch/1.md` (the re-scoped task description, commit `d742d7a6`)
  - Provenance: `~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/01_counterfactual-null-state-verification.md` (Reading B, rejected) and `.../02_context-free-counterfactual-verifiers.md` (F2 Reading I, F3 refutation frame, F4 settler argument, F5 Reading W)
  - Code: `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` (`true_at` :37-52, `false_at` :54-66, `extended_verify`/`extended_falsify` :68-84, `find_verifiers_and_falsifiers` :86-147), `code/src/model_checker/theory_lib/logos/semantic/core.py` (`max_compatible_part` :288-319, `is_alternative` :321-349, `premise_behavior`/`conclusion_behavior` :107-108), `.../counterfactual/frame_oracle.py` (committed phase 2 oracle), `.../counterfactual/tests/test_frame_oracle.py`, `.../tests/test_status_quo_audit.py`, `.../tests/harness.py`, `.../counterfactual/examples.py`
  - Task artifacts: `plans/01_counterfactual-verifier-candidates.md`, `handoffs/phase-1-*.md`, `handoffs/phase-2-*.md`, `baselines/01_*`, `baselines/02_f3-frame-candidate-table.json`, `git stash@{0}` (phase 3 work, F1)
- **Artifacts**:
  - `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/reports/01_exact-imposition-verifier-clauses.md` (this report)
  - `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/03_research-exploration.py` (oracle extension defining every candidate below; modes `f3`, `struct`, `logic`, `hyper`, `rstruct`, `rlogic`, `rhyper`, `g`, `charx`)
  - `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/03_research-witnesses.py` (the three witness frames of F5, F6, F8)
  - `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/03_research-exploration-output.txt` (every table cited below, captured verbatim)
- **Standards**: report-format.md, status-markers.md, artifact-management.md, tasks.md

---

## Executive Summary

- **F3 is confirmed mechanically, and strengthened.** The committed oracle tests (`tests/test_frame_oracle.py`, 24 green) reproduce report 02's eight-atom frame and all four failures of Reading I; additionally the null state falsifies under Reading I, so the bridge gluts at three of the four worlds, and bridge soundness fails in the falsifier polarity too. Reading I is out.
- **The exact-imposition family (consequent verified by a designated part, verifier composed from those parts) is characterized, not just sampled.** A member of the family has a verifier below a true world `w` iff every alternative of `w` carries a `B`-verifier that is *already part of `w`* (0 mismatches over 3,515 true worlds). So the family verifies only "centered" truths and has no verifier at any genuinely counterfactual truth: it gives up sufficiency (and exhaustivity) by construction, and every member fails modus ponens at nested antecedents (384/1,500 sampled models). The variants that impose on the candidate state itself also give up soundness (report 02's holism, 6 exhaustive witnesses at n=3). No member of this family can be the recommended clause; the deliverable is the trade it forces (F4).
- **F4's impossibility claim is refuted; its structural core survives.** Any sound clause has verifiers that are settlers (that is the definition of soundness), but selection among settlers can be both hyperintensional and built from the imposition machinery: `IL` = "imposing every `A`-verifier on `s` reaches only `B`-worlds" (Reading I) AND "imposing every `A`-verifier on every world containing `s` reaches only `B`-worlds" (settling by imposition). Its fusion closure `ILC` is sound, sufficient, exclusive, exhaustive and fusion-closed on every one of 3,204 exhaustive n=3 models, 300 sampled n=4 models and 850 random n=4-6 frames; it has possible verifiers properly below world states in 9/14 and 20/23 contingent random models at n=4 and n=5; and it is hyperintensional: Frame G2 (F8) has two counterfactuals with the same truth-set and distinct `ILC` propositions. What survives of F4: because every true world is itself an `IL`-verifier, `ILC` collapses nested antecedents to the strict conditional exactly as report 02's Reading W does.
- **A non-strict nested logic requires exactness, and exactness is a minimality step.** `ILMC` = fusion closure of the parthood-minimal `IL`-verifiers keeps every structural property of `ILC`, is hyperintensional *in nested truth-value* (Frame G2: `(A []-> B) []-> C` and `(C []-> D) []-> C` differ although the antecedents share a truth-set), validates identity and modus ponens at nested antecedents, and refutes antecedent strengthening and the collapse `X []-> C ⊣⊢ [](X -> C)` — the same profile as the base counterfactual logic. **Recommendation (D1): `ILMC`**, stated as an exact clause (V1-V3 in F9), with `ILC` as the fallback if the minimality step V3 is judged to fall under the disqualification rule. That judgement is surfaced as a non-blocking user decision.
- **The remainder-composed clause the task's item (c) asks for (`SR`/`SRC`: settling fusions of maximal antecedent-compatible parts) is the best clause without a minimality step** — sound, non-strict, hyperintensional, with the most natural falsifiers (`p.q` on the F3 frame) — but it is insufficient in two structurally identifiable situations (F6): holism (Frame F3z) and antecedent-incompatible worlds (null remainder). Recorded, not recommended.
- **The existing 37 counterfactual examples cannot discriminate any candidate** (F10): no premise or conclusion places a counterfactual in a verifier-consuming position, and premise/conclusion constraints use only the shared `true_at`/`false_at`. The regression matrix is provably identical across candidates; discrimination needs new nested-antecedent and constitutive (`\equiv`) examples.

---

## Context & Scope

The re-scoped task (commit `d742d7a6`) fixes the truth clause, binds every candidate to the imposition machinery (`|A|+`, `max_compatible_part`, `is_alternative`, `|B|±`), demotes report 02's Reading W and the settler clauses `L`, `M`, `MC` to comparison baselines, and asks for the exact-imposition family to be developed and measured against them, with the specific desideratum that some *possible* verifiers lie properly below world states.

Method: every candidate is a verifier clause added to the committed pure-Python oracle (`frame_oracle.py`, which the phase-2 tests validate against report 02's frame) via the extension script in `baselines/03_research-exploration.py`. Measurements are (i) the phase-2 `measure` record (closure, exclusivity in two strengths, exhaustivity, bridge soundness and sufficiency in both polarities, impossible-member harmlessness, possible proper-part verifiers), (ii) nested-antecedent principles evaluated by the oracle's recursive truth clause, and (iii) same-truth-set/distinct-proposition searches. Model populations: the F3 frame; exhaustive enumeration at n=3 (3,204 frame-interpretation pairs); the phase-2 enumerator sampled at n=4; a random-frame sampler at n=4-6 (needed because exhaustive enumeration of letter propositions stops at n=4); and three hand-built witness frames at 7-9 atoms. Z3 was not run in this phase; the Z3 side is planning input (F11).

Out of scope here: writing operators, changing any file under `code/`, the manual or Lean trees.

---

## Findings

### F1. Repository state, verified

- Phases 1-2 of plan 01 are committed (`24998369`, `9a706717`): `tests/harness.py`, `tests/test_status_quo_audit.py`, `frame_oracle.py`, `tests/test_frame_oracle.py`, `baselines/01_*`, `baselines/02_f3-frame-candidate-table.json`. `pytest` on the two new test files: 24 passed (re-run this dispatch). The 37 counterfactual examples and the full logos suite (452 passed) are the phase-1 baseline.
- **Phase 3 was in progress when the task was re-scoped and sits in `git stash@{0}`** (snapshot marker `.git-snapshot-marker`, `HEAD_SHA=9a706717`). The tracked-file part of the stash touches `operators.py` (`get_operators()` merges `candidates.get_candidate_operators()`), the plan (phase 3 tasks ticked), `.lock/holder.json` and `events.jsonl`; the untracked part (`stash@{0}^3`) holds `candidates.py` (440 lines: `CandidateCounterfactual` base with memoized per-world truth subterms, `settler_clause`, `closure_clause`, an optional `truth_predicate` encoding, `SolvedModelView`; operators `\boxrightI`, `\boxrightW`, `\boxrightL` and factory-built might variants), `tests/test_candidate_operators.py` (207 lines, 44 tests cross-validating Python side == oracle == Z3 side), `.dispatch/2.md`, and `handoffs/phase-3-handoff-20260908T235211Z.md`. The handoff records the nested-antecedent cost at N=4 as about 1.2 s for `W`/`L` with the direct encoding. Recover with `git checkout stash@{0}^3 -- <paths>` (untracked files) and `git stash show -p stash@{0}` (tracked diff); a plain `git stash pop` also reapplies the plan and lock edits.
- Status quo audit (phase 1) stands: the Z3-side clause gives `{w}` at evaluation world `w`, the Python-side clause gives every true world; the two disagree and every measurement of "SQ" must name its side. Only the Python side (`SQpy`) is context-free; it fails fusion closure (F3 table below).
- The plan's candidate roster (`I, W, L, M, MC, IL`) predates the re-scoping: `W, L, M, MC` are now baselines, and the exact family and `ILMC`/`SR`/`SRC` are absent from it. The plan is obsolete in its candidate list, phases 3-8 scope, and operator names; phases 1-2 remain valid.

### F2. F3 reproduction: verdict CONFIRMED on all four counts, with two additions

Committed in `tests/test_frame_oracle.py` (`test_f3_2_*`, `test_f3_3_1` .. `test_f3_3_4`, `test_f3_5_*`): `[w0]_a = {p.p'.b, q.q'.b, p.q}`; `T(w1)`, `T(w2)` true, `T(w0)`, `T(w3)` false; `{p,p'}` and `{q,q'}` verify under `I` and their fusion does not; `{p,p'}` verifies and `{q}` falsifies with `{p,p',q}` possible; `{p,p'} ⊑ w0` with the counterfactual false at `w0`; identity `(A []-> B) []-> (A []-> B)` false at `w0`. Additions the report did not state: the null state is an `I`-falsifier (imposing `{a}` on the null state reaches every `a`-world, including `w3`), so the bridge gluts at `w0, w1, w2`, and bridge soundness fails in the falsifier polarity (`{q} ⊑ w2`, true there). Impossible states are not vacuous verifiers under `I` (`{a,a'}` is constrained and fails) but are harmless at the bridge for every clause.

### F3. The design space, made precise

Notation over states of an untensed logos model: `W` worlds; `|A|± = (V_A, F_A)`, `|B|± = (V_B, F_B)`; `[s]_a` the maximal `a`-compatible parts of `s` (`max_compatible_part`); `Alt(s, a) = {u ∈ W : a ⊑ u, ∃r ∈ [s]_a. r ⊑ u}` (`is_alternative(u, a, s)`, defined for every state `s`, not only worlds); `T(w)` the fixed truth clause; `P(s) = {(a, u) : a ∈ V_A, u ∈ Alt(s, a)}`. "Settler": `∀w ∈ W. s ⊑ w -> T(w)`; "co-settler" dually with falsity. Every clause below reads the model alone (context-free) except `SQ`/`XE`.

| Key | Verifier clause for `s` | Falsifier clause (dual) | Mechanism status |
|-----|--------------------------|-------------------------|------------------|
| `I` | `∀(a,u) ∈ P(s)`: `B` true at `u` | `∃(a,u) ∈ P(s)`: `B` false at `u` | imposition on `s` (report 02 Reading I) |
| `XS` | `s = ⊔_{(a,u)∈P(s)} b(a,u)`, `b(a,u) ∈ V_B`, `b(a,u) ⊑ u` | `s = ⊔` of `d ∈ F_B`, `d ⊑ u`, over a nonempty subset of `P(s)` | exact, base = `s` |
| `XSr` | as `XS` with `b(a,u) ⊔ r(a,u)`, `r ∈ [s]_a`, `a ⊔ r ⊑ u` | dual | exact + remainder, base = `s` |
| `XPe` | `∃w ⊒ s` (world): `s = ⊔_{(a,u)∈P(w)} b(a,u)` | dual | exact, `s` part of some world |
| `XPer` | `XPe` with remainders `r ∈ [w]_a` | dual | exact + remainder |
| `XPa` | `∀w ⊒ s`: some composition of `s` over `P(w)` | dual | exact, `s` part of every world |
| `XPar` | `XPa` with remainders | dual | exact + remainder |
| `XSx` | `s ∈ V_B` and `s ⊑ u` for some `(a,u) ∈ P(s)` | dual | exact, existential |
| `SB` / `SAB` | settler and `s ∈ closure(V_B)` / `closure(V_A ∪ V_B)` | co-settler and `s ∈ closure(F_B)` / `closure(V_A ∪ F_B)` | settler + composition from letter verifiers |
| `SX` / `SXr` / `SXC` | settler and `XPe` / `XPer`; `SXC` = closure of `SX` | dual | settler + exact composition |
| `SR` / `SRC` | settler and `∃w ⊒ s`: `s = ⊔_a r_a` with `r_a ∈ [w]_a` (one per `A`-verifier with alternatives); `SRC` = closure | co-settler and same composition | settler + surviving remainders (task item (c)) |
| `IL` | `I(s)` and settler | `I`-falsifier and co-settler | imposition on `s` + imposition on every world above `s` |
| `ILC` | fusion closure of `IL` | closure | as `IL` |
| `ILM` / `ILMC` | parthood-minimal members of `IL`; `ILMC` = closure of `ILM` | minimal `IL`-falsifiers; closure | as `IL` + exactness |
| Baselines `SQpy`, `W`, `L`, `M`, `MC` | true worlds; closure of true worlds; settlers; minimal settlers; closure of minimal settlers | duals | truth-set functions (disqualified as candidates) |

"Settler" is written above as a set, but as a clause it is item (a)'s "s is a part of the world on which the imposition is done": `∀w ∈ W. s ⊑ w -> ∀a ∈ V_A ∀u. is_alternative(u, a, w) -> B true at u`. Extensionally that is `L`; the task disqualifies it *as a candidate in its own right* because its extension is a function of the truth-set. Every sound clause is a subset of it (F9), so the question the task actually poses is which mechanical *selection* among settlers to make.

### F4. The exact family: characterized, and out

**Characterization (mechanically confirmed, 0 mismatches over 3,228 true worlds at n=3 exhaustive and 287 true worlds on random n=5 frames; `charx` mode).** For `XPe` (and hence `XPa`, `SX`, `SXC`, which are restrictions of it below a given world): a true world `w` contains a verifier iff for every `(a, u) ∈ P(w)` some `b ∈ V_B` has `b ⊑ u` and `b ⊑ w`. Proof shape: a composed verifier `s ⊑ w` is a fusion of `B`-verifiers each part of an alternative `u`, so each is part of `w ∩ u`; conversely the fusion of such a choice is itself composable. Consequence: **at any world where `B` is false but `A []-> B` is true — the genuinely counterfactual case — the exact family has no verifier.** The consequent's verifiers live in the alternatives, and a sound verifier must live in the base world; the two coincide only for material that survives the imposition.

Measured consequences (n=3 exhaustive, 3,204 models; columns are counts of models failing the property):

| Key | closure V/F | exclusive | exhaustive | sound V/F | sufficient V/F | contingent models with proper possible V |
|-----|-------------|-----------|------------|-----------|----------------|------------------------------------------|
| `XS` | 0/0 | 0 | 3192 | 6/0 | 1554/1644 | 6 of 24 |
| `XSr` | 0/0 | 0 | 3192 | 6/0 | 1554/1644 | 6 |
| `XPe` | 3/18 | 0 | 3192 | 6/0 | 1554/1644 | 6 |
| `XPer` | 9/24 | 0 | 3198 | 0/0 | 1554/1644 | 0 |
| `XPa` | 0/0 | 0 | 3198 | 0/0 | 1560/1644 | 0 |
| `XPar` | 0/0 | 0 | 3204 | 0/0 | 1554/1650 | 0 |
| `XSx` | 18/18 | 0 | 3180 | 78/0 | 1554/1644 | 6 |
| `SB` / `SAB` | 0/0 | 0 | 3192 / 3156 | 0/0 | 1560/1638 / 1554/1602 | 0 |
| `SX` / `SXr` / `SXC` | 3/18, 9/24, 0/0 | 0 | 3198 | 0/0 | 1560/1644 | 0 |

- Base = the candidate state itself (`XS`, `XSr`, `XSx`): unsound (6 witnesses at n=3; 2 of 300 at n=4). On the F3 frame `V_XS = {b}` and `b ⊑ w0` where the counterfactual is false — report 02's holism verbatim: `{b}` cannot see that `w0` accommodates `a` by discarding `p'`.
- Base = worlds containing `s` (`XPe`, `XPa`, and the settler-guarded `SX*`, `SB`, `SAB`): sound, but insufficient in roughly half of all models and non-exhaustive in almost all (a world where the counterfactual is true with `B` false there has neither verifier nor falsifier).
- Adding the remainder (`*r`) does not help and removes the proper verifiers (the remainder is the whole world whenever an `A`-verifier is part of it).
- Nested logic (F7): every member fails modus ponens `X, X []-> C ⊢ C` at nested antecedents (`X []-> C` is vacuous where `X` is true without a verifier).

**Verdict.** Requiring the consequent to be *verified* rather than true, with the verifier composed from those consequent-verifiers, is exactly what makes the clause unable to verify counterfactual truths. Within the fixed truth clause the family must give up sufficiency, and its self-based members soundness too. It does not refute F4 by being sound and sufficient.

### F5. Settler-selection by imposition: `IL`, `ILC`, `ILMC`

`IL(s)` = Reading I at `s` AND settling by imposition. Report 02 refuted Reading I alone; the settler conjunct is the minimal repair (soundness), and Reading I is what makes the selection hyperintensional.

Structural results (counts of failing models; "proper V" = contingent models with a possible verifier properly below a world / contingent models):

| Population | Key | closure V/F | exclusive | exhaustive | sound | sufficient | proper V | proper F |
|------------|-----|-------------|-----------|------------|-------|------------|----------|----------|
| n=3 exhaustive (3204, 24 contingent) | `IL` | 0/0 | 0 | 0 | 0 | 0 | 0/24 | 24/24 |
| | `ILC`, `ILMC` | 0/0 | 0 | 0 | 0 | 0 | 0/24 | 24/24 |
| | `ILM` | 0/0 | 0 | 0 | 0 | 0 | 0/24 | 24/24 |
| n=4 sampled (300, 11 contingent) | `IL` | 0/1 | 0 | 0 | 0 | 0 | 6/11 | 11/11 |
| | `ILC`, `ILMC` | 0/0 | 0 | 0 | 0 | 0 | 6/11 | 11/11 |
| random n=4 (400, 14 contingent) | `ILC`, `ILMC` | 0/0 | 0 | 0 | 0 | 0 | 9/14 | 14/14 |
| random n=5 (300, 23 contingent) | `ILC`, `ILMC` | 0/0 | 0 | 0 | 0 | 0 | 20/23 | 23/23 |
| random n=6 (150, 11 contingent) | `ILC`, `ILMC` | 0/0 | 0 | 0 | 0 | 0 | 10/11 | 11/11 |
| F3 frame | `IL` | fails V (impossible fusion `a.p.p' ⊔ a.q.q'`) | pass | pass | pass | pass | 9 proper (`a.p'`, `a.p.p'`, `a.q'`, `a.q.q'`, `a.b`, `a.p.b`, `a.p'.b`, `a.q.b`, `a.q'.b`) | 30 |
| F3 frame | `ILMC` | pass | pass | pass | pass | pass | `a.p'`, `a.q'`, `a.b`, `a.p'.b`, `a.q'.b` | 14 |

- Soundness, exclusivity (compatibility form) and closure-preservation are theorems: every member is a settler; a possible fusion of a settler and a co-settler lies below a world that would be both true and false; the fusion of settlers is a settler. Sufficiency is a theorem too: a true world `w` satisfies `I(w) = T(w)` and is trivially a settler, so `w ∈ IL`. Exhaustivity follows from sufficiency in both polarities and bivalence at worlds (`bivalent_at_worlds` true on every model measured).
- `IL` is not fusion-closed only at impossible fusions (F3 witness); `ILC` repairs this and, because impossible states are below no world, changes nothing at the bridge (`impossible_harmless_*` true on every model for every candidate; only `L` and `XPa`-type clauses make impossible states vacuous members, and `I` does not — F3.5 confirmed).
- **`IL` differs from `L` (Frame G, 7 atoms; `g` mode).** Worlds `u = a.x.b'`, `u2 = a.x.c.b`, `w = a'.x.y.c.b`; `|A| = ({a},{a'})`, `|B| = ({b},{b'})`. `y` and `a'` are settlers (their only world is `w`, where the counterfactual is true) but not `I`-verifiers: `[y]_a = {null}` since `y` survives no imposition of `a`, so `Alt(y, a)` is every `a`-world including `u` where `B` is false. `IL` keeps `c`, `b`, `x.c`, ... — the states whose own surviving part already forces `B`. At n ≤ 4 the two sets coincide on possible states (hence the identical columns above); the separation needs a settler that is antecedent-incompatible, which the small frames cannot host.
- `ILMC` on Frame G: `V ∩ possible = {c, b, c.b}`; `MC` gives `{a', y, a'.y, c, b, ...}` — the mechanism constraint excludes precisely the antecedent-incompatible settlers, so it is not idle even against the disqualified baselines.

### F6. The remainder clause (`SR`/`SRC`): the best mechanical clause without minimality, and why it is insufficient

`SR`: `s` settles and is a fusion of maximal antecedent-compatible parts of some world containing it. On the F3 frame `V = {w1, w2}` (the `A`-worlds; the whole world survives) and `F = {p.q, w3}`: `p.q` is exactly the part of `w0` that survives imposing `a` and leads to `w3` — the most natural exact falsifier any candidate produced.

| Population | closure V/F (`SR`) | `SRC` closure | sound | sufficient V/F | exhaustive | proper V | proper F |
|------------|--------------------|---------------|-------|----------------|------------|----------|----------|
| n=3 exhaustive | 24/96 | 0/0 | 0 | 0/0 | 0 | 0/24 | 24/24 |
| n=4 sampled (300) | 21/80 | 0/0 | 0 | 0/1 | 1 | 2/11 | 7/11 |
| random n=4 (400) | 15/34 | 0/0 | 0 | 0/1 | 1 | 0/14 | 11/14 |
| random n=5 (300) | 20/38 | 0/0 | 0 | 0/1 | 1 | 2/23 | 19/23 |
| random n=6 (150) | 18/26 | 0/0 | 0 | 0/0 | 0 | 3/11 | 8/11 |

Two structural failure modes, each with a witness in `baselines/03_research-witnesses.py`:
- **Verifier side, holism (Frame F3z, 9 atoms)**: F3 plus `w4 = a'.p.p'.b.z`. `T(w4)` holds (`[w4]_a = {p.p'.b}`, alternatives `{w1}`), the only remainder is `p.p'.b`, and `p.p'.b ⊑ w0` where the counterfactual is false — so no fusion of remainders below `w4` settles, and `w4` has no `SR`/`SRC` verifier (nor falsifier: exhaustivity fails). `ILMC` verifies `w4` by `p'.z`, `b.z`, `p'.b.z`.
- **Falsifier side, null remainder (random n=4 model)**: worlds `a.b, b.c, d`; `|A| = ({b},{d})`, `|B| = ({a, d, a.d},{c})`. At `d` the counterfactual is false, but `b` is incompatible with `d`, so `[d]_b = {null}`; the null state is no co-settler, and `d` has no `SR`/`SRC` falsifier (`MC`/`ILMC` give `d`).

`SR` is hyperintensional (109/187 same-truth-set pairs distinct at random n=5) and non-strict (F7). It is recorded as the clause to reach for if minimality is refused *and* insufficiency at holistic/antecedent-incompatible worlds is accepted; it is not recommended.

### F7. Nested-antecedent logic

Counts of models with a world at which the principle fails, `X := A []-> B` under the candidate, letters `A, B, C, D` (sampled n=3, 1,500 models; random n=5, 300 models). `identity`: `X []-> X`; `MP`: `X, X []-> C ⊢ C`; `AS`: `X []-> C ⊢ (X ∧ D) []-> C`; `strict -> cf`: `[](X -> C) ⊢ X []-> C`; `cf -> strict`: converse; `might id`: `(A <>-> B) []-> (A <>-> B)`.

| Key | identity | MP | AS | strict -> cf | cf -> strict | might id |
|-----|----------|----|----|--------------|--------------|----------|
| `I` | 22 / 17 | 0 / 0 | 6 / 0 | 8 / 3 | 0 / 0 | 22 / 17 |
| `W`, `L`, `IL`, `ILC` | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| `M`, `MC`, `ILM`, `ILMC` | 0 / 0 | 0 / 0 | 361 / 70 | 0 / 0 | 700 / 132 | 0 / 0 |
| `SR`, `SRC` | 0 / 0 | 0 / 0 | 200 / 26 | 0 / 0 | 372 / 51 | 0 / 0 |
| `XS`, `XPe` | 7 / - | 384 / - | 8 / - | 2 / - | 400 / - | 0 / - |
| `XPa` | 0 / 0 | 389 / 59 | 4 / 4 | 0 / 0 | 402 / 69 | 0 / 0 |
| `XPar` | 0 | 388 | 0 | 0 | 388 | 0 |
| `SB` / `SAB` | 0 / 0 | 364, 359 / 53 | 4, 2 / 4 | 0 / 0 | 377, 364 / 63 | 0 / 0 |

- Any clause whose verifiers include every true world collapses to the strict conditional in both directions (`W`, `L`, `IL`, `ILC`): imposing a world state `w'` on any world yields `{w'}`, so `X []-> C` ranges over all true worlds of `X`. This is report 02's F6 logic, now measured, and it holds for `ILC` although `ILC` is hyperintensional — nested `[]->` cannot see the difference, only the constitutive operators can (F8).
- Excluding the non-minimal settlers (`ILMC`, `MC`) gives the base counterfactual profile: identity and modus ponens valid, strengthening invalid (as `CF_CM_1`), `[](X -> C) ⊢ X []-> C` valid and its converse invalid (as `CF_TH_11`/`CF_CM_24`-style examples for atomic antecedents).
- `SR`/`SRC` are non-strict for the same reason (the remainder is a proper part at non-`A`-worlds) and validate identity and MP wherever they have verifiers.
- `I` fails identity (and might-identity) because it is unsound; the exact family fails MP because it is insufficient.

### F8. Hyperintensionality at nested position

Same-truth-set pairs `A []-> B` vs `C []-> D` with distinct propositions (count / same-truth-set pairs): sampled n=3, 723 pairs: `I` 1, `W`/`L`/`M`/`MC`/`IL`/`ILC`/`ILMC` 0, `XS` 482, `XPe` 480, `XPa` 480, `SB` 661, `SAB` 678, `SR` 428. Random n=5 (187 pairs) and n=6 (100 pairs): `SR`/`SRC` 109 and 65; every settler-based clause 0. The zeros for `IL*` are the small-frame coincidence with `L` (F5), not intensionality:

**Frame G2 (8 atoms; `03_research-witnesses.py`)**: worlds `a.x'.b`, `a.x.c.b`, `a'.x.y.c.b`, `a.x.b'`; `|A| = ({a},{a'})`, `|B| = |D| = ({b},{b'})`, `|C| = ({x},{x'})`; all four letters satisfy the logos letter constraints. `A []-> B` and `C []-> D` are true at exactly `{a.x'.b, a.x.c.b, a'.x.y.c.b}`. Then:
- `L`, `MC`: identical propositions (as F4 of report 02 predicts for truth-set functions).
- `IL`, `ILC`: distinct — `x'` verifies `A []-> B` but not `C []-> D`; `a'`, `y` verify `C []-> D` but not `A []-> B`.
- `ILMC`: `V_{A []-> B} ∩ possible = {x', c, b, x'.b, c.b}` versus `{a', y, a'.y, c, a'.c, y.c, ...}`; and the difference is visible in nested truth: `(A []-> B) []-> C` is false at every world while `(C []-> D) []-> C` is true at three of four; likewise with consequent `¬A`.

So `ILC` and `ILMC` are hyperintensional by construction and in fact; for `ILC` the difference is detectable only through `\equiv`/`\leq`-style operators, for `ILMC` through nested counterfactuals as well.

### F9. Verdict on report 02's F4

- The argument's first step is definitional and stands: sound means every verifier is a settler; sufficient means every true world contains one. Every candidate measured obeys this (no sound clause ever had a non-settler verifier, no sufficient clause ever missed a true world).
- Its conclusion — "no context-free sound clause is hyperintensional except by fiat" — is refuted by `IL`/`ILC`/`ILMC`: the selection among settlers is made by a semantic clause with the same shape as the truth clause (imposition on the candidate state) and separates counterfactuals with identical truth-sets (Frame G2). Whether that counts as "fiat" is the user's call; it is not a set-theoretic operation on truth values.
- What the argument correctly forces: possible verifiers are settlers, and hence (i) in some contingent models no proper part of any true world verifies (all 24 contingent n=3 models: only proper falsifiers exist there; from n=4 on most contingent models do have proper verifiers), and (ii) a sufficient clause that keeps every true world as a verifier collapses nested antecedents to the strict conditional. Escaping (ii) needs an exactness (minimality) step; nothing in the imposition machinery short of that removes the worlds themselves without also losing sufficiency (F4, F6).

### F10. Regression over the existing examples is identical for every candidate

- `examples.py` contains no counterfactual in antecedent position (grep for `((X \boxright Y) \boxright`, `\diamondright` likewise: no hits) and no constitutive operator; the only nesting is in consequent position (`CF_CM_19`, `CF_CM_20`), which the shared `true_at` evaluates without verifiers.
- Premise and conclusion constraints are `semantics.true_at(premise, main_point)` and `semantics.false_at(conclusion, main_point)` (`semantic/core.py` :107-108); `\Box`, `\neg`, `\wedge`, `\vee`, `\diamondright` reach the counterfactual only through `true_at`/`false_at`. Proposition constraints apply to sentence letters only.
- Hence, with `true_at`/`false_at` shared verbatim, every candidate produces the same countermodels and the same `expectation` outcomes as the baseline on all 37 examples. Phase 6 of plan 01 hypothesized this; it is now established by inspection and should be run once as a sanity check, not treated as evidence. Discrimination requires new examples: nested-antecedent schemata (identity, MP, strengthening, strict collapse both directions) and constitutive comparisons (`\Box((A \boxright B) \leftrightarrow (C \boxright D))` against `(A \boxright B) \equiv (C \boxright D)`), which needs the constitutive subtheory loaded.

### F11. Z3 implementation notes for the planner

- The stashed `candidates.py` already provides the pieces `ILC`/`ILMC` need: memoized per-world truth subterms, `settler_clause` (`ForAll w. is_world(w) ∧ s ⊑ w -> true_at(A, B, w)`), `closure_clause` (atom-cover encoding of fusion closure from plan 01), and the optional definitional `truth_predicate`. `I(s)` is `self.true_at(A, B, with_world(ep, s))` (already `ImpositionLocalCounterfactual`). Minimality is `IL(s) ∧ ForAll t. t ⊏ s -> ¬IL(t)`; the phase-3 handoff's advice to build clauses by iterating concrete states in Python rather than `utils.ForAll` applies.
- Cost: `ILMC` nests four quantifier layers (closure, minimality, settling, imposition) around the truth clause; the phase-3 handoff measured 1.2 s at N=4 for one layer. The predicate encoding (`cf_true(w)` defined once per argument pair, appended to `frame_constraints` before solving) is the mitigation and is already written; a per-state `il(s)` predicate defined the same way would flatten the minimality and closure layers.
- The oracle bridges `frame_from_model_structure` / `interpretation_from_model_structure` / `formula_from_sentence` cross-validate Z3-side sets against `baselines/03_research-exploration.py`'s clauses on solved models; that is the same pattern the stashed 44 tests use.
- Frames G, G2, F3z need 7-9 atoms and are oracle-only, as F3 is.

---

## Decisions

- **D1 (recommended clause)**: `ILMC` — "exact imposition-settled verification". `s` verifies `A []-> B` iff `s` is a fusion of one or more states `t` such that (V1) every alternative to `t` under any `A`-verifier makes `B` true; (V2) every alternative, under any `A`-verifier, to any world containing `t` makes `B` true; (V3) no proper part of `t` satisfies V1 and V2. Falsifiers dually: some alternative to `t` makes `B` false, and every world containing `t` has such an alternative, and `t` is minimal with these. Rationale: the only clause measured that is context-free, sound, sufficient, exclusive, exhaustive, fusion-closed, hyperintensional in nested truth-value, delivers possible proper verifiers in most contingent models from n=4 on, and reproduces the base counterfactual logic at nested antecedents.
- **D2 (fallback)**: `ILC` (V1 ∧ V2, closed under fusion) if V3 is judged to fall under the disqualification rule. Identical structural profile and proper verifiers; concedes the strict collapse at nested antecedents (F7) and hyperintensionality visible only through constitutive operators (F8).
- **D3 (exact family)**: not adoptable under the fixed truth clause; the trade is stated in F4 and the family is retained in the measurement tables to show what it gives up.
- **D4 (remainder clause)**: `SRC` recorded as the best non-minimal alternative with its two insufficiency modes (F6); not recommended.
- **D5 (baselines)**: `W`, `L`, `M`, `MC` remain comparison columns only; the mechanism constraint is shown to bite (Frame G: `ILMC ≠ MC`, `IL ≠ L`).
- **D6 (plan)**: plan 01 is superseded in its candidate roster; phases 1-2 stand, the stashed phase 3 is reusable as the Z3 substrate but its operator set changes.

---

## Recommendations

1. **Plan the implementation around `ILMC` and `ILC` as candidates, `I` as the refuted control, and `W`/`L`/`MC` as baselines** — six Z3 operators plus might variants, not twelve. Recover the stashed `candidates.py`/tests first (F1), replace `\boxrightW`-style names by keys that match the oracle (`I`, `ILC`, `ILMC`, plus `W`, `L`, `MC`), and add the oracle clauses from `baselines/03_research-exploration.py` to `frame_oracle.py` (they are already written against its API) so Z3 sets cross-validate against them.
2. **Add a second set of example collections that can discriminate**: nested-antecedent schemata (identity, MP, strengthening, both collapse directions, might variants) at N=3/4, and the constitutive comparison with the `constitutive` subtheory loaded; keep them out of `unit_tests` so the 37-example baseline is untouched (F10).
3. **Characterization tests, not expectation tests, for the measurements**: pin the F5/F7/F8 outcomes per candidate (identity/MP valid for `ILMC`, strengthening and `cf -> strict` invalid, strict collapse for `ILC`) with the oracle as the source of truth and Z3 as confirmation at N ≤ 4.
4. **Cost gate**: probe `ILMC` nested at N=4; if over budget, use the stashed predicate encoding extended with an `il(s)` predicate (F11).
5. **Report the concession explicitly** in the final recommendation document: every possible verifier is a settler; V3 is a minimality operation of the same kind as `max_compatible_part`'s maximality; in some contingent models (all at n=3) nothing proper verifies, only proper falsifiers exist.
6. **Record, do not implement**: the tensed generalization (the manual's world-histories), and any change to the current `\boxright`.

Where the evidence does not discriminate:
- `ILMC` vs `MC`: identical nested-logic counts on every sampled population and identical nested truth on Frame G for the consequents tried; they differ in proposition (Frame G: `y`, `a'`). The further test is a constitutive comparison on a Frame-G-type model, or a nested example whose antecedent-incompatible minimal settler reaches a consequent-separating world; the choice is otherwise conceptual (a state that survives no imposition contributes no ground), and `MC` is disqualified in any case.
- `ILC` vs `L`/`W`: identical logic (strict); differ in proposition only (Frame G/G2). The further test is `\equiv` on Frame G2, oracle-only at 8 atoms.

---

## Risks & Mitigations

- **V3 (minimality) may be read as falling under the disqualification rule.** Surfaced as a non-blocking user decision; `ILC` is the fully mechanical fallback with the same structural profile, at the price of the strict collapse.
- **Small-frame coincidences mislead**: `IL = L` on possible states for n ≤ 4, `ILMC = MC` for n ≤ 6 random. Mitigation: the witness frames (7-9 atoms) are archived and scripted; Z3 tests at N ≤ 4 must not be read as showing candidates coincide.
- **Random sampler bias**: letter propositions are generated from 1-2 generators; exotic propositions are under-sampled. Mitigation: exhaustive n=3, the enumerator's n=4 sample, and hand frames cover the structural claims; theorems (soundness, exclusivity, sufficiency of `IL*`) do not rest on sampling.
- **Z3 cost of four quantifier layers**: mitigated by the predicate encoding (F11); oracle remains the primary instrument.
- **Falsifier duals were chosen by the author** (existential over alternatives; nonempty-subset fusion for the exact family). The `IL*` duals are canonical (Reading I's own dual and co-settling); the exact family's duals affect only a family that is out on the verifier side.

---

## Context Extension Recommendations

- **Topic**: settler selection by imposition and the exactness step. **Gap**: `.claude/context/project/logic/domain/counterfactual-semantics.md` does not record why proper parts fail Reading I (holism), that settling-by-imposition is the minimal repair, or that hyperintensional selection among settlers is possible. **Recommendation**: add a short section with the F3 mechanism, the `IL` clause, Frame G, and the strict-collapse-versus-minimality trade.

---

## Appendix

- Witness frames (all in `baselines/03_research-witnesses.py`; `g` mode of the exploration script for Frame G):
  - F3 (report 02): atoms `a a' p p' q q' b b'`; worlds `a'.p.p'.q.q'.b`, `a.p.p'.b`, `a.q.q'.b`, `a.p.q.b'`.
  - G: atoms `a a' x y c b b'`; worlds `a.x.b'`, `a.x.c.b`, `a'.x.y.c.b`.
  - G2: G plus atom `x'` and world `a.x'.b`; `|C| = ({x},{x'})`, `|D| = |B|`.
  - F3z: F3 plus atom `z` and world `a'.p.p'.b.z`.
  - SRC falsifier witness: 4 atoms, worlds `a.b`, `b.c`, `d`; `|A| = ({b},{d})`, `|B| = ({a,d,a.d},{c})`.
- Reproduction: `cd specs/185_.../baselines && python 03_research-exploration.py f3|struct 3|struct 4 300|rstruct 5 300|logic 3 1500|rlogic 5 300|hyper 3 1500|rhyper 5 400|g|charx` and `python 03_research-witnesses.py`; full captured output in `03_research-exploration-output.txt`. Timings: seconds each on this machine.
- Candidate keys used in the output file: `SQpy I W L M MC IL XS XSr XPe XPer XPa XPar XSx SB SAB SX SXr SXC SR SRC ILC ILM ILMC`.
