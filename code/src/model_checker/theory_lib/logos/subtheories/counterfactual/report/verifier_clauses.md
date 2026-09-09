# Verifier Clauses for the Counterfactual: Measurement and Recommendation

[← Back to Counterfactual](../README.md) | [Tests →](../tests/README.md)

This report records which states verify and which falsify `A □→ B` under each candidate
clause, the model-based evidence that separates the candidates, and the recommendation.
Every claim cites the test or saved baseline that produced it. The truth clause
(`CounterfactualOperator.true_at` / `false_at`) is shared verbatim by every candidate and is
not under review; only `extended_verify` / `extended_falsify` and their Python-side
`find_verifiers_and_falsifiers` differ.

## 1. Criterion, mechanism constraint, and disqualification

- **Governing criterion.** A sentence determines one proposition `<V, F>` as a function of
  the model alone. The current clause (`operators.py`, `extended_verify`: `state == eval
  world ∧ true_at`) gives `{w}` at evaluation world `w` and so expresses different
  propositions in different contexts; `tests/test_status_quo_audit.py` pins both of its
  sides (the Z3 side `{w}`, the Python side "every true world") and their disagreement.
- **Mechanism constraint.** Every candidate is built from the antecedent's verifiers,
  `max_compatible_part`, `is_alternative` (imposition of an antecedent verifier on a state)
  and the consequent's verifier/falsifier semantics.
- **Disqualification.** A clause whose verifier set is a function of the truth-set
  `{w : A □→ B is true at w}` — fusion closure of the true worlds (`W`), settlers (`L`),
  minimal settlers (`M`, `MC`) — is a comparison baseline only, never a recommendation.

Notation: `W` worlds; `|A|± = (V_A, F_A)`; `[s]_a` the maximal `a`-compatible parts of `s`;
`Alt(s, a)` the worlds containing `a` and some member of `[s]_a` (`is_alternative(u, a, s)`
with `s` in the world slot); `T(w)` the truth clause; "settler": every world containing `s`
is a `T`-world; "co-settler" dually.

## 2. The roster

| Key | Clause for a verifier `s` | Role | Where |
|-----|---------------------------|------|-------|
| SQ / SQpy | `{w}` at the evaluation world / every true world | status quo (Z3 side / Python side) | `operators.py`, oracle |
| I | `∀a ∈ V_A ∀u ∈ Alt(s, a)`: `B` true at `u` (the truth clause with `s` in the world slot) | refuted control | `\boxrightI`, oracle |
| IL | `I(s)` and `s` is a settler | building block | oracle |
| **ILC** | fusion closure of `IL` | mechanical control | `\boxrightILC`, oracle |
| **ILMC** | fusion closure of the parthood-minimal members of `IL` | **recommended** | `\boxrightILMC`, oracle |
| SR / SRC | settler that is a fusion of remainders `r_a ∈ [w]_a` (one per antecedent verifier with alternatives) of some world `w ⊒ s`; `SRC` its closure | remainder clause (task item (c)) | oracle |
| XS, XSr, XPe, XPer, XPa, XPar, XSx | exact family: the consequent is *verified* at each alternative by a designated part and `s` is the fusion of those parts (alternatives taken to `s` itself / to some world above `s` / to every world above `s`; `r` = surviving remainder fused in; `x` = a single consequent verifier) | developed and rejected | oracle |
| SB, SAB, SX, SXr, SXC | settler-guarded exact clauses | rejected | oracle |
| W, L, M, MC | truth-set functions | disqualified baselines | `\boxrightW`, `\boxrightL`, `\boxrightMC`, oracle |

Falsifier clauses are the polarity duals throughout (the `I`-falsifier clause, co-settling,
minimality, closure; for the exact family a fusion of consequent falsifiers over a nonempty
subset of the alternatives). Every `\diamondrightK` is the defined `¬(A \boxrightK ¬B)`.

**ILMC stated as an exact clause.** `s` verifies `A □→ B` iff `s` is a fusion of one or more
states `t` such that

- (V1) every alternative to `t` under any `A`-verifier makes `B` true;
- (V2) every alternative, under any `A`-verifier, to any world containing `t` makes `B` true;
- (V3) no proper part of `t` satisfies V1 and V2.

`s` falsifies `A □→ B` iff `s` is a fusion of states `t` such that some alternative to `t`
makes `B` false, every world containing `t` has such an alternative, and `t` is minimal with
these. `candidates.py` implements V1 as the truth clause at `t` (`truth_at_world`), V2 as
`settler_at`, V3 as `minimal_clause` over concrete states, and the fusion as
`closure_clause`; the Python side mirrors this with `SolvedModelView`, `minimal_elements`
and `fusion_closure`.

## 3. Verdict on Reading I (the refutation frame)

Report 02's four counts against Reading I are confirmed mechanically on its eight-atom
frame (`tests/witness_frames.py::frame_f3`, `tests/test_frame_oracle.py::test_f3_3_1` ..
`test_f3_3_4`): `{p,p'}` and `{q,q'}` verify but their fusion does not; `{p,p'}` verifies
and `{q}` falsifies with `{p,p',q}` possible; `{p,p'}` is part of `w0` where the
counterfactual is false; identity `(A □→ B) □→ (A □→ B)` fails at `w0`. Strengthened: the
null state is an `I`-falsifier (imposing `{a}` on it reaches `w3`), so the bridge gluts at
`w0, w1, w2` and soundness fails in the falsifier polarity too
(`test_f3_3_3_reading_i_verifier_sits_inside_a_false_world`). On the exhaustive n=3
population `I` fails exclusivity and both soundness polarities on all 24 contingent models
(`tests/test_candidate_structure.py`, `N3_FAILS["I"]`).

## 4. The exact family: characterized, and out

`tests/test_candidate_structure.py::test_f4_exact_sufficiency_characterization` pins, over
3,228 true worlds of the exhaustive n=3 population with 0 mismatches: an exact clause has a
verifier below a true world `w` iff every alternative of `w` under every `A`-verifier carries
a `B`-verifier that is *already part of `w`*. So the family verifies only truths whose
consequent material survives the imposition — never a genuinely counterfactual truth (`B`
false at `w`, `A □→ B` true there).

| Key | closure V/F | exhaustive | sound V/F | sufficient V/F | contingent models with a proper possible verifier (of 24) |
|-----|-------------|------------|-----------|----------------|-----------------------------------------------------------|
| XS | 0/0 | 3192 | 6/0 | 1554/1644 | 6 |
| XPe | 3/18 | 3192 | 6/0 | 1554/1644 | 6 |
| XPa | 0/0 | 3198 | 0/0 | 1560/1644 | 0 |

(Counts of models failing the property out of 3,204; `test_n3_exhaustive_failure_counts`;
`baselines/04_structure-matrix.json` carries the full table with witnesses.) The
self-based members are unsound (report 02's holism: `V_XS = {b}` on the F3 frame with
`b ⊑ w0`), the world-based members are insufficient in about half of all models and
non-exhaustive almost everywhere, and every member fails modus ponens at nested antecedents
(`XPa`: 389 of 1,500 sampled models; `tests/test_candidate_logic_oracle.py`). Requiring the
consequent to be verified rather than true is exactly what prevents verifying counterfactual
truths, so within the fixed truth clause the family must give up sufficiency and
exhaustivity, and its self-based members soundness. It does not refute the settler argument
by being sound and sufficient.

## 5. Structure matrix

Counts of models failing each property; `0` everywhere means sound, sufficient, exclusive,
exhaustive and fusion-closed in both polarities on that population
(`tests/test_candidate_structure.py`; `baselines/04_structure-matrix.json`).

| Population | I | ILC | ILMC | W | L | MC | SRC |
|------------|---|-----|------|---|---|----|-----|
| n=3 exhaustive (3,204; 24 contingent) | exclusivity 24, soundness 24/24 | 0 | 0 | 0 | 0 | 0 | 0 |
| n=4 sample (300, seed 11; 11 contingent) | closure F 1, exclusivity 11, soundness 6/11 | 0 | 0 | 0 | 0 | 0 | exhaustive 1, sufficient F 1 |

Possible verifiers / falsifiers properly below a world, per contingent model
(`test_proper_verifier_desideratum`):

| Population | ILC | ILMC | W | L | MC | SRC | I |
|------------|-----|------|---|---|----|-----|---|
| n=3 exhaustive (24) | 0 / 24 | 0 / 24 | 0 / 0 | 0 / 24 | 0 / 24 | 0 / 24 | 24 / 24 |
| n=4 sample (11) | 6 / 11 | 6 / 11 | 0 / 0 | 6 / 11 | 6 / 11 | 2 / 7 | 10 / 11 |

Random frames at n=5 and n=6 (research run, `baselines/03_research-exploration-output.txt`,
not pinned): `ILMC` has proper possible verifiers in 20 of 23 and 10 of 11 contingent
models. On the F3 frame `ILMC`'s verifiers are `{a.p', a.q', a.p'.q', a.b, a.p'.b, a.q'.b,
a.p'.q'.b}`, five of them possible proper parts of worlds; its falsifiers include `p.q` (the
part of `w0` that survives imposing `a` and leads to `w3`), `a'` and `b'`
(`tests/f3_candidate_sets.json`, `test_f3_ilmc_proper_verifiers_and_il_closure_witness`).

Why the settled clauses are clean: every member is a settler (soundness by definition); a
possible fusion of a settler and a co-settler would lie below a world both true and false
(exclusivity); every true world `w` satisfies `I(w) = T(w)` and settles trivially, so
`w ∈ IL` (sufficiency, hence exhaustivity with bivalence); `IL` fails closure only at
impossible fusions (`a.p.p' ⊔ a.q.q'` on F3), which `ILC`/`ILMC` repair and which no world
contains (`test_impossible_verifiers_are_harmless_for_every_candidate`).

**The mechanism constraint bites (Frame G, 7 atoms).** Worlds `a.x.b'`, `a.x.c.b`,
`a'.x.y.c.b`; `|A| = ({a},{a'})`, `|B| = ({b},{b'})`. The settlers `y` and `a'` survive no
imposition of `a` (`[y]_a = {null}`), so `Alt(y, a)` contains `a.x.b'` where `B` is false:
they settle but are not `I`-verifiers. Hence `IL ≠ L` and `ILMC ∩ possible = {c, b, c.b}`
while `MC ∋ a', y` (`test_frame_g_settlers_that_survive_no_imposition`,
`test_frame_g_il_differs_from_l_and_ilmc_from_mc`). At n ≤ 4 the two coincide on possible
states, which is why the tables above show identical columns for `ILMC` and `MC`.

**The remainder clause (SR/SRC).** The best clause without a minimality step and the source of
the most natural exact falsifier (`p.q` on F3), but insufficient in two structurally
identifiable situations: holism (Frame F3z: at `w4 = a'.p.p'.b.z` the counterfactual is true,
the only remainder `p.p'.b` is part of the false world `w0`, so nothing below `w4` settles;
`ILMC` verifies `w4` via `p'.z`, `b.z`, `p'.b.z` —
`test_frame_f3z_remainder_clause_is_insufficient_at_the_holistic_world`) and
antecedent-incompatible worlds (world `d` with `[d]_b = {null}`: no `SRC` falsifier;
`ILMC`/`MC` give `d` — `test_src_null_remainder_model_has_no_falsifier_at_d`).

## 6. Nested-antecedent logic

`X := A □→ B` under the candidate; counts of models (of 1,500 sampled at n=3, seed 23) with a
world at which the principle fails (`tests/test_candidate_logic_oracle.py::test_f7_*`;
`baselines/06_logic-matrix.json`); Z3 outcome at N=3 for the same schemata
(`tests/test_candidate_logic.py::test_nested_schema_matches_the_oracle_profile`; every cell
agrees with the oracle).

| Key | identity `X □→ X` | MP `X, X □→ C ⊢ C` | strengthening `X □→ C ⊢ (X ∧ D) □→ C` | `□(X → C) ⊢ X □→ C` | `X □→ C ⊢ □(X → C)` | might identity |
|-----|-------------------|--------------------|----------------------------------------|----------------------|----------------------|----------------|
| I | 22 (countermodel) | 0 | 6 (countermodel) | 8 (countermodel) | 0 | 22 (countermodel) |
| ILC, W, L | 0 | 0 | 0 | 0 | 0 | 0 |
| **ILMC**, MC | 0 (theorem) | 0 (theorem) | 361 (countermodel) | 0 (theorem) | 700 (countermodel) | 0 (theorem) |
| SRC | 0 | 0 | 200 | 0 | 372 | 0 |
| XPa | 0 | 389 | 4 | 0 | 402 | 0 |
| XS | 7 | 384 | 8 | 2 | 400 | 0 |

- Any clause whose verifiers include every true world collapses `X □→ C` to `□(X → C)` in
  both directions: imposing a world state on any world yields that world, so the nested
  counterfactual ranges over all true worlds of `X`
  (`test_every_true_world_verifying_collapses_to_the_strict_conditional`, checked at every
  world of every sampled model for `ILC`). This holds for `ILC` although `ILC` is
  hyperintensional.
- Removing the non-minimal settlers (`ILMC`, `MC`) gives the base counterfactual profile —
  identity and modus ponens valid, antecedent strengthening invalid (as `CF_CM_1`), the
  strict conditional entails the counterfactual but not conversely (as `CF_TH_11` versus
  `CF_CM_24`-style examples) — and a sampled model where `ILMC` separates the two
  (`test_ilmc_separates_the_counterfactual_from_the_strict_conditional`; the model is in
  `06_logic-matrix.json`).
- `I` fails identity because it is unsound; the exact family fails modus ponens because it is
  insufficient.

## 7. Hyperintensionality at nested position

Same truth-set pairs `A □→ B` versus `C □→ D` with distinct propositions
(`test_f8_hyperintensionality_counts`, seed 37, 723 pairs of 1,500 models at n=3;
`baselines/07_hyperintensionality.json`): `I` 1; `ILC`, `ILMC`, `W`, `L`, `MC` 0; `SRC` 403;
`XPa` 480; `XS` 482. The zeros for the settled clauses at this sample size are a **sampling
artefact**, not a coincidence of small frames:

- **n=4 possible-state separation (oracle, 4 atoms).** In 20,000-model samples at n=4
  (`baselines/10_possible-state-separation-n4.json`), `ILMC` and `ILC` have same-truth-set
  pairs whose propositions differ on *possible* states (1 and 3 of 9,784 pairs; 1 and 2 of
  9,919 in a second sample), and `L`, `MC` never do. The `ILMC` witness — worlds `a.b, b.c,
  a.d, b.d` — gives `V(A □→ B) ∩ possible = {a.b, c}` and `V(C □→ D) ∩ possible = {a.b,
  b.c}` while `MC` gives `{a.b, c}` for both
  (`test_n4_witness_separates_on_possible_states`, `test_n4_ilmc_witness_details`,
  `tests/n4_separation_witnesses.json`). This is a direct separation of `ILMC` from `MC` at
  four atoms.
- **Z3 confirmation at N=4.** The constitutive comparison — premise `□((A □→K B) ↔ (C □→K
  D))`, conclusion `(A □→K B) ≡ (C □→K D)`, constitutive subtheory loaded — has a
  countermodel for `I`, `ILC` and `ILMC` at N=4 and none for `W`, `L`, `MC`
  (`test_constitutive_comparison_outcome`; at N=3 only `I` has one). The oracle re-evaluates
  each Z3 model and confirms that the settled clause separates the pair while the truth-set
  functions do not (`test_constitutive_countermodel_is_confirmed_by_the_oracle`). The
  particular countermodel Z3 returns is seed-dependent and may separate the pair only on
  impossible states (`baselines/09_constitutive-countermodels.json`): `≡` compares whole
  verifier and falsifier sets, as it does for sentence letters, so impossible members of
  `ILMC` are visible to it even though they are invisible at the bridge.
- **Frame G2 (8 atoms, oracle).** `A □→ B` and `C □→ D` are true at exactly the same three
  worlds; `L`, `MC`, `W` give identical propositions; `IL`, `ILC`, `ILMC` give distinct ones
  (`x'` verifies the first only; `a'`, `y` the second only), and under `ILMC` the difference
  shows in nested truth values: `(A □→ B) □→ C` is false at every world while `(C □→ D) □→
  C` is true at three of four (`test_frame_g2_*` in `test_candidate_logic_oracle.py`). Under
  `ILC` the nested truth values agree — the strict collapse hides the difference, which only
  `≡`-style operators can see.

## 8. Regression over the existing examples

`examples.py` places no counterfactual in a verifier-consuming position and no constitutive
operator, and premise/conclusion constraints use only the shared `true_at`/`false_at`, so the
37 examples cannot separate candidates. Run once as a sanity check
(`baselines/05_regression-matrix.json`, `candidate_examples.regression_examples`): every
candidate meets every example's expectation, identically; a four-example guard per candidate
stays in `tests/test_candidate_logic.py::test_regression_guard`.

## 9. The settler argument (report 02, F4)

- Its first step stands and is measured: sound means every verifier is a settler, sufficient
  means every true world contains one; no sound clause measured ever had a non-settler
  verifier and no sufficient clause ever missed a true world.
- Its conclusion — no context-free sound clause is hyperintensional except by fiat — is
  refuted by `IL`, `ILC`, `ILMC`: the selection among settlers is a semantic clause of the
  same shape as the truth clause (imposition on the candidate state), and it separates
  counterfactuals with identical truth-sets on Frame G2, on 4-atom models, and in Z3's
  constitutive comparison at N=4.
- What survives: possible verifiers are settlers, so (i) in some contingent models — all 24
  at n=3 — nothing proper verifies and only proper falsifiers exist, and (ii) a sufficient
  clause that keeps every true world as a verifier collapses nested antecedents to the strict
  conditional. Escaping (ii) needs the minimality step; nothing in the imposition machinery
  short of it removes the world states without also losing sufficiency (Sections 4, 5).

## 10. Recommendation: ILMC

`\boxrightILMC` (`ExactSettlingImpositionCounterfactual`, `candidates.py`) is the recommended
clause. It is the only clause measured that is, at once: context-free; built entirely from
the imposition machinery; sound, sufficient, exclusive, exhaustive and fusion-closed in both
polarities on every population measured (Section 5); hyperintensional on possible states at
four atoms and confirmed by Z3 at N=4 (Section 7); non-strict at nested antecedents with the
base counterfactual profile (Section 6); and supplied with possible verifiers properly below
world states in most contingent models from n=4 on (Section 5), with a possible proper
falsifier in every contingent model measured.

Against each alternative:

- `ILC` (mechanical control): same structural profile and the same proper verifiers, but
  collapses nested antecedents to the strict conditional in both directions; its
  hyperintensionality is visible only through `≡`.
- `I`: refuted (Section 3).
- `SRC`: sound, non-strict and hyperintensional, but insufficient and non-exhaustive at
  holistic and antecedent-incompatible worlds (Section 5).
- The exact family: cannot verify counterfactual truths (Section 4).
- `W`, `L`, `MC`: disqualified as truth-set functions; `MC` additionally admits settlers
  that survive no imposition (Frame G, the n=4 witness), which `ILMC` excludes.

### Concessions

1. Every possible verifier is a settler: a possible state verifies `A □→ B` only if every
   world containing it makes the counterfactual true. This is soundness, and no candidate
   escapes it.
2. V3 is a parthood-minimality step. It is an extremal condition of the same kind as
   `max_compatible_part`'s maximality, applied to a set (`IL`) built from antecedent
   verifiers and imposition, not to the truth-set; without it (`ILC`) the nested logic is
   strict.
3. In some contingent models — all of them at n=3 — nothing proper verifies; only proper
   falsifiers exist. Proper verifiers appear from n=4 on (6 of 11 sampled contingent models;
   20 of 23 at n=5).
4. `ILMC`'s verifier and falsifier sets contain impossible states (fusions of minimal
   members, and minimal members that are themselves impossible). They lie below no world and
   are harmless at the bridge, but `≡` sees them, exactly as it sees a letter's impossible
   fusions.
5. Nested truth values do not separate `ILMC` from `MC` on any sampled population; the
   separation is in the proposition (Frame G, the n=4 witness) and therefore in `≡`.
6. The tensed generalization (world histories) is not addressed; the untensed fragment is what
   was measured.
7. The existing `\boxright` is untouched: the candidate operators sit beside it, and adopting
   `ILMC` as the successor remains a separate decision.

### Further tests

- `ILMC` versus `MC`: a nested example whose antecedent-incompatible minimal settler reaches a
  consequent-separating world would show the difference in truth value rather than in
  proposition; none was found among the consequents tried on Frame G. The proposition-level
  separation is already established at 4 atoms and can be run through Z3's constitutive
  comparison by constraining the frame to the recorded witness. The choice is otherwise
  conceptual — whether a state that survives no imposition of the antecedent should count as
  a ground of the counterfactual — and `MC` is disqualified in any case.
- `ILC` versus `L`/`W`: separated by `≡` at N=4 in Z3 and by the n=4 oracle witnesses; the
  nested logic is identical (strict) and cannot separate them.
- `ILMC` versus `ILC`: separated by the nested logic (Section 6); the structural profile is
  identical.

## 11. Two findings about the machinery

- `CounterfactualOperator.true_at`/`false_at` reused the constant names `t_cf_x`/`t_cf_u`
  at every nesting level; because `utils.ForAll` expands quantifiers by name substitution, a
  counterfactual in consequent position captured the outer clause's bound world and lost its
  own evaluation world. Each call now draws fresh names
  (`test_status_quo_audit.py::test_nested_consequent_keeps_its_evaluation_world`). The
  semantics is unchanged and the 37 examples' expectations are unchanged.
- The research script's letter `C = ({c}, {y})` on Frame G violates the logos letter
  constraints (`b'` is compatible with neither); Frame G carries only `A`, `B` and the
  same-truth-set comparison uses Frame G2, whose four letters are compliant.

## 12. Reproduction

- Oracle: `pytest tests/test_frame_oracle.py tests/test_candidate_structure.py
  tests/test_candidate_logic_oracle.py` (seconds).
- Z3: `pytest tests/test_candidate_operators.py tests/test_candidate_logic.py` (a few
  minutes); `./dev_cli.py candidate_examples.py` for the curated collection.
- Baselines (task directory `baselines/`): `04_structure-matrix.json`,
  `05_regression-matrix.json`, `06_logic-matrix.json`, `07_hyperintensionality.json`,
  `08_nesting-cost.json` (direct encoding retained; `ILMC` nested at N=4 in about 1 s),
  `09_constitutive-countermodels.json`, `10_possible-state-separation-n4.json`.
