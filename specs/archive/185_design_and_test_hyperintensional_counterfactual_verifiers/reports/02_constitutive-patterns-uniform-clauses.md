# Research Report: Constitutive Clause Patterns and Uniform Verifier Clauses

**Task**: 185 - Design and test hyperintensional counterfactual verifiers (follow-up analysis)
**Date**: 2026-09-08
**Sources**:
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py` (≡, ≤, ⊑, ≼, ⇒)
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py` (□, ◇, \CFBox, \CFDiamond)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`, `candidates.py` (status quo, ILMC)
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py` (¬, ∧, ∨, ⊤, ⊥, →, ↔)
- `code/src/model_checker/theory_lib/logos/semantic/core.py`, `semantic/proposition.py`
- `code/src/model_checker/syntactic/sentence.py` (`derive_type`: defined operators are expanded at parse time)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/report/verifier_clauses.md` (the task 185 recommendation)
- `~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/01_*.md`, `02_*.md`
- `~/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ` (`@def-propid-verification`, `@def-essence-ground`)
**Evidence produced by this report**: `baselines/11_uniformity-experiments.py` and
`baselines/11_uniformity-experiments-output.txt` (13 Z3 examples at N=3, all outcomes as
predicted; run with `./dev_cli.py`).

---

## Executive Summary

1. **The logos language has exactly two mechanisms for assigning verifiers, and their
   direction of definition is opposite.** The extensional operators build verifiers from the
   verifiers of their parts and derive truth from them (the bridge). Every other operator
   (constitutive, modal, counterfactual) writes a truth clause first and then *derives* its
   verifier set from that truth. The bridge (`true at w` iff some verifier is part of `w`) is
   the invariant that links the two; it holds for every clause in the code except the status
   quo counterfactual at a world other than the evaluation world.

2. **The null-state clause of the constitutive and modal operators is the degenerate case of
   the ILMC recipe, not a separate convention.** ILMC says: `s` verifies `φ` iff `s` is a
   fusion of parthood-minimal states `t` such that `φ`'s own truth clause holds with `t` in
   the world slot and at every world above `t`. When the truth clause does not read the world
   slot (≡, ≤, ⊑, ≼, □, ◇), every state passes, the unique minimal state is the null state,
   and the recipe returns `{□}` exactly as `constitutive/operators.py` and `modal/operators.py`
   hard-code it. Z3 confirms the consequence the status quo fails: `□A ≡ (⊤ □→ILMC A)` is a
   theorem at N=3 (U1), while `□A ≡ (⊤ □→ A)` has a countermodel (U2). ILMC therefore restores
   agreement between the modal subtheory's `\Box` and the manual's definition `□A := ⊤ □→ A`.

3. **A single principle covers all three families: the exact verifiers of a sentence are the
   least states that settle it, where "settle" is measured by the operator's own truth
   clause.** Null for what depends on nothing (constitutive, modal), parts of the world for
   what depends on parts (atoms, ∧, ∨), minimal settlers for what depends holistically on the
   world (counterfactuals). Round 2 of the Logos research stated the two ends of this principle
   (null state / whole world-history); ILMC is the middle, and it is the middle precisely
   because its inner condition `I(t)` is hyperintensional while the settler condition `L(t)`
   is not.

4. **The recipe cannot replace the compositional clauses, so the two mechanisms are
   irreducible.** Applied to `A ∧ B` with `|A|⁺ = {a}` and `|B|⁺ = {a.b, b.c, a.b.c}` the
   recipe returns `{a.b}` and loses the exact verifier `a.b.c`. Exactness for content-building
   operators is primitive; exactness for world-quantifying operators has to be manufactured.
   The minimality step V3 is that manufacturing step and is best documented as Fine's
   *whole relevance*, not as an "extremal condition".

5. **The constitutive operators are only as context-free as their operands.** `≡` threads the
   evaluation point into `extended_verify` of both operands, so with the status quo clause
   `(A □→ B) ≡ (C □→ D)` is true at any world where both are true. Context-freedom of every
   verifier clause is therefore *forced* by the presence of a constitutive identity operator,
   which is the deepest reason task 185's governing criterion is right.

6. **Every true constitutive claim, and every true necessity, is the same proposition
   `⟨{□}, ∅⟩`.** `(A ≤ B) ≡ (C ⊑ D)` follows from `A ≤ B` and `C ⊑ D` (U4); `□A ≡ □B` from
   `□A` and `□B` (U3); all counterpossibles coincide (U8). This is exactly the "intensional
   by fiat" behaviour task 185 disqualified for the counterfactual, and it is already the
   behaviour of five operators in the language. It should be recorded as a decision, as the
   manual records it for `≡`.

7. **A true constitutive antecedent turns `□→ILMC` into a minimisation of its consequent.**
   Imposing the null state on `t` yields the worlds above `t`, so `(A ≤ B) □→ILMC C` is true
   exactly where `C` is (U5) but its proposition is the fusion closure of the minimal settlers
   of `C`: in the U6 countermodel `|C| = ⟨{b.c, c}, {a, a.b}⟩` and
   `|(A ≤ B) □→ILMC C| = ⟨{c}, {a}⟩`. The settled core is neither a ground nor an essence of
   `C` (U11–U13). This is the clearest visible signature of V3 and a natural regression probe
   for any future revision of the clause.

8. **Six defined operators carry hand-written clauses that are dead code.** `derive_type` in
   `syntactic/sentence.py` expands every `DefinedOperator` at parse time, so the explicit
   `true_at`/`extended_verify` bodies on `MightCounterfactualOperator`, `CFNecessityOperator`,
   `CFPossibilityOperator`, `ReductionOperator`, `ConditionalOperator` and
   `BiconditionalOperator` are never invoked. One of them
   (`MightCounterfactualOperator.true_at`) is not even type-correct: it passes a Z3 `BoolRef`
   where a `Sentence` is expected. Uniformity lesson: a defined operator has one definition.

Recommendations (Section 6): define truth once by the bridge and drop `eval_point` from
`extended_verify`; implement the settler recipe once as a base class and re-derive the
null-state clauses from it, with `≡`-tests pinning the coincidence; record the constitutive
collapse as a decision; remove the dead clauses.

---

## 1. Inventory: three clause shapes

| Operator family | Truth clause quantifies over | Verifier clause | Verifier set | Reads eval world? | Context-free? |
|---|---|---|---|---|---|
| Atoms | parts of the world (`∃x ⊑ w. verify(x, p)`) | primitive `verify` | arbitrary fusion-closed set | no | yes |
| ¬, ∧, ∨ (and defined →, ↔) | nothing; truth recursion on parts | fusion / polarity swap of operand verifiers | `V_A ⊗ V_B`, `V_A ⊕ V_B`, `F_A` | no | yes |
| ⊤, ⊥ | constant | all states / none | `S` / `∅` (falsifiers `∅` / `{□}`) | no | yes |
| ≡, ≤, ⊑, ≼ | all states, via operand `extended_verify`/`extended_falsify` | `s = □ ∧ true_at` | `{□}` or `∅` | no (operand clauses may) | iff operands are |
| □ (◇ = ¬□¬) | all worlds | `s = □ ∧ true_at` | `{□}` or `∅` | no | yes |
| □→ status quo | `A`-verifiers and alternatives to the eval world | `s = w ∧ true_at` | `{w}` or `∅` | **yes** | **no** |
| □→ ILMC | same truth clause | `closure(min(I ∧ L))` | fusions of minimal settlers | no | yes |

Three observations about the table.

- **Direction of definition.** Rows 1–3 define truth from verifiers (the bridge is the
  definition of `true_at` for atoms and a theorem for the connectives). Rows 4–7 define
  verifiers from truth. The code carries two parallel recursions, `true_at` and
  `extended_verify`, and the family decides which one is primary.
- **Where `eval_point` is consumed.** Only the status quo counterfactual's verifier clause
  reads `eval_point["world"]`. The constitutive clauses pass `eval_point` down without reading
  it; the modal clause reads it only to shift worlds inside `true_at`. So the entire
  context-dependence of the language sat in one line: `state == world` in
  `CounterfactualOperator.extended_verify`.
- **Shape of the output.** Rows 4–6 produce exactly one of two propositions per polarity.
  Rows 1–3 and 7 produce exact-shaped (not upward-closed) sets that vary with content.

## 2. The null-state clause is the degenerate ILMC recipe

Write `T_φ(u)` for the truth clause of `φ` evaluated with state `u` in the world slot (the
code's `true_at` accepts any state there; `candidates.py` calls this `truth_at_world`). ILMC is

```
IL(t)  :=  T_φ(t)  ∧  ∀w (w a world ∧ t ⊑ w → T_φ(w))          -- I(t) ∧ L(t)
V(φ)   :=  { ⊔S : ∅ ≠ S ⊆ Min(IL) }                              -- closure(min(IL))
```

with falsifiers dually. Now instantiate:

- **Constitutive operators.** `T_{A≡B}(u)` compares `|A|` and `|B|` over all states and never
  reads `u`. So `IL` is every state when `A ≡ B` holds and empty otherwise; `Min(IL) = {□}`;
  `V = {□}`. This is `IdentityOperator.extended_verify` verbatim. The same holds for ≤, ⊑, ≼.
- **Necessity.** `T_{□A}(u)` quantifies over all worlds and never reads `u`; same result, and
  it is `NecessityOperator.extended_verify` verbatim.
- **⊤ as antecedent.** `|⊤|⁺` is every state. For any state `t` and any world `u`, `u` is an
  alternative to `t` under `u` itself (`max_compatible_part(z, t, u)` forces `z ⊑ u`), so
  `I(t)` for `⊤ □→ A` is `□A` for every `t`; `L(t)` likewise; `Min(IL) = {□}`. So under ILMC
  `⊤ □→ A` has verifier set `{□}` iff `□A`, which is the modal subtheory's clause. The status
  quo gives `{w}`.
- **⊥ as antecedent.** `|⊥|⁺ = ∅`, so `I` and `L` hold vacuously everywhere; `V = {□}`. A
  counterpossible is necessarily true and null-verified, as the manual's counterpossible
  vacuity proposition requires.

Z3 at N=3 (`baselines/11_uniformity-experiments-output.txt`):

| Example | Claim | Outcome |
|---|---|---|
| U1 | `⊢ □A ≡ (⊤ □→ILMC A)` | theorem |
| U2 | `⊢ □A ≡ (⊤ □→ A)` (status quo) | countermodel |
| U10 | `⊢ □(□A ↔ (⊤ □→ILMC A))` | theorem |
| U9 | `□A, □B ⊢ (⊤ □→ILMC A) ≡ (⊤ □→ILMC B)` | theorem |
| U8 | `⊢ (⊥ □→ILMC A) ≡ (⊥ □→ILMC B)` | theorem |

U1 versus U2 is the cleanest single piece of evidence that ILMC is the *uniform* clause: the
modal subtheory and the counterfactual subtheory currently disagree about what `⊤ □→ A` means
as a proposition, and ILMC makes them agree without any special case. Task 185's report did
not record this; it belongs in `verifier_clauses.md` and in the counterfactual README.

## 3. The general principle, and its two ends

The Logos round-2 report put it this way: the null state verifies what depends on nothing; a
world-history verifies what depends on everything; "the exact verifier of a claim is the least
state that settles it." ILMC occupies the middle of that scale, and the reason it can be
hyperintensional there is visible in the recipe:

- `L(t)` (every world above `t` makes `φ` true) is a function of the truth-set of `φ`. It is
  what soundness needs and it is intensional. Any clause built from `L` alone (`L`, `M`, `MC`
  in task 185's roster) is a truth-set function, which is why they were disqualified.
- `I(t)` (`φ`'s truth clause with `t` itself in the world slot) reads the imposition machinery
  on `t`, hence `|A|⁺` and `|B|`; it is hyperintensional. On its own it is unsound (Reading I).
- Their conjunction is the first sound *and* hyperintensional inexact relation; minimality and
  closure then exactify it.

So the general statement is: **`V(φ) = closure(min(I_φ ∧ L_φ))`, with `I_φ` the operator's
truth clause relativised to the candidate state and `L_φ` its settling condition.** For
world-invariant truth clauses `I` is trivial and the recipe returns the null state; for the
counterfactual it returns ILMC. This is one clause with two visible instances, and it is
exactly what "elegant, uniform, general" should mean here: the null-state convention stops
being a convention and becomes a computed case.

## 4. Where the recipe stops: compositional exactness is primitive

The recipe does not reproduce the extensional clauses, and it is important to say so rather
than to overreach.

- For an atom `p`, `I_p(t)` is "some `p`-verifier is part of `t`", so `IL` is the upward
  closure of `|p|⁺` and `closure(min(IL)) = closure(min |p|⁺)`. This equals `|p|⁺` only when
  `|p|⁺` is generated by its minimal elements. `{a, a.b}` is a legitimate fusion-closed atomic
  verifier set (`proposition.py` imposes closure, exclusivity, exhaustivity and the
  `contingent`/`non_null` settings, nothing about generation) and the recipe returns `{a}`.
- Generation is not preserved by conjunction even when both operands have it: with
  `|A|⁺ = {a}` and `|B|⁺ = {a.b, b.c, a.b.c}`, `|A ∧ B|⁺ = {a.b, a.b.c}` but
  `closure(min) = {a.b}`.
- Replacing a verifier set by its minimal core never changes truth at worlds, but it changes
  `≡` and it changes nested counterfactuals (imposing `a.b.c` and imposing `a.b` reach
  different alternatives). So the information in non-minimal exact verifiers is genuine
  content, and it is exactly what the extensional clauses are built to preserve.

Conclusion: the language has an irreducible two-mechanism structure. Content-building
operators (atoms, ¬, ∧, ∨) take exact verifiers as given and combine them; world-quantifying
operators (≡, ≤, ⊑, ≼, □, ◇, □→) have no given exact verifiers and must manufacture them from
their truth conditions, for which the settler recipe is the canonical procedure. The design
question for any new operator is which family it belongs to, and the answer is decided by
whether its truth clause quantifies over states or worlds beyond the evaluation world.

This also settles the status of V3. Minimality is not an extra stipulation on top of the
machinery; it is the recipe's rendering of Fine's requirement that an exact verifier be
*wholly relevant*, applied to a set (`IL`) in which relevance is not otherwise guaranteed.
Task 185's Concession 2 should be reworded accordingly.

## 5. Four further patterns

### 5.1 Constitutive operators inherit their operands' context-dependence

`IdentityOperator.true_at` is `∀x (verify(x, A, e) ↔ verify(x, B, e)) ∧ (falsify ...)` with the
same `eval_point` `e` threaded into both operands. With the status quo clause the operand sets
are `{w}` or `∅` at `e = w`, so `(A □→ B) ≡ (C □→ D)` holds at every world where the two
counterfactuals agree in truth value. That is the constitutive comparison task 185 used to
separate the candidates, and it shows the lesson in reverse: `≡` is a model-level relation
only if every operand clause is model-level. Since the manual defines ≤ and ⊑ *from* ≡
(`@def-essence-ground`) and the code's `find_verifiers_and_falsifiers` for ≤ and ⊑ compares
whole sets, any context-dependent operand clause silently breaks all four constitutive
operators at once. This is the strongest argument for the governing criterion of task 185 and
should be cited as such.

### 5.2 The constitutive collapse

| Example | Claim | Outcome |
|---|---|---|
| U3 | `□A, □B ⊢ □A ≡ □B` | theorem |
| U4 | `A ≤ B, C ⊑ D ⊢ (A ≤ B) ≡ (C ⊑ D)` | theorem |

All true constitutive claims and all true necessities express `⟨{□}, ∅⟩`; all false ones
`⟨∅, {□}⟩`. By task 185's own standard (Section 1 of the report: a clause whose verifiers are
a function of the truth-set is intensional by fiat) these five operators are intensional, and
in fact coarser than intensional: two necessarily equivalent but distinct constitutive truths
cannot be told apart by any operator in the language. The Logos round-1 report flagged the
same fact (its F6: `(p □→ q) ≡ (r □→ s)` was true in every model when counterfactuals had no
verifiers).

Two positions are available. (a) Accept it, with Fine and the manual: a constitutive claim
has no contingent subject matter, so the null state is its only exact verifier. (b) Treat it
as the same defect task 185 refused for the counterfactual and look for a content-bearing
clause. Position (a) is recommended: the recipe of Section 3 *derives* the null state from
the fact that these truth clauses read no state, and (b) would need verifiers built from
`|A|` and `|B|` (say fusions of an `A`-verifier and a `B`-verifier) that are not settlers of
anything and would break the bridge unless every state were also a verifier. What must
happen in either case is that the decision be recorded in the constitutive README, as the
manual records context-independence for `≡` (`@def-propid-verification`'s closing remark).

### 5.3 A null-verified antecedent minimises its consequent

Imposing `□` on a possible state `t` gives `max_compatible_part(z, t, □) = t`, so the
alternatives to `t` under `□` are the worlds above `t`, and `I_{X □→ C}(t)` for a
null-verified true `X` is `L_C(t)`. Hence:

| Example | Claim | Outcome |
|---|---|---|
| U5 | `A ≤ B ⊢ □(((A ≤ B) □→ILMC C) ↔ C)` | theorem |
| U6 | `A ≤ B ⊢ ((A ≤ B) □→ILMC C) ≡ C` | countermodel: `|C| = ⟨{b.c, c}, {a, a.b}⟩`, `|(A ≤ B) □→ILMC C| = ⟨{c}, {a}⟩` |
| U7 | same with the status quo | countermodel |
| U11 | `A ≤ B ⊢ ((A ≤ B) □→ILMC C) ≤ C` | countermodel |
| U12 | `A ≤ B ⊢ C ≤ ((A ≤ B) □→ILMC C)` | countermodel |
| U13 | `A ≤ B ⊢ ((A ≤ B) □→ILMC C) ⊑ C` | countermodel |

So `(A ≤ B) □→ILMC C` is truth-conditionally `C` but propositionally the fusion closure of
the minimal settlers and co-settlers of `C`: a "settled core" that drops non-minimal exact
verifiers (`b.c`) and impossible members (in U11's model the core's falsifiers are `{b}`
against `C`'s `{a.b.c, a.c, b}`). It is related to `C` by neither ground nor essence. Note the
contrast with `⊤`: because `|⊤|⁺` contains every world, `⊤ □→ C` is `□C`, whereas a
null-verified antecedent is centred. Whether "if `A` grounded `B` then `C`" ought to be
centred (it is under imposition of `□`) or strict (as under `⊤`) is a conceptual question the
present machinery answers in favour of centring; it is worth stating in the report because it
is the one place where the null-state clause and the ⊤ clause visibly diverge.

### 5.4 The constitutive clauses consume fusion closure as a contract

`GroundOperator.true_at` (Z3 side) asserts `V_A ⊆ V_B`, `F_A ⊗ F_B ⊆ F_B`, and that every
`B`-falsifier contains an `A`-falsifier; the Python side asserts
`coproduct(V_A, V_B) = V_B` and `product(F_A, F_B) = F_B`. These agree only if `V_B` and `F_B`
are fusion-closed: `V_A ∪ V_B ∪ (V_A ⊗ V_B) = V_B` needs `V_A ⊗ V_B ⊆ V_B`, which follows from
`V_A ⊆ V_B` by closure of `V_B`; and `F_B ⊆ F_A ⊗ F_B` is "every `B`-falsifier contains an
`A`-falsifier" only because `f = a ⊔ f` for `a ⊑ f`. The same holds for essence with
polarities exchanged. So fusion closure of every derived proposition is a contract the
constitutive operators rely on, and a counterfactual clause that failed closure (Reading I,
`IL` itself) would make `(A □→ B) ≤ C` disagree between the two sides. Task 185 measured
closure as one property among five; this is why it is not optional.

### 5.5 Dead duplicate clauses on defined operators

`syntactic/sentence.py::derive_type` rewrites every non-primitive operator into its
`derived_definition` before any semantic method is called. The explicit `true_at`, `false_at`,
`extended_verify`, `extended_falsify` and `find_verifiers_and_falsifiers` bodies on
`MightCounterfactualOperator`, `CFNecessityOperator`, `CFPossibilityOperator`,
`ReductionOperator`, `ConditionalOperator` and `BiconditionalOperator` are therefore never
executed. `PossibilityOperator` and the candidate might-variants in `candidates.py` already
follow the correct pattern (definition only). The dead bodies are a maintenance hazard: the
might-counterfactual's passes `neg_op.true_at(rightarg, eval_point)`, a `BoolRef`, as the
consequent sentence, which would raise if it ever ran. For uniformity every defined operator
should carry its definition and nothing else.

## 6. Recommendations

R1. **One recursion, truth by the bridge.** Define `LogosSemantics.true_at(φ, w)` as
`∃s ⊑ w. extended_verify(s, φ)` for every `φ`, and `false_at` dually, and drop `eval_point`
from `extended_verify`/`extended_falsify` (verifier sets are model-level). Inside ILMC, replace
"`B` true at `u`" by "`∃b ∈ |B|⁺. b ⊑ u`" and dually; the counterfactual's truth clause `T`
becomes an auxiliary definition inside its verifier clause, stated over `|A|⁺`, `|B|`,
`is_alternative` and parthood, in exactly the shape of the constitutive clauses. Soundness and
sufficiency, which task 185 *measured*, become the theorem that the derived truth agrees with
the imposition clause. Cost: every operator's `true_at` is deleted or becomes derived; the
ordinary counterfactual examples are the regression suite.

R2. **Implement the settler recipe once.** A base class (`SettledOperator`) with a single
abstract `truth_clause(state, *args)` and the generic `closure(min(I ∧ L))` verifier and
falsifier clauses; `candidates.py` already has `settler_at`, `minimal_clause` and
`closure_clause` as generic building blocks. Make □ and the four constitutive operators
instances, and pin the coincidence with the hand-written clauses by `≡`-theorems of the U1
kind (`\Box A ≡ \BoxSettled A`, `(A ≤ B) ≡ (A ≤_settled B)`). Then the three null-state clauses
disappear as separate code and the modal/counterfactual disagreement of U2 cannot recur.

R3. **Record the constitutive collapse (Section 5.2) as a decision** in the constitutive
README, and add U3/U4 as examples so the behaviour is pinned rather than incidental.

R4. **Delete the dead clauses** listed in Section 5.5; keep `derived_definition` and
`print_method` only.

R5. **Extend `verifier_clauses.md`** with: the U1/U2 result (ILMC is conservative over `\Box`);
the settled-core behaviour of null-verified antecedents (U5–U13) as a further test; the
reworded Concession 2 (V3 as whole relevance); and Section 5.1's argument that `≡` forces
context-freedom.

R6. **Further tests.** Re-run U1–U13 at N=4; run the same schemata under `\boxrightILC` and
`\boxrightMC` (prediction: U1 holds for all three, since `⊤`'s verifiers include every
world; U6's settled core is the same for ILMC and MC on small frames and differs on Frame G);
apply the recipe to `imposition/operators.py`, whose counterfactual has the same status quo
clause and the same fixed bound-variable names task 185 flagged; and, if the recipe is
adopted, generate the extended tense/bimodal clauses from it rather than by hand.

## 7. Reproduction

```
cd code
./dev_cli.py ../specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/11_uniformity-experiments.py
```

Thirteen examples, N=3, all under one second of solver time each; expectations in the file
are the predictions of Sections 2 and 5 and every example reports the predicted outcome.
