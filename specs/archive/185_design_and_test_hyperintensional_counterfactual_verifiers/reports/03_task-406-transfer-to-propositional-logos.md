# Research Report: What Logos Task 406 Settles for the Propositional Logos Theory

**Task**: 185 follow-up (reads Logos Theory task 406 as it stands on 2026-09-09)
**Sources**:
- `~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/` — reports 01–03, plan
  `03_ilmc-family-verifier-clause.md`, `.decisions.json`, phase progress files 1–9, `.return-meta.json`
- Logos commits `714a7e14`..`36cb8851` (phases 1–9, all in `typst/manual/chapters/03-dynamics.typ`)
- New manual labels read from the diff: `@def-altworlds-family`, `@def-family-parthood`,
  `@prop-family-parthood-join`, `@def-counterfactual-verification`, `@def-minimal-settler`,
  `@prop-box-diamond-null-verified`, `@prop-stability-non-null`, `@rem-causal-not-recipe`,
  `@rem-event-status-ilmc`, `@rem-bridge-soundness-counterfactual-cases`, the actuality
  falsification clause and `@rem-event-actuality-falsification-properties`
- This repository: `reports/02_constitutive-patterns-uniform-clauses.md`, task 186's
  `reports/01_family-level-settled-verification.md`, `counterfactual/candidates.py`
**New evidence**: `baselines/12_transitivity-and-settled-core.py` and its output (6 Z3 examples,
N=3 and N=4, all as predicted)

---

## 1. Where task 406 stands

Task 406 is `[IMPLEMENTING]`, with the manual half done and the Lean half not started.

| Piece | State |
|---|---|
| Report 03 (family-level ILMC) | complete; consumes task 185's measurements as data and refutes report 02's F4 |
| Plan 03, 16 phases | phases 1–9 (manual, `03-dynamics.typ`) committed; phase 10 (proof-theory chapter) in progress; phases 11–16 (Lean) not started |
| Decision D6 | **ILMC adopted, in both manual and Lean, no split.** Rationale recorded by the user: ILC is inexact by the framework's own standard; the strict collapse is the symptom, inexactness the disease; ILMC keeps the counterfactual an instance of the parthood principle rather than a special case |
| Decision D7 | obligation (N) discharged by a **Minimal Settler frame constraint**, the exact dual of the two maximality constraints; descending-chain hypotheses rejected because the Lean state type has infinite descending chains |

Two of the task's own premises were overturned on the way: counterfactuals are not null-verified
across the board (the null family verifies exactly the necessary ones), and the feared collapse of
all true counterfactuals into one proposition is not incurred.

## 2. What transfers to the propositional logos theory

The ModelChecker logos theory is the untensed fragment: world-histories are world states, anchored
families are states, domains are trivial. Everything below is read through that collapse.

### 2.1 The successor decision is made

Task 185 left adoption of ILMC as `\boxright`'s successor open (Concession 7). Task 406 has now
adopted ILMC upstream, for the manual the logos theory is meant to implement, with an explicit
rejection of ILC and of any manual/implementation split. There is no longer a reason to keep the
status quo clause as the primary operator here. The candidate roster stays as comparison
baselines, exactly as 406 keeps Reading W as a baseline.

### 2.2 The uniform principle is now manual text, and it fixes the architecture

The manual now states the principle report 02 of this task proposed, as
`@rem-cf-primitive-truth` with three instances: atomic truth, propositional identity, and the
counterfactual (`@def-counterfactual-verification`'s closing prose). Three consequences for the code:

- **Truth by the bridge.** The manual's V1 renders the consequent's truth at an alternative as
  *bridge-truth*, that is, parthood of a consequent verifier, not as a recursive truth call. The
  same choice belongs in `candidates.py`: replace `truth_at_world`'s use of `true_at(rightarg, ·)`
  by `∃b ∈ |B|⁺. b ⊑ u`, and dually. Here this is exactly faithful, because the two boundaries the
  manual has to record (`@rem-bridge-soundness-counterfactual-cases`: positive `∀` in a CF
  constituent, since/until at a non-`⊤` guard) involve quantifiers and tense that the propositional
  language lacks. It also removes the nested `true_at` recursion that produced the bound-variable
  capture task 185 fixed, and that `imposition/operators.py` still carries.
- **Necessity is derived, not stipulated.** `@prop-box-diamond-null-verified` derives the null
  clauses for `□` and `◇` from the counterfactual clause at antecedent `⊤`, and states that the
  modal clause and the abbreviation must agree. Report 02's U1 (`□A ≡ (⊤ □→ILMC A)` a theorem) is
  the same fact here and should become a permanent regression test; the status quo fails it (U2).
- **Compositional operators are excluded by name** (`@rem-causal-not-recipe`): the recipe must not
  replace exact compositional clauses. This matches report 02's Section 4 and settles it as
  design, not observation.

### 2.3 The manual's stability operator is the "settled core" found here

`@prop-stability-non-null` gives `S φ` the clause: `π` verifies `S φ` iff `dom(π) = {x}` and every
world-history `β` with `π(x) ⊑ β(x)` makes `φ` bridge-true, that is, every world above the state
makes `φ` true; the members are minimal and fusion closed. In the untensed fragment that is precisely the fusion closure of the minimal settlers of
`φ`, which report 02's U6 exhibited as the proposition of `(A ≤ B) □→ILMC C` (`⟨{c},{a}⟩` from
`|C| = ⟨{b.c, c},{a, a.b}⟩`). The manual's own sanity check (`@rem-counterfactual-verification-sanity-check`)
says the same thing: a null-verified antecedent turns `□→` into `S`. Two new checks confirm the
reading is antecedent-independent:

| Example | Claim | Outcome |
|---|---|---|
| T5 | `A ≤ B, D ⊑ E ⊢ ((A ≤ B) □→ILMC C) ≡ ((D ⊑ E) □→ILMC C)` | theorem |
| T6 | `A ≤ B ⊢ ((A ≤ B) □→ILMC C) ≡ ((⊤ □→ILMC ⊤) □→ILMC C)` | theorem |

So the untensed logos theory is missing an operator the manual has: `S` (stability), whose truth
clause is trivial here (`S φ` is true where `φ` is, since the stability class of a world is that
world) but whose *proposition* is not `|φ|`. It is the cleanest example in the language of an
operator that separates truth from content. Adding it is a small change (one application of the
recipe to the identity truth clause) and makes `((A ≤ B) □→ C) ≡ S C` a statable theorem.

### 2.4 Weakened transitivity does not regress here

Task 406's F8 records a genuine cost of the family-level clause: C3 (weakened transitivity,
`X □→ Y, (X ∧ Y) □→ Z ⊢ X □→ Z`) loses the one case Reading W had won, because ILMC verifiers can
have proper domains and the `(X ∧ Y)`-verifier's domain can grow. That obstruction cannot arise
without domains. Measured here (`baselines/12_*`):

| Example | Antecedent | Clause | N | Outcome |
|---|---|---|---|---|
| T1 | atomic `A` | status quo | 3 | theorem |
| T2 | atomic `A` | ILMC | 3 | theorem |
| T3 | nested `A □→ILMC B` | ILMC | 3 | theorem |
| T4 | nested `A □→ILMC B` | ILMC | 4 | theorem |

Weakened transitivity holds under ILMC in the propositional fragment at both atomic and nested
antecedents, on every model up to four atoms. This is worth feeding back to task 406: the C3
regression is purely a domain-growth phenomenon (obstruction 1), and obstruction 2 ("maximality
does not absorb Incorporation") shows no effect at N ≤ 4 in the untensed setting. Whether it
appears at larger N is unmeasured.

### 2.5 The Minimal Settler constraint is a theorem here

Task 406 had to *adopt* the existence of minimal IL-members as a frame constraint
(`@def-minimal-settler`), because the Lean state lattice is not well-founded. In finite state
spaces every nonempty set has minimal elements, so the constraint is a theorem and sufficiency was
already measured with zero failures. Two things follow: the counterfactual README should say that
ILMC's E4 and modus-ponens side condition rest on finiteness here and on the constraint in the
manual; and if the bimodal theory (time indexed by ℤ) ever receives ILMC, the constraint must be
imported rather than assumed.

### 2.6 Exclusivity: the manual's phrasing matches what was measured

Task 406 found that the manual's pointwise exclusivity fails for the recipe's events on
impossible-valued members, while the "history form" (no world above both a verifier and a
falsifier) holds unconditionally from V2/F2 and bivalence, and it left `@def-anchored-event`
unamended. Task 185's exclusivity measurement is the history form (a possible fusion of a verifier
and a falsifier would lie below a world). So the two repositories agree, and the residual —
impossible members visible to `≡` — is task 185's Concession 4 in both.

### 2.7 A defect in phase 9 that the propositional logic makes visible

Phase 9 gave `Act(t)` a falsification clause by the recipe **without** the minimality step, on the
stated ground that "the motivation for minimality elsewhere is avoiding the strict-conditional
collapse at nested antecedents, which does not apply here, since `Act(t)` has no antecedent of its
own to nest." That misplaces where minimality bites. The collapse is a property of *antecedent
position*, and negation swaps polarities: the falsifiers of `Act(t)` are the verifiers of
`¬Act(t)`. With closure only, every world state at which `Act(t)` is false is a co-settler and
hence a verifier of `¬Act(t)`, so `(¬Act(t)) □→ C` reduces to the strict conditional, exactly the
ILC row of task 185's nested-logic table. With minimality the co-settlers are the minimal states
incompatible with `⟦t⟧`, which is the exact clause. The second reason given, that the co-settler set
is not shown closed under infima, is the same gap `@def-minimal-settler` already discharges for
`IL⁻`; extending the constraint to `Act` costs nothing new.

The general lesson for this repository: **every settler-derived clause needs minimality in both
polarities, whatever the operator's arity**, because `¬` will put its falsifiers into antecedent
position. `candidates.py` already does this; any future operator built on `settler_clause` must too.

### 2.8 What does not transfer

- The lifted DT antecedent restriction (phase 7): the logos theory never had one.
- The domain convention `D = dom(π) ∩ dom(α)` in `Alt(π, α)`, the family parthood order, and
  extension-fusion as join: all collapse to state parthood and fusion.
- The two faithfulness boundaries and C2's convexity sub-case: quantifier and tense phenomena.
- The Lean `Interp` widening and the `Bridge.lean` ripple.
- The stability-class reading of `□` as `S` versus `□`: here the stability class of a world is
  itself, so `(A ≤ B) □→ C` is centred (U5) and `⊤ □→ C` is `□C`; the manual's contrast between
  the two is visible only with time.

## 3. Recommended follow-up for the logos theory

In order of leverage:

1. **Adopt ILMC as `\boxright`.** Move `ExactSettlingImpositionCounterfactual`'s clause into
   `CounterfactualOperator`; keep the roster as baselines; `\CFBox`/`\CFDiamond` then agree with
   `\Box`/`\Diamond` by U1. Task 185's 37 examples are unaffected (regression matrix).
2. **State V1 through the bridge** (`∃b ∈ |B|⁺. b ⊑ u`), and define `true_at` by the bridge for
   every operator, per report 02's R1; the manual now does the former and its principle licenses
   the latter. This also retires the fixed bound-variable names in `imposition/operators.py`.
3. **Add `S` (stability)** as the recipe applied to the identity truth clause, and pin
   `((A ≤ B) □→ C) ≡ S C`, `S C ≡ C` (countermodel), and `S S C ≡ S C` (expected theorem).
4. **Pin as tests**: U1 (necessity conservativity), U3/U4 (constitutive collapse, recorded as a
   decision), T2–T4 (weakened transitivity under ILMC), T5/T6 (settled core independence).
5. **Feed back to task 406**: the C3 datum of Section 2.4 and the phase-9 minimality defect of
   Section 2.7.

## 4. Reproduction

```
cd code
./dev_cli.py ../specs/185_design_and_test_hyperintensional_counterfactual_verifiers/baselines/12_transitivity-and-settled-core.py
```
