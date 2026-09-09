# Research Report: Task #186

**Task**: 186 - Review manual counterfactual semantics for uniform clauses
**Started**: 2026-09-09T02:36:37Z
**Completed**: 2026-09-09T02:59:28Z
**Effort**: 1 research dispatch (read-only on `~/Projects/Logos/Theory/**`; one new oracle under `specs/186_*/baselines/`; nothing under `code/` modified)
**Dependencies**: None (the four provenance reports are read as settled input; see Context)
**Sources/Inputs**:
- Manual: `~/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ` read in full (1938 lines; cited by `@label` and line below), `02-constitutive.typ` (`@def-maximal-compatible-parts` :546, `@def-maximal-constraint` :606, `@def-nullity-constraint` :613, `@lem-anchored-union` :628, `@def-propid-verification` :989, `@def-essence-ground` :1056, `@def-anchored-family` :1489, `@def-anchored-event` :1499, `@def-task-coherent` :1519, `@rem-strict-coherence` :1527, `@def-extension-fusion` :1608, `@lem-zero-duration-embedding` :1630, `@rem-no-domain-closure` :1667), `11-proof-theory.typ` :54-215
- Provenance reports (all four read in full): `~/Projects/Logos/Theory/specs/406_counterfactual_null_state_verification/reports/01_*.md`, `.../02_*.md`; `specs/185_design_and_test_hyperintensional_counterfactual_verifiers/reports/01_exact-imposition-verifier-clauses.md`, `.../02_constitutive-patterns-uniform-clauses.md`
- ModelChecker: `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/candidates.py` (`ExactSettlingImpositionCounterfactual`, `settler_clause`, `minimal_clause`, `closure_clause`), `specs/185_*/baselines/11_uniformity-experiments-output.txt`
- Domain context: `.claude/context/project/logic/README.md`, `.claude/context/project/logic/domain/counterfactual-semantics.md`
- Mathlib lookup MCP: not used (`lean-lsp` failed to connect this session; no Mathlib question arose, every fact used is lattice-elementary and in the manual)
**Artifacts**:
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/reports/01_family-level-settled-verification.md` (this report)
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/baselines/01_family-recipe-oracle.py` (pure-Python family-level oracle; experiments E1-E5)
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/baselines/01_family-recipe-oracle-output-e1.txt`, `...-e235.txt` (E2 before the stability-clause containment patch, E3, E5), `...-e2s.txt` (E2 and the stability nested test after it), `...-e4.txt` (captured output cited below)
**Standards**: report-format.md, subagent-return.md
**Task Type**: formal:logic

---

## Executive Summary

- **Deliverable (i) is met: one principle states cleanly at the manual's family level.** For every operator whose truth clause quantifies over world-histories -- `[]->` and hence `[]`, `<>`, `<>->`; `S` and its derived operators; `==` and hence essence and ground -- the `x`-anchored event of `O phi` is `<x, V, F>` with `V = closure(Min{ pi : I_O(pi) and L_O(pi) })` and `F` dually, where `L_O(pi)` is "every world-history containing `pi` makes `O phi` true at `x`" and `I_O(pi)` is `O`'s own truth clause read with `pi` in the history slot. The counterfactual is an instance (the family-level `ILMC`), the manual's null-state convention for `==` is a computed case (`Min` of the settlers of a history-independent claim is the null singleton family, F3), and necessity gets the same null family (F3, oracle E2). Content-building operators (CF base, connectives, `Act`, since/until, store/recall) keep their compositional clauses, exactly as at the state level (settled result 4); the manual already has this two-mechanism structure, it has simply left the world-quantifying family without verifiers (F1).
- **Three definitional adjustments, none of which touches the truth clause, are what the lift needs (F2).** (a) `@def-maximal-compatible-subevolutions` must accept an arbitrary bounding family, not only an evolution, exactly as `@def-maximal-compatible-parts` takes any `s : S`. (b) Where a truth clause pins the history by equality (`@def-stability-truth`'s `alpha(x) = tau(x)`) the recipe consumes its containment form `alpha(x) >= pi(x)`, equivalent at world-histories by maximality; read with equality, `I_S` is vacuous in one polarity and empty in the other (oracle E2, first run). (c) Outside its domain a candidate family constrains nothing: the bounding family is padded by the full state, and imposing `t` on the full state yields exactly the worlds containing `t` (`@lem-world-state-cover` plus maximality), so this is the state-level "impose on the null state" reading lifted; the alternative "only antecedent verifiers that fit in `dom(pi)`" changes falsifier shapes (E5) and is recorded, not recommended.
- **The strict-conditional collapse recurs at the family level exactly when the minimality step is dropped, and the escape is the same (F5, oracle E3).** With `Min`, identity, modus ponens, strict-to-counterfactual and might-identity are valid at counterfactual, tensed-counterfactual and stability antecedents, while counterfactual-to-strict and antecedent strengthening fail; without `Min` (`ILC`) all six are valid, the Reading-W logic. What blocks the escape in general is not the family structure but the existence of minimal settlers: at the family level an infinite descending chain of settlers exists even over `Q = Z` and a finite state lattice (F5.3), so sufficiency of `closure(Min IL)` needs a *Settler Minimality* principle -- the third member of the family `@def-maximal-constraint`, `@def-evolution-maximality` -- or is conditional. It holds outright wherever settling depends on a bounded time window over a finite lattice.
- **The DT antecedent restriction lifts (F6), and the proof-theory bookkeeping is as follows (F7).** C1, M5 and might-identity are unconditional at every recipe-governed antecedent (soundness needs only settler-hood). C2 is discharged at those antecedents wherever a convex-domain minimal settler lies below the evaluation history -- automatic in the memoryless finite frames the manual's own countermodels use, Settler-Minimality-dependent otherwise -- and its two old sub-cases (`not Act(t)`, non-convex recall) are untouched. C3 does *not* become established: minimality keeps the antecedent verifier thin, so both obstructions of `@rem-c3-not-established` recur; Reading W closed C3 only by making the verifier total, which is the strict collapse. `@thm-soundness`'s qualification is re-stated (DT restriction gone; `forall` boundary at bare CF antecedents kept), not dropped.
- **Report 02's F4 does not survive at the family level, and the manual's own exclusion argument splits in two (F8).** The refutation witness (task 185, Frame G2) is a constant-history model of the manual, so `I` separates settler sets with identical truth-sets there too. `@rem-cf-antecedent-restriction`'s "does not supervene on any part of `tau`" argument is correct for history-independent claims and there it *yields* the null family -- the very convention the manual adopts for `==` two sections earlier -- and is false for contingent counterfactuals, whose proper-part settlers the untensed measurements exhibit.
- **What the family level costs that the state level did not (F9), stated with the same precision the prior refutations had.** Pointwise Exclusivity (E3 as `@def-anchored-event` states it) fails for the recipe's events: a vacuous member can carry its impossibility at a time outside the shared domain (witness `{0:b}` against `{0:null, 1:a.d}`, oracle E1), and in temporally constrained frames a pointwise-possible family below no history is a vacuous settler at every point. The history form of E3 -- no world-history contains a verifier and a falsifier -- holds unconditionally and is the form the bridge consumes; the two forms coincide exactly under the world-history completion principle the manual has already named and deferred at `@rem-occurrence-possible-states` (leg (d)). This has the same status as the E4 refutation the manual already records for the tense fragment at `@rem-event-status`.

---

## Context & Scope

The task asks whether the settler recipe of task 185 report 02 -- established in the untensed ModelChecker fragment with the six settled results (1)-(6) of the dispatch -- states cleanly over the manual's anchored families and world-histories, and what the manual must change to adopt it. It is a review of `03-dynamics.typ` against that recipe; the manual, the Lean tree and the ModelChecker theory are not edited.

Method. The chapter was read in full and the family-level machinery it supplies (`@def-anchored-family`, `@def-event-verification`, `@def-truth-bridge`, `@def-altworlds`, `@def-maximal-compatible-subevolutions`, `@def-fused-family-coherence`, `@def-counterfactual-truth`, `@def-stability-truth`, `@lem-necessity-semantics`) was matched clause by clause against the state-level recipe. Every claim that could be made executable was checked with a new pure-Python oracle (`baselines/01_family-recipe-oracle.py`) implementing the manual's family-level definitions over a finite time window on the manual's own duration-uniform task-relation schema -- the schema shared by `@ex-frame-r` and `@ex-frame-symmetric`, under which world-histories are exactly the world-valued total functions and a thread is a convex-domain family with possible values that are all null or none null. Five experiments (E1-E5) are cited below by name; their captured output is in `baselines/`. Claims the oracle cannot reach (infinitary minimality, temporally constrained frames) are marked as such and the deciding test is named.

Notation. `pi <= f` is Evolution Parthood of `@def-dynamics` (domain inclusion and pointwise parthood); `beta` ranges over world-histories; `T_phi(beta)` is truth of `phi` at `(beta, x, sigma, i)`; `pi_s` is the singleton family with domain `{x}` and value `s`; `pi_null := pi_nullstate`.

---

## Findings

### F1. The manual already has the two-mechanism structure; the world-quantifying family is simply unverified

| Manual clause | Direction of definition | Verifier shape | Reads the evaluation history? |
|---|---|---|---|
| `@def-event-cf-base` (atoms, lambda, first-order identity, `top`, `bot`, quantifier) | verifiers first, truth by `@def-truth-bridge` | singleton domain, state-level exact verifier | no |
| `@def-event-connectives`, `@def-event-actuality`, `@def-event-until`, `@def-event-since`, `@def-event-store`, `@def-event-recall` | verifiers built from sub-formula verifiers by extension-fusion / witness sub-families | exact-shaped, domain-exact (`@rem-no-domain-closure`) | no |
| `==` via `@def-propid-verification` inside `@def-event-cf-base` | truth first (holds in the model), null state stipulated | `{pi_null}` or empty | no |
| `[]->`, `[]`, `<>`, `<>->` (`@def-counterfactual-truth`, `@lem-necessity-semantics`) | truth only | **none** (`@def-event-fragment` excludes them) | -- |
| `S` and `Will`/`will`/`Could`/`could` (`@def-stability-truth`, `@def-derived-stability-operators`) | truth only | **none** | -- |

This is settled result (4) already in place at the family level: the first two rows are content-building, the last three are world-quantifying. The manual's own text confirms the split from the other side -- `@rem-cf-antecedent-restriction` excludes `[]->` and `S` together "on principled grounds" because their truth "does not supervene on any part of `tau`", and `@def-propid-truth` records that `==` "depends on none of `tau`, `x`, `i`". The recipe's claim is that the third, fourth and fifth rows are one case.

### F2. The principle at the family level, stated (question (a))

**Settled Event Verification.** Fix `M`, `sigma`, `i`, an anchor `x`, and an operator `O` from the world-quantifying family. For an `x`-anchored family `pi` with convex domain:

- `L_O(pi)` (settling): for every world-history `beta` with `pi <= beta`, `M, beta, x, sigma, i |= O phi`. `L-_O(pi)` with `=|` (falsity).
- `I_O(pi)` (the operator's own clause at the candidate): the truth clause of `O phi` read with `pi^top` in the history slot, where `pi^top` agrees with `pi` on `dom(pi)` and is the full state elsewhere. `I-_O(pi)` with the falsity clause.
- `V_x(O phi) := closure_ext( Min { pi : I_O(pi) and L_O(pi) } )`, `F_x(O phi) := closure_ext( Min { pi : I-_O(pi) and L-_O(pi) } )`,

with `Min` under Evolution Parthood on `x`-anchored families and `closure_ext` closure under extension-fusion (`@def-extension-fusion`; all members share the anchor, so it is always defined, and by `@lem-anchored-union` convex domains stay convex).

What plays the role of `I` and `L`, operator by operator:

| `O phi` | `I_O(pi)` reads | `L_O(pi)` | Result |
|---|---|---|---|
| `A []-> B` | for every `A`-verifier `pi'`, `rho in [pi^top|_{dom pi'}]_{pi'}`, `beta` with `pi' + rho <= beta` and `pi' + rho` a thread: `B` at `beta` | every `beta >= pi` is a `A []-> B`-history | family `ILMC` |
| `[] phi = top []-> phi` | `top`'s verifiers include every world state `w` as `pi_w`; `[pi^top(x)]_w` gives `beta(x) = w`; so `I` is `[] phi` for every `pi` | `[] phi` | `{pi_null}` iff `[] phi` |
| `S phi` | histories `alpha` with `alpha(x) >= pi(x)`: `phi` | same | minimal parts of world-states settling `S phi` |
| `phi == psi` (and `<=`, `<=|` via `@def-essence-ground`) | nothing (model-level) | nothing | `{pi_null}` iff the identity holds |
| `<>->`, `<>`, `Will`, `Could`, ... | by negation duality (`@def-event-connectives`) | | falsifiers of the dual |

Three definitional adjustments make `I` statable; none changes `@def-counterfactual-truth`:

1. **General bounding family.** `@def-maximal-compatible-subevolutions` fixes "an evolution `tau`". Reading the counterfactual clause at `pi^top` needs `[f]_{pi'}` for an arbitrary function `f : X -> S` (clauses (a)-(d) make sense verbatim). This is the exact parallel of `@def-maximal-compatible-parts` taking any `s : S`, which is what lets the state-level `I(t)` be defined for every state, possible or not. `@def-evolution-maximality` need not be generalized: if `[f]_{pi'}` is empty, `pi'` contributes vacuously to `I`, and `I` only selects.
2. **Containment form of equality-pinned clauses.** `@def-stability-truth` quantifies over `alpha` with `alpha(x) = tau(x)`. At a world-history this is equivalent to `alpha(x) >= tau(x)` by `@def-world-state` maximality, and only the containment form is meaningful at a non-maximal candidate. Read with equality, `I_S(pi)` is vacuously true for every non-world `pi(x)` and `I-_S(pi)` vacuously false, so the falsifiers of `S A` come out as whole world-states (`{0:b.d}`, `{0:c.d}`, `{0:b.c.d}`) while its verifiers are minimal parts -- oracle E2 first run, `...-e235.txt`. With containment both polarities are minimal parts (`{0:a}` / `{0:d}`, `...-e2s.txt`). `@lem-necessity-semantics` and `@def-altworlds` are already in containment form.
3. **Padding.** Outside `dom(pi)` the candidate says nothing. Padding by the null state and keeping clause (c) (the witness `rho` must be a thread) forces `rho` to be the constant null family by the Nullity constraint whenever an antecedent verifier sticks out, which discards `pi`'s content entirely for that verifier. Padding by the full state is the faithful lift: `[top]_t` is the set of world states containing `t` (`r in [top]_t` is `t`-compatible and maximal, any world above `r + t` is `t`-compatible and above `r`, hence equals `r`), so at a padded point the imposition is free, exactly as `Alt(null, a)` is the set of `a`-worlds at the state level. The oracle implements both readings (`padding="full"` / `"restrict"`, the latter being "impose only antecedent verifiers whose domain fits inside `dom(pi)`"). They agree on verifiers in every experiment and differ on falsifiers of tensed-antecedent counterfactuals (E5: co-settlers `{0:c}` under full padding; `{0:c,1:a}`, `{0:c,1:b}`, `{0:c,1:c}`, `{0:c,1:d,2:*}` under restrict, because the existential `I-` needs an antecedent verifier that fits). Full padding is recommended; restrict is recorded.

Availability of the two extremal steps:

- **Fusion closure** is available and sound: if `pi_1, pi_2` settle then `pi_j <= pi_1 + pi_2 <= beta` for every history above the fusion, so the extension-fusion settles. E1 (Closure, same-domain pointwise fusion) is the same-domain instance. Closure adds only fusions of settlers, so soundness of `V` is unconditional.
- **Minimality** is definable (Evolution Parthood is a partial order on `x`-anchored families) and, because domain inclusion is part of the order, it *derives domain-exactness*: the least family that settles a CF-constituent counterfactual has domain `{x}`. But existence of minimal elements is not automatic; see F5.3.

### F3. The null-family convention is a computed case (question (b))

For `==`, `T` reads nothing, so `I` and `L` are the model-level condition and `IL` is either every `x`-anchored family or none. The least `x`-anchored family under Evolution Parthood is the singleton `pi_null` (the domain must contain `x`; the value at `x` must be a part of every value), so `Min IL = {pi_null}` and `closure_ext` of a singleton is itself. This is `@def-event-cf-base`'s `==` case via `@def-propid-verification` verbatim: `dom(pi) = {x}` and `pi(x) = nullstate`. The same computation gives `[] phi` the null family (F2 table), which the manual currently gives no verifiers at all, and `S phi` the null family exactly when `phi` holds at every world (E2: `S(A v ~A)` has `V = {pi_null}`). The manual's own sanity check at 03-dynamics.typ:1259 -- `Alt(tau, pi_null)` collapses to the stability class so `(phi == psi) []-> chi` reads `S chi` -- is thereby the general fact that a null-verified antecedent minimizes its consequent (task 185 report 02, section 5.3), now stated once for `==`, `[]` and every other history-independent operator.

Oracle E2 (window `{0,1}`, 4-atom frame, `...-e2s.txt`): `(A == A)`, `[](A v ~A)`, `[]((A v B) v (C v D))`, `S(A v ~A)` each return `V = {pi_null}`, `F = {}`; `(A == B)` and `[]A` return `V = {}`, `F = {pi_null}`.

So the chapter can state one principle and *derive* `@def-propid-truth`'s "context-independent" remark from it: the null family verifies what every family settles.

### F4. Alignment with the untensed fragment: the family recipe restricted to singleton domains is `ILMC`

For a counterfactual with CF constituents, `T` reads only `beta(x)`, so `L(pi_t)` is "every world above `t` is a `T`-world" (every world occurs at `x` in some history, `@cor-occurrence`) and `I(pi_t)` is the state-level `I(t)` by `@cor-zero-duration-collapse`. Hence the domain-`{x}` slice of the family `IL` is the state-level `IL` in every frame, and its minimal members are minimal there. Oracle E1 (4-atom frame with worlds `a.b`, `a.c`, `d.b`, `d.c`; `|A| = <{a},{d}>`, `|B| = <{b},{c}>`): state-level `ILMC` `V = {b}`, `F = {c, a.d, a.c.d}`; the family recipe at windows `{0}` and `{0,1}` gives exactly the embedding on domain `{0}`, sound and sufficient in both polarities, and no realizable member with a larger domain. This is the counterfactual analogue of `@lem-cf-alignment`, and it is what makes `@prop-cf-conservativity` extend from truth to verifiers. Oracle E4 repeats the check on report 02's certified 8-atom F3 frame (`...-e4.txt`): at windows `{0}` and `{0,1}` the realizable minimal settlers are `{0:a.p'}`, `{0:a.q'}`, `{0:a.b}` and the realizable minimal co-settlers `{0:a'}`, `{0:p.q}`, `{0:p'.q}`, `{0:p.q'}`, `{0:b'}`, the minimal elements of the state-level `ILMC` sets of task 185 report 01 F5, so the refutation of Reading I and its repair transfer to the manual's own machinery unchanged.

Two qualifications. First, the slice equality is a theorem; the *absence* of larger-domain realizable minimal settlers is a property of memoryless frames. In a frame whose task relation constrains cross-time combinations, a family `{x: t, z: u}` can settle a CF-constituent counterfactual although `t` alone does not (the value at `z` rules out the bad worlds at `x` through coherence). Such settlers are legitimate temporal exactness (`@rem-no-domain-closure`) and are invisible at the state level; no certified frame of that kind exists in the manual or the prior reports (see "Where the evidence does not decide"). Second, the vacuous members differ: at the state level a vacuous `IL` member is an impossible state; at the family level it is a family below no world-history, which need not be pointwise impossible (F9).

### F5. The strict collapse and its escape (question (d))

**F5.1 Measured.** Oracle E3, window `{0,1}`, ten consequents (`A, B, C, D`, their negations, `A & C`, `B v D`), three antecedent shapes, both paddings (`...-e235.txt`, `...-e2s.txt`):

| Antecedent `X` | Variant | identity | MP | strict->cf | cf->strict | AS | might-id | `X []-> C <-> S C` |
|---|---|---|---|---|---|---|---|---|
| `A []-> B` | `ILMC` | valid | valid | valid | fails 4/10 | fails 2/10 | valid | fails 6/10 |
| `A []-> B` | `ILC` | valid | valid | valid | valid | valid | valid | fails 10/10 |
| `(F A) []-> B` | `ILMC` | valid | valid | valid | fails 4/10 | fails 2/10 | valid | fails 6/10 |
| `(F A) []-> B` | `ILC` | valid | valid | valid | valid | valid | valid | fails 10/10 |
| `S B` | `ILMC` | valid | valid | valid | fails 4/10 | fails 2/10 | valid | fails 6/10 |
| `S B` | `ILC` | valid | valid | valid | valid | valid | valid | fails 10/10 |

Identical for both paddings. The `ILMC` rows are the base counterfactual profile (settled result 1, task 185 report 01 F7); the `ILC` rows are Reading W's logic (report 02 F6). The last column is Round 1's Reading B, refuted for both.

**F5.2 Why the escape is available.** Reading W and `ILC` include every true world-history in `V_X` (a history `tau` has `I(tau) = T(tau)` and settles trivially), and imposing a world-history on anything yields that history (report 02 M1), so `X []-> C` ranges over all `X`-histories. `Min` removes `tau` from `V_X` whenever some proper part of it settles, and then `Alt(tau, pi)` for a thin `pi` is a genuine imposition. Nothing about families blocks this: E3 shows it at a tensed antecedent (`(F A) []-> B`, whose realizable minimal settler is `{0:b}`) and at a stability antecedent.

**F5.3 What blocks it in general: existence of minimal settlers.** `closure(Min IL)` is sound unconditionally but sufficient only if some minimal settler lies below every history at which `X` is true. The set of settlers below `tau` is nonempty (`tau` itself), and a minimal element exists iff descending chains are bounded in `IL`. The pointwise meet of a chain of settlers need not settle (a history above the meet need not be above any member), so nothing in the frame supplies minimal elements. At the state level this is an issue only for infinite lattices; at the family level it arises over `Q = Z` with a finite lattice, because domains descend: with `X = G p`, the settlers below `tau` on the forward ray can be thinned point by point without end when the lattice allows (values fixed, domain a ray, no finite-domain settler exists at all). So the recipe needs a **Settler Minimality** principle -- every settler of a world-quantifying `O phi` has a minimal settler below it -- which is the descending twin of `@def-maximal-constraint` and `@def-evolution-maximality`, with the same motivation ("no strictly decreasing series with no bound"). Where it holds automatically: `S` finite and settling dependent on a bounded window of times (every CF-constituent counterfactual, `S phi` with CF `phi`, every bounded-interval tense antecedent over `Q = Z`), which covers every frame the manual's countermodels use and every oracle run here. Where it is a genuine assumption: dense `Q`, ray-dependent antecedents, infinite lattices. Without it the honest statement is: `C2` is sound at a recipe-governed antecedent `X` at `tau` iff a minimal settler of `X` lies below `tau`; `ILC` (report 02's Reading L in imposition form) is the fallback with unconditional sufficiency and the strict logic.

### F6. The DT antecedent restriction lifts (question (c))

With verifiers for `[]->`, `[]`, `<>`, `<>->`, `S`, `Will`, `will`, `Could`, `could`, the `phi_DT` subscript in `@def-wff-dynamics` and the exclusion sentence of `@def-event-fragment` go; the grammar is recursive with `[]->` taking any formula as antecedent, and nested counterfactuals, necessity, possibility, might-counterfactuals and stability are admissible antecedents with no syntactic side condition. `@rem-store-recall-coverage`'s widening becomes unrestricted and `@rem-cf-two-layer`'s "formulas outside the DT fragment receive the empty event-verifier clause" is replaced by the principle.

What does not change, and is not a counterfactual matter: (i) `@def-wff-dynamics`'s design decision that DT does not close under lambda application or quantification -- `(lambda v. p U q)(t)` has a truth clause but its verifiers would have to be built by a lifted *content* clause, not by the recipe (applying the recipe there would discard exact content exactly as it does for conjunction, settled result 4); (ii) the causal operators, which have no truth clause (04-verification.typ :431), hence no `I` or `L`; (iii) the quantifier-range boundary of `@rem-bridge-soundness-quantifier` at bare CF antecedents, which is about the CF verification clauses.

### F7. The proof-theory chapter under the recipe (question (e))

| Item | Status now | Under the recipe | Why | Becomes unconditional? |
|---|---|---|---|---|
| DT restriction (`@rem-dt-antecedent-restriction-ch7`, R1, M5 remarks) | in force | retired | F6 | yes (removed) |
| C1 `X []-> X` at recipe antecedents | inexpressible | sound | every `X`-verifier `pi` settles; `pi <= pi + rho <= beta` gives `X` at every alternative | **yes** (soundness only) |
| C1 at bare CF antecedents with positive `forall` | refuted | refuted | untouched CF clauses | no |
| M5 `[](X -> Y) |- X []-> Y` at recipe antecedents | inexpressible | sound | alternatives are `X`-histories, so `Y`-histories | **yes** |
| Might-identity `X <>-> X` | inexpressible | valid (E3) | falsifiers of `X []-> ~X` | yes |
| C2 at recipe antecedents | inexpressible | sound iff a convex-domain minimal settler of `X` lies below `tau` | `@lem-actuality-families` needs `pi <= tau` with convex domain; sufficiency needs Settler Minimality (F5.3); a non-convex minimal settler is discarded by the coherence filter exactly as `@rem-counterfactual-recall-handling` records for recall | conditional; automatic in bounded-window finite frames |
| C2 sub-cases `not Act(t)`, non-convex recall | open | open | not counterfactual clauses | no |
| C3 at a nested first antecedent | not established | not established | the first antecedent's verifier is thin, so Obstruction 1 (domain growth under extension-fusion with the `psi`-witness) and Obstruction 2 (maximality does not absorb Incorporation) of `@rem-c3-not-established` recur verbatim; Reading W avoided them only because its verifier was total (report 02 F6.1), which is the collapse F5 escapes | no |
| C4-C7 | unconditional | unconditional | formula-independent inclusion argument (`@rem-c4-c7-unconditional`) | already |
| T, M1-M4, P1-P6, `@prop-cf-conservativity`, `@thm-perpetuity` | insulated | insulated | truth clauses unchanged; the recipe only adds verification arms | already |
| `@thm-soundness` qualification | "within the stated antecedent restrictions" | re-stated: DT restriction gone; `forall` boundary kept at bare CF antecedents; C2's condition at recipe antecedents named; C3 excluded | | no |

The C2/C3 rows are the honest cost of non-strictness: report 02 bought C2 and nested C3 unconditionally by making every verifier total, and Round 1 bought a centered logic by reading `tau`. The recipe buys hyperintensional, non-strict nested logic (F5.1) and keeps `@rem-c3-not-established` open.

### F8. Report 02's F4 at the family level, and the manual's own argument (question (f))

The family analogue of F4 reads: any context-free sound family clause has settler verifiers; settler-hood is a function of the truth set over world-histories; therefore no such clause is hyperintensional except by fiat. Its first two steps stand. The conclusion is refuted by the same witness that refuted it at the state level: Frame G2 (task 185 report 01 F8, `baselines/03_research-witnesses.py`) with the identity task relation is a dynamical model of the manual whose world-histories are the constant histories, and there `I` separates `A []-> B` from `C []-> D` (same truth set, distinct `ILMC` propositions, distinct nested truth-values). `I` is a semantic clause of the same shape as the truth clause, not an operation on truth values.

The manual's text does rest on the F4 shape, in `@rem-cf-antecedent-restriction`: "any would-be verifier that is a part of `tau` would have to make the necessity claim true in *every* history containing it -- either no such part exists (vacuity) or verification collapses into necessity itself." Both halves of the dilemma are correct, and both are the recipe: for a history-independent claim every part settles or none does, `Min` is the null family, and "verification collapses into necessity" *is* the null-family convention the manual already adopts for `==` at `@def-propid-verification` ("no other content is relevant"). The remark treats as a reason for exclusion, for `[]`, what `@def-propid-truth` treats as the correct verifier, for `==`. For the counterfactual proper the argument's premise is false: a contingent counterfactual's truth at `tau` does supervene on proper parts of `tau` in most contingent models from four atoms on (task 185 report 01 F5, "proper V" columns), and the family-level minimal settler `{0:b}` of E1/E3/E5 is one. The supervenience paragraph should survive as the *derivation* of the null family, not as an exclusion.

### F9. What the family level costs that the state level did not

**F9.1 Pointwise Exclusivity fails; history-form Exclusivity holds.** `@def-anchored-event` E3 requires some shared time at which a verifier and a falsifier are incompatible. Oracle E1 at window `{0,1}`: `V = {{0:b}}`, and `F` contains `{0:null, 1:a.d}` (`a.d` impossible), a vacuous minimal co-settler (below no history, so `L-` is vacuous, and `I-` holds since its anchor value is null). The shared domain is `{0}`, where `b` and `null` are compatible: pointwise E3 fails, although no history contains both (history-form E3 holds in every run: E1, E5, the `S B` report). At the state level the analogous vacuous member is an impossible state, which is incompatible with everything; at the family level "below no world-history" is strictly weaker than "pointwise impossible somewhere", and the gap is exactly the world-history completion of a pointwise-possible family that `@rem-occurrence-possible-states` records as deferred (leg (d)). In memoryless frames every pointwise-possible family is realizable, so restricting E3 to realizable members restores it ("E3 pointwise (realizable members): True" in every run); in a temporally constrained frame a pointwise-possible family below no history is a vacuous settler and co-settler with no impossible value anywhere, and even realizable members can be pointwise compatible yet jointly unrealizable. Consequences: (i) the recipe's events satisfy E1 and history-form E3 unconditionally and E4 iff sufficiency holds in both polarities (F5.3) plus `@thm-bivalence`; (ii) pointwise E3 holds iff pointwise-compatible pairs complete to a common world-history -- the completion instance of the maximality family, named and not adopted at `@rem-occurrence-possible-states`; (iii) this is the same situation the manual already accepts for the tense fragment, whose clause-generated triples fail E4 at a non-`top` guard (`@rem-event-status`), so the record belongs beside that one. The tense fragment satisfies pointwise E3 only because its falsifiers are fat (whole rays); the recipe's are thin on both sides.

**F9.2 Settler Minimality** (F5.3): a new principle or a conditional sufficiency.

**F9.3 Non-convex minimal settlers.** `Min` under domain inclusion can return non-convex domains; the coherence filter then makes them vacuous as antecedents. In every oracle run the non-convex minimal members were unrealizable (E5: `{0:null, 2:a.b.c.d}`), so nothing was lost; whether a *realizable* minimal settler can have a non-convex domain in a constrained frame is untested. The principle is stated over convex-domain families (F2) to sidestep this; the cost is that convexification can change `I` (more antecedent verifiers fit), which the oracle does not exercise.

**F9.4 Padding** (F2, adjustment 3): affects falsifier shapes for tensed antecedents; a decision, recorded.

### F10. What must change in the manual to adopt the principle

Edit sites in `03-dynamics.typ` (current line numbers):

1. `@def-wff-dynamics` :53-69: drop `phi_DT` on `[]->`; keep the DT grammar as the definition of the *content-building fragment*. `@def-event-fragment` :551-561: replace the exclusion sentence by "the world-quantifying operators receive their events by Settled Event Verification below". Syntactic-primitives table :41 likewise.
2. `@def-maximal-compatible-subevolutions` :315-324: state for an arbitrary bounding family `f : X -> S` (adjustment 1), with a sentence that `@def-evolution-maximality` is asserted for evolutions only and that emptiness elsewhere is harmless.
3. New definition after `@rem-cf-two-layer` :1206-1218: "Settled Event Verification" (F2), followed by (a) the counterfactual instance written out in the shape of `@def-counterfactual-truth` (`I` = the clause at `pi^top`; `L`; `Min`; `closure_ext`), (b) a proposition deriving the `==` case (F3) and citing 03:1259's `Alt(tau, pi_null)` computation, (c) the same for `[]` and `<>`, (d) `S` and `@def-derived-stability-operators`, (e) a remark recording the alignment with the untensed clause at singleton domains (F4) as the verifier-level extension of `@prop-cf-conservativity`.
4. `@def-event-cf-base` :565-573: the `==` item becomes a pointer to the derived case (or stays, with "as Settled Event Verification computes").
5. `@def-stability-truth` :1395-1403: containment form, or a remark that the recipe reads it so (adjustment 2).
6. `@rem-cf-antecedent-restriction` :1355-1374: rewrite per F8: the supervenience paragraph becomes the derivation of the null family for history-independent claims; the exclusion is lifted; the "can be unsatisfiable" qualification stays (it is the coherence filter, unchanged).
7. `@rem-event-status` :841-866: add the E1/E3/E4 record for the new events (F9.1), in the same register as the existing E4 refutation.
8. New axiom candidate beside `@def-evolution-maximality` :365-367: Settler Minimality (F5.3), stated with where it is automatic, or the conditional form of sufficiency recorded instead.
9. `@lem-bridge-soundness` :1719-1727 and `@lem-cf-verification-soundness`: new cases that close by the definition of `L`. `@lem-bridge-equivalence` :1599-1614: the sufficiency half for the new operators, conditional on item 8. `@def-truth-bridge` :816-824 unchanged.
10. `@rem-imposition` :1376-1380: note that `[]->`-antecedents now impose their minimal settlers; `@rem-store-recall-coverage` :1091-1099 and `@rem-multi-time-pinning` :1340-1353: drop the DT wording.

`02-constitutive.typ`: `@def-anchored-event` :1499 -- either add the history form of E3 as the notion the bridge consumes, or leave E3 pointwise and record F9.1 at `@rem-event-status`; `@rem-no-domain-closure` :1667 -- a sentence that `Min` derives domain-exactness for the world-quantifying family.

`11-proof-theory.typ`: retire `@rem-dt-antecedent-restriction-ch7` :64-73 to a superseded record (keep the label; :64, :120, :168 cite it); extend `@rem-c2-discharge-corollary` :114-117 with the recipe antecedents and the F7 condition; rewrite `@rem-c1-m5-bridge-soundness` :171-182 (sound at all recipe antecedents; the `forall` boundary is a bare-CF matter); add one sentence to `@rem-c3-not-established` :119-127 that the obstructions recur at thin nested antecedents; restate `@thm-soundness` :191-195.

Lean (recorded for the follow-up task, not planned here): report 406/02's shape 1 remains the landing (truth and world-history callbacks into `verifies_evo_ext`), and the recipe additionally needs `maxCompatSubevolutions` over an arbitrary bounding family and the counterfactual truth body callable at a family rather than a world-history (the `I` conjunct); `Min` and `closure_ext` are generic and can be one definition shared by every world-quantifying arm, which is report 02's rejected "generic truth-defined operators" shape 2 made attractive by the uniformity.

---

## Decisions

- **D1 (principle)**: Settled Event Verification as stated in F2 is recommended as the single clause for the world-quantifying family, with the counterfactual as the family-level `ILMC` instance. It meets the task's standard: one stated principle, the counterfactual not a special case, no syntactic antecedent restriction, the null-state convention derived.
- **D2 (three adjustments)**: general bounding family; containment form for equality-pinned clauses; full-state padding. Recorded alternatives: null padding (rejected: Nullity empties it), restrict padding (recorded: changes falsifier shapes, E5).
- **D3 (minimality)**: keep `Min`. Adopt Settler Minimality as a named principle of the maximality family, or state sufficiency conditionally; `ILC` is the strict fallback. This is the one place a user judgment is genuinely involved (an axiom versus a conditional theorem), surfaced below as non-blocking.
- **D4 (E3)**: state the events' Exclusivity in history form; record the pointwise failure beside the tense fragment's E4 record; tie the two forms' coincidence to the deferred completion principle.
- **D5 (proof theory)**: C1, M5, might-identity unconditional at recipe antecedents; C2 conditional as in F7; C3 stays not established; `@thm-soundness` re-stated, not unqualified.
- **D6 (F4)**: refuted at the family level; `@rem-cf-antecedent-restriction`'s argument is kept as the derivation of the null family for history-independent claims and dropped as an exclusion.

---

## Risks & Mitigations

- **Temporally constrained frames are unmeasured.** All executable evidence uses the manual's memoryless schema, in which pointwise-possible families are realizable and CF-constituent settlers are singleton-domain. Mitigation: the frame-dependent claims (multi-time realizable settlers, realizable non-convex minimal settlers, history-less pointwise-possible families) are stated as such, and the deciding construction is named below.
- **Settler Minimality is a new principle.** Mitigation: the conditional statement of sufficiency is exact and can be adopted instead; the principle is automatic on every frame the manual's own countermodels use.
- **`@def-anchored-event`'s E3 is consumed elsewhere only vacuously** (`@rem-event-status`: "nothing in this scope consumes E3"), so changing its form has no downstream cost the manual records; the risk is conceptual, not technical. Mitigation: D4 offers the record-only option.
- **The oracle's thread shortcut is schema-specific** (products of pointwise maximal compatible parts, with the null coupling). Mitigation: documented in the script's `mcs` docstring; any constrained-frame test must replace it with the manual's clauses (a)-(d) directly.
- **`lean-lsp` was unavailable**; no Mathlib lookups were performed. No fact used needs one.

---

## Where the evidence does not decide, and the test that would

1. **Multi-time realizable settlers, and realizable non-convex minimal settlers** (F4, F9.3): need a dynamical model in which the task relation forbids some world-to-world transition while satisfying the containment pair and the parthood constraints. Test: certify such a frame in the style of `@def-certified-frame`, then run the oracle with `mcs` replaced by the manual's clauses (a)-(d); the prediction is a settler `{x: t, z: u}` with `t` not a state-level settler.
2. **Pointwise E3 among realizable members** (F9.1): the same frame, with a pointwise-compatible settler/co-settler pair on disjoint non-anchor domains and no history above both. Prediction: history-form E3 holds, pointwise E3 fails without any impossible value.
3. **Settler Minimality's necessity** (F5.3): an explicit descending chain of settlers of `G p` with no minimal element requires an infinite lattice or dense `Q`; over `Q = Z` and a finite lattice the ray-domain settlers of `G p` have pointwise-minimal members. Test: state the chain in the manual's continuous candidate model (`@rem-threading-general-open`, closed subsets of `R`).
4. **Padding** (F2.3): the two readings agree on every verifier measured and differ on tensed-antecedent falsifiers. The conceptual test is which exact falsifier of "if `A` were going to happen, `B` would" the manual wants: `c` now (full padding), or `c` now together with a way of `A` happening (restrict). Full padding is the lift of the state-level clause; the choice is recorded as D2.
5. **Frame G2 at the family level** (F8): the refutation is by embedding as constant histories. The oracle reproduces the 8-atom F3 frame at windows `{0}` and `{0,1}` (E4, `...-e4.txt`: the family-level realizable minimal settlers are exactly the state-level `ILMC` minimal elements); G2 is the same size and its family-level run would add only the same embedding, since the G2 result at window `{0}` is the state-level result already pinned by task 185. Running it is a one-line addition to `experiment_f3` if a pinned family-level hyperintensionality witness is wanted.

---

## Appendix

### A. The oracle

`baselines/01_family-recipe-oracle.py` (pure Python). Frame: atoms as bits, states as bitmasks, a downward-closed possibility set generated by the listed world states, a finite time window, world-histories as all world-valued functions on the window. Implements: `@def-maximal-compatible-parts`; Evolution Parthood; `@def-extension-fusion`; threads under the duration-uniform schema (singleton domains unconditionally, per `@rem-strict-coherence`); `@def-event-cf-base`, `@def-event-connectives`, `@def-event-until` at guard `top` (verifiers with the anchor convention, falsifiers on the forward ray); `@def-altworlds` with the coherence filter over an arbitrary bounding family (`mcs`); `@def-counterfactual-truth` in both polarities; `@def-stability-truth` (containment form); `@lem-necessity-semantics` via `top []->`; state-level verification for CF formulas and `==`; the recipe (`L`, `I`, `Min`, `closure_ext`) with variants `ILMC`/`ILC` and paddings `full`/`restrict`; the state-level `ILMC` for cross-checking; soundness, sufficiency, pointwise and history-form E3, convexity and realizability reports.

Frames: `frame_small` (atoms `a b c d`, worlds `a.b`, `a.c`, `d.b`, `d.c`, letters `A = <{a},{d}>`, `B = <{b},{c}>`, `C = <{c},{b}>`, `D = <{d},{a}>`); `frame_f3` (report 02's F3 frame, letters `A`, `B`).

Reproduction: `cd specs/186_*/baselines && python3 01_family-recipe-oracle.py [e1|e2|e3|e4|e5|all]`. E1-E3, E5 run in about a minute each; E4 at window `{0,1}` (65,792 candidate families over 256 states) takes longer and was run in the background.

### B. Results index

| Experiment | Window | Claim checked | Outcome | File |
|---|---|---|---|---|
| E1 | `{0}`, `{0,1}`; both paddings | family `IL` on domain `{0}` = state `ILMC`; no realizable larger-domain members; sound/sufficient; E3 | all as predicted; pointwise E3 fails on the vacuous member `{0:null,1:a.d}` at window `{0,1}`, holds on realizable members, history-form holds | `...-e1.txt` |
| E2 | `{0,1}` | null family for `==`, `[]`, `S(top-like)`; minimal parts for `S A` | as F3; the equality-reading asymmetry for `S` (`...-e235.txt`, run before the containment patch) is removed by the containment form (`...-e2s.txt`) | `...-e235.txt`, `...-e2s.txt` |
| E3 | `{0,1}`; three antecedents; both paddings; ten consequents | nested logic under `ILMC` vs `ILC` | F5.1 table | `...-e235.txt`, `...-e2s.txt` |
| E4 | `{0}`, `{0,1}` | report 02's F3 frame at the family level | realizable minimal settlers `{0:a.p'}`, `{0:a.q'}`, `{0:a.b}` and co-settlers `{0:a'}`, `{0:p.q}`, `{0:p'.q}`, `{0:p.q'}`, `{0:b'}` at both windows: exactly the minimal elements of the state-level `ILMC` sets (task 185 report 01 F5, including the `p.q` falsifier its F6 called the most natural); sound and sufficient; pointwise E3 fails at window `{0,1}` only on a vacuous member (`{0:p', 1:a.p.q'.b'}` against `{0:p.q}`), history-form holds | `...-e4.txt` |
| E5 | `{0,1,2}`; both paddings | tensed antecedent `(F A) []-> B`: truth agrees with `B` at the anchor; settlers; co-settler shapes | true; `V` minimal settler `{0:b}` under both; co-settlers `{0:c}` (full) vs multi-time (restrict); non-convex members unrealizable only | `...-e235.txt` |

### C. Search and lookup record

- Codebase: `Glob`/`Grep` over `03-dynamics.typ` and `02-constitutive.typ` labels; `candidates.py` for the `ILMC` clause text; `11_uniformity-experiments-output.txt` for U1-U3.
- Mathlib lookup MCP: none performed (server unavailable; not needed).
- Web: none (the questions are internal to the manual's own semantics; the literature anchors are those already cited by report 02: Fine 2012 md :279-397).
