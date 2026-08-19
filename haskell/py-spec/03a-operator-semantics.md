# Operator Semantics
[← Spec map](./README.md)

> The actual truth, falsity, verification, and falsification conditions computed by every
> operator in the four shipped theories — the formulas behind the method shapes of
> [`03-operators.md`](./03-operators.md).

## How to read this document

[`03-operators.md`](./03-operators.md) specifies the operator *abstraction*: the six-method
shape, definitional expansion, the collection machinery, and the three-register drift risk. This
document supplies the *content* that document deliberately abstracts over: for each primitive
operator, the formula each semantic method computes; for each defined operator, its definitional
expansion. All formulas are stated in the mathematical register of
[`05-state-encoding.md`](./05-state-encoding.md) and were transcribed from the cited source
files, not from documentation. The per-theory sections are parallel in shape: an inventory, a
table block per primitive operator, then the defined operators' expansions.

**Notation** (uniform across this document):

| Notation | Meaning | Source method |
|---|---|---|
| `true(A, w)` / `false(A, w)` | sentence `A` is true / false at the evaluation point whose world is `w` | `true_at` / `false_at` |
| `ver(x, A)` / `fal(x, A)` | state `x` verifies / falsifies `A` (at the ambient evaluation point) | `extended_verify` / `extended_falsify` |
| `x ⊑ y`, `x ⊔ y`, `∅`, `s` | part-of, fusion, the null state, the candidate state argument | see [`05-state-encoding.md`](./05-state-encoding.md) |
| `is_world`, `is_alternative`, … | the helper predicates | [`05-state-encoding.md`](./05-state-encoding.md)'s helper table |

On a sentence letter `p`, `ver(x, p)` and `fal(x, p)` are exactly the primitives
`verify(x, p)` and `falsify(x, p)`; on complex sentences they recurse through the operator
clauses below (the double dispatch of
[`04-constraint-generation.md`](./04-constraint-generation.md)). All quantifiers below range
over the full `2^N` state space via finite expansion **except where explicitly bounded by
`is_world`** — the quantifier domain is part of the truth condition, and getting it wrong (e.g.
quantifying `□` over all states) changes the logic.

## Logos

18 operators across four subtheories, matching the counts in
[`11-theory-catalog.md`](./11-theory-catalog.md):

| Subtheory | Primitive | Defined |
|---|---|---|
| extensional | `¬` `∧` `∨` `⊤` `⊥` | `→` `↔` |
| modal | `□` | `◇` `\CFBox` `\CFDiamond` |
| counterfactual | `□→` (`\boxright`) | `◇→` (`\diamondright`) |
| constitutive | `≡` `≤` `⊑` (essence) `≼` | `⇒` (`\Rightarrow`) |

(11 primitive, 7 defined. The essence operator's symbol `⊑` collides with part-of only
typographically; context disambiguates — essence relates sentences, part-of relates states.)

### Primitive operators — extensional

**Negation `¬A`** — pure delegation; verification and falsification swap roles:

| Register | Condition |
|---|---|
| `true(¬A, w)` | `false(A, w)` |
| `false(¬A, w)` | `true(A, w)` |
| `ver(s, ¬A)` | `fal(s, A)` |
| `fal(s, ¬A)` | `ver(s, A)` |

**Conjunction `A ∧ B`** — verifiers are fusions of verifiers; falsifiers are falsifiers of
either conjunct or fusions thereof:

| Register | Condition |
|---|---|
| `true(A ∧ B, w)` | `true(A, w) ∧ true(B, w)` |
| `false(A ∧ B, w)` | `false(A, w) ∨ false(B, w)` |
| `ver(s, A ∧ B)` | `∃x, y. ver(x, A) ∧ ver(y, B) ∧ s = x ⊔ y` |
| `fal(s, A ∧ B)` | `fal(s, A) ∨ fal(s, B) ∨ ∃x, y. fal(x, A) ∧ fal(y, B) ∧ s = x ⊔ y` |

**Disjunction `A ∨ B`** — the structural mirror of conjunction (verifier and falsifier clauses
swap shapes; this asymmetry is the bilateral-semantics content, not an implementation accident):

| Register | Condition |
|---|---|
| `true(A ∨ B, w)` | `true(A, w) ∨ true(B, w)` |
| `false(A ∨ B, w)` | `false(A, w) ∧ false(B, w)` |
| `ver(s, A ∨ B)` | `ver(s, A) ∨ ver(s, B) ∨ ∃x, y. ver(x, A) ∧ ver(y, B) ∧ s = x ⊔ y` |
| `fal(s, A ∨ B)` | `∃x, y. fal(x, A) ∧ fal(y, B) ∧ s = x ⊔ y` |

**Top `⊤`** and **Bottom `⊥`** (arity 0) — note the asymmetry, which is the source's actual
behavior: *every* state verifies `⊤`, but only the null state falsifies `⊥`:

| Register | `⊤` | `⊥` |
|---|---|---|
| `true(·, w)` | always | never |
| `false(·, w)` | never | always |
| `ver(s, ·)` | always (all `2^N` states) | never |
| `fal(s, ·)` | never | `s = ∅` |

### Primitive operators — modal

**Necessity `□A`** — quantifies over **worlds only** (states satisfying `is_world`), not all
`2^N` states; its verifier collapses to the null state (necessity claims carry no
subject-matter):

| Register | Condition |
|---|---|
| `true(□A, w)` | `∀u. is_world(u) → true(A, u)` |
| `false(□A, w)` | `∃u. is_world(u) ∧ false(A, u)` |
| `ver(s, □A)` | `s = ∅ ∧ true(□A, w)` |
| `fal(s, □A)` | `s = ∅ ∧ false(□A, w)` |

The evaluation world `w` is inert in `true(□A, w)` — the condition is world-independent — but
the null-state verifier clause still evaluates it at the ambient point.

### Primitive operators — counterfactual

**Counterfactual `A □→ B`** — the operator built on `is_alternative` (defined in
[`05-state-encoding.md`](./05-state-encoding.md)): every world that results from imposing any
verifier of the antecedent on the evaluation world must make the consequent true:

| Register | Condition |
|---|---|
| `true(A □→ B, w)` | `∀x, u. (ver(x, A) ∧ is_alternative(u, x, w)) → true(B, u)` |
| `false(A □→ B, w)` | `∃x, u. ver(x, A) ∧ is_alternative(u, x, w) ∧ false(B, u)` |
| `ver(s, A □→ B)` | `s = w ∧ true(A □→ B, w)` |
| `fal(s, A □→ B)` | `s = w ∧ false(A □→ B, w)` |

Unlike the modal and constitutive operators, whose degenerate verifier is the **null state**,
the counterfactual's verifier/falsifier is the **evaluation world itself** — a porter matching
golden output will see `w`, not `∅`, in a counterfactual's verifier set.

### Primitive operators — constitutive

All four constitutive primitives are world-independent (their truth conditions never mention
`w`) and share the null-state collapse: `ver(s, ·) = (s = ∅ ∧ true(·, w))` and
`fal(s, ·) = (s = ∅ ∧ false(·, w))`. Only their truth conditions differ; each `false` condition
is the literal negation (De Morgan dual) of its `true` condition, written out
existentially in the source.

**Identity `A ≡ B`** — same verifiers and same falsifiers (the source writes this as four
inclusion conjuncts; the biconditional form is equivalent):

```
true(A ≡ B, w)  =  [∀x. ver(x, A) ↔ ver(x, B)] ∧ [∀x. fal(x, A) ↔ fal(x, B)]
```

**Ground `A ≤ B`** ("A grounds B" / A is a disjunctive part of B) — three conjuncts:

```
true(A ≤ B, w)  =  [∀x. ver(x, A) → ver(x, B)]
                 ∧ [∀x, y. (fal(x, A) ∧ fal(y, B)) → fal(x ⊔ y, B)]
                 ∧ [∀x. fal(x, B) → ∃y. fal(y, A) ∧ y ⊑ x]
```

**Essence `A ⊑ B`** ("A is the essence of B" / A is a conjunctive part of B) — the
verifier/falsifier dual of ground:

```
true(A ⊑ B, w)  =  [∀x, y. (ver(x, A) ∧ ver(y, B)) → ver(x ⊔ y, B)]
                 ∧ [∀x. ver(x, B) → ∃y. ver(y, A) ∧ y ⊑ x]
                 ∧ [∀x. fal(x, A) → fal(x, B)]
```

**Relevance `A ≼ B`** — the two fusion-closure conjuncts alone (the shared content of ground
and essence, without either containment direction):

```
true(A ≼ B, w)  =  [∀x, y. (ver(x, A) ∧ ver(y, B)) → ver(x ⊔ y, B)]
                 ∧ [∀x, y. (fal(x, A) ∧ fal(y, B)) → fal(x ⊔ y, B)]
```

### Defined operators — expansions

Definitional expansion is total and eager ([`03-operators.md`](./03-operators.md)): by
constraint-generation time every occurrence of a defined operator has been rewritten to its
expansion, so **the expansion below is the complete solve-path semantics** of each operator:

| Operator | Expansion |
|---|---|
| `A → B` | `¬A ∨ B` |
| `A ↔ B` | `(A → B) ∧ (B → A)` |
| `◇A` | `¬□¬A` |
| `\CFBox A` | `⊤ □→ A` |
| `\CFDiamond A` | `⊤ ◇→ A` |
| `A ◇→ B` | `¬(A □→ ¬B)` |
| `A ⇒ B` | `(A ≤ B) ∧ (A ⊑ B)` (ground and essence) |

### Irregularities a porter must not reproduce

These are the concrete instances of [`03-operators.md`](./03-operators.md)'s abstract warning
that defined operators hand-maintain dead semantic methods:

- **`→` hand-maintains a full independent register set.** Despite being defined as `¬A ∨ B`,
  the material conditional carries hand-written `true_at`/`false_at`/`extended_verify`/
  `extended_falsify` implementations that re-derive the `¬A ∨ B` clauses inline (as does `↔`
  for its expansion, and `⇒` for ground-and-essence). These duplicates are dead code on the
  solve path and exist only as drift risk. A port should implement defined operators by
  expansion only.
- **`◇` is the clean counterexample** — it declares only its definition and a print method, no
  hand-maintained semantics. This is the pattern to follow.
- **`\CFBox`, `\CFDiamond`, and `◇→` hand-maintain methods that are not even well-typed.**
  Their dead methods construct a fresh `CounterfactualOperator` instance ad hoc — bypassing
  the operator-collection wiring — and pass a bare operator *class* (`\CFBox`, `\CFDiamond`)
  or an already-built Z3 formula (`◇→`) where the recursion expects a sentence object. These
  methods would raise if ever called; expansion is the only reason they never are. Port the
  expansions in the table above and nothing else.

## Exclusion

4 operators, all primitive: `¬` (`\neg`), `∧` (`\wedge`), `∨` (`\vee`), `≡` (`\equiv`)
(classes `UniNegation…`/`UniConjunction…`/`UniDisjunction…`/`UniIdentityOperator`). The register
set is **different in kind** from logos:

- **Verifier-only (unilateral)**: there is no `false_at`, no `extended_falsify`, and no
  falsifier sets. Operators implement `true_at`, `extended_verify`, and a post-solve
  `compute_verifiers` (the concrete register). The countermodel query compensates: a premise
  contributes `true(P, w)`, a conclusion contributes `¬true(C, w)` — negation of truth, not a
  falsity condition.
- **Atomic base cases**: `ver(s, p) = verify(s, p)` as in logos, but atomic truth is
  `true(p, w) = verify(w, p)` — the *world itself* must verify the atom, not some part of it
  (contrast logos's `∃x ⊑ w. verify(x, p)`).
- `possible` and `is_world` are *derived* from the `excludes` primitive — see
  [`05-state-encoding.md`](./05-state-encoding.md)'s helper-predicate section.

| Operator | `true(·, w)` | `ver(s, ·)` |
|---|---|---|
| `A ∧ B` | `true(A, w) ∧ true(B, w)` | `∃x, y. x ⊔ y = s ∧ ver(x, A) ∧ ver(y, B)` |
| `A ∨ B` | `true(A, w) ∨ true(B, w)` | `ver(s, A) ∨ ver(s, B)` — **no** fusion clause, unlike logos disjunction |
| `A ≡ B` | `∀x. ver(x, A) ↔ ver(x, B)` | the same state-independent condition — when it holds, *every* state verifies `A ≡ B`; when it fails, none does |
| `¬A` | `∃x. ver(x, ¬A) ∧ x ⊑ w` | the three-condition witness formula below |

**Unilateral negation** is the theory's core, and the reason its witness machinery exists. With
`h_f, y_f : BitVec(N) → BitVec(N)` the witness-function pair registered for this negation
occurrence `f = ¬A` (see [`11a-exclusion-witnesses.md`](./11a-exclusion-witnesses.md) for the
mechanism, registry lifecycle, and the higher-order condition this Skolemizes):

```
ver(s, ¬A)  =  [∀x. ver(x, A) → (y_f(x) ⊑ x ∧ excludes(h_f(x), y_f(x)))]      (exclusion)
             ∧ [∀x. ver(x, A) → h_f(x) ⊑ s]                                    (upper bound)
             ∧ [∀z. (∀x. ver(x, A) → h_f(x) ⊑ z) → s ⊑ z]                      (least upper bound)
```

**Frame constraints** (the closed list promised in
[`04-constraint-generation.md`](./04-constraint-generation.md)) — exactly four are asserted:

1. **Actuality**: `is_world(main_world)`
2. **Exclusion symmetry**: `∀x, y. excludes(x, y) → excludes(y, x)`
3. **Harmony**: `∀x, y. (is_world(x) ∧ coheres(x, y)) → possible(y)`
4. **Rashomon**: `∀x, y. (possible(x) ∧ possible(y) ∧ coheres(x, y)) → possible(x ⊔ y)`

Three further candidate constraints are defined in the source but deliberately **not** asserted
(the null state excludes nothing; every non-null state has an excluder; every non-null state has
a partially excluded part). A port must reproduce the asserted four only.

## Imposition

13 operators, of which **9 are logos classes reused verbatim** — the same class objects, not
re-implementations: the seven extensional operators (`¬ ∧ ∨ ⊤ ⊥ → ↔`) and the two basic modal
operators (`□ ◇`), imported directly from the logos subtheory modules. Their semantics are
exactly the logos tables above; do not re-derive them. The four imposition-specific operators:

| Operator | Kind | Semantics |
|---|---|---|
| `A ⊡ B` (`\boxright`, `ImpositionOperator`) | primitive | table below |
| `A ◇⊡ B` (`\diamondright`) | defined | `¬(A ⊡ ¬B)` |
| `\boxrightlogos` | primitive (renamed subclass) | logos's `□→`, verbatim, under a second name |
| `\diamondrightlogos` | defined | `¬(A \boxrightlogos ¬B)` |

The two `…logos` names exist so one example can run Fine's counterfactual and logos's
counterfactual side by side; they add no new semantics.

**The imposition counterfactual `A ⊡ B`** replaces logos's *defined* `is_alternative(u, x, w)`
with the *primitive* relation `imposition(x, w, u)` — the shape is otherwise identical to the
logos counterfactual:

| Register | Condition |
|---|---|
| `true(A ⊡ B, w)` | `∀x, u. (ver(x, A) ∧ imposition(x, w, u)) → true(B, u)` |
| `false(A ⊡ B, w)` | `∃x, u. ver(x, A) ∧ imposition(x, w, u) ∧ false(B, u)` |
| `ver(s, A ⊡ B)` | `s = w ∧ true(A ⊡ B, w)` |
| `fal(s, A ⊡ B)` | `s = w ∧ false(A ⊡ B, w)` |

**Fine's four frame conditions** on `imposition` (asserted in addition to logos's two frame
constraints — this is the closed six-member list promised in
[`04-constraint-generation.md`](./04-constraint-generation.md)):

1. **Inclusion**: `∀x, y, z. imposition(x, y, z) → x ⊑ z`
2. **Actuality**: `∀x, y. (x ⊑ y ∧ is_world(y)) → ∃z. z ⊑ y ∧ imposition(x, y, z)`
3. **Incorporation**: `∀x, y, z, u. (imposition(x, y, z) ∧ u ⊑ z) → imposition(x ⊔ u, y, z)`
4. **Completeness**: `∀x, y, z. imposition(x, y, z) → is_world(z)`

(A `derive_imposition` setting replaces these with derived constraints and trivializes the
premise/conclusion behaviors, turning a run into the meta-proof described in
[`11-theory-catalog.md`](./11-theory-catalog.md); the table above is the normal mode.)

## Bimodal

17 operators: 9 primitive (`¬ ∧ ∨ ⊥ □`, `\Future`, `\Past`, `\Until`, `\Since`) and 8
defined. The register set differs from both families above:

- **No verifiers at all.** Truth is evaluated at `(w, t)` pairs — `w` a world-history ID, `t`
  an integer time. Operators implement `true_at`/`false_at` plus a concrete post-solve
  `find_truth_condition` returning, per world, the pair (times where true, times where false) —
  the theory's *extension* register, replacing `find_verifiers_and_falsifiers`.
- **Notation** for this section: `true(A, w, t)`; `w(t)` is the world state of history `w` at
  time `t` (`world_function` applied and selected); `dom(w)` is `w`'s valid time interval; `D`
  is the global time domain (all valid times, determined by the `M` setting); `is_world(w)`
  here is the primitive world-ID validity predicate (see
  [`05-state-encoding.md`](./05-state-encoding.md)).

**Atomic base case** — atoms are false outside their world's interval by definition:

```
true(p, w, t)  =  t ∈ dom(w) ∧ truth_condition(w(t), p)
```

**Primitive operators** (`false(·)` for `¬ ∧ ∨ ⊥` is the classical dual; for the quantified
operators it is the mirrored existential, shown where the domain matters):

| Operator | `true(·, w, t)` |
|---|---|
| `¬A` | `false(A, w, t)` |
| `A ∧ B` | `true(A, w, t) ∧ true(B, w, t)` |
| `A ∨ B` | `true(A, w, t) ∨ true(B, w, t)` |
| `⊥` | never (`false(⊥, w, t)` always) |
| `□A` | `∀w'. is_world(w') → true(A, w', t)` — all world histories, same time, **no domain guard** on `t` |
| `\Future A` | `∀s ∈ D. s > t → true(A, w, s)` — all *globally* valid future times, not just `dom(w)` |
| `\Past A` | `∀s ∈ D. s < t → true(A, w, s)` |
| `\Until(A, B)` | `∃s ∈ D. s > t ∧ true(A, w, s) ∧ [∀r ∈ D. t < r < s → true(B, w, r)]` — strict witness, open guard interval |
| `\Since(A, B)` | `∃s ∈ D. s < t ∧ true(A, w, s) ∧ [∀r ∈ D. s < r < t → true(B, w, r)]` |

Two domain subtleties a port must preserve exactly: (1) `□` quantifies over **all** valid world
histories with no check that `t ∈ dom(w')` — combined with the atomic base case, an atom is
simply false at worlds whose interval excludes `t`; (2) the temporal quantifiers range over the
**global** time domain `D`, not the current world's interval — the same interaction applies.
Both choices align the theory with its external formal specification (see
[`11-theory-catalog.md`](./11-theory-catalog.md)) and were deliberate corrections; a port that
"helpfully" guards these quantifiers by `dom(w)` changes which formulas are valid.

**Defined operators**:

| Operator | Expansion | Reading |
|---|---|---|
| `A → B` | `¬A ∨ B` | material conditional |
| `A ↔ B` | `(A → B) ∧ (B → A)` | biconditional |
| `⊤` | `¬⊥` | tautology |
| `◇A` | `¬□¬A` | possibly |
| `\future A` | `¬\Future ¬A` | at some future time (lowercase = existential) |
| `\past A` | `¬\Past ¬A` | at some past time |
| `\next A` | `\Until(A, ⊥)` | at the immediately next time |
| `\prev A` | `\Since(A, ⊥)` | at the immediately previous time |

`\next` deserves a porter's note: `\Until(A, ⊥)` demands a future witness `s` with `⊥` true at
every time strictly between `t` and `s` — satisfiable only when that open interval is empty,
i.e. `s = t + 1`. The same trick gives `\prev` via `\Since`.


## Source files

- [`theory_lib/logos/subtheories/extensional/operators.py`](../../code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py)
  — `¬ ∧ ∨ ⊤ ⊥` primitives; `→ ↔` defined
- [`theory_lib/logos/subtheories/modal/operators.py`](../../code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py)
  — `□` primitive; `◇ \CFBox \CFDiamond` defined
- [`theory_lib/logos/subtheories/counterfactual/operators.py`](../../code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py)
  — `□→` primitive; `◇→` defined
- [`theory_lib/logos/subtheories/constitutive/operators.py`](../../code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py)
  — `≡ ≤ ⊑ ≼` primitives; `⇒` defined
- [`theory_lib/logos/semantic/core.py`](../../code/src/model_checker/theory_lib/logos/semantic/core.py)
  — the atomic base cases and helper predicates the clauses above recurse into
- [`theory_lib/exclusion/operators.py`](../../code/src/model_checker/theory_lib/exclusion/operators.py)
  — the four unilateral operators and the witness-predicate negation clause
- [`theory_lib/exclusion/semantic/core.py`](../../code/src/model_checker/theory_lib/exclusion/semantic/core.py)
  — exclusion's atomic base cases, derived helpers, and frame constraints
- [`theory_lib/imposition/operators.py`](../../code/src/model_checker/theory_lib/imposition/operators.py)
  — `ImpositionOperator`, the logos reuse imports, the renamed side-by-side pair
- [`theory_lib/imposition/semantic/core.py`](../../code/src/model_checker/theory_lib/imposition/semantic/core.py)
  — the `imposition` primitive and Fine's four frame conditions
- [`theory_lib/bimodal/operators.py`](../../code/src/model_checker/theory_lib/bimodal/operators.py)
  — the nine bimodal primitives and eight defined operators
- [`theory_lib/bimodal/semantic/core.py`](../../code/src/model_checker/theory_lib/bimodal/semantic/core.py)
  — bimodal's atomic base case, time-domain quantifier helpers, primitives

## Related

- [Operators](./03-operators.md) — the abstraction these formulas plug into
- [Constraint generation](./04-constraint-generation.md) — the double dispatch that unfolds them
- [State encoding](./05-state-encoding.md) — the state space, helpers, and primitive signatures
- [The theory catalog](./11-theory-catalog.md) — how the four theories relate
