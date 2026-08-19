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

*Sections for the exclusion, imposition, and bimodal theories follow the same shape and are
being added alongside the witness-mechanism specification
([`11a-exclusion-witnesses.md`](./11a-exclusion-witnesses.md)).*

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

## Related

- [Operators](./03-operators.md) — the abstraction these formulas plug into
- [Constraint generation](./04-constraint-generation.md) — the double dispatch that unfolds them
- [State encoding](./05-state-encoding.md) — the state space, helpers, and primitive signatures
- [The theory catalog](./11-theory-catalog.md) — how the four theories relate
