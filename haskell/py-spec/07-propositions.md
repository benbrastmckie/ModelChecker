# Propositions
[← Spec map](./README.md)

> The proposition contract, the three evaluation schemes used by the shipped theories, the
> untyped evaluation-point shape, and post-solve extraction.

## What a proposition is

A `Proposition` is **the semantic value of one sentence in one solved model** — the object that
knows how to compute and print a truth value once a model exists. Propositions are constructed
**eagerly, bottom-up, exactly once per solved model**: `interpret` (the pipeline's final stage)
walks the sentence tree, recursing into arguments first so
that every subformula's proposition exists before its parent's is built, and attaches one
`Proposition` per `Sentence` node. Nothing prevents calling `interpret` twice — a second call
silently overwrites the propositions with fresh, equal ones.

## The per-theory contract

| When | What |
|---|---|
| Constraint time (class-level, no instance) | `proposition_constraints(letter)` — the per-atom constraint menu |
| Post-solve | extraction of the concrete extension — see below, three different method names |
| Post-solve | `truth_value_at(eval_point)` |
| Post-solve | `print_proposition(eval_point, indent, use_colors)` |

## Evaluation points

An evaluation point is a plain, untyped dict — `{"world": w}` for the state-mereology family,
`{"world": id, "time": t}` for the temporal theory. Nothing in the base classes types or validates
this shape; each theory's dispatchers and operators agree on its keys purely by convention.

## Three evaluation schemes, one abstraction missing

Post-solve extraction — "given a found model, what is this sentence's semantic value?" — is
implemented under **three different method names**, discovered at runtime by the printer and
proposition layer rather than declared anywhere as a shared interface:

| Scheme | Method | Shape of the result |
|---|---|---|
| Bilateral (verifier/falsifier) | `find_verifiers_and_falsifiers` | a pair of state sets |
| Unilateral (verifier only) | `compute_verifiers` | one state set |
| Bivalent temporal profile | `find_truth_condition` | truth per world-history at each time |

```mermaid
flowchart TD
    A["solved model<br/>(z3_model)"] --> B["bottom-up walk of the<br/>sentence tree"]
    B --> C["per node: theory's extraction method<br/>(one of three names above)"]
    C --> D["Proposition attached<br/>to Sentence"]
    D --> E["truth_value_at(eval_point)"]
```

A port should make "evaluation scheme" an explicit, named abstraction with at least these three
inhabitants, rather than three unrelated method names a caller must discover by inspection.

## Identity is by formula name only

A proposition's equality and hash are computed **from the sentence's formula name alone** — so
two propositions of the *same formula* constructed from **different solved models** compare
equal. This is a real hazard for any collection-based logic (deduplicating propositions across
models, memoizing by proposition) and is not preserved intentionally; a port should key identity
by (formula, model) or avoid needing proposition identity across models at all.

## Source files

- [`models/proposition.py`](../../code/src/model_checker/models/proposition.py) —
  `PropositionDefaults`: construction, aliasing, identity, the abstract-by-guard contract
- [`theory_lib/logos/semantic/proposition.py`](../../code/src/model_checker/theory_lib/logos/semantic/proposition.py)
  — `find_verifiers_and_falsifiers`, the bilateral scheme
- [`theory_lib/exclusion/operators.py`](../../code/src/model_checker/theory_lib/exclusion/operators.py)
  — `compute_verifiers`, the unilateral scheme
- [`theory_lib/bimodal/operators.py`](../../code/src/model_checker/theory_lib/bimodal/operators.py)
  — `find_truth_condition`, the temporal-profile scheme
- [`models/structure.py`](../../code/src/model_checker/models/structure.py) — `interpret`, the
  bottom-up attachment walk

## Related

- [Operators](./03-operators.md) — `find_verifiers_and_falsifiers` as one of the six semantic
  methods
- [Solving and results](./06-solver-and-results.md) — the solved model propositions are computed
  against
- [Output and display](./09-output-and-display.md) — `print_proposition` in the display contract
