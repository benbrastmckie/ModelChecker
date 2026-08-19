# Glossary
[← Spec map](./README.md)

> One canonical definition per load-bearing term, in the tree's mathematical register, each
> linking to the document that treats it fully. Ordered alphabetically for lookup, not
> narrative. Definitions here follow the state-mereology family (logos) unless a theory is
> named; the exclusion and bimodal variants are noted where they differ.

| Term | Definition |
|---|---|
| **alternative world** | `is_alternative(u, y, w)`: a world `u` containing the imposed state `y` and a maximal `y`-compatible part of `w` — the worlds a counterfactual's consequent is checked at. Defined formula in [`05-state-encoding.md`](./05-state-encoding.md); used by the counterfactual in [`03a-operator-semantics.md`](./03a-operator-semantics.md). Imposition replaces it with a primitive relation. |
| **compatible** | `compatible(x, y) := possible(x ⊔ y)` — two states whose fusion is possible. [`05-state-encoding.md`](./05-state-encoding.md). |
| **evaluation point** | The point of evaluation for truth: an untyped dict, `{world}` in the state-mereology family, `{world-id, time}` in bimodal. [`07-propositions.md`](./07-propositions.md). |
| **evaluation scheme** | Which kind of semantic value a theory extracts post-solve: bilateral (verifier/falsifier sets), unilateral (verifiers only), or temporal profile (truth per world at each time). [`07-propositions.md`](./07-propositions.md). |
| **falsifier** | A state `x` with `falsify(x, A)` (extended to complex `A` by the operator clauses): `A`'s truth at `w` is refuted by a falsifier that is part of `w`. Absent entirely in exclusion (unilateral) and bimodal. [`05-state-encoding.md`](./05-state-encoding.md), [`03a-operator-semantics.md`](./03a-operator-semantics.md). |
| **frame constraint** | A theory's model-shape axioms, asserted once per example independently of the formulas — a closed, exact list per theory. [`04-constraint-generation.md`](./04-constraint-generation.md); the lists are in [`03a-operator-semantics.md`](./03a-operator-semantics.md) and [`05-state-encoding.md`](./05-state-encoding.md). |
| **fusion** | The mereological sum of states: bitwise OR, written `x ⊔ y`. [`05-state-encoding.md`](./05-state-encoding.md). |
| **interning** | One node per distinct subformula: the syntax layer builds each subformula string once and shares the node; exclusion's witness registry keys its function pairs by formula string the same way. [`02-syntax-and-ast.md`](./02-syntax-and-ast.md), [`11a-exclusion-witnesses.md`](./11a-exclusion-witnesses.md). |
| **isomorphism (of models)** | Sameness-of-shape between two found models, checked as graph isomorphism over worlds and the accessibility relation — attribute-blind as implemented. Iteration yields only non-isomorphic models. [`08-iteration.md`](./08-iteration.md). |
| **main_point** | The designated evaluation point the countermodel query is stated at: premises true, conclusions false at `main_point`. Its world (`main_world`) is a solver-chosen constant in the state-mereology family; bimodal fixes world-id and time to 0. [`04-constraint-generation.md`](./04-constraint-generation.md). |
| **maximal** | `maximal(w) := ∀x. compatible(x, w) → x ⊑ w` — `w` absorbs everything compatible with it. [`05-state-encoding.md`](./05-state-encoding.md). |
| **part-of** | The mereological order on states: `x ⊑ y := x ⊔ y = y` (bit-vector: `x \| y == y`). [`05-state-encoding.md`](./05-state-encoding.md). |
| **possible** | Primitive unary predicate on states in logos/imposition (`possible : BitVec(N) → Bool`); *derived* in exclusion (`possible(x) := coheres(x, x)`). Downward closed under parthood by frame constraint. [`05-state-encoding.md`](./05-state-encoding.md). |
| **state** | A bit-vector of width `N`; the state space is all `2^N` values. Atomic substates display as `a, b, c, …`, fusions as `a.b`, the null state as `□`. [`05-state-encoding.md`](./05-state-encoding.md). |
| **verifier** | A state `x` with `verify(x, A)` (extended to complex `A` by the operator clauses): `A` is true at `w` iff some verifier of `A` is part of `w` (exclusion: iff `w` itself verifies `A`). [`05-state-encoding.md`](./05-state-encoding.md), [`03a-operator-semantics.md`](./03a-operator-semantics.md). |
| **witness predicate** | One of the fresh Skolem function pair `h_f, y_f : BitVec(N) → BitVec(N)` declared per negation formula in exclusion, replacing the second-order ∃ over functions in unilateral negation. [`11a-exclusion-witnesses.md`](./11a-exclusion-witnesses.md). |
| **world** | A maximal possible state: `is_world(w) := possible(w) ∧ maximal(w)` (exclusion: no possible proper extension; bimodal: a primitive validity predicate on world-history IDs). [`05-state-encoding.md`](./05-state-encoding.md). |

## Source files

- [`theory_lib/logos/semantic/core.py`](../../code/src/model_checker/theory_lib/logos/semantic/core.py)
  — the primitive declarations and helper predicates behind most terms above
- [`models/semantic.py`](../../code/src/model_checker/models/semantic.py) — the state space and
  mereology primitives
- [`theory_lib/exclusion/semantic/registry.py`](../../code/src/model_checker/theory_lib/exclusion/semantic/registry.py)
  — witness predicates

## Related

- [State encoding](./05-state-encoding.md) — the full encoding and helper-predicate tables
- [Operator semantics](./03a-operator-semantics.md) — where the terms do their work
