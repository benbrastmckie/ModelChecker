# Worked Trace
[← Spec map](./README.md)

> Two concrete examples — one valid argument, one countermodel — traced through all five
> pipeline stages with the actually generated constraints and the actually solved model,
> captured from a real run. Doubles as the golden test for a port's first working pipeline.

## The anchoring examples

Both anchors are `unit_tests` entries in
[`theory_lib/logos/subtheories/extensional/examples.py`](../../code/src/model_checker/theory_lib/logos/subtheories/extensional/examples.py),
so they stay tied to the executable conformance suite. Anyone editing this document should
re-run them (recipe below) and update the captured output.

| Anchor | Premises | Conclusions | Expected | Settings |
|---|---|---|---|---|
| `EXT_TH_1` (modus ponens) | `A`, `(A \rightarrow B)` | `B` | valid — no countermodel | `N=3`, `contingent=False`, `non_empty=True`, `non_null=True`, `disjoint=False` |
| `EXT_CM_1` (A does not entail ¬A) | `A` | `\neg A` | invalid — countermodel | `N=3`, `contingent=True`, `non_empty=True`, `non_null=True`, `disjoint=False` |

The extensional fragment keeps the constraint dump small: no modal/counterfactual operators, so
no helper-predicate expansions inside the premise constraints.

## Reproducing this trace

Run via the development CLI with constraint and raw-model printing enabled. The capture below
used a minimal example module (the standard example-file shape,
[`13-examples-and-cli.md`](./13-examples-and-cli.md)) importing the two anchors:

```python
from model_checker.theory_lib.logos.subtheories.extensional.examples import (
    EXT_TH_1_example, EXT_CM_1_example,
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics, LogosProposition, LogosModelStructure,
)

general_settings = {"print_constraints": True, "print_impossible": True,
                    "print_z3": True, "save_output": False, "maximize": False}

registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional'])
semantic_theories = {"Brast-McKie": {
    "semantics": LogosSemantics, "proposition": LogosProposition,
    "model": LogosModelStructure, "operators": registry.get_operators()}}
example_range = {"EXT_TH_1": EXT_TH_1_example, "EXT_CM_1": EXT_CM_1_example}
```

```bash
cd code && ./dev_cli.py trace_examples.py
```

Two capture quirks to know: `EXT_CM_1` ships with `iterate: 2`, so it prints two models plus an
iteration report — the trace below shows its **first** model (override `iterate` to `1` for a
single-model run). And `print_constraints` produces a constraint dump only together with an
unsat core — for a `sat` example the raw Z3 model (`print_z3`) is what you get.

## Stage 1 — parse

Formulas arrive in LaTeX-flavored prefix/infix notation (`\rightarrow`, `\neg`) and become
`Sentence` trees ([`02-syntax-and-ast.md`](./02-syntax-and-ast.md)). One consequential rewrite
happens here: `(A \rightarrow B)` is a *defined* operator, and definitional expansion is total
and eager ([`03a-operator-semantics.md`](./03a-operator-semantics.md)) — by constraint time the
second premise is `(¬A ∨ B)`. The premise-2 constraint below is visibly a disjunction whose
left disjunct is A's falsification clause: the expansion in action.

## Stage 2 — semantics

With `N = 3`: 8 states (`∅ = #b000` through `a.b.c = #b111`), primitives
`verify, falsify : BitVec(3) × AtomSort → Bool` and `possible : BitVec(3) → Bool` declared as
uninterpreted functions, and the designated world `w : BitVec(3)` left for the solver to choose
([`05-state-encoding.md`](./05-state-encoding.md)).

## Stage 3 — constraints

The four groups ([`04-constraint-generation.md`](./04-constraint-generation.md)), asserted with
tracked labels `frame1…`, `model1…`, `premises1…`, `conclusions1` (the labels reappear verbatim
in the raw model dump below; see [`06-solver-and-results.md`](./06-solver-and-results.md)).
What each example asserts:

| Group | `EXT_TH_1` (2 atoms) | `EXT_CM_1` (1 atom) |
|---|---|---|
| frame | 2 | 2 |
| model (per-atom menu) | 14 (7 per atom) | 8 |
| premise | 2 | 1 |
| conclusion | 1 | 1 |

In the mathematical register, the distinct constraints are:

- **Frame** (always, for logos): downward closure `∀x, y. (possible(y) ∧ x ⊑ y) → possible(x)`
  and actuality `is_world(w)`.
- **Model, classical four** (always, per atom `p`): verifier fusion closure
  `∀x, y. (verify(x, p) ∧ verify(y, p)) → verify(x ⊔ y, p)`; falsifier fusion closure (dual);
  no glut `∀x, y. (verify(x, p) ∧ falsify(y, p)) → ¬compatible(x, y)`; no gap
  `∀x. possible(x) → ∃y. compatible(x, y) ∧ (verify(y, p) ∨ falsify(y, p))`.
- **Model, settings-gated**: `contingent` adds a possible verifier
  `∃x. possible(x) ∧ verify(x, p)` and a possible falsifier (so `EXT_CM_1`: 4+2+2 = 8);
  `non_empty` (only when `contingent` is off) adds `∃x, y. verify(x, p) ∧ falsify(y, p)`
  (so `EXT_TH_1`: 4+1+2 = 7 per atom); `non_null` adds `¬verify(∅, p)` and `¬falsify(∅, p)`.
- **Premises/conclusions** (the countermodel framing): each premise `P` contributes
  `true(P, w)`, each conclusion `C` contributes `false(C, w)`.

Every quantifier is finitely expanded over all 8 states
([`05-state-encoding.md`](./05-state-encoding.md)). The premise-1 constraint `true(A, w)` =
`∃x ⊑ w. verify(x, A)` arrives at the solver as this 8-way disjunction (captured verbatim):

```
Or(And(0 | w == w, verify(0, A)),
   And(1 | w == w, verify(1, A)),
   ...
   And(7 | w == w, verify(7, A)))
```

and `EXT_TH_1`'s premise 2 — the expanded `(¬A ∨ B)` — as
`Or(⟨8-way falsify-A disjunction⟩, ⟨8-way verify-B disjunction⟩)`.

## Stage 4 — solve

- **`EXT_TH_1`**: `unsat` in 0.0085 s — **no countermodel, the argument is valid.** The
  captured unsat core touches 11 of the 19 asserted constraints (2 frame, 6 model, 2 premise,
  1 conclusion); the 6 model constraints in the core are exactly no-glut, `¬verify(∅, ·)`, and
  `¬falsify(∅, ·)` for each atom. (The core is solver-dependent — evidence, not a contract.)
- **`EXT_CM_1`**: `sat` in 0.0019 s — a countermodel exists, the inference fails. Bilateral
  semantics permits `A` true and `¬A` false at the same world without contradiction because
  falsifiers of `A`, not truth-functional negation, decide `¬A`.

## Stage 5 — interpret

The found `EXT_CM_1` model, captured verbatim. Raw Z3 assignment (`print_z3`):

```
w = 5,
possible = [3 -> False, 7 -> False, else -> True],
verify   = [(5, A) -> True, else -> False],
falsify  = [(2, A) -> True, (7, A) -> True, (6, A) -> True, else -> False]
```

Interpreted ([`07-propositions.md`](./07-propositions.md)): possible states are all but
`a.b (#b011)` and `a.b.c (#b111)`; the maximal possible states — the worlds — are `a.c (#b101)`
and `b.c (#b110)`; the evaluation world is `w = a.c`. The displayed state space and
propositions:

```
State Space:
  #b000 = □          #b001 = a          #b010 = b          #b011 = a.b (impossible)
  #b100 = c          #b101 = a.c (world)  #b110 = b.c (world)  #b111 = a.b.c (impossible)

The evaluation world is: a.c

1.  |A| = < {a.c}, {a.b.c, b, b.c} >   (True in a.c)
2.  |\neg A| = < {a.b.c, b, b.c}, {a.c} >   (False in a.c)
```

Read the checks directly: `A` is true at `a.c` because its verifier `a.c` is part of the world;
`¬A`'s verifiers are `A`'s falsifiers and vice versa (negation swaps the registers,
[`03a-operator-semantics.md`](./03a-operator-semantics.md)), and `¬A` is false at `a.c` because
its falsifier `a.c` is part of the world. Note the displayed set order — `{a.b.c, b, b.c}` is
*lexicographic on the rendered state names*, not bit-vector order (`b=2, b.c=6, a.b.c=7`); see
the ordering contract in [`07-propositions.md`](./07-propositions.md).

## Use as a golden test

A port reproducing this trace should treat as **required**:

- The verdicts: `EXT_TH_1` unsat (valid), `EXT_CM_1` sat (invalid), under exactly the settings
  above.
- For any `EXT_CM_1` model found: all frame/model/premise/conclusion constraints hold when
  checked concretely — in particular `A` true and `¬A` false at the designated world, no glut,
  the null state neither verifying nor falsifying, at least one possible verifier and
  falsifier.
- Given *this specific* Z3 assignment (injectable as a fixed model), the derived artifacts must
  match exactly: possible set, world set `{a.c, b.c}`, `|A| = ⟨{a.c}, {b, b.c, a.b.c}⟩`, and
  the truth values shown.

And as **incidental** (do not chase byte equality):

- *Which* countermodel the solver returns — any model of the constraints is correct; this one
  is a solver artifact (Z3 version, seed). `EXT_CM_1`'s shipped `iterate: 2` demonstrates a
  second, non-isomorphic model exists.
- Unsat-core membership, solver runtimes, tracked-label names, and display colors.
- Display formatting — though if golden *display* output is compared, the set-ordering contract
  in [`07-propositions.md`](./07-propositions.md) matters.

## Source files

- [`theory_lib/logos/subtheories/extensional/examples.py`](../../code/src/model_checker/theory_lib/logos/subtheories/extensional/examples.py)
  — `EXT_TH_1_example`, `EXT_CM_1_example`, the anchor definitions
- [`theory_lib/logos/semantic/proposition.py`](../../code/src/model_checker/theory_lib/logos/semantic/proposition.py)
  — the per-atom constraint menu asserted in stage 3; `find_proposition` for stage 5
- [`models/structure.py`](../../code/src/model_checker/models/structure.py) — verdict handling,
  constraint/core printing, the raw-model dump
- [`utils/formatting.py`](../../code/src/model_checker/utils/formatting.py) — the sorted set
  rendering the displayed output goes through

## Related

- [The pipeline](./01-pipeline.md) — the five stages this trace instantiates
- [Constraint generation](./04-constraint-generation.md) — the four groups and countermodel framing
- [Operator semantics](./03a-operator-semantics.md) — the formulas behind each constraint
- [Propositions](./07-propositions.md) — post-solve extraction and the ordering contract
