Subject: How ModelChecker's modular architecture works

Hi [Name],

I wanted to give you a quick tour of ModelChecker's architecture, since I think you'll appreciate
how the extension mechanism is put together. ModelChecker is a Python framework for automating
Z3-backed model/countermodel search across several modal, counterfactual, and hyperintensional
semantic theories, built so a new theory or a new logical operator can be added without touching
the shared engine.

**Layered architecture.** There's a shared, theory-agnostic core: `models/` holds the semantics
base class, the bridge that turns parsed formulas into Z3 constraints, and the solver-facing
model structure and proposition classes; `syntactic/` holds parsing and the operator base
classes; `solver/` is a thin Z3/cvc5 backend abstraction. On top of that, each theory
(`theory_lib/logos`, `exclusion`, `imposition`, `bimodal`) supplies its own semantic primitives
and its own operator set. Logos further splits its 20+ operators into subtheories (extensional,
modal, constitutive, counterfactual, relevance, first-order) that get loaded à la carte.

**The pipeline.** This is the live, currently-exercised path — it's exactly what every theory's
pytest suite runs, via `Syntax` → `Semantics` → `ModelConstraints` → `ModelStructure`, not a CLI
tool (worth flagging: the `model-checker` command-line entry point is mid-refactor and not
functional right now, so I'm describing the programmatic API, which is stable). Concretely: a
formula string is parsed by `Syntax` into a `Sentence` tree, resolving operator symbols against
the theory's operator collection. `Semantics` then declares the theory's Z3 primitives (for
logos: `verify`, `falsify`, `possible`, as Z3 uninterpreted functions) plus frame constraints.
`ModelConstraints` is the bridge: it binds one instance of each operator to that semantics
object, walks the sentence tree, and assembles everything — frame constraints, per-letter model
constraints, premise and conclusion constraints — into a single list of Z3 `BoolRef` assertions,
i.e. compiled into SMT-level constraints. `ModelStructure.solve()` hands those to Z3 (via the
`solver/` abstraction) and gets back sat/unsat plus a model. Finally `interpret()`/`print_all()`
walk the same `Sentence` tree again, calling back into each operator's own
`find_verifiers_and_falsifiers()` and `print_method()` to turn the solved Z3 model into a
human-readable countermodel or proof.

**The operator abstraction.** This is the actual extension point. Every operator is a small
Python class subclassing `syntactic.Operator` (or `syntactic.DefinedOperator`, for operators
defined in terms of others) that implements a fixed contract: `true_at`, `false_at`,
`extended_verify`, `extended_falsify`, `find_verifiers_and_falsifiers`, and `print_method`. The
shared semantics and model-structure code dispatches *into* these methods rather than the other
way around — an operator is free to call back into the shared semantics object's own primitives
(`is_part_of`, `fusion`, `compatible`, or theory-specific relations) to state its truth
conditions in terms of that theory's resources.

**Worked example.** `theory_lib/logos/subtheories/counterfactual/operators.py` is a clean,
self-contained illustration. `CounterfactualOperator` (the primitive `\boxright`, "if A were the
case, B would be the case") implements `true_at` as a quantified Z3 formula — `ForAll([x, u],
Implies(And(extended_verify(x, A, eval_point), is_alternative(u, x, world)), true_at(B,
with_world(eval_point, u))))` — using two fresh Z3 bitvectors and the shared `is_alternative`
relation (a world-shifting helper built from `is_world`/`is_part_of`/`max_compatible_part`).
`extended_verify` uses a neat "world-identity" trick: a state verifies the whole conditional iff
that state *is* the evaluation world and the conditional is true there. `find_verifiers_and_falsifiers`
is pure post-solve logic — it reads the solved Z3 model directly and classifies each world as a
verifier or falsifier by checking whether all of the antecedent's alternative worlds satisfy the
consequent. And `print_method` doesn't reinvent rendering — it just delegates to the inherited
`print_over_worlds` helper from the `Operator` base class, showing the antecedent in the
evaluation world and the consequent in each alternative world. `MightCounterfactualOperator`
(`\diamondright`) is the `DefinedOperator` counterpart: `A ◇→ B := ¬(A □→ ¬B)`, built by
instantiating `CounterfactualOperator` internally rather than duplicating its logic.

That one file touches every stage of the pipeline — quantified constraint-building, the
verifier/falsifier trick, post-solve interpretation, and printing — while staying under 320
lines. New theories and operators get added the same way: subclass the same handful of base
classes and supply those six methods. Right now that's 4 theories and 25+ operators sharing one
engine.

Happy to walk through the Z3 side in more depth if useful.

Best,
[Your name]
