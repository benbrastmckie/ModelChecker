# Research Report: Task #116

**Task**: 116 - Draft an email for a Python expert explaining ModelChecker's modular architecture
**Started**: 2026-07-18
**Completed**: 2026-07-18
**Effort**: Medium (source-grounded architecture research, no implementation)
**Dependencies**: None
**Sources/Inputs**:
- Codebase: `code/src/model_checker/` (models/, syntactic/, solver/, theory_lib/)
- READMEs: root, `code/`, `code/src/model_checker/`, `code/src/model_checker/theory_lib/`
- `docs/architecture/*.md`, `code/docs/core/ARCHITECTURE.md`
- Git history (`git log`) to confirm current vs. stale subsystems
- `specs/archive/104_programmatic_api_cleanup/` (dead-code removal task)
**Artifacts**: This report — `specs/116_draft_email_modelchecker_architecture/reports/01_architecture-pipeline-operators.md`
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- ModelChecker's actual, currently-working pipeline is **not** the `model-checker` CLI /
  `BuildExample`/`BuildModule` workflow described in most READMEs and `docs/architecture/*.md` —
  that `builder/` package was **deleted** as dead code and `__main__.py`/`dev_cli.py` are
  presently broken (`ModuleNotFoundError: No module named 'model_checker.builder'`, verified by
  import). **The email must describe the live programmatic pipeline**, not the CLI workflow.
- The live pipeline (exercised by every theory's test suite today) is exactly four object
  constructions chained together: `Syntax(premises, conclusions, operator_collection)` →
  `Semantics(settings)` → `ModelConstraints(settings, syntax, semantics, proposition_class)` →
  `ModelStructure(model_constraints, settings)`, then `.check_result()` / `.print_all()`. This is
  literally what `model_checker.utils.testing.run_test()` does and what every
  `test_*_examples.py` file in `theory_lib/*/subtheories/*/tests/` calls.
- Shared general infrastructure (theory-agnostic) lives in `models/` (`SemanticDefaults`,
  `ModelConstraints`, `ModelDefaults`/`ModelStructure`, `PropositionDefaults`), `syntactic/`
  (`Syntax`, `Sentence`, `Operator`/`DefinedOperator`, `OperatorCollection`), and `solver/`
  (Z3/cvc5 adapter layer, `create_solver`). Each theory (logos, exclusion, imposition, bimodal)
  subclasses these to add its own semantic primitives; each theory's *subtheories*
  (logos only) further subclass/compose to add operator families.
- The operator abstraction is the modular-extension mechanism: every operator subclasses
  `syntactic.Operator` (or `syntactic.DefinedOperator` for operators defined in terms of others)
  and supplies `true_at`, `false_at`, `extended_verify`, `extended_falsify`,
  `find_verifiers_and_falsifiers`, and `print_method`. These methods are called back into by the
  shared semantics/model-structure/proposition classes during constraint generation, Z3 solving,
  and printing — this is precisely how "each model structure ... supports a range of operators
  supplied semantic clauses using that model structure's resources."
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` is a clean,
  complete worked example: `CounterfactualOperator` (primitive, `\boxright`/□→) implements all
  five required methods using semantics primitives (`extended_verify`, `is_alternative`,
  `true_at`, `with_world`) plus a hand-rolled ForAll/Exists Z3 quantifier pattern;
  `MightCounterfactualOperator` (`\diamondright`/◇→) is a `DefinedOperator` built from
  `CounterfactualOperator` + `NegationOperator` via `derived_definition`.
- Recommended narrative arc for the email is given in section (e) below.

## Context & Scope

The task is to gather accurate, source-grounded material for drafting a short email to a Python
expert explaining (1) ModelChecker's layered architecture, (2) the pipeline from a logical claim
through Z3 constraint solving back to a printed model, (3) the operator abstraction that lets
each "model structure" (theory) support a family of operators supplying their own semantic
clauses, and (4) `counterfactual/operators.py` as a worked example. This report does not write
the email — it supplies exact file paths, class/method names, and verified behavior so the
writer does not need to re-read source.

**Important scope-affecting discovery**: the repository is mid-refactor. Documentation (READMEs,
`docs/architecture/*.md`) describes a `BuildExample`/`BuildModule`/`model-checker` CLI pipeline
that was **removed** in task 104 ("Dead-code cleanup and thin CLI", commit `e1d9b6b2` "remove
builder directory and fix __init__.py", 2026-06-01). The CLI entry points (`__main__.py`,
`code/dev_cli.py`) still literally `import` the deleted `model_checker.builder` package and
currently fail with `ModuleNotFoundError` (verified directly — see Appendix). The task
description's mention of "SMTlib, solved, then passed back to print a model" pipeline is real and
current, but it is exercised via the **programmatic API** (`Syntax` → `Semantics` →
`ModelConstraints` → `ModelStructure`, i.e. what `model_checker.utils.testing.run_test()` and
every theory's pytest suite does), not via the `model-checker examples.py` CLI workflow the
READMEs advertise. The email should describe the programmatic pipeline as the ground truth and,
if it mentions the CLI at all, should not claim it currently works.

## Findings

### (a) Architecture Overview

**Top-level package**: `code/src/model_checker/` (installed as `model_checker`).

```
model_checker/
├── __init__.py         # public API: ModelConstraints, Syntax, get_theory, get_example, run_test
├── __main__.py          # CLI entry point — currently BROKEN (imports deleted builder/ package)
├── z3_shim.py            # backend-agnostic Z3/cvc5 re-export shim
├── models/               # SHARED general infrastructure: semantics base, constraints, model structure, propositions
├── syntactic/            # SHARED general infrastructure: parsing, Sentence, Operator base classes
├── solver/                # SHARED general infrastructure: Z3/cvc5 adapter abstraction layer
├── settings/              # SHARED: centralized settings management (theory-relevance principle)
├── output/                 # SHARED: result formatters (markdown/json/jupyter — trimmed in task 104)
├── utils/                   # SHARED: api.py (get_theory/get_example), testing.py (run_test — THE live pipeline entry point)
└── theory_lib/               # Per-theory (model-structure) implementations: logos, exclusion, imposition, bimodal
```

`code/src/model_checker/README.md:12-17` and `docs/architecture/README.md` both still list
`builder/`, `iterate/`, `jupyter/` as subdirectories — **these no longer exist on disk**
(confirmed via `find`/`ls`, and via `git log --diff-filter=D` showing their removal). Treat those
READMEs' *narrative* about "modularity" and "layered architecture" as broadly accurate context,
but do not cite their code-flow specifics (`BuildExample`, `model.runner.run_examples()`, etc.)
as literally true today.

**Genuinely shared/general infrastructure** (theory-agnostic, used by all 4 theories):

| Module | Key class(es) | Role |
|---|---|---|
| `models/semantic.py` | `SemanticDefaults` | Base semantics: state bit-vectors (`N`, `all_states`, `full_state`, `null_state`), `fusion`, `is_part_of`, settings plumbing. Every theory's `Semantics` class subclasses this. |
| `models/constraints.py` | `ModelConstraints` | Bridges syntax + semantics: instantiates operators with the semantics, walks the sentence tree (`instantiate`), and assembles `frame_constraints` + `model_constraints` + `premise_constraints` + `conclusion_constraints` into `all_constraints`. |
| `models/structure.py` | `ModelDefaults` (aliased/extended per-theory as `*ModelStructure`) | Owns the Z3 solver lifecycle: `solve()`, `check_result()`, `interpret()`, `print_all()`/`print_model()`/`print_grouped_constraints()`. |
| `models/proposition.py` | `PropositionDefaults` | Base class linking a parsed `Sentence` to its semantic interpretation in a solved model. |
| `syntactic/syntax.py` | `Syntax` | Parses infix premises/conclusions into a `Sentence` tree, resolves operators via the theory's `OperatorCollection`, extracts atomic sentence letters. |
| `syntactic/operators.py` | `Operator`, `DefinedOperator` | **The** modular-extension base classes (see section c). |
| `syntactic/sentence.py`, `collection.py` | `Sentence`, `OperatorCollection` | AST node + operator-name→class registry. |
| `solver/` | `create_solver`, `Z3SolverAdapter`, `Cvc5Adapter`, `SolverResult` | Backend-agnostic SMT solving; Z3 is a thin passthrough (`solver/z3_adapter.py`), cvc5 optional. |

**Per-theory (per model-structure) layer**: `theory_lib/{logos,exclusion,imposition,bimodal}/`,
each with `semantic.py` (subclasses `SemanticDefaults`/`ModelDefaults`/`PropositionDefaults`),
`operators.py` (theory's operator registry/collection), `examples.py` (validated test formulas).
Logos additionally splits its operators into **subtheories**
(`theory_lib/logos/subtheories/{extensional,modal,constitutive,counterfactual,relevance,first_order}/`),
each following the same `operators.py`/`examples.py`/`tests/` convention, loaded selectively via
`LogosOperatorRegistry.load_subtheories([...])` (`theory_lib/logos/operators.py:23-93`). This is
the concrete instance of "each model structure is built over shared general infrastructure and
supports a range of operators" — logos's `LogosSemantics` is the model structure; its 20+
operators across 5 subtheories are the "range of operators."

### (b) The Processing Pipeline (concrete modules/classes)

**This is the pipeline actually exercised today** — verified against
`theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py:13-48` and
`model_checker/utils/testing.py:12-55` (`run_test`), which are identical in structure:

1. **Parsing** — `Syntax(premises, conclusions, operator_collection)`
   (`code/src/model_checker/syntactic/syntax.py:45`). Parses infix formula strings (e.g.
   `'(A \\boxright C)'`) into a tree of `Sentence` objects, resolving each operator symbol against
   the theory's `OperatorCollection`, and collecting all atomic `sentence_letters`.

2. **Semantics instantiation** — `semantic_class(settings)`, e.g.
   `LogosSemantics(settings)` (`theory_lib/logos/semantic.py:110-193`). Declares the theory's Z3
   *uninterpreted functions* (for logos: `verify`, `falsify`, `possible` —
   `semantic.py:142-158`), the `main_point`/`main_world` evaluation point, and `frame_constraints`
   (structural axioms every model must satisfy, e.g. possibility downward closure and
   "main_world is a world").

3. **Constraint generation** — `ModelConstraints(settings, syntax, semantics, proposition_class)`
   (`models/constraints.py:19-94`). This is the bridge: it (a) instantiates one copy of every
   operator bound to this semantics (`copy_dictionary`, line 132), (b) recursively calls
   `sent_obj.update_objects(self)` on every parsed sentence (`instantiate`, line 150) so each
   `Sentence` gets linked to a `Proposition`, and (c) builds four constraint lists —
   `frame_constraints`, `model_constraints` (per-sentence-letter, via
   `proposition_class.proposition_constraints`), `premise_constraints` (via
   `semantics.premise_behavior`, which for logos is `lambda p: self.true_at(p, main_point)`), and
   `conclusion_constraints` (via `semantics.conclusion_behavior`, `false_at` at `main_point`) —
   concatenated into `all_constraints`. These are ordinary Z3 `BoolRef` expressions built via the
   Python API (`z3.And`, `z3.Implies`, `z3.ForAll`/custom `ForAll` helper, etc.) — i.e.
   *conceptually* SMT-LIB assertions, though generated and solved through Z3's Python bindings
   rather than literal `.smt2` text emission (see note in Appendix on terminology).

4. **Solving** — `ModelStructure(model_constraints, settings)`, e.g. `LogosModelStructure`
   (`models/structure.py:22-`, subclassed at `theory_lib/logos/semantic.py:1440`). Its `__init__`
   calls `self.solve(self.model_constraints, self.max_time)` immediately
   (`models/structure.py:100-102`). `solve()` (`structure.py:210-255`) creates a fresh solver via
   `create_solver(settings)` (`solver/registry.py`, backend selected by `settings['solver']`,
   default `'z3'`), asserts every constraint with `assert_tracked` for unsat-core support
   (`_setup_solver`, `structure.py:136-172`), sets a timeout, and calls `solver.check()`. Z3's own
   engine performs the actual SAT/SMT search; `Z3SolverAdapter` (`solver/z3_adapter.py:14-`) is a
   near-zero-overhead wrapper around `z3.Solver`. Results are normalized into
   `self.z3_model` (satisfiable) or `self.unsat_core` (unsatisfiable), plus `z3_model_status`,
   `z3_model_runtime` (`_process_solver_results`, `structure.py:108-134`).

5. **Result checking** — `check_result()` (`structure.py:292-305`) compares
   `z3_model_status` against the example's declared `settings["expectation"]` — this is the
   boolean `run_test()` returns and what pytest asserts on.

6. **Interpretation / printing back to a model** — `interpret(sentences)`
   (`structure.py:307-348`) recursively attaches a `Proposition` to every `Sentence` via
   `sent_obj.update_proposition(self)`, which (for logos) calls
   `LogosProposition.find_proposition()` (`theory_lib/logos/semantic.py:1182-1249`) — for atomic
   letters this reads the `verify`/`falsify` Z3 functions directly out of the solved model; for
   complex sentences it **delegates to `operator.find_verifiers_and_falsifiers(*arguments,
   eval_point)`** (line 1235) — the first of several points where operator-supplied methods close
   the loop back from "solved Z3 model" to "displayable semantic content." Printing is driven by
   `print_all()` (`structure.py:847-867`, calls `print_input_sentences` →
   `recursive_print` → `print_grouped_constraints` → `print_model`) and, per-sentence, by
   `recursive_print(sentence, eval_point, indent_num, use_colors)`
   (`structure.py:550-576`): atomic sentences print directly via
   `sentence.proposition.print_proposition(...)`; complex sentences delegate to
   **`operator.print_method(sentence, eval_point, indent_num, use_colors)`** (line 576) — the
   second point where an operator's own code renders the model.

**Data-flow one-liner for the email**: `formula string → Syntax → Sentence tree → (bound to)
Semantics/operators → ModelConstraints (Z3 BoolRef assertions) → ModelStructure.solve() via the
solver/ abstraction (Z3 by default) → z3_model → ModelStructure.interpret()/print_all(), which
call back into each operator's find_verifiers_and_falsifiers()/print_method() to render the
result.`

### (c) The Operator Abstraction / Modular Extension Mechanism

**Base classes**: `code/src/model_checker/syntactic/operators.py`.

- `Operator` (`operators.py:26-260`) — abstract base for all primitive operators. Required class
  attributes: `name` (the symbol, e.g. `"\\boxright"`), `arity` (int), `primitive` (bool, default
  `True`). `__init__(self, semantics)` stores `self.semantics` and raises if `name`/`arity` are
  unset or if `Operator` is instantiated directly (`operators.py:52-61`). Provides shared,
  reusable printing helpers every concrete operator can call: `general_print` (atomic-style
  recursive print), `print_over_worlds` (for modal/counterfactual-style operators that need to
  show the antecedent's evaluation and the consequent across alternative worlds —
  `operators.py:103-198`, this is exactly what `CounterfactualOperator.print_method` uses), and
  `print_over_times` (temporal analogue).
- `DefinedOperator(Operator)` (`operators.py:263-345`) — for operators expressed in terms of
  others. Subclasses implement `derived_definition(*args)` returning a nested prefix-notation
  list, e.g. `[NegationOperator, [CounterfactualOperator, leftarg, [NegationOperator, rightarg]]]`.
  `_validate_arity` (line 308) checks the declared `arity` matches `derived_definition`'s
  parameter count via `inspect.signature`. `primitive = False` is fixed on the class.

**The theory-specific operator protocol** (documented, not enforced by inheritance, at
`theory_lib/logos/protocols.py:74-150`, `OperatorProtocol`) — the methods a concrete operator
must implement for hyperintensional truthmaker semantics:

| Method | Signature | Purpose |
|---|---|---|
| `true_at(*arguments, eval_point)` | → Z3 `BoolRef` | Truth condition at an evaluation point (world). |
| `false_at(*arguments, eval_point)` | → Z3 `BoolRef` | Falsity condition at an evaluation point. |
| `extended_verify(state, *arguments, eval_point)` | → Z3 `BoolRef` | Whether `state` verifies the formula (hyperintensional truthmaker relation). |
| `extended_falsify(state, *arguments, eval_point)` | → Z3 `BoolRef` | Whether `state` falsifies the formula. |
| `find_verifiers_and_falsifiers(*arguments, eval_point)` | → `(set, set)` | Post-solve: compute the concrete verifier/falsifier state sets from the solved Z3 model, for display. |
| `print_method(sentence_obj, eval_point, indent_num, use_colors)` | → None (prints) | Theory/operator-specific rendering, typically delegating to `general_print`/`print_over_worlds`/`print_over_times` from the `Operator` base class. |

These are called back into by the shared infrastructure rather than called by the operator
itself: `LogosSemantics.true_at`/`false_at`/`extended_verify`/`extended_falsify`
(`theory_lib/logos/semantic.py:225-433`) each check whether the sentence is atomic (uses the raw
`verify`/`falsify` Z3 functions directly) or complex, and if complex, dispatch to
`operator.true_at(*arguments, eval_point)` etc. (e.g. `semantic.py:276`,
`operator.true_at(*arguments, eval_point)`). This is the exact mechanism by which "each model
structure ... supports a range of operators [that] supply semantic clauses using that model
structure's resources": the resources are the semantics' own primitives (state bit-vectors of
width `N`, `is_part_of`, `fusion`, `compatible`, `possible`, `verify`/`falsify`, `is_world`, plus
theory-specific relations like logos's `is_alternative`/`max_compatible_part`), which operators
call directly on `self.semantics` inside their `true_at`/`extended_verify`/etc. implementations.

**Theory/subtheory file convention**: `semantic.py` (the model structure: `*Semantics`,
`*Proposition`, `*ModelStructure` classes), `operators.py` (an operator collection or
`get_operators()` function returning `{symbol: OperatorClass}`), `examples.py` (validated
`premises, conclusions, settings` triples, organized into `countermodel_examples`/
`theorem_examples`/`unit_tests`/`example_range` dicts per
`code/src/model_checker/README.md:85-140`). Logos additionally has a
`LogosOperatorRegistry` (`theory_lib/logos/operators.py:23-221`) that loads subtheories on
demand, tracks inter-subtheory `dependencies` (e.g. `'counterfactual': ['extensional']`,
`'modal': ['extensional', 'counterfactual']` — line 34-41), and merges their operators into one
`OperatorCollection`, enabling `logos.get_theory(['extensional', 'modal'])`-style selective
loading (`theory_lib/README.md:44`).

### (d) Worked Example: `counterfactual/operators.py`

File: `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` (313
lines). Defines two operators, both consumed via `get_operators()` at the bottom of the file
(lines 302-312), returning `{"\\boxright": CounterfactualOperator, "\\diamondright":
MightCounterfactualOperator}`.

#### `CounterfactualOperator` (primitive; `\boxright`, displayed □→; arity 2) — lines 30-179

Semantic idea (from `theory_lib/logos/subtheories/counterfactual/README.md:63-99`, Brast-McKie
2025 "Counterfactual Worlds"): "if A were the case, B would be the case," implemented via
**alternative worlds**: given world `w` and a verifier `x` of `A`, an `x`-alternative to `w` is a
world containing `x` plus a maximal part of `w` compatible with `x` (the "minimal change" to
accommodate `A`). Method-by-method:

- **`true_at(leftarg, rightarg, eval_point)`** (lines 43-58): builds a `ForAll([x, u], Implies(
  And(extended_verify(x, leftarg, eval_point), is_alternative(u, x, world)), true_at(rightarg,
  with_world(eval_point, u))))`. Draws directly on `self.semantics.extended_verify`,
  `self.semantics.is_alternative` (`theory_lib/logos/semantic.py:468-496` — the semantics'
  alternative-worlds relation, itself built from `is_world`, `is_part_of`, and
  `max_compatible_part`), `self.semantics.true_at` (recursion back into the shared dispatcher),
  and `self.semantics.with_world` (returns a copy of `eval_point` with `world` replaced — a
  shared `SemanticDefaults`/`LogosSemantics` helper for world-shifting). Introduces two fresh Z3
  `BitVec`s (`t_cf_x`, `t_cf_u`, width `N`) and uses the project's own `ForAll`/`Exists` wrappers
  (`model_checker.utils`) rather than raw `z3.ForAll`.
- **`false_at(...)`** (60-72): the dual — `Exists([x, u], And(extended_verify(x, leftarg,
  eval_point), is_alternative(u, x, world), false_at(rightarg, with_world(eval_point, u))))`.
- **`extended_verify(state, leftarg, rightarg, eval_point)`** (74-81): "a state verifies A□→B at
  world w iff the state *is* w and A□→B is true at w" — `And(state == world, self.true_at(...))`.
  This is the standard "world-only" hyperintensional-verifier pattern for a
  possible-world-conditional embedded in truthmaker semantics.
- **`extended_falsify(...)`** (83-90): dual, using `self.false_at`.
- **`find_verifiers_and_falsifiers(leftarg, rightarg, eval_point)`** (92-150): **post-solve**
  logic (not Z3-constraint-building) — reads `leftarg.proposition.model_structure.z3_model`,
  iterates `model.z3_world_states`, for each world checks (via `z3_model.evaluate(...)`) whether
  it has any `A`-alternatives among `leftarg.proposition.verifiers`, and if so whether `B` is true
  (`rightarg.proposition.truth_value_at(alt_world)`) at all of them; classifies each world into
  `verifiers` (□→ true there, including vacuous truth when no alternatives exist) or `falsifiers`.
  This is exactly the callback described in pipeline stage 6 above.
- **`print_method(sentence_obj, eval_point, indent_num, use_colors)`** (152-179): computes
  `alt_worlds` by evaluating `semantics.is_alternative(world, state, eval_world)` for each
  antecedent verifier state and world in `model_structure.z3_world_states`, then delegates to the
  **inherited** `self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num,
  use_colors)` from the `Operator` base class — printing the antecedent at the current world and
  the consequent at each alternative world (color-coded true/false).

#### `MightCounterfactualOperator` (defined; `\diamondright`, displayed ◇→; arity 2) — lines 182-299

Subclasses `syntactic.DefinedOperator`. `derived_definition(leftarg, rightarg)` (194-196) returns
`[NegationOperator, [CounterfactualOperator, leftarg, [NegationOperator, rightarg]]]` — i.e.
`A ◇→ B := ¬(A □→ ¬B)`. Despite being "defined," it also implements `true_at`/`false_at`/
`extended_verify`/`extended_falsify`/`find_verifiers_and_falsifiers`/`print_method` directly
(199-299) rather than relying purely on substitution — each constructs a local, throwaway
`CounterfactualOperator()`/`NegationOperator()` instance, manually assigns `.semantics = self.semantics`
(since these ad hoc instances bypass the normal `ModelConstraints.copy_dictionary` instantiation
path), and expresses its own condition in terms of the primitive operator's methods (e.g.
`true_at`: `z3.Not(cf_op.true_at(leftarg, negated_right, eval_point))` where `negated_right =
neg_op.true_at(rightarg, eval_point)`). `find_verifiers_and_falsifiers` (249-260) evaluates
`self.true_at(...)`/`self.false_at(...)` directly against the solved model and returns
`{self.semantics.null_state}` as a stand-in verifier/falsifier singleton (rather than a computed
state set) — worth flagging in the email as a simplification specific to this defined operator.
`print_method` (262-299) mirrors the primitive operator's approach, with a fallback path that
also checks for an optional `semantics.calculate_alternative_worlds` helper
(`theory_lib/logos/semantic.py:498-521`) before falling back to the manual `is_alternative` loop.

**Concrete example** to anchor the narrative (from `.../counterfactual/examples.py:55-68`,
`CF_CM_1`): premises `['\\neg A', '(A \\boxright C)']`, conclusion `['((A \\wedge B) \\boxright
C)']` — a countermodel showing counterfactual antecedent strengthening is invalid (a classical
inference pattern that fails for counterfactuals, unlike material implication). This is a good
one-line illustration of the "non-monotonic" character called out in the subtheory's README
(`counterfactual/README.md:97`).

### (e) Suggested Narrative Arc for the Email

1. **Opening framing** (1-2 sentences): ModelChecker is a Python framework for automating
   Z3-backed model checking / countermodel search across multiple modal/counterfactual/
   hyperintensional semantic theories, built so new theories and new logical operators can be
   added without touching the shared engine.
2. **Layered architecture** (short paragraph): shared general infrastructure — `models/`
   (semantics base, constraint bridge, solver-facing model structure, propositions), `syntactic/`
   (parsing + operator base classes), `solver/` (Z3/cvc5 abstraction) — versus per-theory
   "model structures" in `theory_lib/{logos,exclusion,imposition,bimodal}/`, each supplying its
   own semantic primitives and its own operator set. Logos further splits operators into
   subtheories loaded à la carte.
3. **The pipeline**, one paragraph or a short numbered list mapping 1:1 onto section (b) above:
   formula string → `Syntax` (parse) → `Semantics` (declare Z3 primitives/frame constraints) →
   `ModelConstraints` (assemble all Z3 assertions — "compile to SMT-equivalent constraints") →
   `ModelStructure.solve()` (hand to Z3 via the solver abstraction, get back sat/unsat + a model)
   → `interpret()`/`print_all()` (walk the result back through the same Sentence tree, calling
   each operator's own `find_verifiers_and_falsifiers`/`print_method` to render it).
   *Caveat to include*: name this the programmatic pipeline (`Syntax`/`ModelConstraints`/
   `ModelStructure`, as used by every theory's test suite via `run_test()`), not the CLI, since
   the `model-checker` CLI currently has a broken import.
4. **The operator abstraction** (the "supports a range of operators" claim): every operator is a
   small Python class (`syntactic.Operator` or `DefinedOperator`) that implements a fixed
   contract — `true_at`, `false_at`, `extended_verify`, `extended_falsify`,
   `find_verifiers_and_falsifiers`, `print_method` — and is free to call back into the shared
   semantics object's own primitives (`is_part_of`, `fusion`, `compatible`, theory-specific
   relations like `is_alternative`) to state its truth conditions in terms of that theory's
   resources. This is what lets 20+ logos operators, 4 exclusion operators, etc. all plug into
   the same constraint-generation/solving/printing pipeline.
5. **Worked example — `counterfactual/operators.py`**: walk `CounterfactualOperator` method by
   method as in section (d) — this is the natural "show, don't tell" culmination for a Python
   expert, since it is a compact, self-contained ~150-line class that touches every stage of the
   pipeline (Z3 quantified constraint construction in `true_at`/`false_at`, the
   verifier-as-world-identity trick in `extended_verify`/`extended_falsify`, post-solve set
   computation in `find_verifiers_and_falsifiers`, and delegation to a shared print helper in
   `print_method`). Mention `MightCounterfactualOperator` briefly as the `DefinedOperator`
   counterpart (operator-in-terms-of-operators).
6. **Close**: optionally note the theory count/operator count (4 theories, 25+ operators;
   citation: Brast-McKie 2025 "Counterfactual Worlds" for this specific semantics) and that new
   theories/operators are added by subclassing the same small set of base classes — this is the
   "modular extension" claim made concrete.

## Decisions

- Use the **programmatic pipeline** (`Syntax`/`Semantics`/`ModelConstraints`/`ModelStructure`,
  i.e. what `run_test()` and the pytest suites do) as the pipeline description in the email, not
  the `model-checker` CLI / `BuildExample` workflow described in the READMEs, because the latter
  is currently non-functional (verified `ModuleNotFoundError`).
- Use `CounterfactualOperator` (the primitive `\boxright` operator) as the primary worked-example
  focus per the task instructions, with `MightCounterfactualOperator` as a brief secondary note
  illustrating `DefinedOperator`.
- Phrase the "SMTlib" step carefully: constraints are built as Z3 Python-API `BoolRef` trees
  (conceptually SMT assertions) and solved via Z3's own engine (through the `solver/` abstraction
  layer), not via literal `.smt2` text round-tripping — the email can still say "compiled into
  SMT-level constraints solved by Z3" without technical inaccuracy, but should not claim a
  textual SMT-LIB serialization step exists.

## Risks & Mitigations

- **Risk**: Email cites `model-checker examples.py` or `BuildExample` as the way to run this,
  which is currently broken. **Mitigation**: this report flags the breakage explicitly (Appendix)
  and gives the actual working pattern (mirrors `test_counterfactual_examples.py`) to cite
  instead, or the email can simply avoid mentioning a specific CLI/entry point and stay at the
  class-level pipeline description, which is accurate regardless of CLI status.
- **Risk**: Overstating "SMT-LIB" literally. **Mitigation**: see Decisions above — phrase as
  "Z3 constraints" or "SMT-level constraints" rather than implying literal SMT-LIB text.

## Context Extension Recommendations

- **Topic**: `docs/architecture/BUILDER.md`, `PIPELINE.md`, and the `builder/`-referencing
  sections of `code/src/model_checker/README.md` / `docs/architecture/README.md`.
- **Gap**: These describe a `BuildExample`/`BuildModule`/CLI pipeline that was deleted in task 104
  (2026-06-01) but the docs were never updated to match, and `__main__.py`/`dev_cli.py` still
  import the deleted module, so the CLI is currently broken.
- **Recommendation**: A follow-up `general`/`meta` task to either (a) restore a minimal working
  CLI entry point that uses the current `Syntax`/`Semantics`/`ModelConstraints`/`ModelStructure`
  pipeline directly, or (b) rewrite `docs/architecture/README.md`, `BUILDER.md`, `PIPELINE.md`,
  and `code/src/model_checker/README.md` to describe the current programmatic-only pipeline and
  remove/mark-deprecated the CLI usage examples. Out of scope for this email-drafting task, noted
  here for the requester's awareness.

## Appendix

### Verified breakage (do not cite CLI workflow as functional)

```
$ cd code && PYTHONPATH=src python3 -c "from model_checker.__main__ import main"
Traceback (most recent call last):
  ...
  File ".../code/src/model_checker/__main__.py", line 13, in <module>
    from model_checker.builder import (
ModuleNotFoundError: No module named 'model_checker.builder'
```
`code/dev_cli.py` has the same failure mode (imports `src.model_checker.__main__.main`).

### Key file/line references

- `code/src/model_checker/utils/testing.py:12-55` — `run_test()`, the canonical pipeline driver.
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py:13-48`
  — live example of the pipeline in use for the counterfactual subtheory.
- `code/src/model_checker/syntactic/syntax.py:19-80` — `Syntax` class.
- `code/src/model_checker/syntactic/operators.py:26-345` — `Operator`, `DefinedOperator` base classes.
- `code/src/model_checker/models/constraints.py:19-242` — `ModelConstraints`.
- `code/src/model_checker/models/structure.py:22-900+` — `ModelDefaults`/`ModelStructure`
  (`solve` 210-255, `check_result` 292-305, `interpret` 307-348, `print_model` 644-667, `print_all`
  847-867, `recursive_print` 550-576).
- `code/src/model_checker/models/proposition.py:15-123` — `PropositionDefaults`.
- `code/src/model_checker/solver/z3_adapter.py:14-193` — `Z3SolverAdapter`.
- `code/src/model_checker/theory_lib/logos/semantic.py:110-521` — `LogosSemantics`
  (`true_at`/`false_at`/`extended_verify`/`extended_falsify` 225-433, `is_alternative`/
  `max_compatible_part` 435-497, `calculate_alternative_worlds` 498-521), `1011-1440`
  `LogosProposition` (`find_proposition` 1182-1249, `truth_value_at` 1338+), `1440+`
  `LogosModelStructure`.
- `code/src/model_checker/theory_lib/logos/operators.py:23-221` — `LogosOperatorRegistry`.
- `code/src/model_checker/theory_lib/logos/protocols.py:74-150` — `OperatorProtocol` (documents
  the required operator methods).
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py:1-313` — full
  worked example (`CounterfactualOperator` 30-179, `MightCounterfactualOperator` 182-299,
  `get_operators()` 302-312).
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/README.md:19-99` — semantic
  narrative and citation (Brast-McKie 2025, "Counterfactual Worlds", *Journal of Philosophical
  Logic*).
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py:55-68` —
  `CF_CM_1` example formula used for illustration.
- `specs/archive/104_programmatic_api_cleanup/summaries/01_dead-code-cleanup-summary.md` — record
  of the `builder/` removal.

### Search queries / exploration used

- Directory listings (`ls`, `find`) of `code/`, `code/src/model_checker/`, `docs/architecture/`,
  `theory_lib/`, `theory_lib/logos/`, `theory_lib/logos/subtheories/counterfactual/`.
- `git log --oneline --diff-filter=D -- code/src/model_checker/builder`, `git show
  e1d9b6b2 --stat` — confirmed builder/ deletion and scope.
- `grep -n "class BuildModule\|class BuildProject\|class BuildExample"` across the repo — zero
  hits outside stale docs, confirming the classes no longer exist.
- Direct Python import test to verify CLI breakage (see Appendix).
- Targeted `Read` of: root `code/src/model_checker/README.md`, `docs/architecture/README.md`,
  `code/src/model_checker/__init__.py`, `__main__.py`, `models/constraints.py`,
  `syntactic/operators.py`, `models/structure.py` (2 ranges), `models/proposition.py`,
  `solver/README.md`, `solver/z3_adapter.py`, `theory_lib/logos/protocols.py`,
  `theory_lib/logos/operators.py`, `theory_lib/logos/subtheories/counterfactual/operators.py`
  (full file), `theory_lib/logos/semantic.py` (2 ranges), `models/semantic.py` (partial),
  `theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py`,
  `theory_lib/logos/subtheories/counterfactual/README.md`, `theory_lib/README.md`,
  `code/docs/core/ARCHITECTURE.md` (partial, confirmed also stale re: `builder/protocols.py`).
