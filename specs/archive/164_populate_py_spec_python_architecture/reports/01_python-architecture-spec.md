# Research Report: ModelChecker Python Architecture as a Porting Specification

- **Task**: 164 - Populate haskell/py_spec.md with a concise description of the core architecture for the Python implementation of the ModelChecker
- **Started**: 2026-08-18T22:15:00Z
- **Completed**: 2026-08-19T05:30:44Z
- **Effort**: ~7 hours (5 parallel territory investigations + synthesis)
- **Dependencies**: None
- **Sources/Inputs**:
  - Documentation sweep (92 markdown files): `docs/architecture/*` (12 files), `docs/usage/*`, `docs/theory/*`, `code/docs/core/ARCHITECTURE.md`, `code/docs/specific/*`, `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md`, per-package `README.md` files
  - Source verification across all 353 production/test Python modules under `code/src/model_checker/` (~46k production LOC, ~40.7k test LOC, 174 test files)
  - Executable contracts: `code/tests/test_layering.py`, `theory_lib/tests/test_theory_conformance.py`, `code/tests/cli/test_docs_flag_matrix.py`, `code/tests/packaging/`
  - Build/packaging: `code/pyproject.toml` (v1.3.3), `code/MANIFEST.in`, `flake.nix`, `.github/workflows/`
  - Project history: `specs/ROADMAP.md` Durable Decisions, `specs/CHANGE_LOG.md`
  - Live verification runs (`PYTHONPATH=code/src`): theory conformance suite (50 passed), operator/example enumeration per theory
- **Artifacts**:
  - `specs/164_populate_py_spec_python_architecture/reports/01_python-architecture-spec.md` (this report)
  - `specs/164_populate_py_spec_python_architecture/reports/findings/01_compiler-pipeline.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/02_core-utilities.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/03_tools-features.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/04_ui-cli.md`
  - `specs/164_populate_py_spec_python_architecture/reports/findings/05_theory-lib.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **The system is a five-stage compiler**: `Syntax` (infix string → mutable AST) → `Semantics` (theory-specific Z3 declarations + frame constraints) → `ModelConstraints` (four labelled constraint groups) → `ModelStructure` (solves in its constructor) → `interpret` (attaches propositions post-solve). Everything else — CLI, iteration, output, Jupyter — orbits this spine, and it is assembled by hand in **five separate places** in the codebase.
- **The extensibility story is genuinely good and is executably enforced.** A three-layer dependency model (core / `theory_lib` / upper) is verified by an AST-walking test that forbids core→theory imports *and* hardcoded theory-name literals; a single registration-based registry replaced three drifting "which theories exist" sources; and a parametrized conformance test asserts every theory implements one canonical module set. These three test files, not the documentation, are the real contract.
- **The semantic core is small and re-derivable.** States are `BitVec(N)`; fusion is bitwise OR; parthood is `s | t == t`; quantifiers are *finite expansions* over all `2^N` values rather than native Z3 quantifiers. An operator is a class with `name`, `arity`, and 4–6 methods. A theory is a 4-tuple of classes `{semantics, proposition, model, operators}`. This is the whole surface a port must reproduce.
- **The dominant structural weakness is phase-dependent mutation.** One `Sentence` class is mutated through four lifecycle phases, with the *type* of a field changing at each (`operator`: `None` → class → instance). `ModelDefaults` is a 933-line god object holding solver lifecycle, result flags, ANSI colors, and five printers. There is no typed result value flowing from solve to display — output is produced by `print()` and, when saving, recaptured from `sys.stdout` and regex-converted from ANSI to markdown.
- **Documentation is extensive (92 files) and materially stale in specific, identifiable ways.** 30+ concrete doc/source divergences were verified, including wrong operator method signatures in the syntactic README, a documented `--sequential` workflow whose flag raises `NotImplementedError`, three iterator settings (`iteration_attempts`, `escape_attempts`, `max_iterations`) that exist only in prose, and a `max_time` unit inversion (docstring says milliseconds, code means seconds). **Treat the executable tests and the source as ground truth; treat `docs/architecture/` as intent.**
- **Two live correctness defects and a substantial dead-code surface were found** during verification: the model iterator's generic difference constraint iterates `range(N)` where the state space is `range(2**N)` (under-constrains, silently relying on the isomorphism check); `stored_solver` retains a solver that never received assertions; theory-supplied iteration constraint hooks are never called by the live loop; and `check_result()` in the builder reads a stale `"model"` settings key, inverting validity reporting in the Jupyter path.

## Context & Scope

**What is being specified.** The deliverable this research feeds is `haskell/py_spec.md`: a description of the Python ModelChecker at a level of generality suitable for designing a Haskell implementation from scratch, with systematic improvements identified but *no Haskell design decisions made*. This report is therefore organized as a specification of observable behavior, data shapes, and contracts — plus an explicit inventory of what should not be reproduced.

**Method.** Five parallel investigations with exclusive file-ownership territories (compiler pipeline; core data structures/utilities/settings/registry; iteration/output/comparison; CLI/builder/Jupyter/packaging; theory library), each under hard-mode contracts requiring (a) a written findings file, (b) `file.py:LINE` grounding for every substantive claim, and (c) adversarial verification of documentation claims against source. A documentation sweep and cross-cutting invariant check (layering, packaging, concurrency, test scale) was run in the lead session. Line-level detail lives in the five `findings/` files; this report is the synthesis.

**Scale.** Package version 1.3.3. ~46k production LOC across 11 packages plus ~40.7k test LOC in 174 test files. `theory_lib` alone is 35k LOC including tests (bimodal 12.8k, logos 10.2k, exclusion 5.4k, imposition 4.5k). Runtime dependencies are exactly two: `z3-solver>=4.8.0` and `networkx>=2.0`, on Python `>=3.10`.

**Boundary.** The `oracle/` tree at repo root is a standalone differential-testing harness for the bimodal theory only, excluded from the wheel. It is quality infrastructure (N-version programming), not part of the framework, and is out of scope for a port — but its existence is a signal that bimodal's encoding was hard enough to warrant three independent implementations.

## Findings

### 1. The modular compiler design (DSL sentence → SMT constraints)

#### 1.1 Surface syntax and parsing

The DSL is a LaTeX-token propositional language with a deliberately minimal, **theory-agnostic** parser:

- **Atoms**: any token where `token.isalnum()` holds (`utils/parsing.py:33`). So `p`, `A`, `B1` are atoms; `isalnum()` is Unicode-aware, so `π` is technically one too.
- **Operators**: any token beginning with `\` (`utils/parsing.py:35`). The parser does *not* know which operators exist — names are resolved to classes in a later pass. This is the central modularity decision: **parsing is independent of the operator set**.
- **Nullary**: exactly `\top` and `\bot`, hard-coded in five places (see §1.7).
- **Unary**: prefix, unparenthesized (`\neg p`, `\Box \neg p`).
- **Binary**: strictly infix and **mandatorily parenthesized**, with no precedence — every binary application carries its own parentheses: `((p \vee q) \rightarrow r)`.
- **Tokenization**: pad parens with spaces, split on whitespace (`syntactic/sentence.py:139`).

The algorithm is hand-written recursive descent over a mutable token list (`utils/parsing.py:11-45`) with a binary-splitting helper `op_left_right` (`utils/parsing.py:48-119`) that scans left-to-right tracking parenthesis depth to locate the main connective.

**Output shape** — a nested prefix list where every argument is itself a list: `"(p \wedge q)"` → `["\\wedge", ["p"], ["q"]]`. (Several docs show a flat `["∧", "p", "q"]` form; that is stale — see §6.)

**Two verified parser gaps a port should close:**
- **Leftover tokens are silently discarded.** `parse_expression` never checks that input was fully consumed (`syntactic/sentence.py:139-141`). `"p q"` parses as `p`; `"\wedge p q"` parses as a *unary* application of `\wedge`, dropping `q`. A parser returning `(ast, rest)` with an end-of-input assertion eliminates the class.
- **Arity is never checked syntactically.** The parser infers unary-vs-binary from parentheses alone; `is_syntactically_wff` (`syntactic/formulas.py:15-76`) inspects only the head token and never recurses or checks arity. `ArityError` exists (`syntactic/errors.py:180`) and is imported but never raised anywhere. `(p \neg q)` parses fine and dies later as a raw `TypeError` deep inside constraint generation. Operator arity is available at the type-resolution pass and could be checked there trivially.

#### 1.2 The AST and its four-phase mutation lifecycle

There is **one** AST node class, `Sentence` (`syntactic/sentence.py:23`) — no node hierarchy — and it is mutated through four phases, documented at `syntactic/sentence.py:30-34`:

| Phase | Trigger | Effect |
|---|---|---|
| 1. Creation | `Sentence(infix)` | parse → `prefix_sentence`, `complexity`, `original_arguments` (as **infix strings**), `original_operator` (as a **string**) |
| 2. Type update | `Syntax.initialize_sentences` → `update_types(collection)` | operator strings → operator **classes**; atom strings → Z3 `Const(atom, AtomSort)`; **defined operators expanded**; `arguments` mutated from strings to `Sentence` objects |
| 3. Object update | `ModelConstraints.instantiate` → `update_objects(mc)` | operator classes → operator **instances** (looked up by `name`), carrying the theory's semantics |
| 4. Proposition update | `ModelStructure.interpret` → `update_proposition(ms)` | `proposition` field populated with a theory `Proposition` instance |

So the field `operator` holds, over time, `None` → class → instance; `original_arguments` holds strings then `Sentence`s. Every consumer must know the current phase, and nothing enforces ordering. `Syntax.all_sentences` additionally **interns nodes by infix string** (`syntactic/syntax.py:107-109`), so a subformula appearing in several premises is one shared mutable object.

**Spec-level statement**: the four phases are four distinct types (parsed / operator-resolved / semantics-bound / interpreted), and the "interning" is a hash-cons on syntactic identity.

#### 1.3 The operator abstraction

```
class Operator:
    name: str          # e.g. "\\wedge"
    arity: int
    primitive: bool = True
    def __init__(self, semantics): ...
```

Only `name`, `arity`, `primitive` and the semantics reference are declared on the base class (`syntactic/operators.py:26-260`). The **semantic methods are not declared at all** — not even as abstract methods; the docstring merely lists them, and the contract is enforced by `AttributeError` at constraint-generation time. Their actual shapes, uniform across every concrete operator:

```
def true_at(self, *arguments, eval_point)                    # -> Z3 BoolRef
def false_at(self, *arguments, eval_point)                   # -> Z3 BoolRef
def extended_verify(self, state, *arguments, eval_point)     # -> Z3 BoolRef
def extended_falsify(self, state, *arguments, eval_point)    # -> Z3 BoolRef
def find_verifiers_and_falsifiers(self, *sentence_objs, eval_point)  # -> (set, set)
def print_method(self, sentence_obj, eval_point, indent, use_colors)
```

Arguments are **splatted** `Sentence` objects followed by an `eval_point` — a plain untyped dict, `{"world": w}` for state theories and `{"world": id, "time": t}` for bimodal.

`DefinedOperator` (`syntactic/operators.py:263-344`) supplies only `derived_definition(*args)` returning a nested prefix list of operator *classes*, e.g. `\Diamond` → `[NegationOperator, [NecessityOperator, [NegationOperator, argument]]]`. Its arity is validated against the parameter count of `derived_definition` via `inspect.signature`.

`OperatorCollection` (`syntactic/collection.py:16-127`) is a name-keyed registry. **Duplicate names are silently skipped, first-registration-wins** (`collection.py:79-80`), despite a defined-but-unraised `DuplicateOperatorError`; unknown names surface as a bare `KeyError` despite a defined `UnknownOperatorError`. Load order therefore silently resolves name conflicts between composed subtheories, with no diagnostics.

**Definitional expansion is total and eager.** Expansion happens at phase 2 and, because derived arguments are re-parsed and recursively type-updated, the entire evaluated tree ends up primitive. Two consequences: (a) a `DefinedOperator`'s own `true_at`/`extended_verify` implementations are **dead code on the solve path** yet are hand-maintained in every logos operator — duplicated semantics that can drift from the definition; (b) `Syntax.circularity_check` runs *after* `initialize_sentences` has already expanded definitions, so a circular definition that is actually used blows the Python recursion limit before the intended cycle report fires. Expansion also instantiates the operator with the string `'a'` as a stand-in semantics (`syntactic/sentence.py:218`) — type-unsound by construction; `derived_definition` should be a static description.

#### 1.4 Constraint generation: four groups and double dispatch

`ModelConstraints(settings, syntax, semantics, proposition_class)` (`models/constraints.py:21-103`) produces exactly four labelled groups, in this order:

| Group | Generated by | Content |
|---|---|---|
| `frame_constraints` | theory semantics `__init__` | model-shape axioms (e.g. possibility downward-closed under parthood; `is_world(main_world)`) |
| `model_constraints` | `proposition_class.proposition_constraints(mc, letter)`, per sentence letter | the per-atom "what is a proposition" menu, settings-gated |
| `premise_constraints` | `semantics.premise_behavior(p)` | one per premise |
| `conclusion_constraints` | `semantics.conclusion_behavior(c)` | one per conclusion |

`premise_behavior` and `conclusion_behavior` are **lambdas set by the theory**, canonically:

```
self.premise_behavior    = lambda p: self.true_at(p, self.main_point)
self.conclusion_behavior = lambda c: self.false_at(c, self.main_point)
```

This encodes **countermodel search**: premises true and conclusions false at the designated point. A `sat` result is a countermodel (the argument is invalid); `unsat` means valid. Note this framing is baked in — alternative queries (entailment by quantification, equivalence checking) must be expressed through these two lambdas.

The formula→constraint translation itself is **mutual recursion (double dispatch)** between the theory's semantics object and the operator instances: `semantics.true_at(sentence, point)` checks whether `sentence.sentence_letter` is set (base case: emit the atomic clause) and otherwise delegates to `operator.true_at(*arguments, point)`; each operator recurses back into `semantics.true_at`/`extended_verify` for its subformulas. There is no memoization of emitted subformulas — Z3's internal hash-consing is the only sharing.

One idiom needs explicit re-modelling in a port: `proposition_constraints` is written as an *instance method of the proposition class* but is invoked **on the class with a `ModelConstraints` instance bound as `self`** (`models/constraints.py:81-88`). It works only because both classes happen to expose `.semantics` and `.settings`. Spec it as a pure function `(settings, semantics, letter) -> [Constraint]`.

#### 1.5 The semantic base contract

`SemanticDefaults` (`models/semantic.py:47-417`) provides for free:

- **State space**: `N` validated to `1 <= N <= MAX_N` where `MAX_N = 20` (the comment records measured RSS: 275 MB at N=16, 3.5 GB at N=20). Materializes `full_state`, `null_state`, and eagerly `all_states = [BitVecVal(i, N) for i in range(2**N)]`. Optional `M`/`all_times` for temporal theories.
- **Mereology over bit-vectors**: `fusion(s,t) = s | t`; `is_part_of(s,t) = fusion(s,t) == t`; plus `is_proper_part_of`, `non_null_part_of`, `total_fusion`, `product`, `coproduct` (pairwise-fusion closure), and Z3-set ↔ Python-set converters.
- **`DEFAULT_GENERAL_SETTINGS`** and a global-state reset hook.
- **A construction concurrency guard** (see §2.4).

A theory subclass must supply — enforced by **nothing** except `None` placeholders that later code dereferences: `DEFAULT_EXAMPLE_SETTINGS`, `main_point`, `frame_constraints`, `premise_behavior`, `conclusion_behavior`, its Z3 primitive declarations, and the `true_at`/`false_at`/`extended_verify`/`extended_falsify` dispatchers. Failures surface as `TypeError: 'NoneType' is not callable` deep inside `ModelConstraints`. Note also that although `N` is nominally optional at the semantics layer, `ModelDefaults.__init__` reads `semantics.all_states` and `.N` unconditionally, so **every usable theory must have `N`**.

#### 1.6 Quantifiers, encoding, and the solver layer

**Quantifiers are finite expansions, not Z3 quantifiers.** `utils.ForAll`/`Exists` (`utils/z3_helpers.py:16-87`) substitute all `2^N` bit-vector values for each bound variable and build an explicit `And`/`Or` — cost `(2^N)^k` for `k` bound variables. Logos uses these for nearly everything, so logos constraints are quantifier-free bit-vector formulas exponential in `N`. This is a deliberate semantic choice (decidable, model-completion-friendly) that a port must preserve *as a semantics*, but the expansion is recomputed at every call site with no sharing, and it is mixed inconsistently: logos's `get_non_empty_constraints` uses native `z3.Exists`, and bimodal uses native quantifiers throughout — which is why the Z3 adapter configures MBQI/e-matching globally.

**Encoding summary** (the whole of it):

| Concept | Encoding |
|---|---|
| state | `BitVec(N)` |
| fusion (mereological sum) | `s \| t` |
| part-of | `s \| t == t` |
| null / full state | `BitVecVal(0, N)` / `BitVecVal(2^N - 1, N)` |
| possible | uninterpreted `BitVec(N) -> Bool` |
| compatible(x,y) | `possible(fusion(x,y))` |
| world | `possible(w) ∧ ∀x. compatible(x,w) → is_part_of(x,w)` |
| atomic truthmaking | uninterpreted `verify, falsify : BitVec(N) × AtomSort -> Bool` |
| truth at a world | `∃x ⊑ w. verify(x, p)` (expanded to a `2^N`-way disjunction) |
| sentence letter | Z3 `Const(name, AtomSort)` where `AtomSort` is a `DeclareSort` |

**The solver layer** (`solver/`) is a backend abstraction supporting Z3 and cvc5: a `SolverProtocol`/`TrackedSolverProtocol` (add / check / model / push / pop / `assert_tracked` / `unsat_core`), per-backend adapters, ~80 thin expression wrappers, a lifecycle hook registry for cache invalidation, and backend-tolerant compatibility helpers. Backend selection priority is CLI override > env `MODEL_CHECKER_SOLVER` > `settings["solver"]` > default `"z3"`.

Solving happens **inside `ModelDefaults.__init__`** (`models/structure.py:126-131`). Each of the four constraint groups is asserted with a tracking label (`frame1`, `model1`, `premises1`, `conclusions1`, …) so an `unsat` result yields a labelled unsat core. `max_time` is in **seconds** and converted to milliseconds for the solver (the docstring saying milliseconds is wrong). Critically, **any `unknown` result is treated as a timeout**, never as `unsat` — a deliberate soundness fix documented in a long comment: Z3 reports "canceled" rather than "timeout", and treating unknown as unsat would unsoundly report validity.

There is no incremental solving on the main path (adapters expose `push`/`pop`; the core never calls them) and no constraint caching. Isolation between examples is achieved instead by fresh solvers plus a per-example **C-level Z3 context swap** (`utils/context.py:isolated_z3_context`), which prevents learned-lemma leakage between examples (the docstring cites 2–10× slowdowns without it).

#### 1.7 Extensibility seams — and where modularity leaks

**The seams (all four are clean):** a new operator is a class added to a collection; a new theory is the 4-tuple `{semantics, proposition, model, operators}`; a new subtheory is a `get_operators()` module; a new solver backend implements `TrackedSolverProtocol`.

**The leaks (verified):**
1. `\top`/`\bot` are special-cased in five core locations — a theory cannot add a nullary operator without editing core parsing.
2. The parser fixes the notational regime: unary-prefix / binary-infix-parenthesized. A ternary *primitive* operator cannot be parsed (though it can be represented and constructed programmatically).
3. Operator method shapes and `eval_point` dict keys (`"world"`, `"time"`) are stringly-typed conventions shared between each theory's dispatchers and its operators; core never sees them, and base-class print helpers already branch heuristically on their runtime shape.
4. `ModelConstraints` assumes the countermodel framing (§1.4).
5. `AtomSort` is a process-global; sentence-letter Z3 constants are shared by name across examples in a process. Isolation relies on fresh contexts, not fresh sorts.
6. A third solver backend requires editing `registry.py`, the expression-module chooser, and two name-validation sets — the registration hook exists but `create_solver` hard-codes the z3/cvc5 branch.

### 2. Core utilities and data structures

#### 2.1 The object graph

Construction order is strict and enforced only by each constructor taking the previous stage's product:

```
Syntax(premises, conclusions, operator_collection)
  → Semantics(settings)
    → ModelConstraints(settings, syntax, semantics, proposition_class)
      → ModelStructure(model_constraints, settings)     # SOLVES HERE
        → model_structure.interpret(premises + conclusions)
```

The graph is acyclic through stage 4 and becomes **cyclic at interpretation**: `Sentence.proposition ↔ Proposition.sentence`, and `ModelStructure → Sentence → Proposition → ModelStructure`. There is also pervasive **downward aliasing** — each later stage copies references out of earlier stages into flat attributes on itself (`ModelDefaults.N`, `Proposition.settings`, …). A port should treat those as derived accessors, not independent state.

#### 2.2 `ModelStructure` state and mutation

`ModelDefaults` is 933 lines and is simultaneously the solver driver and the result presenter. Ten fields form a mutable solver-state block initialized to sentinels and written after `solve()`: `solver`, `stored_solver`, `timeout`, `z3_model`, `unsat_core`, `z3_model_status`, `z3_model_runtime`, `solved`, `satisfiable`, `result` (a raw positional 4-tuple). An unsat or timed-out structure is still a fully constructed object, distinguished only by these flags.

**Verified defect worth naming**: `solve()` assigns `stored_solver = self.solver` *before* `_setup_solver` creates a second, constraint-loaded solver. After cleanup nulls `self.solver`, the only surviving handle — `stored_solver` — is a solver that never received any assertions, and the iterator's fallback path reaches for exactly that handle.

**Spec-level statement**: separate `build : Constraints -> Problem` from `solve : Problem -> Result`, and make the result a sum type (SAT model / unsat core with labels / timeout) rather than a ten-field mutable flag cluster.

#### 2.3 Propositions

A `Proposition` is *the semantic value of one sentence in one solved model*. It is constructed eagerly per sentence node, bottom-up, exactly once per solved model. `PropositionDefaults` is abstract-by-guard (direct instantiation raises `NotImplementedError`), validates its `model_structure` argument only by duck-typing, and copies a dozen aliases. **Its `__hash__`/`__eq__` are by formula name only**, so two propositions of the same formula in *different models* compare equal — a real hazard for any collection-based logic. The base class also contains presentation logic (ANSI color computation, and a stdout warning when a formula is neither true nor false).

The real per-theory contract is: `proposition_constraints(letter)` (constraint-time, class-level), plus post-solve `find_proposition()`/`find_extension()`, `truth_value_at(eval_point)`, and `print_proposition(...)`.

#### 2.4 Concurrency model

**Model construction and solving are single-threaded-only, and this is enforced, not merely documented.** Every theory's semantics constructor plus `ModelConstraints` and `ModelDefaults` build Z3 AST nodes against the single process-global Z3 context, which is not safe for concurrent use — two threads race on its hash-consing/refcount tables and can corrupt process memory. A process-global, thread-**reentrant** guard (`models/concurrency.py`) wraps the outermost constructor of every such class via `__init_subclass__`: the same thread may re-enter freely (so iteration building nested constraints works), but a second thread raises `ConcurrentConstructionError` immediately instead of segfaulting. The sanctioned parallelism is **one model per process**, which `--maximize` uses via `ProcessPoolExecutor`.

A port with per-run solver contexts and immutable terms can drop the guard apparatus entirely, but must preserve the invariant it protects: *construction of one model is a single serialized transaction*.

#### 2.5 Settings

Settings are declared in three places (base general settings on `SemanticDefaults`; per-theory `DEFAULT_EXAMPLE_SETTINGS` and optional `ADDITIONAL_GENERAL_SETTINGS`; a module-level fallback that diverges from the first and is currently dead). Precedence, lowest to highest:

1. base + theory-additional general defaults
2. user module-level `general_settings` (only keys already in the general defaults are merged)
3. theory `DEFAULT_EXAMPLE_SETTINGS`
4. user per-example settings (only keys in the example defaults are merged)
5. example settings wholesale overwrite general on key collision
6. CLI flags the user *actually typed*

That last qualifier is the fragile part: because `store_true` defaults are indistinguishable from explicit `False` in an argparse namespace, the settings layer re-scans raw `argv` to determine provenance, aided by a hand-maintained short→long flag map. **Clustered short flags (`-cn`) are parsed by argparse but not detected as user-provided, so their overrides silently do not apply** — documented in source as a known gap. `default=SUPPRESS` or tri-state options eliminate the whole mechanism.

Unknown settings produce a **printed warning and are discarded**, not an error, unless an opt-in `strict_mode` is set — which nothing in the production path enables. Combined with print-based (not `logging`) warnings, misconfiguration is easy to miss. This contradicts the project's own stated fail-fast principle.

**Setting inventory** (union across shipped theories; defaults as logos / bimodal / exclusion / imposition):

| Setting | Meaning | Defaults |
|---|---|---|
| `N` | bit-width; state space is `2^N` | 16 / 2 / 3 / 3 |
| `M` | number of time points (temporal only) | – / 2 / – / – |
| `contingent` | atoms forced contingent | True / False / False / False |
| `non_empty` | verifier/falsifier sets non-empty | True / – / False / False |
| `non_null` | null state verifies/falsifies nothing | True / – / False / False |
| `disjoint` | distinct letters get disjoint subject-matter | True / False / False / False |
| `possible`, `fusion_closure` | exclusion-only closure toggles | – / – / False / – |
| `max_time` | Z3 timeout in **seconds** | 10 / 1 / 1 / 1 |
| `iterate` | number of distinct models to find | False / 1 / 1 / 1 |
| `expectation` | expected verdict, for tests | None / True / None / None |
| `solver` | backend override | `"z3"` |

General settings: `print_impossible`, `print_constraints`, `print_z3`, `save_output`, `sequential`, `maximize`, `solver`, plus theory-additional `derive_imposition` (imposition) and `align_vertically` (bimodal).

Note `iterate` defaults to `False` in logos while the iterator validates it as a positive integer and the runner compares it against `1` — type-unsound, working only because examples always set an explicit integer. Spec it as a natural number `>= 1`.

#### 2.6 Utilities and the registry

`utils/` splits cleanly into **load-bearing** (`parsing.py` — the recursive-descent parser; `z3_helpers.py` — the finite-expansion quantifiers; `context.py` — C-level Z3 context isolation; `bitvector.py` — state ↔ display-name conversion, e.g. `a.b.c` fusion notation and `□` for the null state; `testing.py` — the canonical pipeline in miniature) and **incidental glue** (`formatting.py`, `version.py`, `api.py`).

The **registry** (`registry.py`, 218 lines) is a generic mechanism containing **zero theory-name literals** — the catalog lives in `theory_lib/__init__.py`. Each `TheoryEntry` holds four components (`semantics`, `proposition`, `model`, `operators`) supplied either as direct values or as zero-argument thunks, resolved once and memoized on first access; the four thunks of one theory share a cache so the theory's `get_theory()` runs at most once. Registration is idempotent and fail-fast on duplicates. A *registered but broken* theory raises nothing at registration time — the `ImportError` surfaces re-wrapped at first component access, so discovery errors are deferred to first use.

**Error-handling philosophy in practice**: errors that would produce *wrong logical verdicts* are handled strictly (unknown-as-timeout, `N` validation, model-state extraction, concurrency guard). Errors in *presentation and metadata* are absorbed with placeholder fallbacks (bare `except:` returning `"0.0.0-dev"`; unparseable bit-vectors becoming `"<unknown-…>"`). Configuration errors are warnings by default. This is a coherent policy and worth preserving explicitly — but it should be *stated* as a policy rather than emerging from scattered choices.

### 3. Tools and features (post-first-model machinery)

#### 3.1 Model iteration

The live loop is `BaseModelIterator.iterate_generator`. Per attempt: generate difference constraints against all previously found models → **permanently add** them to a persistent solver and `check()` → extract model → rebuild a full `ModelStructure` → reject if it has zero worlds → check isomorphism against all previous models → accept, compute differences, yield.

**"Distinct" is two-tiered**: (a) *syntactic difference* on designated semantic predicates, enforced by solver constraints; (b) *semantic distinctness up to isomorphism*, enforced post-hoc by a NetworkX graph check. A model satisfying (a) but failing (b) is counted as "isomorphic skipped" and never yielded.

The generic difference constraint is a disjunction "at least one state flips its `is_world` status relative to previous model M", conjoined across all previous models. **Two significant findings here:**

- **The generic constraint iterates `range(N)`, not `range(2**N)`** — so it only forces differences among the first `N` of `2^N` states, under-constraining and relying on the (expensive) isomorphism check to reject duplicates. The same off-by-representation appears in the non-isomorphic constraint.
- **The theory-supplied constraint hooks are never called by the live loop.** `BaseModelIterator` delegates constraint generation to a `ConstraintGenerator` component, which calls its *own* generic method — so each theory's carefully written `_create_difference_constraint` (logos's smart-ordered world-count / verify / falsify / parthood disjunction; imposition's ternary-relation differences; bimodal's world-history differences) is dead on the live path. The universal `z3.BoolVal(True)` stubs for `_create_non_isomorphic_constraint` and `_create_stronger_constraint` in every theory confirm the seam was never finished.

Rebuilding MODEL 2+ is heavier than it looks: the iterator constructs a *fresh* `Syntax`, semantics, and `ModelConstraints`, then **pins the new model's concrete values as constraints** (asserting `is_world(s)`/`possible(s)` for every state and `verify`/`falsify` for every (state, letter) pair to match the found model), replaces `all_constraints` with the pinned set, and re-solves — trivially sat, forced to the intended model — then interprets. A cleaner injection design exists in the codebase (`ModelConstraints.inject_z3_values` plus `iterate/build_example.py`) but has zero callers.

Isomorphism uses NetworkX over a graph whose nodes are worlds (keyed by *list index*, with `accessible(i, j)` called on indices rather than state values) and whose edges are accessibility. The definitive check calls `nx.is_isomorphic(g1, g2)` **without `node_match`/`edge_match`**, so proposition valuations and relation labels are ignored: genuinely distinct models can be skipped as isomorphic, while hyperintensional structure (verify/falsify, parthood) is invisible to the check entirely. The graph builder also appends to a hard-coded `/tmp/graph_debug.log` on every build — debug file I/O on a production hot path.

Termination: `iterate` (target count), per-search `max_time`, `max_invalid_attempts` (20 consecutive invalid models), a lack-of-progress heuristic, solver exhaustion, and `KeyboardInterrupt`. A mid-iteration timeout abandons only the current search; previously yielded models are kept, because yielding is incremental.

`iterate/` also contains a large dead-code surface worth *not* porting: three near-clone ~200-line iteration loops, an unused abstract base, an unused push/pop-based difference search (which is the cleaner pattern), an unused build-example injection module, and an aspirational protocol/enum vocabulary with no implementations.

#### 3.2 Output

**Exactly three output modes exist**: ANSI-colored terminal (default), a combined `EXAMPLES.md`, and a combined `MODELS.json`. Notebook and LaTeX constants exist but no corresponding formatters do; a sequential per-model save mode is fully scaffolded but **hard-disabled with `NotImplementedError`**.

The architecture is **capture-then-format, not data-then-render**. When saving is enabled, `sys.stdout` is redirected into a `StringIO`, the model prints itself, stdout is restored, the raw capture is re-printed to the console, and the markdown artifact is produced by regex-converting ANSI escape codes (red → bold, green → italic, strip the rest). The "markdown formatter" is, for non-empty input, `model_output.strip()`. Structured data comes from a *separate* collector that duck-types four extraction hooks on the model structure.

**Nothing reads the JSON back.** There is no persisted, re-loadable model.

The **display contract** a theory must satisfy: `print_to`, `print_all`, `print_states`, `print_evaluation`; propositions implement `print_proposition`; operators implement `print_method`, normally one of three base helpers (`general_print`, `print_over_worlds`, `print_over_times`). Recursive truth-tree printing is mutual recursion between `ModelStructure.recursive_print` and operator `print_method`s, producing the indented evaluation tree. Because propositions and operators print to *bare stdout*, the structure wraps recursion in `redirect_stdout`, and color choice tests object identity `output is sys.__stdout__` — which silently disables colors under capture and breaks under stream wrapping.

**Spec-level statement**: make `model → typed result → renderer` the only path. The existing collector schema is a reasonable starting shape.

#### 3.3 Comparison and progress

`--maximize` is narrower than its documentation suggests: its metric is **maximum `N` reachable within the time limit per theory**, not validity agreement. Each theory is serialized (classes → module/class-name strings), submitted to a `ProcessPoolExecutor`, and each worker increments `N` until failure. Results are printed as plain stdout text and bypass the output-saving subsystem entirely. Genuine cross-theory *semantic* comparison is just the ordinary path: `semantic_theories` with translation dictionaries runs each example under every theory sequentially.

Progress feedback is a daemon-thread animated bar whose fill is *elapsed/timeout*, plus a spinner for unmeasurable waits, with a deliberate "deferred completion" protocol (freeze the bar at the instant a model is found, then print bar → differences → header → model) so that bars and model blocks interleave correctly. The iterator itself writes the final ITERATION REPORT directly to `sys.stdout` — presentation logic inside the search engine.

### 4. UI and CLI components

#### 4.1 The verified CLI surface

One argparse parser, one positional argument, **17 options**. The `-l/--load_theory` choices are derived at parser-construction time from the runtime registry, not hardcoded. Verified against source (not docs):

| Flag | Short | Kind | Effect |
|---|---|---|---|
| `file_path` | — | positional, optional | examples file to run |
| `--load_theory` | `-l` | choice from registry | generate a project from that theory instead of running a file |
| `--contingent` | `-c` | store_true | settings override |
| `--non_null` | `-n` | store_true | settings override |
| `--non_empty` | `-e` | store_true | settings override |
| `--disjoint` | `-d` | store_true | settings override |
| `--maximize` | `-m` | store_true | theory-comparison mode |
| `--save [FMT…]` | `-s` | `nargs='*'`, `{markdown,json}` | enable saving; bare = both |
| `--sequential` | `-q` | store_true | **nonfunctional — raises `NotImplementedError`** |
| `--align_vertically` | `-a` | store_true | bimodal temporal display |
| `--z3` / `--cvc5` | — | mutually exclusive | solver backend |
| `--print_constraints` | `-p` | store_true | show constraints |
| `--print_z3` | `-z` | store_true | show raw Z3 output |
| `--print_impossible` | `-i` | store_true | include impossible states |
| `--version` | `-v` | version action | print and exit |
| `--upgrade` | `-u` | store_true | `pip install --upgrade` via subprocess |

Entry points: the installed console script `model-checker`, `python -m model_checker`, and the development wrapper `code/dev_cli.py` (which prepends `code/src` to `sys.path` so the working tree shadows any installed wheel, and accepts two extra wrapper-only flags). With no arguments, both entry points run interactive project generation.

The repo defends this surface with a **parser-derived documentation guard**: a test scans every fenced shell block in the docs for invocation lines and asserts each flag token is registered on the real parser. Its declared blind spot is exactly the `--sequential` case — flags that exist but do not work.

#### 4.2 The example-file format (the user's actual input language)

An examples file is **an ordinary Python module, executed on load**. The loader requires two module-level names and accepts a third:

- **`semantic_theories`** (required): `Dict[displayName, TheoryDict]`
- **`example_range`** (required): `Dict[exampleName, ExampleCase]` — what actually runs
- **`general_settings`** (optional): `Dict[str, Any]`

`TheoryDict` is validated to have `semantics` (a `SemanticDefaults` subclass), `proposition` (a `PropositionDefaults` subclass), `operators` (an `OperatorCollection` *instance*), `model` (a `ModelDefaults` subclass), and optionally `dictionary` — an operator-rename map applied by **plain string replacement** to every premise and conclusion before parsing.

`ExampleCase` is a list/tuple of exactly three elements: `[premises: [str], conclusions: [str], settings: dict]`.

Conventions (not enforced by anything): `{PREFIX}_CM_{n}` names a countermodel-expected example (`expectation: True`, i.e. the argument is invalid), `{PREFIX}_TH_{n}` a theorem (`expectation: False`); per-example variables are named `{NAME}_premises/_conclusions/_settings/_example`; a `unit_tests` dict holds the complete set for pytest while `example_range` is a curated subset maintained as a **comment-toggled dict literal**; an `if __name__ == '__main__':` block shells out to `model-checker` on the file itself.

Module loading picks one of three import strategies (theory-lib dotted import; package import triggered by a `.modelchecker` marker file; standard file-location import), **all three of which permanently mutate `sys.path`** and register modules under bare names.

**Spec-level statement**: configuration-by-arbitrary-code-execution makes the input "format" unspecifiable — any module attribute may exist, side effects run at load time, and validation is piecemeal at runtime. A declarative core (example records plus theory references by name) with an explicit escape hatch is strictly easier to port, verify, and sandbox.

#### 4.3 Project generation, Jupyter, packaging

**Project generation** (`BuildProject`) copies a theory directory according to an explicit manifest (required items, semantic-package alternatives, optional items), writes a `.modelchecker` marker (which is what later triggers package-import mode for the generated project), ensures `__init__.py` files exist, and rewrites version strings by regex over source text. It mixes `input()` prompting, `print()`, `subprocess.run(["model-checker", …])`, and `sys.path` mutation in one class, making it untestable without pty simulation and unusable programmatically.

**Jupyter integration** is a two-tier package: always-available helpers (Unicode ↔ LaTeX conversion for `□ ◇ ¬ ∧ → ↔ ▷`, environment setup, example loading, a `build_and_check` bridge) plus a dependency-gated interactive layer (widget-based `ModelExplorer` with formula box, theory dropdown, per-theory settings accordion, "Find Next Model" button, and a matplotlib/NetworkX graph view driven by per-theory display adapters attached to registry entries). Missing optional dependencies yield stub functions that raise a typed error on call. The notebook path **bypasses `BuildModule`, the module loader, and the output manager entirely** by fabricating a minimal mock module object — evidence that the real dependency is a small settings/output interface rather than the whole builder.

**Verified defect**: `BuildExample.check_result()` compares the solver status against a stale `settings.get("model", True)` key while the rest of the system uses `"expectation"`. Since no caller supplies `"model"`, it degenerates to "was a Z3 model found" — so the Jupyter `check_formula` reports "Valid" precisely when a **countermodel exists**, and `find_countermodel`'s branch logic is likewise inverted. The CLI and pytest paths are unaffected (they use the `"expectation"`-based `ModelDefaults.check_result`).

**Packaging**: setuptools with `src` layout; version declared once in `pyproject.toml` and read back from installed metadata; wheel contents governed by an explicit package-data allowlist (README/CITATION/LICENSE/`docs/*.md`/`notebooks/*.ipynb`) rather than a blanket glob, mirrored by `MANIFEST.in` prunes; a Nix flake providing the wheel, a dev shell, and a `checks.default` running the full suite; and a `code/tests/packaging/` suite that builds real wheels and sdists and asserts inclusions, exclusions, parity, entry points, and generate-then-execute round trips.

**Testing surface**: each theory's examples *are* its test suite — theory unit tests parametrize over `unit_tests` and run each example through `utils.run_test()`, which rebuilds the same pipeline without any builder involvement and asserts `z3_model_status == settings["expectation"]`.

### 5. The theory library — the extensible DSL's content

#### 5.1 The four theories

| Theory | Model theory | Atomic primitives | Distinctive machinery |
|---|---|---|---|
| **logos** (flagship) | bilateral truthmaker semantics; state lattice of `BitVec(N)` under fusion/parthood; worlds = maximal possible states | `verify`, `falsify`, `possible` | subtheory system; counterfactuals via `is_alternative` (maximal compatible parts); 18 operators when fully loaded |
| **exclusion** | Champollion–Bernard **unilateral** truthmaker semantics; verifiers only | `verify`, primitive `excludes`; `possible` **derived** (self-coherence) | per-formula Skolem witness functions `h`/`y` making minimality-quantified negation first-order; 4 operators |
| **imposition** | Kit Fine's counterfactuals over the same state lattice | logos primitives plus ternary `imposition(state, world, outcome)` | Fine's four frame conditions; a `derive_imposition` mode that turns a run into a meta-proof (UNSAT ⇒ logos's `is_alternative` satisfies Fine's axioms); 13 operators including *both* rival counterfactuals side-by-side |
| **bimodal** | temporal + modal over **world histories**; genuinely different model theory | `truth_condition(world_state, atom)` — no verifiers at all; ternary `task_rel`; `world_function : WorldId → Array(Time → WorldState)` | evaluation points are (world-id, time) pairs; 11 frame constraints incl. Lean-aligned TaskFrame axioms and a "skolem abundance" shift-closure constraint; 17 operators |

There are really **two families**: the state-mereology family (logos as trunk, with exclusion subclassing `LogosSemantics` and imposition reusing logos's proposition class, model structure, and extensional/modal operator classes verbatim), and bimodal, which shares only the abstract core and the operator machinery.

#### 5.2 The theory contract — verified

The `CLAUDE.md` claim that every theory follows one canonical structure (a `semantic/` **package**, plus `operators.py`, `iterate.py`, `examples.py`, `tests/`, `docs/`) is **true for all four theories** and is executable rather than aspirational: a 396-line parametrized conformance test asserts the required file set, the six-file docs set, the `examples.py` attribute set (via AST walk, because a plain `hasattr` cannot detect a duplicate assignment silently overwriting the first — which had actually happened), the `get_theory()` key set, and the `iterate.py` entry points. It passes 50/50 with every `xfail` dict now empty, guarded against silent re-admission.

Hard requirements: `get_theory(config=None) -> {semantics, proposition, model, operators}`; a `semantic/` package with re-export-only `__init__.py`, `core.py`, `model.py`; a semantics class with `DEFAULT_EXAMPLE_SETTINGS` (which must include `iterate`), `frame_constraints`, `premise_behavior`, `conclusion_behavior`, `main_point`, and the truth-condition dispatchers; a proposition class; a model-structure class supplying display and extraction; an operator collection; `examples.py` defining `example_range`, `test_example_range`, `semantic_theories`, `unit_tests` each exactly once; and `iterate.py` exposing an iterator class plus eager and generator entry points, the latter carrying a marker attribute the builder detects by `hasattr` — **silently degrading to the eager path when the marker is missing**.

The **layering rule** is the other executable contract: core (`models`, `syntactic`, `solver`, `utils`, `iterate`, `builder`, `settings`, `output`, `z3_shim`) may never import `theory_lib` — not via static import, function-local import, or `importlib` string literal — and may never hardcode a theory name; `theory_lib` may import core freely; only the upper layer (`__init__.py`, `api.py`, `__main__.py`, `jupyter/`) may know both. An AST-walking test enforces both rules with file:line violation reporting. The result: `theory_lib` imports core in ~90 places, core imports `theory_lib` in zero.

#### 5.3 The subtheory system (logos)

Logos organizes its operators into four subtheories — `extensional` (7 operators), `modal` (4), `constitutive` (5), `counterfactual` (2) — loaded through a registry with a hardcoded dependency graph (notably `modal` depends on `counterfactual`, because `\CFBox`/`\CFDiamond` are defined via `\boxright` with a `\top` antecedent). **Semantics is never defined in a subtheory**; it stays centralized in `logos/semantic/`. Subset loading is a first-class user feature: `logos.get_theory(subtheories=['extensional', 'modal'])` builds a fresh registry with those plus transitive dependencies, so differently-configured logos instances coexist. A subtheory contributing zero operators is defined to be a defect — the rule that retired the former `relevance` subtheory by folding it into `constitutive`.

#### 5.4 What an operator actually looks like

The three-register pattern is the most important thing for a port to internalize. Every logos-family primitive operator writes the *same truth condition* in up to three registers:

1. **`true_at` / `false_at` / `extended_verify` / `extended_falsify`** — the symbolic Z3 clause used while solving;
2. **`find_verifiers_and_falsifiers`** — a *concrete* Python computation against the found model, used post-solve;
3. **`print_method`** — a display routine that often re-derives the same structure a third time.

For the counterfactual operator, all three independently re-derive alternative worlds. This is the single largest source of drift risk in the theory library, and the highest-leverage structural change for a port: derive (2) from (1) where possible, and make (3) consume data rather than recompute semantics.

Post-solve extraction is also *named differently per evaluation scheme*: `find_verifiers_and_falsifiers` (logos family, bilateral), `compute_verifiers` (exclusion, unilateral), `find_truth_condition` (bimodal, temporal profiles). These are discovered at runtime by the proposition/printer layer. A port should make "evaluation scheme" an explicit abstraction rather than three unrelated method names.

#### 5.5 Examples as the executable specification

The examples corpus — **~253 example records across 8 modules** — is the de-facto behavioral spec, and the theory test suites parametrize directly over it:

| Module | `unit_tests` | `example_range` (curated) |
|---|---|---|
| logos aggregate | 16 | 16 |
| logos/extensional | 14 | 2 |
| logos/modal | 18 | 4 |
| logos/constitutive (incl. relevance) | 54 | 6 |
| logos/counterfactual | 37 | 4 |
| exclusion | 38 | 2 |
| imposition | 40 | 2 |
| bimodal | 52 | 22 |

**Important caveat for anyone treating this as the spec**: the logos *aggregate* `unit_tests` merges the subtheories' curated `example_range` subsets — 16 examples — not their full `unit_tests` (123 examples). Logos's real behavioral specification lives in the four subtheory example modules, exercised only by the subtheory test files.

### 6. Documentation reliability

The docs are extensive (92 markdown files, including a 12-file `docs/architecture/` set with ASCII pipeline diagrams and a 932-line `code/docs/core/ARCHITECTURE.md`) and often architecturally accurate at the conceptual level. But **30+ specific divergences were verified against source**. The most consequential, grouped:

**Wrong contracts (would not run if copied):**
- The syntactic README's operator example shows `true_at(self, world, sentence)` accessing `sentence.arguments[0]`; the real signature is `true_at(self, *arguments, eval_point)` with the *semantics*, not the operator, unpacking arguments.
- The same README shows `ModelConstraints(syntax, semantics)`; the real signature takes four arguments.
- Prefix lists are documented as flat with Unicode operators (`["∧", "p", "q"]`); the real form is nested with LaTeX names (`["\\wedge", ["p"], ["q"]]`), and Unicode operators are not resolvable at all.
- `models/README.md` calls `semantics.generate_constraints()` — no such method exists anywhere.

**Wrong units and inverted claims:**
- `ModelDefaults.solve`'s docstring says `max_time` is in milliseconds; it is seconds (the code multiplies by 1000).
- `ModelConstraints.instantiate`'s docstring says it "should only be called after a valid Z3 model has been found"; it is called from `__init__`, before any solving.
- `SemanticDefaults`'s docstring types `premise_behavior`/`conclusion_behavior` as `str`; they are callables.

**Documented features that do not exist:**
- `docs/usage/OUTPUT.md` documents a complete interactive save workflow for `--sequential`; the flag raises `NotImplementedError`, and the components were deliberately deleted and are "not being restored".
- `output/README.md` lists five modules and a whole notebook subsystem that do not exist on disk.
- `iterate/README.md` documents four settings (`max_iterations`, `timeout`, `use_isomorphism`, `debug`) that the code does not read, a summary dict with entirely different keys, and an API (`LogosIterator`, `BuildExample(semantics_module_name=…)`) that does not exist.
- `docs/architecture/ITERATE.md` documents `iteration_attempts` and `escape_attempts`; grep over all Python returns zero hits.
- The pipeline architecture doc uses a `max_models` setting; the live setting is `iterate` (`max_models` survives only in tests and a type stub).

**Stale self-descriptions:**
- `theory_lib/__init__.py`'s docstring lists only two of four theories and instructs extension authors to implement `semantic.py` — contradicting the `semantic/`-package contract its own conformance test enforces.
- The repository's top-level `TODO.md` is organized around a "critical path to v1.0" while the shipped version is 1.3.3.
- Two theory core docstrings misattribute their source papers relative to their own `CITATION.md` files.

**The reliable sources**, by contrast, are: `theory_lib/docs/THEORY_ARCHITECTURE.md` (written alongside its enforcing test and verified accurate), `specs/ROADMAP.md`'s Durable Decisions, `code/docs/core/ARCHITECTURE.md`'s concurrency section, and the four executable contracts (`test_layering.py`, `test_theory_conformance.py`, `test_docs_flag_matrix.py`, `code/tests/packaging/`).

## Decisions

- **The specification is written from source, with documentation used only as a hypothesis generator.** Every architectural claim in this report is grounded in a verified `file.py:LINE` citation recorded in the five `findings/` files.
- **Five territories, not four.** The user's four named areas were extended with `theory_lib` as a fifth — it is the largest package (35k LOC), it *is* the extensible DSL's content, and the four-area decomposition would otherwise have split it across the compiler and tools areas. (The repo's own `haskell/TODO.md` was independently updated during this research to add `theory-lib` to the same list.)
- **The report specifies observable behavior and data shapes, not implementation.** No Haskell design decisions are made or implied, per the task's explicit constraint.
- **Defects found during verification are reported as findings, not fixed.** Four live defects (iterator `range(N)`, `stored_solver`, disconnected theory constraint hooks, inverted `check_result`) are documented here; each warrants its own task against the Python implementation, independent of the port.
- **Dead code is called out explicitly** so the port does not reproduce scaffolding: the sequential-save subsystem, three duplicate iteration loops, the unused push/pop difference search, `iterate/base.py`, `iterate/build_example.py`, `iterate/types.py`'s protocol vocabulary, the unreachable interactive/prompt branch set, and the aspirational `theory_lib/types.py` protocol layer.

## Recommendations

Ordered by leverage for the porting specification.

1. **Write `haskell/py_spec.md` around the five-stage pipeline as the organizing spine** (§1, §2.1), with the four constraint groups and the countermodel framing stated as the central semantics. Everything else in the system is a satellite of that spine.
2. **Specify the semantic core as data, not classes.** A theory is: a signature (which primitives are Z3 functions vs derived definitions), frame constraints, an atomic-proposition constraint menu, premise/conclusion behaviors, an evaluation-point shape, and a set of named/arity-tagged operator clauses. The bit-vector encoding table (§1.6) and the operator method table (§1.3) are the two most reusable artifacts in this report.
3. **State the four lifecycle phases as four types.** The single deepest structural problem in the Python implementation is that one mutable `Sentence` carries phase-dependent field *types*; naming the phases (parsed / operator-resolved / semantics-bound / interpreted) in the spec makes the port's separation obvious without prescribing a design.
4. **Specify a typed result value and a pure renderer boundary.** Replace "solve inside the constructor, then print to stdout, then recapture stdout and regex ANSI to markdown" with `Constraints → Result (SAT model | UnsatCore [Label] | Timeout) → Renderer`. The existing model-data collector schema (§3.2) is a workable starting shape for the data half.
5. **Specify the three-register operator problem explicitly** (§5.4) and mark deriving concrete evaluation from the symbolic clause as an intended improvement. This is the highest-leverage change identified anywhere in the codebase.
6. **Carry the enforced invariants forward as spec obligations, not just observations**: one-way core/theory dependency; a registry as the sole source of theory identity with no theory-name literals in core; one canonical theory module set; single-threaded (or per-run-context) model construction; per-example solver isolation.
7. **Specify the example-file format declaratively** (name, premises, conclusions, settings, expectation, tags), noting that the Python implementation achieves this by executing arbitrary Python modules and that the resulting format is unspecifiable. Include the `PREFIX_CM_n` / `PREFIX_TH_n` convention and the `expectation` oracle bit, since those *are* the behavioral specification.
8. **Record the settings model with its precedence chain** (§2.5) and mark two intended changes: strictness by default (the project's own fail-fast principle, currently opt-in and never enabled in production), and typed settings (`iterate : Nat >= 1`, `max_time` in seconds with units in the type).
9. **Include the iteration algorithm's two-tier notion of distinctness** (§3.1) and note that the theory-declarative half — a list of "model dimensions" per theory — is the shape the four copy-adapted iterators are all approximating.
10. **Include the divergence inventory as a standing warning** in the spec: any future reader consulting `docs/architecture/` should be told which claims were verified false. Alternatively, file follow-up tasks to correct the specific stale documents identified in §6.
11. **File separate tasks for the four live defects** — they are defects in the Python implementation and should not wait on the port.

## Risks & Mitigations

- **Risk: the spec drifts from the implementation the moment it is written.** The Python system's own documentation demonstrates this failure mode at scale (§6). *Mitigation*: ground the spec in the four executable contracts rather than prose, and cite file paths for anything a future reader might need to re-verify.
- **Risk: the spec over-specifies incidental Python behavior.** Much of what the codebase does (monkey-patched `verify`/`falsify` for iteration, `sys.path` mutation, ANSI recapture, `hasattr` capability detection, the concurrency guard) is a workaround for Python-specific constraints, not semantics. *Mitigation*: this report separates *semantics that must be preserved* (finite quantifier expansion, unknown-as-timeout, the countermodel framing, the bit-vector encoding, the atomic-proposition constraint menu) from *mechanism that should not be reproduced* (each Improvement Opportunity section in the findings files).
- **Risk: the exponential encoding is mistaken for an implementation detail.** Finite quantifier expansion produces `(2^N)^k`-leaf formulas and is the reason `MAX_N = 20` exists with measured memory figures. *Mitigation*: the spec must state this as a *semantic* choice with its cost model, not as an optimization to be revisited casually.
- **Risk: bimodal is treated as a variation on logos.** It is a different model theory (world histories, no verifiers, integer times, Lean-aligned frame axioms) and constitutes 12.8k LOC. *Mitigation*: the spec must make "evaluation scheme" a first-class axis with at least three inhabitants (bilateral verifier/falsifier, unilateral verifier, bivalent temporal profile).
- **Risk: the logos example-coverage gap is inherited.** The aggregate `unit_tests` covers 16 of 123 subtheory examples (§5.5). *Mitigation*: the spec should name the full 123-example corpus as the behavioral reference, not the aggregator.

## Context Extension Recommendations

- **Topic**: ModelChecker semantic-framework architecture as durable project context
- **Gap**: The repository has no single accurate, source-verified architectural reference. `docs/architecture/` is conceptually useful but contains verified-false API claims; `code/docs/core/ARCHITECTURE.md` mixes accurate contracts (concurrency) with generic advisory patterns; the accurate contracts are distributed across three test files and `THEORY_ARCHITECTURE.md`.
- **Recommendation**: Once `haskell/py_spec.md` is written, consider promoting its architecture-of-record sections (the five-stage pipeline, the four constraint groups, the encoding table, the theory contract, the layering rule) into `.claude/context/repo/` or a single canonical `docs/architecture/OVERVIEW.md` that supersedes the stale per-module claims, with a note directing readers to the executable contracts for authority.

## Appendix

### A. Territory findings files

| File | Territory | Lines |
|---|---|---|
| `findings/01_compiler-pipeline.md` | `syntactic/`, `solver/`, `z3_shim.py`, constraint-generation half of `models/` | 821 |
| `findings/02_core-utilities.md` | `models/`, `utils/`, `settings/`, `registry.py`, `api.py`, `__init__.py` | 667 |
| `findings/03_tools-features.md` | `iterate/`, `output/` | 670 |
| `findings/04_ui-cli.md` | `builder/`, `__main__.py`, `jupyter/`, `dev_cli.py`, packaging | 614 |
| `findings/05_theory-lib.md` | `theory_lib/` (all four theories, subtheories, contract), `oracle/` | 986 |

Each contains full `file.py:LINE` grounding, verbatim code excerpts for the shapes that matter, a `Doc/Source Divergences` section, and an `Improvement Opportunities` section.

### B. Executable contracts (authoritative over documentation)

- `code/tests/test_layering.py` — three-layer dependency direction; forbids core→`theory_lib` imports (static, function-local, and `importlib` string literals) and hardcoded theory-name literals in core + upper layers.
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` — parametrized over the registry; required file set, docs set, `examples.py` attributes (AST-walked for duplicate assignment), `get_theory()` keys, `iterate.py` entry points. 50 passed, zero `xfail`.
- `code/tests/cli/test_docs_flag_matrix.py` — scans fenced shell blocks in all docs and asserts every flag token exists on the real parser (derived from `parser._actions`).
- `code/tests/packaging/` — builds real wheels and sdists; asserts inclusions, exclusions, wheel/sdist parity, entry points, console-script execution, generate-then-execute round trips.

### C. Measurements taken during this research

- Production source: 353 Python modules, ~46k LOC across 11 packages (`theory_lib` 23.6k excluding tests, `builder` 5.3k, `jupyter` 4.3k, `iterate` 4.0k, `solver` 2.1k, `models` 2.1k, `output` 1.9k, `syntactic` 1.6k, `utils` 1.0k, `settings` 0.8k).
- Tests: 174 test files, ~40.7k LOC.
- `theory_lib` including tests: 35,036 LOC (bimodal 12,844; logos 10,235; exclusion 5,434; imposition 4,476).
- Operators per theory: logos 18 (all subtheories loaded), bimodal 17, imposition 13, exclusion 4.
- Examples: ~253 records across 8 modules.
- Dependencies: `z3-solver>=4.8.0`, `networkx>=2.0`; Python `>=3.10`; version 1.3.3.

### D. References

- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` — the theory contract and layering rule (verified accurate)
- `specs/ROADMAP.md` — Durable Decisions: package identity, the enforced three-layer model, the rejected `theory_lib` extraction and its revisit trigger
- `code/docs/core/ARCHITECTURE.md` §"Concurrency Model" — the single-threaded construction contract (verified accurate)
- `docs/architecture/PIPELINE.md` — conceptually accurate five-stage flow; specific settings names are stale
- `docs/theory/HYPERINTENSIONAL.md`, `docs/theory/REFERENCES.md` — semantic background and provenance
