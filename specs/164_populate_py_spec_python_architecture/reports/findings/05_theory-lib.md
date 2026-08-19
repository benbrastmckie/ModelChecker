# Theory Library (`theory_lib/`) — Architectural Findings

Scope: `code/src/model_checker/theory_lib/` (all four theories, the theory contract, the
subtheory system) plus a brief account of the top-level `oracle/` tree. All paths below are
relative to `code/src/model_checker/theory_lib/` unless stated otherwise. Line numbers were
verified against the working tree on 2026-08-18.

Size: `theory_lib` totals 35,036 Python LOC including per-theory tests
(`wc -l` over all `*.py`). Per theory (sources + tests): logos 10,235; exclusion 5,434;
imposition 4,476; bimodal 12,844; shared top-level modules (`__init__.py` 489, `meta_data.py`
452, `errors.py` 238, `types.py` 133) plus `docs/` and `tests/`.

---

## Q1. Theory Inventory

Four theories are registered. The single authoritative enumeration of theory names is
`_THEORY_NAMES` in `theory_lib/__init__.py:63-70` ("the ONE place theory names are enumerated
as literals"); the core layer's registry is populated from it and core code is forbidden from
naming theories (see Layering, Q2). `AVAILABLE_THEORIES` is a view over the core registry
(`tests/test_theory_conformance.py:28`: `registry.get_registered()`).

### logos — hyperintensional truthmaker semantics (flagship, modular)

- **Semantics**: Bilateral truthmaker ("hyperintensional") semantics in the Kit Fine /
  Brast-McKie tradition. Models are built over a state space of bit-vectors of width `N`;
  states are ordered by parthood (bitwise, via `is_part_of` from `SemanticDefaults`), fused by
  bitwise OR, and classified by a primitive Z3 predicate `possible`. A *world* is a maximal
  possible state (`semantic/core.py:129-137`). Atomic sentences get primitive *verifier* and
  *falsifier* relations (`verify`, `falsify` Z3 functions, `semantic/core.py:63-80`); truth at
  a world is existence of a verifying part of that world (`semantic/core.py:140-178`).
  Counterfactuals use "alternative worlds" defined via maximal compatible parts
  (`semantic/core.py:288-349`).
- **Provenance**: Benjamin Brast-McKie's semantics (papers cited in `logos/CITATION.md`);
  identity/ground/essence operators from Brast-McKie's "Identity and Aboutness";
  counterfactuals from Brast-McKie's counterfactual worlds work; the constitutive subtheory
  carries its own `CITATION.md`.
- **Layout**: `__init__.py`, `semantic/` (`core.py` 512, `model.py` 419, `proposition.py`
  377, re-export `__init__.py` 21), `operators.py` (218 — a *registry*, not operator
  definitions), `protocols.py` (415, `typing.Protocol` interfaces), `iterate.py` (470),
  `examples.py` (208 — an *aggregator*), `subtheories/` with `extensional/`, `modal/`,
  `constitutive/`, `counterfactual/`, plus `tests/`, `docs/` (6-file set), `README.md`,
  `CITATION.md`, `LICENSE.md`. Canonical-structure claim: **conforms** (semantic/ package
  present; all required files present).
- 18 operators when all subtheories are loaded (verified by instantiating
  `get_theory()`): `\neg \wedge \vee \top \bot \rightarrow \leftrightarrow \Box \Diamond
  \CFBox \CFDiamond \boxright \diamondright \Rightarrow \equiv \leq \sqsubseteq \preceq`.

### exclusion — unilateral witness-predicate semantics

- **Semantics**: Champollion & Bernard's *unilateral* truthmaker semantics: atomic sentences
  have only verifiers (no falsifiers), and negation is defined via a primitive binary
  `excludes` relation between states plus per-formula *witness functions*. A state verifies
  ¬φ iff (1) for every verifier v of φ there are witness values h(v), y(v) with y(v) ⊑ v and
  h(v) excludes y(v), (2) each h(v) is part of the state, and (3) the state is minimal with
  that property (`exclusion/operators.py:20-130`). The `possible` predicate is *derived*, not
  primitive: a state is possible iff it coheres with itself, where coherence is absence of
  parts that exclude each other (`semantic/core.py:150-170`); `is_world` is redefined as
  possible + no proper possible extension (`semantic/core.py:183-204`). Witness functions are
  first-class Z3 functions `{formula}_h`, `{formula}_y` created per negated subformula by a
  `WitnessRegistry` (`semantic/registry.py:19-90`) and constrained by a
  `WitnessConstraintGenerator` (`semantic/constraints.py:20,30`), making the (inherently
  higher-order) minimality-based negation semantics expressible in first-order Z3 by naming
  the Skolem functions up front.
- **Provenance**: Kit Fine's unilateral truthmaker content semantics as revised by Champollion
  & Bernard, "Negation and Modality in Unilateral Truthmaker Semantics" (L&P 2024)
  (`exclusion/CITATION.md:20-45`); implementation by Miguel Buitrago and Benjamin Brast-McKie.
- **Layout**: `semantic/` = `core.py` 572, `model.py` 556, `proposition.py` 103,
  `constraints.py` 175, `registry.py` 126, re-export `__init__.py` 30; `operators.py` 395;
  `iterate.py` 305; `examples.py` 1061; `notebooks/` (optional extra); full `tests/`,
  `docs/` (6-file set + extra `DATA.md`). **Conforms** to the canonical structure.
- 4 operators: `\neg \wedge \vee \equiv` (`UniNegation`, `UniConjunction`, `UniDisjunction`,
  `UniIdentity`, `operators.py:20,247,291,325`).
- `WitnessSemantics` **subclasses `LogosSemantics`** (`semantic/core.py:34`), inheriting
  fusion/parthood and the constraint pipeline but overriding `possible`, `is_world`, and
  the whole verification story.

### imposition — Kit Fine's imposition counterfactuals

- **Semantics**: Fine's counterfactual semantics from "Counterfactuals without Possible
  Worlds" (J.Phil 2012) and "A Difficulty for the Possible Worlds Analysis of
  Counterfactuals". Adds a primitive ternary Z3 relation `imposition(state, world, outcome)`
  (`semantic/core.py:131-138`) constrained by Fine's four frame conditions — *inclusion*,
  *actuality*, *incorporation*, *completeness* (`semantic/core.py:140-192`). `A \boxright B`
  is true at w iff for every verifier x of A and every outcome world u with
  `imposition(x, w, u)`, B is true at u (`imposition/operators.py:24-160`). A
  `derive_imposition` setting switches the frame constraints to *derived* analogs computed
  from logos's defined `is_alternative`, to test whether Fine's primitive relation is entailed
  by the logos definition (`semantic/core.py:194-209,255-321`) — the theory is explicitly
  built for head-to-head comparison with logos's counterfactual.
- **Provenance**: Kit Fine (semantics); implementation Benjamin Brast-McKie
  (`imposition/CITATION.md`).
- **Layout**: `semantic/` = `core.py`, `model.py`, `helpers.py` (display/format helpers),
  re-export `__init__.py` — **no `proposition.py`**: imposition reuses `LogosProposition`
  wholesale (`imposition/__init__.py:53`: `from
  model_checker.theory_lib.logos.semantic import LogosProposition as Proposition`).
  `operators.py` 395-ish lines defines 4 native operators and *imports* logos's extensional
  + modal operators to assemble its collection (`operators.py:222-243`). **Conforms** to the
  canonical structure (contract requires `core.py` and `model.py`; `proposition.py` is not
  named as required by `docs/THEORY_ARCHITECTURE.md`).
- 13 operators exposed, incl. both Fine-style and logos-style counterfactuals for in-model
  comparison: `\boxright \diamondright \boxrightlogos \diamondrightlogos`
  (`operators.py:213-219`).

### bimodal — temporal + modal logic over world histories

- **Semantics**: Genuinely different model theory (see Q6). Worlds are not states: a model
  has instantaneous *world states* (bit-vectors of width `N`), and *world histories* — arrays
  from integer times to world states (`z3.ArraySort(TimeSort, WorldStateSort)`), indexed by
  integer world IDs via `world_function` (`bimodal/semantic/core.py:194-198`). Evaluation
  points are (world-id, time) pairs. A ternary task relation `task_rel(source, duration,
  target)` (`semantic/core.py:185-192`) constrains lawful evolution; truth of atoms is a
  binary `truth_condition(world_state, atom)` — *no verifiers/falsifiers at all*. Modal
  operators quantify over all valid world histories at a fixed time; temporal operators
  shift the time within a history. Modal accessibility uses witness predicates (a single
  `accessible_world` predicate per formula — `semantic/witness_registry.py:29-49`,
  distinct from exclusion's dual h/y).
- **Provenance**: Brast-McKie's bimodal logic ("JPL paper" per code comments), co-developed
  with a Lean 4 ProofChecker: the code repeatedly cites `Frame.lean` and aligns Z3
  primitives with the Lean formalization (`semantic/core.py:8-18,180-192`;
  `operators.py:482-560` "Paper/Lean-aligned semantics").
- **Layout**: `semantic/` = `core.py` **2,194 lines**, `model.py` 833, `proposition.py` 325,
  `witness_registry.py` 185, `witness_constraints.py` 186, re-export `__init__.py`;
  `operators.py` **1,777 lines**; `iterate.py` 564; `examples.py` 1,482. **Conforms** to the
  canonical structure.
- 17 operators: primitives `\neg \wedge \vee \bot \Box \Future \Past \Until \Since`; defined
  `\rightarrow \leftrightarrow \top \Diamond \future \past \next \prev`
  (`operators.py:166-1734`).

**Canonical-structure verification (H4)**: The CLAUDE.md claim ("one canonical structure: a
`semantic/` package …") is **true for all four theories** and is *executable*, not just
documented: `tests/test_theory_conformance.py` (396 lines) parametrizes the required file
set, docs six-file set, `examples.py` attribute set, `get_theory()` contract, and `iterate.py`
entry points over the registry. All previously-tracked gaps have been fixed — every
`*_XFAIL_REASON` dict is now empty (`test_theory_conformance.py:83-108`) — and the suite
passes: **50 passed in 0.66s** (run during this research with `PYTHONPATH=code/src`).

---

## Q2. The Theory Contract

Normative source: `docs/THEORY_ARCHITECTURE.md` (113 lines), encoded executably in
`tests/test_theory_conformance.py`. Requirements, with hard/soft classification:

### Hard requirements (crash or wrong results without)

1. **`__init__.py` exposing `get_theory(config=None)`** returning a dict with exactly the keys
   `{'semantics', 'proposition', 'model', 'operators'}`
   (`docs/THEORY_ARCHITECTURE.md:17-19`; `test_theory_conformance.py:64`
   `REQUIRED_GET_THEORY_KEYS`). Verified in logos (`logos/__init__.py:31-73` — logos
   additionally accepts keyword-only `subtheories=`) and imposition
   (`imposition/__init__.py:80-110`). The values are *classes* (semantics, proposition, model)
   and an `OperatorCollection` instance (operators). This dict is what the builder consumes;
   a missing key breaks example construction.
2. **`semantic/` as a package** with re-export-only `__init__.py`, `core.py` (the
   `SemanticDefaults` subclass) and `model.py` (the `ModelDefaults` subclass)
   (`docs/THEORY_ARCHITECTURE.md:20-28`).
3. **Semantics class obligations** (consumed by core's `ModelConstraints` and the builder;
   defined by inheritance from `models/semantic.py:SemanticDefaults`):
   - `DEFAULT_EXAMPLE_SETTINGS` class attr, which **must include an `'iterate'` key** (this is
     why `iterate.py` is mandatory — `docs/THEORY_ARCHITECTURE.md:33-36`). Each theory's
     defaults differ: logos `{'N': 16, 'M': None, contingent/non_empty/non_null/disjoint:
     True, 'max_time': 10, ...}` (`logos/semantic/core.py:39-51`); exclusion `N=3` with all
     constraint toggles False (`exclusion/semantic/core.py:93-104`); imposition `N=3`
     (`imposition/semantic/core.py:95-104`); bimodal `{'N': 2, 'M': 2, ...}`
     (`bimodal/semantic/core.py:47-66`).
   - Optional `ADDITIONAL_GENERAL_SETTINGS` (imposition's `derive_imposition`,
     `imposition/semantic/core.py:106-109`; bimodal's `align_vertically`,
     `bimodal/semantic/core.py:67-70`).
   - Instance attrs set in `__init__`: `frame_constraints` (list of Z3 BoolRefs),
     `premise_behavior(premise)` and `conclusion_behavior(conclusion)` (callables returning
     Z3 constraints — the invalidity encoding: premises true, conclusions false at
     `main_point`; `logos/semantic/core.py:101-108`), `main_point` (an *evaluation point*
     dict — `{"world": BitVec}` for the state theories,
     `{"world": world_id, "time": IntVal}` for bimodal, `bimodal/semantic/core.py:236-242`).
   - `true_at(sentence, eval_point)` / `false_at(...)` dispatching on
     `sentence.sentence_letter` vs `sentence.operator` (`logos/semantic/core.py:140-211`).
     Hyperintensional theories additionally provide `extended_verify` / `extended_falsify`
     (`logos/semantic/core.py:212-287`).
4. **Proposition class** subclassing `PropositionDefaults` with `proposition_constraints
   (sentence_letter)` (settings-gated Z3 constraints per atom — see Q3),
   `find_proposition()`/`find_extension()` (extract the proposition's extension from a found
   Z3 model), `truth_value_at(eval_point)`, and `print_proposition(...)`
   (`logos/semantic/proposition.py:21-377`; `exclusion/semantic/proposition.py:14-103`;
   `bimodal/semantic/proposition.py:18-325`).
5. **Model-structure class** subclassing `ModelDefaults`, providing display (`print_all`,
   `print_to`, `print_evaluation`, `print_states`) and JSON-ish extraction (`extract_states`,
   `extract_evaluation_world`, `extract_relations`, `extract_propositions` —
   `logos/semantic/model.py:118-419`), plus `print_model_differences` for iteration output.
6. **`operators.py`** yielding an `OperatorCollection` of `syntactic.Operator` /
   `syntactic.DefinedOperator` subclasses, each with class attrs `name` (LaTeX-style token,
   e.g. `"\\boxright"`) and `arity`, and the semantic methods the theory's evaluation scheme
   needs (see Q4).
7. **`examples.py`** defining, *each exactly once* (the conformance test walks the AST to
   detect duplicate top-level assignment, `test_theory_conformance.py:126-135`):
   `example_range`, `test_example_range`, `semantic_theories`, `unit_tests`
   (`docs/THEORY_ARCHITECTURE.md:56-68`).
8. **`iterate.py`** exposing `{Theory}ModelIterator`, `iterate_example`, and
   `iterate_example_generator`, the latter carrying the marker
   `iterate_example_generator.__wrapped__.returns_generator == True` — the builder detects
   the generator interface via `hasattr(fn, '__wrapped__')`; without the marker it *silently*
   falls back to eager iteration (`docs/THEORY_ARCHITECTURE.md:31-43`). Presence of the module
   is hard (reachable `ImportError` when a user sets `iterate: 2`); the marker is
   soft-degrading.

### Soft requirements (degraded features, not crashes)

- **`docs/`** six-file set (`README.md`, `API_REFERENCE.md`, `ARCHITECTURE.md`, `ITERATE.md`,
  `SETTINGS.md`, `USER_GUIDE.md`) and `README.md`/`CITATION.md`/`LICENSE.md` — enforced by
  the conformance test but not by the runtime. Verified present in all four theories
  (exclusion adds a 7th, `DATA.md`).
- **`notebooks/`** — explicitly optional, "reported but not enforced"
  (`docs/THEORY_ARCHITECTURE.md:71-74`); present in exclusion and imposition only.
- **`__version__`** in theory `__init__.py` — single source of truth for
  `get_theory_version()` / `check_theory_compatibility()` (`meta_data.py:30-90`); absence
  degrades to `"unknown"`.
- **Translation dictionaries**: a `semantic_theories` entry may carry a 5th key
  `"dictionary"` mapping this theory's operator tokens to another theory's for cross-theory
  comparison runs (`exclusion/examples.py:974-996`: `exclusion_to_logos`); optional, empty
  dicts allowed.

### Layering rule

`docs/THEORY_ARCHITECTURE.md:96-113`: three layers with one-way dependencies — core
(`models`, `syntactic`, `solver`, `iterate`, `builder`, …) must never import `theory_lib`
nor hardcode a theory name; `theory_lib` imports core freely; only the upper layer
(`model_checker/__init__.py`, `api.py`, `jupyter/`) may know both. Enforced by
`code/tests/test_layering.py`. Theory identity flows through the core `registry`, which
`theory_lib/__init__.py` populates at import time from `_THEORY_NAMES`.

### Subtheory contract (logos only)

Each `logos/subtheories/<name>/` must provide `__init__.py`, `operators.py` (whose
`get_operators()` must return a **non-empty** dict — a zero-operator subtheory is defined to
be a defect), `examples.py`, `tests/`, `README.md` (`docs/THEORY_ARCHITECTURE.md:79-90`).
Semantics is *never* defined in a subtheory — it stays centralized in `logos/semantic/`.

---

## Q3. Logos In Depth

### State space and model primitives

- `N` (default 16, `semantic/core.py:40`) fixes the bit-vector width; states are
  `BitVec(N)` values, so the state space is the powerset lattice of `N` atoms with parthood =
  bitmask inclusion and fusion = bitwise OR (inherited from `SemanticDefaults`; used e.g. at
  `semantic/core.py:376-394` where fusion is literally `bit_a | bit_b`).
- Z3 primitives (`semantic/core.py:62-80`): `verify : BitVec(N) × AtomSort → Bool`,
  `falsify : BitVec(N) × AtomSort → Bool`, `possible : BitVec(N) → Bool`.
- Derived notions: `compatible(x,y) := possible(fusion(x,y))` (`core.py:117-119`);
  `maximal(w)` (`core.py:121-127`); `is_world(w) := possible(w) ∧ maximal(w)`
  (`core.py:129-137`); `max_compatible_part(x,w,y)` (`core.py:288-319`);
  `is_alternative(u,y,w)` — u is a world containing y and a maximal part of w compatible
  with y (`core.py:321-349`) — the engine of the counterfactual semantics.
- Frame constraints: just two — downward closure of possibility under parthood, and
  `is_world(main_world)` (`core.py:88-105`).
- Evaluation points are dicts (`main_point = {"world": main_world}`, `core.py:83-86`);
  `with_world(eval_point, w)` copies the point with the world replaced (`core.py:493-511`) —
  the mechanism intensional operators use to shift worlds while preserving other keys.

### Verifier/falsifier propositions and settings-gated constraints

`LogosProposition.proposition_constraints(sentence_letter)`
(`semantic/proposition.py:43-190`) always emits four *classical* closure constraints per
atom — verifier-fusion closure, falsifier-fusion closure, no-glut (no verifier compatible
with a falsifier), no-gap (every possible state compatible with a verifier or falsifier) —
then conditionally adds, per settings: `contingent` (a possible verifier and possible
falsifier exist), `non_empty` (only when not `contingent`), `disjoint` (verify/falsify
disjointness plus non-null), `non_null` (null state verifies/falsifies nothing; only when
not `disjoint`). This settings-conditional constraint menu *is* the per-theory notion of an
"atomic proposition" and is the most re-implemented piece of code across theories (Q5).

### The subtheory system

- Registry of names: `subtheories/__init__.py:19-31` — `AVAILABLE_SUBTHEORIES =
  ['extensional', 'modal', 'constitutive', 'counterfactual']` with description strings.
- Loader: `LogosOperatorRegistry` (`logos/operators.py:23-218`). Holds
  `loaded_subtheories: dict[name, module]`, an `OperatorCollection`, and a hardcoded
  dependency graph `{'modal': ['extensional', 'counterfactual'], 'counterfactual':
  ['extensional'], 'constitutive': [], 'extensional': []}` (`operators.py:33-38`) — note
  modal depends on *counterfactual* (its `CFBox`/`CFDiamond` are defined via `\boxright`
  with a `\top` antecedent, `modal/operators.py:125-230`). `load_subtheory(name)`
  (`operators.py:40-77`) loads dependencies recursively, imports
  `.subtheories.<name>`, calls the module's `get_operators()`, and adds each operator class
  to the collection; idempotent per registry instance. Utilities: conflict detection
  (`validate_operator_compatibility`, `operators.py:186-210`), per-subtheory operator
  listing, unload/reload.
- **Subset loading is a first-class user feature**: `logos.get_theory(subtheories=
  ['extensional', 'modal'])` (`logos/__init__.py:31-73`) builds a registry with only those
  subtheories (plus transitive dependencies); default loads all four. Each call creates a
  fresh registry, so differently-configured logos instances can coexist.
- The former **relevance** subtheory no longer exists as a directory: it contributed zero
  operators and was folded into constitutive (`RelevanceOperator` at
  `constitutive/operators.py:376`; REL_* examples pass through the constitutive example
  module — `logos/examples.py:13-16,124-127`; rationale codified as the non-empty
  `get_operators()` rule in `docs/THEORY_ARCHITECTURE.md:82-86`, and constitutive carries a
  `RELEVANCE.md`).
- Subtheory contents: extensional 7 operators (5 primitive, 2 defined;
  `extensional/operators.py`); modal 4 (1 primitive `\Box`, 3 defined;
  `modal/operators.py`); constitutive 5 (`\equiv` identity, `\leq` ground, `\sqsubseteq`
  essence, `\preceq` relevance primitive, `\Rightarrow` reduction defined;
  `constitutive/operators.py:33-554`); counterfactual 2 (`\boxright` primitive,
  `\diamondright` defined; `counterfactual/operators.py:30-302`).
- `examples.py` per subtheory follows the same standard shape as a theory's (Q8), and each
  subtheory has its own `tests/` parametrizing over its full `unit_tests`
  (`subtheories/modal/tests/test_modal_examples.py:26-29`).
- `protocols.py` defines `typing.Protocol` interfaces for the whole plumbing —
  `SubtheoryProtocol`, `OperatorProtocol`, `SemanticsProtocol`, `RegistryProtocol`,
  `PropositionProtocol`, `ModelIteratorProtocol` (`logos/protocols.py:34-383`) — the closest
  thing in the codebase to a typed statement of the theory contract, used only under
  `TYPE_CHECKING`.

---

## Q4. Operator Implementations (verbatim, increasing complexity)

An operator is a class with `name`, `arity`, and a set of semantic methods. Two kinds exist:
`syntactic.Operator` (primitive — supplies its own semantic clauses) and
`syntactic.DefinedOperator` (supplies only `derived_definition`, which returns a nested
prefix-list of other operator classes; e.g. `\Diamond`:
`return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]`,
`modal/operators.py:110-113`). For logos-family theories the primitive-operator method set is:
`true_at`, `false_at` (intensional truth conditions → Z3 constraints), `extended_verify`,
`extended_falsify` (which *state* verifies/falsifies the compound → Z3 constraints),
`find_verifiers_and_falsifiers` (post-solve: compute the concrete proposition from the found
model), and `print_method` (display dispatch).

### 4.1 Negation (simplest: pure delegation with V/F swap) — `logos/subtheories/extensional/operators.py:28-64`

```python
class NegationOperator(syntactic.Operator):
    semantics: "LogosSemantics"
    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        return self.semantics.true_at(argument, eval_point)

    def extended_verify(self, state, argument, eval_point):
        return self.semantics.extended_falsify(state, argument, eval_point)

    def extended_falsify(self, state, argument, eval_point):
        return self.semantics.extended_verify(state, argument, eval_point)

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        arg_V, arg_F = argument.proposition.find_proposition()
        return arg_F, arg_V

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)
```

### 4.2 Conjunction (fusion-based verifiers) — `extensional/operators.py:67-138`

```python
class AndOperator(syntactic.Operator):
    semantics: "LogosSemantics"
    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        return z3.And(
            self.semantics.true_at(leftarg, eval_point),
            self.semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        return z3.Or(
            self.semantics.false_at(leftarg, eval_point),
            self.semantics.false_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("and_verify_x", N)
        y = z3.BitVec("and_verify_y", N)
        return Exists(
            [x, y],
            cast(z3.BoolRef, z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.extended_verify(y, rightarg, eval_point),
                state == sem.fusion(x, y)
            ))
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("and_falsify_x", N)
        y = z3.BitVec("and_falsify_y", N)
        return z3.Or(
            sem.extended_falsify(state, leftarg, eval_point),
            sem.extended_falsify(state, rightarg, eval_point),
            Exists(
                [x, y],
                cast(z3.BoolRef, z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    state == sem.fusion(x, y)
                ))
            )
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        left_V, left_F = left_sent_obj.proposition.find_proposition()
        right_V, right_F = right_sent_obj.proposition.find_proposition()
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        return product(left_V, right_V), coproduct(left_F, right_F)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)
```

Note the two layers: `extended_verify` builds a *symbolic* constraint (existential over
fusion decompositions) used while solving; `find_verifiers_and_falsifiers` computes the
*concrete* verifier set (Python-level `product` of the argument sets,
`semantic/core.py:376-394`) after a model is found.

### 4.3 Necessity (world quantification + null-state verifier) — `modal/operators.py:33-98`

```python
class NecessityOperator(syntactic.Operator):
    semantics: "LogosSemantics"
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return ForAll(
            u,
            z3.Implies(
                sem.is_world(u),
                sem.true_at(argument, sem.with_world(eval_point, u)),
            ),
        )

    def false_at(self, argument, eval_point):
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return Exists(
            u,
            cast(z3.BoolRef, z3.And(
                sem.is_world(u),
                sem.false_at(argument, sem.with_world(eval_point, u)),
            )),
        )

    def extended_verify(self, state, argument, eval_point):
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(argument, eval_point)
        )

    def extended_falsify(self, state, argument, eval_point):
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(argument, eval_point)
        )

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        evaluate = argument.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(argument, eval_point))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(argument, eval_point))):
            return set(), {self.semantics.null_state}
        raise ValueError(
            f"{self.name} {argument} "
            f"is neither true nor false in the world {eval_point}.")

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        all_worlds = sentence_obj.proposition.model_structure.z3_world_states
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)
```

The hyperintensional treatment of modality: a necessity claim, when true, is verified by the
*null state* only (world-insensitive content). `print_method` switches to a different display
routine (`print_over_worlds`) — display is part of the operator contract.

### 4.4 Counterfactual (alternative-world semantics; symbolic + concrete + display all diverge) — `counterfactual/operators.py:30-180`

```python
class CounterfactualOperator(syntactic.Operator):
    semantics: "LogosSemantics"
    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_cf_x", N)
        u = z3.BitVec("t_cf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.is_alternative(u, x, eval_point["world"])
                ),
                semantics.true_at(rightarg, semantics.with_world(eval_point, u)),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("f_cf_x", N)
        u = z3.BitVec("f_cf_u", N)
        return Exists(
            [x, u],
            cast(z3.BoolRef, z3.And(
                semantics.extended_verify(x, leftarg, eval_point),
                semantics.is_alternative(u, x, eval_point["world"]),
                semantics.false_at(rightarg, semantics.with_world(eval_point, u)))),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        world = eval_point["world"]
        return z3.And(state == world,
                      self.true_at(leftarg, rightarg, eval_point))

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        world = eval_point["world"]
        return z3.And(state == world,
                      self.false_at(leftarg, rightarg, eval_point))

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        model = leftarg.proposition.model_structure
        semantics = self.semantics
        z3_model = model.z3_model
        verifiers = set()
        falsifiers = set()
        leftarg_verifiers = leftarg.proposition.verifiers
        for world in model.z3_world_states:
            alternative_found = False
            all_alternatives_satisfy_B = True
            for x_state in leftarg_verifiers:
                for alt_world in model.z3_world_states:
                    if z3_model.evaluate(semantics.is_alternative(alt_world, x_state, world)):
                        alternative_found = True
                        B_truth = rightarg.proposition.truth_value_at(alt_world)
                        if B_truth is False:
                            all_alternatives_satisfy_B = False
                            break
                if not all_alternatives_satisfy_B:
                    break
            if not alternative_found:
                verifiers.add(world)          # vacuously true
            elif all_alternatives_satisfy_B:
                verifiers.add(world)
            else:
                falsifiers.add(world)
        return verifiers, falsifiers

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        semantics = self.semantics
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_verifiers = left_argument_obj.proposition.verifiers
        N = semantics.N
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        alt_worlds = set()
        for state in left_verifiers:
            for world in world_states:
                if eval(semantics.is_alternative(world, state, eval_world)):
                    alt_worlds.add(world)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)
```

### Variant method sets in other theories

- **Exclusion** operators implement `true_at`, `extended_verify`, and **`compute_verifiers`**
  (no `false_at`, no `extended_falsify`, no `find_verifiers_and_falsifiers`) — unilateral
  propositions have only verifiers. `UniNegationOperator.compute_verifiers` enumerates all
  `2**N` states and checks the three witness conditions plus minimality against the model's
  witness functions via `model.get_h_witness` / `get_y_witness`
  (`exclusion/operators.py:41-130`; `exclusion/semantic/model.py:57-96`). Exclusion also
  gensyms bound variables with a counter (`z3.BitVec(f"ver_{counter}")`,
  `operators.py:30-32`) where logos uses fixed names.
- **Bimodal** operators implement `true_at`, `false_at`, **`find_truth_condition`** (returns
  temporal truth *profiles* per world rather than verifier sets), and `print_method`; bound
  variables are gensym'd via `_fresh_bound_int()` with a process-global counter to avoid Z3's
  `(name, sort)` interning aliasing nested quantifiers (`bimodal/operators.py:507-560` and
  the long comment there; counter reset hook at `bimodal/semantic/core.py:117-125`).

---

## Q5. Cross-Theory Variation

Base-class relationships (all verified at class-statement sites):

| theory | semantics | proposition | model structure | iterator |
|---|---|---|---|---|
| logos | `SemanticDefaults` (`logos/semantic/core.py:31`) | `PropositionDefaults` (`proposition.py:21`) | `ModelDefaults` (`model.py:23`) | `BaseModelIterator` (`iterate.py:36`) |
| exclusion | **`LogosSemantics`** (`exclusion/semantic/core.py:34`) | `PropositionDefaults` (`proposition.py:14`) | `ModelDefaults` (`model.py:138` `WitnessStructure`) | **`LogosModelIterator`** (`iterate.py:19`) |
| imposition | **`LogosSemantics`** (`imposition/semantic/core.py:18`) | **reuses `LogosProposition`** (`imposition/__init__.py:53`) | **`LogosModelStructure`** (`model.py:19`) | `BaseModelIterator` (`iterate.py:34`) |
| bimodal | `SemanticDefaults` (`bimodal/semantic/core.py:42`) | `PropositionDefaults` (`proposition.py:18`) | `ModelDefaults` (`model.py:17`) | `BaseModelIterator` (`iterate.py:31`) |

So there are really **two families**: the state-based truthmaker family (logos as trunk;
exclusion and imposition as subclasses reusing its state mereology, and imposition also its
proposition and model classes and its extensional/modal operator *classes* verbatim,
`imposition/operators.py:222-243`) — and **bimodal**, which shares only the abstract core
(`SemanticDefaults`/`PropositionDefaults`/`ModelDefaults`/`BaseModelIterator`) and the
`Operator`/`OperatorCollection` machinery, re-implementing everything else including its own
`NegationOperator`/`AndOperator`/`OrOperator` with truth-condition (not verifier) semantics
(`bimodal/operators.py:166-418`).

Genuinely shared across all four: the syntactic pipeline (`syntactic.Operator`,
`DefinedOperator`, `OperatorCollection`, `Sentence`), the settings pipeline
(`DEFAULT_EXAMPLE_SETTINGS` merge), `ModelConstraints`/solver drive, the
`BaseModelIterator` skeleton (each theory only fills in `_calculate_differences`,
`_create_difference_constraint`, `_create_non_isomorphic_constraint`,
`_create_stronger_constraint`), and the example-file format.

Quantified duplication (see also Improvement Opportunities):
- `_evaluate_z3_boolean` — robust Z3-boolean coercion — exists three times:
  `logos/semantic/proposition.py:235`, `exclusion/semantic/model.py:227`,
  `imposition/semantic/model.py:49` (plus a wrapper
  `logos/semantic/model.py:87` and three `hasattr(..., '_evaluate_z3_boolean')` fallback
  branches inside `exclusion/semantic/proposition.py:51,74,94`).
- Witness-predicate infrastructure exists twice, structurally parallel but incompatible:
  exclusion's `WitnessRegistry` (dual h/y, `exclusion/semantic/registry.py:19`) vs bimodal's
  `WitnessRegistry` (single `accessible_world`, `bimodal/semantic/witness_registry.py:27`),
  each with its own `WitnessConstraintGenerator`
  (`exclusion/semantic/constraints.py:20`, `bimodal/semantic/witness_constraints.py:26`).
- The iterator `_calculate_differences`/`_create_difference_constraint` pattern is
  re-implemented in logos (470 lines), imposition (508 lines, near-identical shape tracking
  `imposition` triples instead of verify/falsify), and bimodal (564 lines, tracking world
  histories); only exclusion reuses logos's by subclassing and overriding two methods
  (`exclusion/iterate.py:19,196-258`).
- Every theory's `examples.py` repeats the same boilerplate: `sys.path.insert` mangling
  (11 occurrences across the 8 example modules), `general_settings` dicts, and the
  `semantic_theories`/`example_range`/`test_example_range`/`unit_tests` scaffolding.

---

## Q6. Bimodal Specifics

Why it doesn't fit the mold: its models are not a mereological state lattice but a
two-dimensional world-history structure.

- **Sorts** (`bimodal/semantic/core.py:145-156`): `WorldStateSort = BitVecSort(N)` (an
  instantaneous configuration — the bit-vector is just a finite state descriptor, with *no*
  parthood/fusion role), `TimeSort = IntSort()`, `WorldIdSort = IntSort()`.
- **Primitives** (`core.py:158-242`): ternary `task_rel(source_state, duration,
  target_state)` — refactored 2026-05-29 from binary `task(w,u)` to match the Lean
  ProofChecker's `taskRel : S → Q → S → Prop` (`core.py:8-18,180-192`);
  `world_function : WorldId → Array(Time → WorldState)` mapping IDs to histories;
  `is_world : WorldId → Bool` (valid-history predicate — a Z3 *function*, where logos's
  `is_world` is a Python method emitting a formula); `truth_condition(world_state, atom)`
  — plain bivalent truth at instantaneous states; interval bookkeeping functions
  `world_interval_start/end`; `main_point = {"world": 0, "time": IntVal(0)}`.
- **Frame constraints** (`build_frame_constraints`, `core.py:537-720`): 11 constraints in two
  documented categories — model-building constraints (valid main time/world, world-ID
  enumeration cap `max_world_id = M * 2**(M*N)` (`core.py:206-208`), lawful task
  transitions between consecutive states, world-interval validity, *skolem abundance* — the
  requirement that time-shifted copies of every world history exist, aligning with the Lean
  side's ShiftClosed property, implemented as a capped Skolemized constraint with a
  `temporal_depth` knob added for the oracle work (`core.py:76-80,695-707`)) — and TaskFrame
  axioms proper: nullity (`task_rel(w,0,u) ↔ w=u`, `core.py:280`), converse/time-reversal
  (`task_rel(w,d,u) ↔ task_rel(u,-d,w)`, `core.py:305`), and forward compositionality with
  explicit Z3 multi-patterns (`core.py:344`). One constraint (`task_restriction`) is
  deliberately disabled with a documented soundness argument (`core.py:574-580`).
- **Operators**: temporal (`\Future`, `\Past`, `\Until`, `\Since` primitive; `\future`,
  `\past`, `\next`, `\prev` defined) shift/quantify the time coordinate within a history
  using per-world time-domain quantifiers `ForAllTime`/`ExistsTime` (`core.py:396-505`);
  modal `\Box` quantifies over *all* valid world histories at the same time with no domain
  guard — deliberately paper/Lean-aligned (`operators.py:509-560`).
- **Propositions**: `BimodalProposition.extension` maps `world_id → (true_times,
  false_times)` (`semantic/proposition.py:18-70`) — a temporal truth profile, not
  verifier/falsifier sets; `proposition_constraints` gates only contingent/disjoint
  variants over `truth_condition` (`proposition.py:83-110`).
- **Display**: world histories printed horizontally or vertically per the
  `align_vertically` general setting (`semantic/model.py:360,427,547-575`).
- **Engineering artifacts of the Lean/oracle alignment**: `_fresh_bound_int` gensym counter
  (aliasing hazard note, `operators.py:507-560`), `_reset_global_state` with explicit GC
  (`core.py:95-143`), measured-and-rejected Z3 pattern experiments recorded inline as
  comments (`operators.py:536-556`), `temporal_depth` setting consumed by the oracle
  (`core.py:76-80`). These make bimodal by far the heaviest theory (12.8k LOC incl. tests).

---

## Q7. Exclusion / Imposition Specifics

- **Exclusion** = Champollion–Bernard *unilateral* semantics (verified against
  `exclusion/CITATION.md:20-45`, not just assumption): primitive `excludes` relation
  (`semantic/core.py:129-136`), derived `possible` (self-coherence, `core.py:150-181` —
  overriding logos's primitive `possible` Z3 function with a Python method), witness
  functions `h`/`y` per negated formula giving a first-order encoding of the
  minimality-quantified negation clause (`operators.py:20-130`). Propositions are
  verifier-only (`semantic/proposition.py:14-60`); the model wrapper `WitnessAwareModel`
  exposes `get_h_witness`/`get_y_witness` for post-solve queries
  (`semantic/model.py:34-96`), and `WitnessStructure.print_witness_functions` /
  `print_negation` display them (`model.py:388-540`). Its `semantic_theories` supports
  running the same examples under logos via a translation `"dictionary"`
  (`examples.py:974-1002`).
- **Imposition** = Kit Fine's imposition counterfactuals (verified against
  `imposition/CITATION.md:20-40`): primitive ternary `imposition(state, world, outcome)`
  with Fine's inclusion/actuality/incorporation/completeness frame constraints
  (`semantic/core.py:128-192`), operator `\boxright` quantifying over imposition outcomes.
  Everything else is borrowed from logos — proposition class, model structure
  (`ImpositionModelStructure(LogosModelStructure)` adds imposition-relation printing,
  `semantic/model.py:19,101-172`), extensional+modal operator classes, and even rival
  operators `\boxrightlogos`/`\diamondrightlogos` (logos's alternative-worlds
  counterfactual) loaded side-by-side for comparison (`operators.py:189-243`). The
  `derive_imposition` mode flips the run into a meta-proof: it asserts the negated derived
  frame conditions and trivializes premise/conclusion behaviors, so UNSAT means logos's
  `is_alternative` satisfies Fine's axioms (`semantic/core.py:194-209,255-321`).

---

## Q8. Examples as Specification

Shape (uniform across theories and subtheories; e.g.
`logos/subtheories/extensional/examples.py:53-69`): each example is a module-level triple

```python
EXT_CM_1_premises   = ['A']
EXT_CM_1_conclusions = ['\\neg A']
EXT_CM_1_settings   = {'N': 3, 'contingent': True, 'non_null': True, 'non_empty': True,
                       'disjoint': False, 'max_time': 1, 'iterate': 2, 'expectation': True}
EXT_CM_1_example    = [EXT_CM_1_premises, EXT_CM_1_conclusions, EXT_CM_1_settings]
```

i.e. `[premises: list[str], conclusions: list[str], settings: dict]`, formulas written in the
LaTeX-token concrete syntax. `expectation` is the oracle bit: `True` = a countermodel is
expected (the argument is *invalid*), `False` = no countermodel (valid). Naming:
`{PREFIX}_CM_{n}` = countermodel expected, `{PREFIX}_TH_{n}` = theorem. Prefixes: `EXT_`,
`MOD_`, `CON_` (renamed from `CL_` at aggregation, `logos/examples.py:120-127`), `CF_`,
`REL_` (logos); `EX_` (exclusion); `IM_` (imposition); `EX_/MD_/TN_/BM_` for bimodal's
extensional/modal/tense/bimodal-interaction sections plus a large axiom-suite block with
bespoke names (`PROP_K_TH`, `MODAL_5_TH`, `BX7_LINEAR_U_TH`, …) — 31 of bimodal's 52
unit tests use the axiom-suite naming rather than `_CM_`/`_TH_`.

Two tiers per module (required by the contract, Q2):
- `unit_tests` — the complete dict; `test_example_range` is defined as an alias of it in all
  four theories (checked at runtime: `test_example_range is unit_tests` → True for all).
  The theory test suites parametrize over this
  (`logos/subtheories/modal/tests/test_modal_examples.py:26-29`).
- `example_range` — the *curated* subset run on direct CLI execution; built literally as a
  dict with most entries commented out (`imposition/examples.py:997-1010`).

Measured counts (imported live, `PYTHONPATH=code/src`):

| module | unit_tests | (CM / TH) | example_range |
|---|---|---|---|
| logos aggregate | 16 | 9 / 7 | 16 |
| logos/extensional | 14 | | 2 |
| logos/modal | 18 | | 4 |
| logos/constitutive (incl. REL_*) | 54 | | 6 |
| logos/counterfactual | 37 | | 4 |
| exclusion | 38 | 23 / 15 | 2 |
| imposition | 40 | 29 / 11 | 2 |
| bimodal | 52 | 13 / 8 (+31 axiom-suite) | 22 |

**Caveat discovered (important for a port)**: the logos *aggregate* `unit_tests`
(`logos/examples.py:118-127`) merges the subtheories' curated `example_range` subsets — 16
examples — not their full `unit_tests` (123 examples). The full per-subtheory suites are
exercised only by the subtheory test files. So "logos's behavioral spec" lives in the four
subtheory example modules (123 examples), not in the aggregator.

`semantic_theories` (each theory's `examples.py`) maps display names to theory-config dicts
and enables cross-theory comparison runs — exclusion's `"BernardChampollion"` entry carries
a `"dictionary"` translation table and a commented-out `"Brast-McKie"` logos entry
(`exclusion/examples.py:996-1002`; `imposition/examples.py:992-995` similarly has `"Fine"`
plus commented `"Brast-McKie"`).

---

## Q9. Theory-Specific Iteration and Printing

`iterate.py` per theory subclasses `BaseModelIterator` (core `iterate/` package) and supplies
the theory-aware parts — "what makes two models different, and what constraint forces the
next model to differ":

- **logos** (`logos/iterate.py:36-470`): differences over worlds / possible states /
  verify / falsify per letter / parthood (`_calculate_logos_differences`,
  `iterate.py:85-215`); difference constraints force a change in some `verify`/`falsify`
  atom value or world membership (`_create_difference_constraint`, `iterate.py:215`);
  isomorphism-escape and "stronger" constraints (`iterate.py:329,345`). Entry points
  `iterate_example` / `iterate_example_generator` (with the `returns_generator` marker)
  at `iterate.py:414,440`.
- **exclusion** (`exclusion/iterate.py:19-305`): subclasses `LogosModelIterator`; overrides
  letter-value constraints for verifier-only propositions and adds witness-function
  difference constraints (`_create_witness_constraints`, `iterate.py:196`).
- **imposition** (`imposition/iterate.py:34-540`): its own `BaseModelIterator` subclass
  tracking changes to the `imposition(x,w,u)` triples in addition to
  verify/falsify/worlds (`_create_difference_constraint`, `iterate.py:369`).
- **bimodal** (`bimodal/iterate.py:31-564`): differences over world histories,
  `truth_condition` values, and `task_rel` edges (`_create_difference_constraint`,
  `iterate.py:403`).

Display overrides (all building on `ModelDefaults.print_to`/`print_all`):
- logos: states table with world/possible/impossible classification and colors
  (`logos/semantic/model.py:273-303`), evaluation-world report, model-differences printer
  for iteration (`model.py:176-259`).
- exclusion: adds `print_negation` (witness-based negation report) and
  `print_witness_functions` (`exclusion/semantic/model.py:388,453`).
- imposition: adds `print_imposition` — the list of `imposition` triples grouped per world,
  color-coded (`imposition/semantic/model.py:125-172`), with formatting helpers isolated in
  `semantic/helpers.py:19-148`.
- bimodal: `print_world_histories` horizontal/vertical (`bimodal/semantic/model.py:360,427`),
  selected by the `align_vertically` setting inside `print_all` (`model.py:547-575`).

---

## Q10. The `oracle/` Tree

`oracle/` at the repo root is a **standalone differential-testing harness for the bimodal
theory only**, deliberately excluded from the shipped wheel (moved from
`code/src/bimodal_logic/` to top level; `oracle/bimodal_logic/README.md:1-12`). Contents:

- `oracle/bimodal_logic/` (1,925 LOC): a *second, independently written* Z3 encoding of the
  bimodal semantics — `provider.py` (`Z3OracleProvider.find_countermodel()`),
  `translation.py` (formula JSON ↔ prefix/infix, temporal-depth computation),
  `serialization.py` (Z3 model → JSON countermodel), `ground_truth.py` (a third,
  brute-force finite-window evaluator used to adjudicate disagreements),
  `KNOWN_EXTERNAL_DEFECTS.md`, a CLI (`cli.py`), and its own tests.
- Scan infrastructure: `scan_runner.py` (instrumented self-consistency scan CLI over one
  shared enumerate-solve-compare core that lives in
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`),
  `run-oracle-suite.sh` / `run-oracle-exhaustive-scan.sh`, results under
  `oracle/scan-results/` with a `SCAN_COMPLETE` marker contract.
- Relation to the main package: **not self-contained** — it imports `model_checker` (e.g.
  `model_checker.utils.context.isolated_z3_context`, `ModelConstraints`, `Syntax`, and
  `theory_lib.bimodal` symbols) to build the in-package semantics it compares against;
  requires `PYTHONPATH=oracle:code/src` (`README.md:31-78`). Its package metadata (console
  script `bimodal-logic`, entry point `bimodal_harness.oracle_providers`) still lives in
  `code/pyproject.toml`. It also *feeds back* into the theory: bimodal's `temporal_depth`
  setting exists for the oracle's depth-bounded scans (`bimodal/semantic/core.py:76-80`).

For a port: the oracle is quality infrastructure (N-version programming for one theory), not
part of the semantic framework, but its existence signals that bimodal's Z3 encoding was
hard enough to get right that three independent implementations were maintained.

---

## Doc/Source Divergences

1. **`theory_lib/__init__.py` module docstring is stale** (`__init__.py:1-45`): claims
   "Available Theories: bimodal, logos" (omitting exclusion and imposition, which *are* in
   `_THEORY_NAMES` at `__init__.py:63-70`), and instructs extension authors to "Implement
   **semantic.py**, operators.py, and examples.py" — contradicting
   `docs/THEORY_ARCHITECTURE.md:20-22`, which mandates a `semantic/` *package* and which the
   conformance test enforces. It also says "Register the theory name in AVAILABLE_THEORIES"
   whereas registration now flows through `_THEORY_NAMES` → core registry.
2. **CLAUDE.md's canonical-structure claim**: verified TRUE against all four theory
   directories and against the passing conformance suite (50 passed) — no divergence, but
   note the contract's own history: `test_theory_conformance.py:83-108` records that logos
   and bimodal only recently had `semantic.py` split into packages, and bimodal's
   `iterate.py` was restored/rewritten; docs written before that refactor (and any external
   description of a "semantic.py module") are describing the pre-refactor world.
3. **Imposition core docstring misattributes the source paper**
   (`imposition/semantic/core.py:83-86`): says it "Implements Kit Fine's 'The Logic of
   Essence' imposition semantics"; the actual sources per `imposition/CITATION.md:20-40` are
   "Counterfactuals without Possible Worlds" (2012) and "A Difficulty for the Possible
   Worlds Analysis of Counterfactuals" — 'The Logic of Essence' is a different Fine paper.
4. **Exclusion core docstring vs citation**: `exclusion/semantic/core.py:90-93` calls the
   theory "Brast-McKie witness-based negation semantics"; `CITATION.md` attributes the
   *semantics* to Fine (unilateral content) as revised by Champollion & Bernard, with
   Brast-McKie/Buitrago as implementers. The witness-*predicate encoding strategy* is the
   implementation's contribution; the docstring blurs theory and encoding.
5. **`exclusion/docs/` has a seventh file** (`DATA.md`) beyond the documented six-file set —
   harmless (the contract enforces presence, not exhaustiveness), but the six-file list in
   `docs/THEORY_ARCHITECTURE.md:44-45` is not an exact inventory.
6. **`LogosSemantics.closer_world` is a stub** (`logos/semantic/core.py:415-431`): docstring
   describes counterfactual similarity ordering but the body returns `z3.BoolVal(False)`
   ("placeholder"). Any documentation implying ordering-based counterfactual semantics is
   wrong; the real semantics is alternative-worlds (`is_alternative`).
7. **Dead try/except in `logos/examples.py:82-116`**: four `try/for .../except ImportError`
   blocks guard loops over dicts already imported unconditionally at module top — the
   `except ImportError` arms are unreachable (an import failure would have raised at
   line 46-57). The code implies optional subtheories; the imports make them mandatory.
8. **`types.py` protocols are largely aspirational**: `theory_lib/types.py:49-126` defines
   `Proposition.to_z3()`, `ModelStructure.get_states()`, `Operator.apply()` — methods that
   the real classes do not implement (real propositions have `find_proposition`/
   `truth_value_at`; real operators have `true_at`/etc.). Only the witness protocols
   (`WitnessSemantics`, `WitnessRegistry`) match reality. `logos/protocols.py` is the
   accurate protocol set.

---

## Improvement Opportunities

Concrete, cited weaknesses a from-scratch port should design away rather than reproduce:

1. **The theory "contract" is enforced socially + by tests, not by types.** The required
   method surface (Q2) exists only as base classes with implicit expectations, a Markdown
   doc, an AST-walking conformance test, and `logos/protocols.py` used solely under
   `TYPE_CHECKING`. Duck-typed variation has already crept in: `proposition_constraints` is
   an instance method in logos (`logos/semantic/proposition.py:43`) but an
   implicitly-classmethod-style function taking `model_constraints` as its first parameter
   in exclusion (`exclusion/semantic/proposition.py:22-40` — "This is called as a class
   method (without an instance)"); operator post-solve extraction is
   `find_verifiers_and_falsifiers` (logos family), `compute_verifiers` (exclusion), or
   `find_truth_condition` (bimodal). A port should make "evaluation scheme" (bilateral
   verifier/falsifier vs unilateral verifier vs bivalent temporal profile) an explicit
   abstraction instead of three unrelated method names discovered by the printer/proposition
   layer at runtime.
2. **Capability detection via `hasattr` and marker attributes.** The generator-interface
   detection contract (`hasattr(fn, '__wrapped__') and hasattr(fn.__wrapped__,
   'returns_generator')`, `docs/THEORY_ARCHITECTURE.md:37-43`) *silently* degrades when the
   marker is missing; `exclusion/semantic/proposition.py:51,74,94` branches on
   `hasattr(self.model_structure, '_evaluate_z3_boolean')`;
   `logos/iterate.py:71-77` branches on `hasattr(new_structure,
   'detect_model_differences')`. These are latent-failure points a typed port eliminates.
3. **Triplicated Z3-boolean coercion**: `_evaluate_z3_boolean` implemented three times
   (`logos/semantic/proposition.py:235`, `exclusion/semantic/model.py:227`,
   `imposition/semantic/model.py:49`) — pure library code that belongs in the solver layer.
4. **Two parallel witness frameworks**: exclusion's h/y registry+generator
   (`exclusion/semantic/registry.py`, `constraints.py`) and bimodal's accessible_world
   registry+generator (`bimodal/semantic/witness_registry.py`, `witness_constraints.py`)
   share structure (register-per-formula, name-mangled Z3 functions, clear-on-rebuild) with
   no shared abstraction. "Per-formula Skolem function registry" is a reusable concept.
5. **Iterator difference logic is copy-adapted per theory** (~470/305/508/564 lines;
   Q9): the skeleton — diff worlds, diff a per-letter relation, diff a theory-specific
   relation, emit a disjunctive difference constraint, escape isomorphs — is identical; only
   the relation lists differ. A port can drive this from a declarative list of "model
   dimensions" per theory.
6. **Semantics entangled with display and with Z3-model querying.** Operators carry
   `print_method` and post-solve set computation alongside their constraint semantics
   (Q4.4's three divergent encodings of the *same* clause: `true_at`,
   `find_verifiers_and_falsifiers`, `print_method` each re-derive alternative worlds —
   `counterfactual/operators.py:44-180`). The same truth condition is thus written 2–3
   times per operator and can drift. Separating (a) symbolic clause, (b) concrete
   evaluation against a found model, (c) presentation — with (b) derived from (a) where
   possible — is the single highest-leverage structural change.
7. **Bound-variable hygiene is ad hoc and inconsistent**: logos uses fixed Z3 variable names
   (`"t_nec_u"`, `"and_verify_x"` — collision-safe only by convention), exclusion a
   per-semantics counter (`exclusion/operators.py:30-32`), bimodal a process-global counter
   with an explicit reset hook and a long aliasing post-mortem
   (`bimodal/operators.py:507-560`, `bimodal/semantic/core.py:117-125`). A port needs a
   principled fresh-name supply (or de Bruijn / HOAS) from day one.
8. **Example modules are stringly, duplicated boilerplate**: 8 modules × (sys.path hacks —
   11 `sys.path.insert` occurrences; hand-maintained `_premises/_conclusions/_settings/
   _example` quadruples; curated `example_range` as comment-toggled dict literals,
   `imposition/examples.py:997-1010`); the "assigned exactly once" rule has to be enforced
   by AST inspection (`test_theory_conformance.py:126-135`) because plain attribute checks
   can't see silent overwrites — which actually happened (logos duplicate `example_range`,
   `test_theory_conformance.py:104-106`). A declarative example datatype
   (name, premises, conclusions, settings, expectation, tags) removes the whole class of
   defects, and would also fix the logos aggregation gap where the top-level `unit_tests`
   silently covers 16 of 123 subtheory examples (Q8).
9. **Primitive-vs-derived mismatch across the family**: `possible` is a Z3 function in
   logos (`logos/semantic/core.py:75-80`) but a Python method in exclusion
   (`exclusion/semantic/core.py:166-181`); `is_world` is a Python method in
   logos/exclusion but a Z3 function in bimodal (`bimodal/semantic/core.py:200-204`).
   Subclassing across these (WitnessSemantics extends LogosSemantics and *shadows* the
   inherited Z3 function attribute with a method) works only because everything is dynamic;
   it is exactly the kind of thing a port should model as an explicit "signature +
   definitional extensions" structure.
10. **Inline experiment logs bloat hot files**: bimodal's `operators.py` (1,777 lines) and
    `semantic/core.py` (2,194 lines) carry multi-paragraph records of tried-and-rejected
    Z3 patterns and task-numbered dead ends (`operators.py:536-556`,
    `core.py:541-580`) — valuable history, wrong location; it obscures the ~15 lines of
    actual semantics per operator.
11. **`meta_data.py` mutates source files as a maintenance mechanism**
    (`update_all_theory_versions`, `create_all_license_files`, `create_all_citation_files`,
    `meta_data.py:91-287`): version/license management by rewriting `__init__.py` text.
    Ordinary package metadata in a port.
12. **Aspirational/duplicate type layers** (`types.py` vs `logos/protocols.py`, item 8 in
    divergences) — pick one, make it real.

---

## Summary for the Port

The theory library's real interface is: a theory = (semantics class constructing Z3
primitives + frame constraints + premise/conclusion behaviors over an *evaluation-point*
dict; proposition class = per-atom constraint menu + post-solve extension extraction; model
structure = display/extraction; operator collection = named, arity-tagged clauses in 2–3
registers; examples = named (premises, conclusions, settings, expectation) records;
iterator = difference dimensions). Two genuinely distinct semantic families exist (state
mereology vs world histories), with exclusion and imposition as principled variations on
the logos trunk — the variation points being: which atomic primitives exist
(verify/falsify vs verify+excludes vs truth_condition), which relations are primitive vs
derived (imposition vs is_alternative), and which evaluation scheme propositions use. The
conformance suite (`tests/test_theory_conformance.py`) and the examples corpus
(~253 example records across 8 modules) together form the executable specification.
