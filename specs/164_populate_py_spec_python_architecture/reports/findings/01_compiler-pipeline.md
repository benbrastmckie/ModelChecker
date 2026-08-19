# Findings: The Modular Compiler Pipeline (DSL sentence -> Z3 constraints)

Territory: `code/src/model_checker/syntactic/`, `code/src/model_checker/solver/`,
`code/src/model_checker/z3_shim.py`, and the constraint-generation half of
`code/src/model_checker/models/` (`constraints.py`, `semantic.py`, `proposition.py`, the
solve path of `structure.py`). All paths below are relative to
`code/src/model_checker/` unless prefixed otherwise. All claims were verified against
source; every doc claim relied on was re-checked (see Doc/Source Divergences).

## Pipeline at a glance

The end-to-end wiring, exactly as executed by `builder/runner.py:79-89` (and
equivalently `builder/example.py:173-190`):

```python
syntax = Syntax(premises, conclusions, operators)          # parse + operator linking
semantics = semantics_class(settings)                       # theory semantics (Z3 decls, frame constraints)
model_constraints = ModelConstraints(settings, syntax, semantics, proposition_class)
model_structure = model_structure_class(model_constraints, settings)   # solves in __init__
model_structure.interpret(premise_and_conclusion_sentences)            # post-sat interpretation
```

Four constraint groups are produced (`models/constraints.py:80-103`), asserted with
tracking labels, and checked by the solver abstraction. Everything upstream of
`ModelConstraints` is pure syntax; everything downstream is Z3/cvc5 expression
construction driven by double dispatch between the theory's `Semantics` object and
per-operator classes.

---

## 1. Lexing/parsing: concrete surface syntax and algorithm

### Surface syntax

- **Sentence letters**: any token for which `token.isalnum()` is true
  (`utils/parsing.py:33`, re-checked at `syntactic/collection.py:119`). So `p`, `q`,
  `A`, `B1`, `man1` are all valid atoms. Note `isalnum()` is Unicode-aware, so `π` is
  technically an atom too.
- **Operators**: LaTeX-style backslash tokens: `\\neg`, `\\wedge`, `\\vee`,
  `\\rightarrow`, `\\Box`, `\\boxright`, etc. Any token starting with `\\` is treated
  as an operator by the parser (`utils/parsing.py:35`). Operator *names* are declared
  by operator classes (`name` class attribute) and resolved after parsing, not during.
- **Nullary operators** (extremal constants): exactly `\\top` and `\\bot` are
  special-cased as complete formulas (`utils/parsing.py:38-39`). This set is
  **hard-coded in the parser** — a theory cannot add a new nullary operator without
  touching `utils/parsing.py` (see Improvement Opportunities).
- **Unary operators**: prefix, no parentheses: `\\neg p`, `\\Box \\neg p`.
- **Binary operators**: strictly infix and **must** be parenthesized:
  `(p \\wedge q)`, `((p \\vee q) \\rightarrow r)`. There is no precedence — every
  binary application needs its own parentheses. The outermost parentheses are
  mandatory for a top-level binary formula.
- **Tokenization**: whitespace splitting after padding parens
  (`syntactic/sentence.py:139`):
  ```python
  tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
  ```
  So operators and atoms must be whitespace-separated (except adjacent to parens).

### Algorithm

Hand-written recursive descent over a mutable token list, in
`utils/parsing.py:11-45` (`parse_expression`) plus the binary-splitting helper
`op_left_right` (`utils/parsing.py:48-119`):

1. Pop the first token.
2. If `(`: pop the **last** token (must be `)`), then call `op_left_right` on the
   interior to split it into `(operator, left_tokens, right_tokens)`; recursively
   parse both sides; return `[operator, left_arg, right_arg]` with
   `complexity = left + right + 1` (`utils/parsing.py:18-32`).
3. If `token.isalnum()`: return `[token], 0` (atom, `utils/parsing.py:33-34`).
4. If token starts with `\\`: if `\\top`/`\\bot` return `[token], 0`; otherwise treat
   as **unary**: parse one argument, return `[token, arg], comp+1`
   (`utils/parsing.py:35-43`).
5. Any other token (line 44-45): silently treated as a unary operator —
   `return [token, arg], comp + 1`.

`op_left_right`'s `extract_arguments` (`utils/parsing.py:99-114`) scans left-to-right:
if the first token is `(`, it consumes tokens tracking paren depth
(`cut_parentheses`, lines 74-92) until depth returns to zero; the next token is the
binary operator, and the remainder is the right argument (checked only for balanced
parens, lines 64-72). If the first token is an atom or `\\top`/`\\bot`, that single
token is the left argument. Otherwise (unary operator on the left), tokens accumulate
into `left` until one of the previous cases fires — this is how `(\\neg p \\wedge q)`
finds `\\wedge`. Note the unary-left path (line 112-113 `else: left.append(token)`)
accumulates without arity knowledge, so left arguments like `\\Box \\neg p` work.

**Complexity metric**: the returned int is operator-application count along the
deepest... actually it is total for binary (`left + right + 1`, line 31) and
depth-ish for unary chains; `Sentence.complexity` stores it (`sentence.py:71`) but it
is only meaningfully used as "0 = atomic, >0 = complex" (`sentence.py:84`).

**No all-tokens-consumed check**: `Sentence.prefix` (`sentence.py:126-141`) discards
whatever `parse_expression` did not consume. `"p q"` parses as `p`; `"\\wedge p q"`
parses as the unary application `["\\wedge", ["p"]]`, silently dropping `q`. See
Improvement Opportunities.

**Well-formedness check**: after parsing, `Sentence._validate_well_formedness`
(`sentence.py:112-124`) calls `is_syntactically_wff` (`syntactic/formulas.py:15-76`).
This check is extremely permissive: it inspects only the *head* of the prefix list
(accepts any non-backslash string atom, any backslash operator, extremal constants,
any single non-string object) and never checks arity or recursion into arguments.
It exists mainly to reject e.g. empty structures. Arity is *never* validated against
the parsed shape (see §3 and Improvement Opportunities).

### Prefix-list shape (the parse output)

`PrefixList = List[Union[str, List]]` (`syntactic/types.py:19`). Examples verified
against the parser:

```
"p"                      -> ["p"]                                complexity 0
"\\top"                  -> ["\\top"]                            complexity 0
"\\neg p"                -> ["\\neg", ["p"]]                     complexity 1
"(p \\wedge q)"          -> ["\\wedge", ["p"], ["q"]]            complexity 1
"((p \\vee q) \\rightarrow r)"
                         -> ["\\rightarrow", ["\\vee", ["p"], ["q"]], ["r"]]
```

Arguments are always themselves lists (even atoms), i.e. `[op, arg1, arg2]` where
each `arg` is a prefix list — *not* the flat `["∧", "p", "q"]` some docs show.

---

## 2. AST representation: the `Sentence` class

`syntactic/sentence.py:23` defines the single AST node type. There is no separate
node hierarchy (no `AtomNode`/`BinaryNode`); one mutable class covers all cases, with
`None`-valued fields marking the phases not yet run.

### Fields and when they are populated

Construction (`__init__`, `sentence.py:49-107`):

| Field | Set at | Value |
|---|---|---|
| `name` | construction | original infix string (also `__str__`/`__repr__`) |
| `prefix_sentence` | construction | prefix list from the parser (`sentence.py:71`) |
| `complexity` | construction | int from parser |
| `original_arguments` | construction | for complex sentences: list of **infix strings** of the args (`sentence.py:86-89`); later **mutated** into a list of `Sentence` objects by `Syntax.build_sentence` (`syntax.py:120-124`); `None` for atoms |
| `original_operator` | construction | operator **string** (or `\\top`/`\\bot` for extremals, else `None`); later mutated twice (see below) |
| `arguments` | `None` at construction | phase 2 |
| `operator` | `None` at construction | phase 2 then phase 3 |
| `sentence_letter` | `None` at construction | phase 2 |
| `proposition` | `None` at construction | phase 4 |
| `_internal` | construction | True for subformulas — skips WFF validation |

### The four-phase mutation lifecycle (documented at `sentence.py:30-34`)

1. **Creation** — parse infix to prefix (above).
2. **Type update** — `update_types(operator_collection)` (`sentence.py:185-254`),
   invoked from `Syntax.initialize_sentences`. Steps:
   - `operator_collection.apply_operator(self.prefix_sentence)` replaces operator
     strings with operator **classes** and atom strings with Z3
     `Const(atom, AtomSort)` objects (`collection.py:85-127`).
   - `derive_type` (`sentence.py:207-222`) recursively **expands defined
     operators**: if the head class has `primitive == False`, it calls
     `operator_class('a').derived_definition(*args)` (note the throwaway `'a'`
     passed as the semantics argument — `sentence.py:218`) and recurses until the
     head is primitive.
   - `store_types` (`sentence.py:224-248`) splits the result into the triple
     `(operator, arguments, sentence_letter)`: for a lone Z3 const →
     `(None, None, const)`; for `\\top`/`\\bot` (detected by `self.name`) →
     `(OpClass, None, None)`; for complex → `(OpClass, [infix strings of derived
     args], None)`.
   - `original_operator` is separately overwritten with the *pre-derivation* class
     (`sentence.py:251-252`) so printing shows what the user wrote.
   - The derived argument infix strings are then re-parsed into `Sentence` objects
     by `Syntax.initialize_types` (`syntax.py:128-152`), which recursively
     type-updates them and mutates `sentence.arguments` from strings to `Sentence`s.
     **Consequence**: after phase 2, the whole `arguments` tree contains only
     primitive operators; defined operators survive only in `original_operator` /
     `original_arguments` (the display tree).
3. **Object update** — `update_objects(model_constraints)` (`sentence.py:256-281`),
   invoked from `ModelConstraints.instantiate` (`models/constraints.py:158-178`):
   replaces both `original_operator` and `operator` (currently classes) with operator
   **instances** looked up **by name** in `model_constraints.operators`
   (`sentence.py:270-276`) — the instances carry the theory's semantics object.
4. **Proposition update** — `update_proposition(model_structure)`
   (`sentence.py:283-285`), invoked post-solve by `ModelDefaults.interpret`
   (`models/structure.py:347`): sets `self.proposition =
   model_structure.proposition_class(self, model_structure)`.

So the same field (`operator`) holds, over time: `None` → class → instance. The AST
is aggressively mutable and identity-shared: `Syntax.all_sentences` interns nodes by
infix string (`syntax.py:107-109`), so a subformula appearing in several
premises/conclusions is one shared mutable object.

### Alternate constructor

`Sentence.from_prefix` (`sentence.py:288-372`) builds a node directly from a prefix
list using `object.__new__` to bypass `__init__` (no parsing, no WFF validation),
with standalone helpers `_compute_infix_from_prefix` (`sentence.py:375-407`) and
`_compute_prefix_complexity` (`sentence.py:410-431`). Used for JSON-sourced formulas.
Note `_compute_prefix_complexity` computes `1 + max(child complexities)` (nesting
depth) whereas the parser computes `left + right + 1` for binary — the docstring's
claim that it "matches the complexity values that Sentence.__init__ produces" is
false for e.g. `((p \wedge q) \wedge (r \wedge s))` (parser: 3; helper: 2). Harmless
today because complexity is only tested against 0, but it is a latent divergence.

### Infix rendering

`Sentence.infix` (`sentence.py:145-183`) renders a prefix structure back to a string;
it accepts `Sentence` objects (via `.name`), strings, lists/tuples, operator classes
(via the `hasattr(prefix, 'name')` check — class attribute `name`), and solver
expressions (duck-typed via callable `.sort`, checked *after* list to avoid
`list.sort` — `sentence.py:176-179`). Unary renders as `op arg` (no parens); binary
as `(left op right)`; arity ≥3 has no parenthesized form (`from_prefix` helper falls
back to space-joining, `sentence.py:403-407`).

---

## 3. Operator abstraction

### `Operator` base class (`syntactic/operators.py:26-260`)

Contract (class attributes + constructor):

```python
class Operator:
    name: Optional[OperatorName] = None    # e.g. "\\wedge"
    arity: Optional[int] = None
    primitive: bool = True

    def __init__(self, semantics: SemanticDefaults) -> None: ...
```

- `__init__` (`operators.py:53-62`) refuses direct instantiation of `Operator`
  itself and raises `NameError` if `name` or `arity` is missing; stores
  `self.semantics`.
- Equality/hash by `(name, arity)` (`operators.py:70-77`).
- Three **printing** helpers are provided in the base class: `general_print`
  (`operators.py:79-104`), `print_over_worlds` (`operators.py:107-203`),
  `print_over_times` (`operators.py:205-260`) — these are output-side and consume
  `sentence.proposition`/`model_structure`.

The *semantic* methods (`true_at`, `false_at`, `extended_verify`,
`extended_falsify`, `find_verifiers_and_falsifiers`, `print_method`) are **not
declared** on the base class at all — not even as abstractmethods; the docstring
merely lists them (`operators.py:33-38`). The contract is enforced only by
`AttributeError` at constraint-generation time. Their shapes, as implemented by every
concrete operator (verified in
`theory_lib/logos/subtheories/extensional/operators.py`):

```python
# arity-2 operator (AndOperator, extensional/operators.py:79-134)
def true_at(self, leftarg, rightarg, eval_point):        # args are Sentence objects
def false_at(self, leftarg, rightarg, eval_point):
def extended_verify(self, state, leftarg, rightarg, eval_point):   # state: BitVecRef
def extended_falsify(self, state, leftarg, rightarg, eval_point):
def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
```

i.e. every method takes the operator's arguments **splatted** (`*arguments`) followed
by `eval_point` (a plain dict, e.g. `{"world": w}`); callers invoke them as
`operator.true_at(*arguments, eval_point)` (`logos/semantic/core.py:174`,
`core.py:210`, `core.py:249`, `core.py:287`). `find_verifiers_and_falsifiers`
returns a pair of Python sets of states and is used post-solve
(`logos/semantic/proposition.py:229-231`), not during constraint generation.

Arity mismatches between the declared `arity` and the parsed shape are caught only
as a Python `TypeError` when the splat call fires. `ArityError` exists
(`syntactic/errors.py:180`) and is imported (`operators.py:20`) but never raised
anywhere in the package (verified by grep).

### `DefinedOperator` (`operators.py:263-344`)

```python
class DefinedOperator(Operator):
    primitive = False
    def derived_definition(self, *args) -> list: ...   # must override
```

- `derived_definition` returns a prefix structure whose head is an operator
  **class**, e.g. `ConditionalOperator.derived_definition`
  (`logos/subtheories/extensional/operators.py:296-298`):
  ```python
  def derived_definition(self, leftarg, rightarg):
      return [OrOperator, [NegationOperator, leftarg], rightarg]
  ```
- `__init__` validates that `arity` equals the parameter count of
  `derived_definition` via `inspect.signature` (`operators.py:302-344`, raising
  `ValueError` on mismatch).

**Definitional expansion** happens at *type-update time* in
`Sentence.update_types.derive_type` (`sentence.py:207-222`): the definition is
instantiated with the dummy semantics `'a'` and applied to the raw argument
structures, recursing until the head is primitive. Expansion is head-only per node,
but because arguments are re-parsed as sentences and type-updated recursively
(`syntax.py:128-152`), the entire evaluated tree ends up primitive. Two consequences
verified in source:

1. A `DefinedOperator`'s own `true_at`/`extended_verify` implementations (e.g.
   `ConditionalOperator.true_at`, extensional/operators.py:300-306) are **dead code
   on the constraint path** — `sentence.operator` is always the derived primitive
   head. They are exercised only if a theory calls them directly (none do on the
   solve path; the logos operators nevertheless all implement them).
2. `Syntax.circularity_check` (`syntax.py:163-240`) validates definitions
   *statically* by calling `derived_definition` with `None` dummy args, flattening,
   and collecting operator classes: missing dependencies raise `ValueError`
   (`syntax.py:212-216`); cycles are detected by DFS with a recursion stack raising
   `RecursionError` (`syntax.py:225-240`). Note this happens *after*
   `initialize_sentences` in `Syntax.__init__` (`syntax.py:76-80`) — so a circular
   definition that is actually *used* would blow the Python stack inside
   `derive_type` before the checker ever runs; the checker only catches cycles in
   operators not used by the current example (or would, had parsing not already
   recursed). See Improvement Opportunities.

### `OperatorCollection` (`syntactic/collection.py:16-127`)

A name-keyed registry: `operator_dictionary: Dict[str, Type[Operator]]`.

- `add_operator` (`collection.py:44-88`) accepts a class, list/tuple/set of classes,
  or another `OperatorCollection` (merge). **Duplicate names are silently skipped —
  first registration wins** (`collection.py:79-80`). `DuplicateOperatorError` exists
  in `syntactic/errors.py` but is not raised here.
- `apply_operator` (`collection.py:85-127`) is the string→class/const resolution pass
  described in §2. Unknown operator names raise `KeyError` from `self[op]`
  (`collection.py:125`), not the defined `UnknownOperatorError`.
- Composition across theories: theories build collections by adding class lists;
  logos composes per-subtheory operator dicts through `LogosOperatorRegistry`
  (`theory_lib/logos/operators.py:23-100`), which merges each loaded subtheory's
  `get_operators()` dict into one `OperatorCollection` with dependency auto-loading
  (`dependencies` table at `logos/operators.py:34-39`, e.g. `modal` requires
  `extensional`+`counterfactual`). Because first-wins, load order silently resolves
  name conflicts between subtheories.

---

## 4. The `Syntax` object

`syntactic/syntax.py:22-240`. Constructor signature
(`syntax.py:56-80`): `Syntax(infix_premises: List[str], infix_conclusions:
List[str], operator_collection)`. Construction is wrapped in a process-global
single-threaded guard (`@guard_construction`, `syntax.py:55`; contract documented at
`syntax.py:47-52` and `models/concurrency.py`).

End-to-end behavior:

1. `initialize_sentences` for premises then conclusions (`syntax.py:77-78`), which
   runs the interning `build_sentence` closure (dedupe on infix string via
   `all_sentences`, `syntax.py:106-126`) and `initialize_types` (phase-2 recursion,
   `syntax.py:128-152`).
2. Populates:
   - `all_sentences: Dict[str, Sentence]` — every sentence and subsentence, keyed by
     infix string (both the original tree and the derived/expanded tree).
   - `sentence_letters: List[Sentence]` — the `Sentence` wrappers of atoms, collected
     during `build_sentence` when a 1-element prefix holds a non-`\\top`/`\\bot`
     string (`syntax.py:115-119`). Dedupe is inherited from interning.
   - `premises` / `conclusions: List[Sentence]`.
   - `start_time` (wall-clock, `syntax.py:63`).
3. `circularity_check` (§3).

### Sentence letters and `AtomSort`

An atom string `p` becomes `Const("p", AtomSort)` during `apply_operator`
(`collection.py:118-120`), stored in `sentence.sentence_letter`. `AtomSort` is a Z3
**uninterpreted sort** created lazily per backend: `DeclareSort("AtomSort")` with a
module-global cache and `reset_atom_sort()` hook (`syntactic/atoms.py:18-56`),
registered with the solver lifecycle so backend switches invalidate it
(`atoms.py:77-79`). `AtomVal(i)` makes `Const(f"AtomSort!val!{i}", AtomSort)`
(`atoms.py:59-75`) — used by theories when enumerating atom constants.
`syntactic/__init__.py:48-65` exposes `AtomSort` via module `__getattr__` so
`from model_checker.syntactic import AtomSort` always reflects the active backend.
Distinctness of atom constants is by Z3's name-interning of constants (same
name+sort → same AST); nothing asserts `p != q` — the `verify`/`falsify` functions
take the atom as an argument, so distinct names suffice.

`ModelConstraints._load_sentence_letters` (`models/constraints.py:118-138`) unpacks
`syntax.sentence_letters` into raw Z3 consts, validating only by duck-typing
(`hasattr(unpacked_letter, 'sort')`); note its error message has an f-string bug —
`"The sentence letter {letter} is not..."` without the `f` prefix
(`constraints.py:134`).

---

## 5. Compilation to constraints: `ModelConstraints`

`models/constraints.py:21-103`. Constructor (guarded, `constraints.py:52-59`):
`ModelConstraints(settings, syntax, semantics, proposition_class)`.

Ordered steps inside `__init__` (all at `constraints.py:60-103`):

1. Store `premises`/`conclusions` from syntax; `_load_sentence_letters()`.
2. `self.operators = self.copy_dictionary(self.syntax.operator_collection)`
   (`constraints.py:74`, method at 140-156): instantiate **every** operator class in
   the collection with this semantics — `{name: op_class(self.semantics)}`. (This is
   where `DefinedOperator._validate_arity` actually runs, for all registered defined
   operators whether used or not.)
3. `self.instantiate(self.premises + self.conclusions)` (`constraints.py:77`, method
   at 158-178): recursive walk over `sentence.arguments` calling
   `sent_obj.update_objects(self)` — phase 3 of the sentence lifecycle (class →
   instance by name lookup).
4. Build the four constraint groups, in this order (`constraints.py:80-96`):
   ```python
   self.frame_constraints = self.semantics.frame_constraints
   self.model_constraints = [c for letter in self.sentence_letters
                               for c in self.proposition_class.proposition_constraints(self, letter)]
   self.premise_constraints = [self.semantics.premise_behavior(p) for p in self.premises]
   self.conclusion_constraints = [self.semantics.conclusion_behavior(c) for c in self.conclusions]
   self.all_constraints = frame + model + premise + conclusion
   ```

Who generates what:

- **Frame constraints**: the theory's semantics `__init__` builds them eagerly. E.g.
  `LogosSemantics` (`theory_lib/logos/semantic/core.py:87-104`): possibility
  downward-closure under part-of, plus `is_world(main_world)` for the designated
  evaluation world `w = BitVec("w", N)` (`core.py:82-85`).
- **Model constraints** (per sentence letter): generated by the *proposition
  class*'s `proposition_constraints`. In logos
  (`logos/semantic/proposition.py:43-190`): always classical constraints (verifier/
  falsifier fusion closure, no-glut, no-gap), plus settings-gated `contingent`,
  `non_empty`, `disjoint`, `non_null` groups (gating logic at
  `proposition.py:183-190`). **Cross-class `self` quirk**: `proposition_constraints`
  is written as an instance method (`def proposition_constraints(self,
  sentence_letter)`) but is invoked on the class with the `ModelConstraints`
  instance as `self` (`constraints.py:84-88`); it works because the body only
  touches `self.semantics` and `self.settings`, which both classes happen to have.
  A Haskell port should treat it as a function
  `(semantics, settings, letter) -> [Constraint]`.
- **Premise/conclusion constraints**: `premise_behavior`/`conclusion_behavior` are
  **lambdas** set by the theory semantics
  (`logos/semantic/core.py:107-108`):
  ```python
  self.premise_behavior    = lambda premise:    self.true_at(premise, self.main_point)
  self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)
  ```
  i.e. countermodel search: premises true, conclusions false at the main point; a
  `sat` result is a countermodel, `unsat` means the argument is valid.

### The recursive constraint compiler (double dispatch)

The actual formula→Z3 translation is mutual recursion between the semantics and the
operator instances (verified in `logos/semantic/core.py:140-287`):

- `semantics.true_at(sentence, eval_point)`: if `sentence.sentence_letter` is set,
  emit `Exists x. is_part_of(x, eval_world) ∧ verify(x, letter)`
  (`core.py:165-167`); else delegate `operator.true_at(*arguments, eval_point)`.
- `false_at`: dual with `falsify` (`core.py:198-203`).
- `extended_verify(state, sentence, eval_point)`: atoms → `verify(state, letter)`
  (`core.py:238-240`); else `operator.extended_verify(state, *arguments,
  eval_point)`.
- `extended_falsify`: dual (`core.py:250-287`).

Operators recurse back into the semantics for their subsentences, e.g.
`AndOperator.true_at` = conjunction of `semantics.true_at` on both args
(extensional/operators.py:79-84); `AndOperator.extended_verify` = ∃x,y with
`state == fusion(x, y)` (extensional/operators.py:93-107). The recursion bottoms out
at sentence letters. There is no memoization of emitted subformulas; shared
subsentences re-emit their Z3 subtrees each time (Z3 hash-consing dedupes ASTs
internally).

### `SemanticDefaults` — the base-class contract (`models/semantic.py:47-...`)

What the framework core provides and what a theory must add:

Provided (`semantic.py:110-137` and method suite):
- `__init__(combined_settings)`: validates `N` (`_validate_N`, `semantic.py:142-179`;
  must be int in `[1, MAX_N=20]`, `semantic.py:44`), then eagerly materializes
  `full_state = BitVecVal(2^N - 1, N)`, `null_state = BitVecVal(0, N)`, and
  `all_states = [BitVecVal(i, N) for i in range(2^N)]` (`semantic.py:120-124`);
  optional `M`/`all_times` for temporal theories (`semantic.py:127-129`); initializes
  `main_point`, `frame_constraints`, `premise_behavior`, `conclusion_behavior` to
  `None` (`semantic.py:132-137`) — **the theory subclass must overwrite all four**.
- Mereology helpers: `fusion` = `bit_s | bit_t` (`semantic.py:225-239`),
  `is_part_of` = `fusion(s,t) == t` (`semantic.py:296-306`), `is_proper_part_of`
  (`semantic.py:308-319`), `non_null_part_of` (`semantic.py:321-333`), `product` /
  `coproduct` (pairwise-fusion closure, `semantic.py:335-372`), `total_fusion`,
  Z3-set↔Python-set converters (`semantic.py:241-294`).
- `DEFAULT_GENERAL_SETTINGS` (`semantic.py:79-87`).
- Construction concurrency guard: `__init_subclass__` wraps every subclass
  `__init__` in `guard_construction` (`semantic.py:89-109`) because subclasses do Z3
  work after `super().__init__()` returns.
- Iterator support: `initialize_with_state` /
  `_make_constrained_verify`/`_make_constrained_falsify` (`semantic.py:374-416`)
  monkey-patch `self.verify`/`self.falsify` with closures returning fixed `BoolVal`s
  for known (state, letter) pairs — used by the model iterator to pin MODEL 2+
  constraints.

Required of a theory (by convention; nothing abstract): declare Z3 primitives (logos:
`verify`, `falsify` as `Function(BitVecSort(N), AtomSort, BoolSort())`, `possible` as
`Function(BitVecSort(N), BoolSort())` — `logos/semantic/core.py:63-78`), set
`main_point`, `frame_constraints`, `premise_behavior`, `conclusion_behavior`, and
implement `true_at`/`false_at`/`extended_verify`/`extended_falsify` dispatchers.
Optionally `inject_z3_model_values` for the iterator
(hook: `ModelConstraints.inject_z3_values`, `constraints.py:180-205`, which
delegates via `hasattr` check).

### Quantifiers: finite expansion, not native Z3 quantifiers (mostly)

`model_checker.utils.ForAll/Exists` (`utils/z3_helpers.py:16-87`) are **not** Z3
quantifiers: they enumerate all `2^N` bitvector values and build an explicit
`And`/`Or` of substituted formulas (recursive over multiple bound variables — cost
`(2^N)^k` conjuncts). Logos uses these for nearly everything (import at
`logos/semantic/core.py:16`), so logos constraints are quantifier-free bitvector
formulas whose size is exponential in `N`. Exceptions verified: logos
`get_non_empty_constraints` uses native `z3.Exists` (`logos/semantic/
proposition.py:169-177`), and other theories (bimodal) use native quantifiers —
which is why `Z3SolverAdapter._configure_quantifier_mode` exists
(`solver/z3_adapter.py:33-60`: `auto_config=False`, `smt.mbqi=True`,
`smt.ematching=True`, `smt.mbqi.max_iterations=1000`, `max_memory=4096` MB).

---

## 6. Solver layer (`solver/` + `z3_shim.py`)

### Package roles

| File | Role |
|---|---|
| `registry.py` | backend selection (`get_active_backend`, `solver/registry.py:90-121`): priority CLI override (`set_cli_backend`) > env `MODEL_CHECKER_SOLVER` > `settings["solver"]` > default `"z3"`; `create_solver(settings)` factory (`registry.py:155-186`) |
| `backend.py` | cached `get_backend_module()` returning the `z3` or `cvc5.pythonic` module (`solver/backend.py:27-60`) |
| `expressions.py` | ~80 thin wrapper functions (`And`, `Or`, `BitVec`, `BitVecVal`, `Function`, `DeclareSort`, `Const`, `substitute`, `simplify`, quantifiers, sets, …) each calling `_get_backend_module().<name>(...)` — a per-call dynamic dispatch (`solver/expressions.py:17-363`) |
| `protocols.py` | `SolverProtocol` (add/check/model/push/pop), `TrackedSolverProtocol` (+`assert_tracked`, `unsat_core`), `ModelProtocol` (eval/getitem), and `SolverResult` — string constants `"sat"/"unsat"/"unknown"` with converters (`solver/protocols.py:108-178`) |
| `z3_adapter.py` | thin `z3.Solver` wrapper (below) |
| `cvc5_adapter.py` | cvc5.pythonic wrapper with label↔term mapping for unsat cores |
| `lifecycle.py` | cache-invalidation hook registry; `set_backend_with_invalidation` invalidates all caches then switches (`solver/lifecycle.py:75-96`) |
| `compat.py` | backend-tolerant `is_true`/`is_false`/`simplify`/`eval_model`/`get_bitvec_value` |
| `types.py` / `types_runtime.py` / `type_guards.py` | static aliases (TYPE_CHECKING-gated); lazily-resolved runtime types for `isinstance`; `assert_backend_types` guards that raise `TypeError` when a Z3 AST reaches the cvc5 solver or vice versa (`solver/type_guards.py:21-48`) |

### `z3_shim.py`

A transitional module-level `__getattr__` shim (`z3_shim.py:23-50`):
`from model_checker.z3_shim import X` resolves `X` from the active backend module,
cached in `_backend_module` and reset via a registered lifecycle hook
(`z3_shim.py:64-77`). Its own docstring calls it transitional
(`z3_shim.py:12-13`), yet it is the *primary* import style in theory code
(`from model_checker import z3_shim as z3`, `logos/semantic/core.py:11`) — the
"migration" target `solver.expressions` is used by core packages instead. Both paths
coexist.

### Solver invocation (`models/structure.py`)

`ModelDefaults.__init__` (`structure.py:75-131`) **solves during construction**:
reads `max_time` from settings (default 5 — seconds, `structure.py:94`), calls
`self.solve(model_constraints, max_time)` and stores results
(`_process_solver_results`, `structure.py:133-160`: `timeout`, `z3_model` or
`unsat_core`, `z3_model_status`, `z3_model_runtime`, `satisfiable`, `solved`).

`solve` (`structure.py:235-292`):
1. `create_solver(self.settings)` — fresh solver per example.
2. `_setup_solver` (`structure.py:161-197`): iterates the four groups
   `[("frame"), ("model"), ("premises"), ("conclusions")]` asserting each constraint
   via `solver.assert_tracked(constraint, f"{group}{i+1}")` and recording it in
   `self.constraint_dict` for unsat-core reporting.
3. `solver.set_timeout(int(max_time * 1000))` — **max_time is seconds**, converted
   to ms (`structure.py:262`; the docstring wrongly says ms, see Divergences).
4. `result = solver.check()`; `sat` → `(False, model, True, runtime)`; `unsat` →
   `(False, unsat_core_labels, False, runtime)`; **any `unknown` → treated as
   timeout** `(True, None, False, runtime)` regardless of `reason_unknown()` — a
   deliberate soundness fix documented in a long comment (`structure.py:270-283`).
5. `finally: _cleanup_solver_resources()` (`structure.py:215-233`) — nulls
   `self.solver` and `self.z3_model` references... but note
   `_process_solver_results` runs *after* `solve` returns and re-sets `z3_model`;
   also `self.stored_solver` keeps the solver alive for the iterator.

Incremental solving: the adapters expose `push`/`pop`
(`z3_adapter.py:135-146`) but the core pipeline never calls them; instead the
iterator adds constraints to `stored_solver` and calls `re_solve`
(`structure.py:294-330` re-checks the same solver instance). There is no constraint
caching or cross-example incrementality; isolation is achieved by fresh solvers and
explicit cleanup.

### The Z3 adapter specifics (`solver/z3_adapter.py`)

- `assert_tracked` uses `z3.Bool(label)` + `solver.assert_and_track`
  (`z3_adapter.py:74-89`).
- `check` maps `z3.CheckSatResult` to strings via `SolverResult.from_z3`
  (`z3_adapter.py:91-104`).
- `unsat_core` maps tracking bools back to labels (`z3_adapter.py:117-131`).
- Quantifier/memory configuration in `_configure_quantifier_mode`
  (`z3_adapter.py:29-60`), applied to every solver instance.

### cvc5 adapter deltas (`solver/cvc5_adapter.py`)

Timeout option `tlimit-per` (`cvc5_adapter.py:242-248`); no `assert_and_track` — the
constraint is plain-`add`ed and unsat-core terms are mapped back to labels through a
3-layer lookup (Python `id`, cvc5 term id, string repr; `cvc5_adapter.py:167-220`);
diagnostic mode sets `produce-unsat-cores` + `cegqi`/`cegqi-bv`/`cegqi-full`,
performance mode sets `decision=stoponly`, `bv-eager-eval` + cegqi options
(`cvc5_adapter.py:66-88`); mode chosen by `_detect_unsat_core_requirement` from
`print_constraints`/`print_z3` settings (`registry.py:189-206`).

---

## 7. Bit-vector encoding of states

- A **state** is a bitvector of width `N` (setting `N`; logos default 16,
  `logos/semantic/core.py:40`). The state space is all `2^N` values, materialized as
  `all_states` (`models/semantic.py:124`); `MAX_N = 20` caps the width with measured
  RSS rationale in the comment (`semantic.py:31-44`).
- **Fusion** (mereological sum): bitwise OR — `bit_s | bit_t`
  (`models/semantic.py:239`).
- **Part-of**: `fusion(s, t) == t`, i.e. `s | t == t` (`models/semantic.py:306`).
  (Not bitwise-and as sometimes described; `s & t == s` would be equivalent, but the
  code uses the OR form.)
- **Null/full state**: `BitVecVal(0, N)` / `BitVecVal(2^N - 1, N)`
  (`semantic.py:122-123`).
- **Possible** is an uninterpreted predicate `possible: BitVec(N) -> Bool`
  (`logos/semantic/core.py:75-78`), constrained downward-closed under part-of by the
  frame constraint (`core.py:88-97`).
- **World**: `is_world(w) := possible(w) ∧ maximal(w)` where
  `maximal(w) := ∀x. compatible(x, w) → is_part_of(x, w)` and
  `compatible(x, y) := possible(x | y)` (`core.py:118-137`).
- **Atomic truthmaking**: uninterpreted functions
  `verify, falsify : BitVec(N) × AtomSort -> Bool` (`core.py:63-74`). Truth at a
  world: `∃x ⊑ w. verify(x, p)` — expanded to a `2^N`-way disjunction by the finite
  `Exists` (§5).
- **Model extraction**: post-sat, verifier/falsifier sets are computed by evaluating
  `verify(state, letter)` for every state in `all_states` against the Z3 model
  (`logos/semantic/proposition.py:206-228`, with the truth-evaluation helper
  `_evaluate_z3_boolean`).
- Display helpers turn bitvectors into fusions of atomic substates like `a.b.c`
  (`utils/bitvector.py:49-123`, `bitvec_to_substates`).

---

## 8. Extensibility seams: pluggable vs hard-coded

### Pluggable (the intended seams)

A new theory supplies exactly four things, wired through the `get_theory()` dict
convention (`theory_lib/imposition/__init__.py:104-109`):

```python
{"semantics": <SemanticDefaults subclass>,
 "proposition": <PropositionDefaults subclass>,
 "model": <ModelDefaults subclass>,
 "operators": <OperatorCollection>}
```

- **New operator (existing theory)**: subclass `Operator` with `name`, `arity`, the
  five semantic methods + `print_method`; add the class to the theory's
  `OperatorCollection`. Nothing else. Defined operators additionally implement
  `derived_definition` and get free expansion + circularity checking.
- **New theory**: subclass `SemanticDefaults` (declare primitives, frame
  constraints, `main_point`, `premise_behavior`/`conclusion_behavior`, the four
  dispatch methods), subclass `PropositionDefaults` (must provide
  `proposition_constraints` and post-sat interpretation), subclass `ModelDefaults`
  (printing/extraction), and provide operators. The core pipeline
  (`Syntax`/`ModelConstraints`/`ModelDefaults.solve`) is theory-agnostic.
- **New solver backend**: implement `TrackedSolverProtocol`, register a factory
  (`registry.register_backend_factory`, `registry.py:143-152`) — though in practice
  `create_solver` hard-codes the z3/cvc5 branch (`registry.py:171-181`), so a third
  backend requires editing `registry.py`, `expressions.py`'s module chooser, and
  the backend-name validation sets (`registry.py:74`, `backend.py:52-57`).

### Hard-coded (where modularity leaks)

1. **`\\top` / `\\bot`** are special-cased in four places: the parser
   (`utils/parsing.py:38`), `Sentence.__init__` (`sentence.py:92`),
   `store_types` (`sentence.py:238-240` via `self.name` comparison),
   `Syntax.build_sentence` (`syntax.py:117`), and `op_left_right`
   (`utils/parsing.py:106`). A theory cannot introduce another nullary operator
   without editing core.
2. **Parser fixes the notational regime**: unary-prefix/binary-infix-parenthesized
   is baked into `parse_expression`; a ternary primitive operator cannot be parsed
   (though `from_prefix` can represent one, and `infix` cannot round-trip it).
3. **The operator method shapes** (`true_at(*args, eval_point)` etc.) are a
   convention shared between each theory's semantics dispatchers and its operators —
   the core never sees them. The `eval_point` dict keys (`"world"`, `"time"`) are
   stringly-typed contracts; base-class print helpers already branch on their
   presence and runtime shape (`operators.py:155-175`).
4. **Settings keys** (`N`, `M`, `contingent`, `disjoint`, …) are stringly-typed and
   scattered; `SemanticDefaults` interprets `N`/`M`, theories interpret the rest.
5. **`ModelConstraints` assumes the countermodel framing** (premise/conclusion
   behaviors as constraint generators) — alternative queries (entailment via
   quantification, equivalence checking) must be encoded through those two lambdas.
6. **AtomSort is a process-global** (`atoms.py:21-38`) shared by all theories and
   examples in a process; sentence-letter Z3 consts are shared by name across
   examples. Isolation relies on fresh solvers, not fresh sorts.

---

## Doc/Source Divergences

Each item: what the doc says vs what the code does.

1. **`syntactic/README.md:113-133` operator example has the wrong method
   signatures**: it shows `true_at(self, world, sentence)` and accesses
   `sentence.arguments[0]`. Actual operators receive splatted `Sentence` arguments
   followed by an `eval_point` dict: `true_at(self, argument, eval_point)`
   (`logos/subtheories/extensional/operators.py:41-46`), and the semantics — not the
   operator — unpacks `arguments`. Porting from the README example would not run.
2. **`syntactic/README.md:222` claims `model = ModelConstraints(syntax,
   semantics)`**. Actual signature is `ModelConstraints(settings, syntax, semantics,
   proposition_class)` (`models/constraints.py:52-59`).
3. **`syntactic/README.md:57-58` shows `prefix: PrefixList = ["∧", "p", "q"]`** —
   flat, with a Unicode operator. Actual prefix lists nest each argument as a list
   and use LaTeX names: `["\\wedge", ["p"], ["q"]]` (parser output,
   `utils/parsing.py:32`; also the docstring inside `sentence.py:128-131` shows the
   same stale flat/Unicode form `["∧", "p", "q"]`). Unicode `∧` is additionally not
   resolvable: `apply_operator` only accepts `.isalnum()` atoms or registered
   operator names (`collection.py:113-125`).
4. **`ModelDefaults.solve` docstring says `max_time (int): Maximum solving time in
   milliseconds`** (`structure.py:242-247`); the code multiplies by 1000
   (`structure.py:262`) and the default comment says "Default 5 seconds timeout"
   (`structure.py:94`). `max_time` is in **seconds**.
5. **`Sentence.from_prefix` docstring claims its complexity "matches" `__init__`'s**
   (`sentence.py:410-417`): the helper computes nesting depth
   (`1 + max(children)`, `sentence.py:424-431`) while the parser computes
   `left + right + 1` for binary nodes (`utils/parsing.py:31`); they differ on any
   formula with complex subtrees on both sides.
6. **`solver/README.md:22-36` attributes the cvc5 speedup to `mbqi` + `enum-inst`
   options**; the shipped adapter sets neither — it configures
   `cegqi`/`cegqi-bv`/`cegqi-full` (+ mode-specific options)
   (`cvc5_adapter.py:66-88`). The README partially self-acknowledges this ("not
   that this abstraction layer's current cvc5 backend reproduces the same numbers"),
   but the specific option names in the README do not describe the adapter.
7. **`ModelConstraints.instantiate` docstring**: "This method should only be called
   after a valid Z3 model has been found" (`constraints.py:171-172`). It is in fact
   called from `ModelConstraints.__init__` (`constraints.py:77`) — *before* any
   solving. The note appears to be a stale copy from `interpret`.
8. **`Syntax` docstring for `initialize_types`** refers to updating
   `sentence.original_type` (`syntax.py:133-141`); no attribute of that name exists
   on `Sentence` — the real attributes are `operator`/`arguments`/
   `sentence_letter` (`sentence.py:254`).
9. **`docs/architecture/SYNTACTIC.md:123` says `parse_expression()` is "in
   `utils.py`"** — utils is a package; it lives in `utils/parsing.py:11`.
10. **`syntactic/README.md` "Automatic validation includes ... Type consistency
    validation"** (README lines ~186-192): no arity or type-consistency validation of
    parsed formulas exists; `is_syntactically_wff` checks only the head token
    (`formulas.py:15-76`), and arity errors surface as raw `TypeError` at dispatch
    time (§3).

## Improvement Opportunities

Concrete, cited weaknesses a re-design can fix structurally.

1. **Leftover-token loss in the parser**: `Sentence.prefix` ignores tokens not
   consumed by `parse_expression` (`sentence.py:139-141`; `utils/parsing.py:11-45`
   never checks emptiness on return). `"p q"` → `p`; `"\\wedge p q"` → unary
   `\\wedge p`. Silent acceptance of malformed input. A parser returning
   `(ast, rest)` with an end-of-input check eliminates the class of bug.
2. **Arity is never checked syntactically**: the parser decides unary-vs-binary from
   parentheses alone, `is_syntactically_wff` checks only heads
   (`formulas.py:15-76`), and `ArityError` is imported but never raised
   (`operators.py:20`; grep shows zero raise sites). `(p \\neg q)` parses fine and
   dies later as `TypeError: true_at() takes 3 positional arguments...` deep in
   constraint generation. Operator-aware post-parse validation (name → arity) is
   trivially available at `update_types` time.
3. **One mutable AST node with phase-dependent field meanings**: `operator` holds
   `None` → class → instance; `original_arguments` holds strings then `Sentence`s
   (`sentence.py:86-89` vs `syntax.py:120-124`); `arguments` likewise
   (`syntax.py:146-152`). Every consumer must know the current phase; nothing
   enforces ordering. In a typed port, the four lifecycle phases are four distinct
   types (parsed / operator-resolved / semantics-bound / interpreted).
4. **Cross-class `self` in `proposition_constraints`**: written as an instance
   method of the proposition class but invoked unbound with a `ModelConstraints`
   instance as `self` (`constraints.py:84-88`, `logos/semantic/proposition.py:43`).
   Works by attribute coincidence (`.semantics`, `.settings`). Should be a
   classmethod/static function with explicit parameters.
5. **Stringly-keyed operator identity**: instances are re-linked by
   `op_dict[some_type.name]` (`sentence.py:270-274`); collections silently
   first-wins on duplicate names (`collection.py:79-80`) despite a defined
   `DuplicateOperatorError`; unknown operators surface as bare `KeyError`
   (`collection.py:125`) despite `UnknownOperatorError`. Name collisions across
   composed subtheories are resolved by load order with no diagnostics.
6. **Dead semantic methods on `DefinedOperator`s**: expansion at `derive_type`
   (`sentence.py:207-222`) guarantees `sentence.operator` is primitive, so e.g.
   `ConditionalOperator.true_at/extended_verify`
   (extensional/operators.py:300-355) are unreachable on the solve path yet
   maintained by hand — duplicated semantics that can drift from the definition. A
   port should pick one mechanism (expansion *or* direct semantics) per operator.
7. **Circularity check runs after use**: `Syntax.__init__` parses sentences (which
   expands definitions, potentially infinitely) *before* `circularity_check`
   (`syntax.py:77-80`); a used circular definition hits Python recursion limits in
   `derive_type` (`sentence.py:222`) rather than the intended `RecursionError` with
   a cycle report (`syntax.py:225-232`). The check also calls
   `derived_definition(*[None]*n)` (`syntax.py:203-206`), which only works because
   definitions never inspect their arguments — an unstated contract.
8. **Dummy-semantics instantiation hack**: `derive_type` builds
   `operator('a')` (`sentence.py:218`) — passing the string `'a'` where a
   `SemanticDefaults` is expected — because expansion needs an instance but has no
   semantics yet. Type-unsound by construction; `derived_definition` should be a
   classmethod/static description.
9. **Exponential eager structures**: `all_states` materializes `2^N` `BitVecVal`s at
   semantics construction (`semantic.py:124`, MAX_N guard at 44); the finite
   `ForAll`/`Exists` expand to `(2^N)^k` substituted conjuncts per quantifier
   (`utils/z3_helpers.py:16-87`). This is a semantic choice (quantifier-free
   output), but the expansion is re-computed per call site with no sharing;
   `substitute`-based expansion of an already-expanded inner quantifier makes the
   nested case multiplicative in AST size. Mixed native/finite quantifier usage
   within one theory (native `z3.Exists` at `logos/semantic/proposition.py:169-177`
   vs finite elsewhere) also means the MBQI configuration matters unpredictably.
10. **Per-call dynamic backend dispatch**: every `And`/`BitVec`/`substitute` call
    re-resolves the backend module (`solver/expressions.py:17-31` — `_get_backend_
    module()` inside each of ~80 wrappers, itself calling `get_active_backend()`
    which reads `os.environ` on every call, `registry.py:90-121`). Meanwhile
    `backend.py` implements the cached version but `expressions.py` doesn't use it.
    Three overlapping access styles coexist: `z3_shim` (`__getattr__` shim),
    `solver.expressions` (wrappers), and direct `import z3` in adapters and some
    theories — the "transitional" shim (`z3_shim.py:12-13`) is the dominant style in
    theory code (`logos/semantic/core.py:11`).
11. **Process-global mutable state everywhere**: `AtomSort` cache
    (`atoms.py:21-38`), backend registry (`registry.py:16-22`), lifecycle hook list
    (`lifecycle.py:23`), plus the process-global construction guard required
    because Z3 AST construction is not thread-safe (`syntax.py:47-52`,
    `semantic.py:89-109`). The `Syntax` docstring itself documents the
    cross-thread `AtomSort` race ("two threads ... produce sentence letters that
    are not sort-compatible"). A port with per-run contexts removes the entire
    guard apparatus.
12. **Solve-in-constructor**: `ModelDefaults.__init__` runs the solver
    (`structure.py:126-131`), conflating construction with computation and forcing
    the `stored_solver`/`re_solve`/cleanup dance (`structure.py:254-255`,
    `215-233`, `294-330`) plus the iterator's partial duplication of model building
    (warning comment at `builder/example.py:182-185`).
13. **Duck-typing at API boundaries**: sentence letters validated by
    `hasattr(x, 'sort')` (`constraints.py:130-136`, with an f-string-less error
    message at line 134); `infix` type-switches on `hasattr(prefix, 'name')` /
    callable `.sort` (`sentence.py:168-180`); `total_fusion` distinguishes Z3
    arrays from Python sets by `hasattr(set_P, 'sort')` (`semantic.py:286-289`).
14. **`eval_point` as untyped dict**: keys `"world"`/`"time"` probed with
    `in`/`hasattr` heuristics in base-class printing (`operators.py:155-175`
    branches on `as_ast`/`__getitem__` shape to guess bimodal vs default worlds) —
    invariants held by convention across theories.
15. **`SolverResult` strings**: results are compared as the strings
    `"sat"/"unsat"/"unknown"` (`protocols.py:108-125`), and `from_cvc5` classifies
    by substring matching on `str(result)` (`protocols.py:139-152`) — fragile
    against any repr change; a closed enum is the obvious replacement.
