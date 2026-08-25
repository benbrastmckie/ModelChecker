# Core Data Structures, Utilities, Settings, and Registry/API Surface

Territory: `code/src/model_checker/models/`, `utils/`, `settings/`, `registry.py`, `api.py`,
`__init__.py`. All paths below are relative to `code/src/model_checker/` unless prefixed.
Every claim was verified against source on 2026-08-18; docs were treated as suspect and
cross-checked (see "Doc/Source Divergences").

## 1. The Core Object Graph

### 1.1 The canonical construction pipeline

The entire system is organized around one linear four-stage pipeline, executed per example.
The minimal, dependency-free statement of it is `utils/testing.py:12-71` (`run_test`), and the
production version is `builder/example.py` (`BuildExample._build_model_structure`,
builder/example.py:171-196):

```python
# utils/testing.py:272-287 (run_test body, identical shape in BuildExample)
example_syntax   = syntax_class(premises, conclusions, operator_collection)   # 1. Syntax
semantics        = semantic_class(settings)                                   # 2. Semantics
model_constraints = model_constraints(settings, example_syntax, semantics,
                                      proposition_class)                      # 3. ModelConstraints
model_structure  = model_structure(model_constraints, settings)               # 4. ModelStructure
```

followed by a fifth stage, interpretation (`builder/example.py:192-194`):

```python
sentence_objects = self.model_structure.premises + self.model_structure.conclusions
self.model_structure.interpret(sentence_objects)   # 5. Propositions attached to Sentences
```

Construction ORDER is strict and enforced only by convention (each constructor takes the
previous stage's product as an argument):

1. **`Syntax(premises, conclusions, operator_collection)`** — parses infix strings into a tree
   of `Sentence` objects (owned by the compiler-pipeline territory; consumed here).
2. **`SemanticsClass(settings)`** — a theory's subclass of `SemanticDefaults`
   (`models/semantic.py:47`). Builds the state space (`all_states`) and theory-specific Z3
   primitives/frame constraints in its own `__init__` after `super().__init__()`.
3. **`ModelConstraints(settings, syntax, semantics, proposition_class)`**
   (`models/constraints.py:51-102`) — bridges syntax and semantics; instantiates operators,
   mutates every `Sentence` (via `update_objects`), and materializes four constraint lists.
4. **`ModelStructureClass(model_constraints, settings)`** — a theory's subclass of
   `ModelDefaults` (`models/structure.py:24`). **Solving happens inside the constructor**
   (`models/structure.py:126`), not in a separate method call.
5. **`model_structure.interpret(sentences)`** (`models/structure.py:347-372`) — walks the
   sentence tree bottom-up and attaches a `Proposition` (theory subclass of
   `PropositionDefaults`) to each `Sentence` via `sent_obj.update_proposition(self)`
   (`syntactic/sentence.py:283-285`).

### 1.2 Ownership / reference graph

Arrows mean "holds a reference to" (field name in parentheses); citations are the assignment
sites.

```
BuildExample
  ├── .example_syntax      → Syntax                       (builder/example.py:174)
  ├── .model_constraints   → ModelConstraints             (builder/example.py:177)
  ├── .model_structure     → ModelStructure               (builder/example.py:186)
  ├── .settings_manager    → SettingsManager              (builder/example.py:154)
  └── .solver              → always None (see §10.2)      (builder/example.py:196)

ModelConstraints (models/constraints.py:51-102)
  ├── .syntax              → Syntax                       (constraints.py:61)
  ├── .semantics           → Semantics instance           (constraints.py:62)
  ├── .proposition_class   → Proposition CLASS (not inst) (constraints.py:63)
  ├── .settings            → merged settings dict         (constraints.py:64)
  ├── .premises/.conclusions → aliases into syntax        (constraints.py:68-69)
  ├── .sentence_letters    → list of Z3 ExprRef           (constraints.py:71, 118-138)
  ├── .operators           → {name: OperatorInstance}, each operator instance
  │                          holds → semantics            (constraints.py:74, 153-156)
  └── .frame/model/premise/conclusion/all_constraints     (constraints.py:80-102)

ModelDefaults (models/structure.py:74-131)
  ├── .model_constraints   → ModelConstraints             (structure.py:91)
  ├── .semantics           → model_constraints.semantics  (structure.py:98)
  ├── .syntax              → model_constraints.syntax     (structure.py:104)
  ├── .main_point/.all_states/.N → aliases into semantics (structure.py:99-101)
  ├── .premises/.conclusions/.sentence_letters → aliases into syntax (structure.py:106-108)
  ├── .proposition_class   → from model_constraints       (structure.py:111)
  └── .solver/.z3_model/... → solver state (see §2)       (structure.py:114-123)

Sentence (syntactic/sentence.py; mutated by three later stages)
  ├── .operator/.original_operator → Operator instance (after ModelConstraints.instantiate,
  │                                  sentence.py:256-281)
  └── .proposition         → Proposition instance (after ModelStructure.interpret,
                             sentence.py:283-285)

Proposition (models/proposition.py:41-72)
  ├── .sentence            → Sentence                     (proposition.py:55)
  ├── .model_structure     → ModelStructure               (proposition.py:56)
  ├── .model_constraints   → via model_structure          (proposition.py:69)
  ├── .semantics           → via model_constraints        (proposition.py:70)
  └── .N/.main_point/.settings/.sentence_letters → copied aliases (proposition.py:59-72)
```

### 1.3 Cycles

The graph is acyclic during stages 1-4 and becomes cyclic at interpretation time (stage 5):

- **Sentence ↔ Proposition**: `Sentence.proposition` points to a `Proposition` whose
  `.sentence` points back (`syntactic/sentence.py:285`, `models/proposition.py:55`).
- **ModelStructure → Sentence → Proposition → ModelStructure**: the structure holds
  premises/conclusions (aliases of the syntax's sentences), each interpreted sentence's
  proposition holds `model_structure` (`models/proposition.py:56`).
- **Operator → Semantics** is one-way (`constraints.py:153-156`); semantics holds no back
  reference to operators, constraints, or structure in the base class (a theory subclass may
  add one — `SemanticDefaults._reset_global_state`'s docstring anticipates a
  `self.model_structure` attribute, `models/semantic.py:181-205`).

There is deliberate **downward aliasing everywhere**: each later stage copies references out
of earlier stages into flat attributes on itself (e.g. `ModelDefaults.N` at
`structure.py:101`, `Proposition.settings` at `proposition.py:72`). A port should treat these
as *derived accessors*, not independent state.

### 1.4 A critical cross-class idiom: `proposition_constraints`

`ModelConstraints` generates per-atom constraints by calling a method **on the proposition
class with itself as the receiver**:

```python
# models/constraints.py:81-88
self.model_constraints = [
    constraint
    for sentence_letter in self.sentence_letters
    for constraint in self.proposition_class.proposition_constraints(
        self,             # <-- a ModelConstraints instance bound as `self`
        sentence_letter,
    )
]
```

Theory-side, the method is declared as an ordinary *instance* method of the proposition class
(`theory_lib/logos/semantic/proposition.py:43`:
`def proposition_constraints(self, sentence_letter)`), and its body only touches
`self.semantics` and `self.settings` — attributes that `ModelConstraints` happens to share
with `PropositionDefaults`. So the "proposition class" is used in two unrelated roles: (a) a
namespace for static per-letter constraint generation at constraint time (no proposition
instance exists yet), and (b) a real instantiable class at interpretation time. This is
duck-typed self-substitution; any port must model it as two separate functions (a
class-level `atomConstraints : Settings -> Semantics -> Letter -> [Constraint]` and an
instance constructor).

## 2. `ModelDefaults` / ModelStructure State and Mutation Timeline

`ModelDefaults` (`models/structure.py:24-933`, 933 lines) is both the solver driver and the
result presenter. Complete field inventory with write-points:

**Set once in `__init__` (structure.py:74-123), before solving:**

| Field | Value | Line |
|---|---|---|
| `COLORS`, `RESET`, `WHITE` | ANSI codes | 77-85 |
| `constraint_dict` | `{}` → filled per solve with `{label: constraint}` | 88, 182-195 |
| `model_constraints`, `settings` | ctor args | 91-92 |
| `max_time` | `settings.get("max_time", 5)` (seconds) | 94 |
| `expectation` | `settings.get("expectation", True)` | 95 |
| `semantics`, `main_point`, `all_states`, `N` | aliases of semantics | 98-101 |
| `syntax`, `start_time`, `premises`, `conclusions`, `sentence_letters` | aliases of syntax | 104-108 |
| `proposition_class` | from model_constraints | 111 |

**Initialized to sentinel then mutated (the mutable solver-state block, structure.py:113-123):**

| Field | Init | Mutated by | When |
|---|---|---|---|
| `solver` | `None` | `solve()` sets it twice (254, 259), `_cleanup_solver_resources()` nulls it (228) | always `None` again by the time the ctor returns |
| `stored_solver` | `None` | `solve()` (255) | survives cleanup; see caveat below |
| `timeout` | `False` | `_process_solver_results` (148) | after solve |
| `z3_model` | `None` | nulled in cleanup (229), then set by `_process_solver_results` (157) iff SAT | after solve |
| `unsat_core` | `None` | `_process_solver_results` (159) iff UNSAT | after solve |
| `z3_model_status` | `None` | `_process_solver_results` (149) — `True`=SAT | after solve |
| `z3_model_runtime` | `None` | via result tuple (150; computed 199-213, rounded to 4 dp) | after solve |
| `solved` | `False` | `True` (152) | after solve |
| `satisfiable` | `None` | `= z3_model_status` (151) | after solve |
| `result` | `None` | raw 4-tuple `(timeout, model_or_core, status, runtime)` (153) | after solve |

**Solve control flow** (`structure.py:126-131` inside `__init__`):
`solve()` runs synchronously in the constructor; `_process_solver_results()` stores the tuple;
then `if self.timeout or self.z3_model is None: return` — an unsat or timed-out structure is
still a fully-constructed object, distinguished only by these flags.

**Solver lifecycle inside `solve()`** (`structure.py:235-292`):
1. `self.solver = create_solver(self.settings)` (254) — solver A, never given constraints.
2. `self.stored_solver = self.solver` (255) — **stores solver A**.
3. `self.solver = self._setup_solver(model_constraints)` (259) — `_setup_solver` calls
   `create_solver` *again* (179) producing solver B, asserts all four constraint groups with
   tracking labels `frame1..`, `model1..`, `premises1..`, `conclusions1..` (184-195).
4. `set_timeout(int(max_time * 1000))` (262) — settings value is seconds, solver API is ms.
5. `check()`; SAT → `(False, model, True, rt)`; UNSAT → `(False, unsat_core, False, rt)`;
   UNKNOWN → **always** treated as timeout `(True, None, False, rt)` regardless of
   `reason_unknown()` (267-285; the long comment at 273-284 documents that Z3 reports
   "canceled", not "timeout", and that treating UNKNOWN as UNSAT would unsoundly report
   validity).
6. `finally: _cleanup_solver_resources()` (290-292) — nulls `self.solver` and `self.z3_model`
   (215-233). So after construction the *constrained* solver B is unreachable except through
   the discarded local, and `stored_solver` holds constraint-free solver A. The iterator's
   fallback (`iterate/constraints.py:52-58`) reaches for `stored_solver` when `solver` is
   `None` — i.e. it gets a solver with **no assertions** (flagged in §10.1; iterate is another
   agent's territory, but the defect originates here).

**Later mutations by other components** (not written by this class): `model_differences` and
`isomorphic_to_previous` are read defensively via `hasattr` (`structure.py:721, 733`) and are
written by the iterator. `re_solve()` (`structure.py:294-330`) asserts `self.solver is not
None` (309) — which is false after any normal construction, so `re_solve` only works if an
external party (the iterator) has re-installed a solver.

**Presentation surface** (all on the same class): `interpret` (347), `print_grouped_constraints`
(374), `print_constraints` (483), `build_test_file` (508), `recursive_print` (574),
`print_input_sentences` (602), `print_model` (668), `calculate_model_differences` (693,
returns `None` by default for theory override), `print_model_differences` (712),
`print_info`/`print_all` (794, 871), `extract_verify_falsify_state` (893-933, evaluates
`semantics.verify/falsify` over all `2^N × letters` pairs with `model_completion=True`).

## 3. `PropositionDefaults`

A proposition is the **semantic value of one sentence in one solved model** — the object that
knows how to compute and print truth values. `models/proposition.py` (122 lines):

- **Abstract-by-guard**: instantiating `PropositionDefaults` directly raises
  `NotImplementedError` (`proposition.py:43-45`, message from
  `utils/formatting.py:35` `not_implemented_string`).
- **Constructor** (`proposition.py:41-72`): takes `(sentence, model_structure)`; validates
  only that `model_structure` has a `.semantics` attribute (duck-typing, 47-52); then copies
  aliases: from structure — `N`, `main_point`; from sentence — `name`, `operator`,
  `arguments`, `sentence_letter`; from `model_structure.model_constraints` —
  `model_constraints`, `semantics`, `sentence_letters`, `settings` (55-72).
- **Identity**: `__hash__`/`__eq__` by `name` string only (`proposition.py:74-80`) — two
  propositions of the same formula in *different models* compare equal.
- **`set_colors`** (`proposition.py:82-123`): ANSI color computation for printing; also
  prints a warning to stdout when a top-level formula is neither true nor false (truth-value
  gap) — presentation logic living in the "data" base class.
- The real contract is completed by subclasses plus the `IProposition` protocol
  (`models/types.py:56-70`): `truth_value_at(eval_point) -> bool` and
  `print_proposition(eval_point, indent, use_colors)`. Theory examples add
  `find_proposition()` returning (verifiers, falsifiers) sets
  (`theory_lib/logos/semantic/proposition.py:41`: `self.verifiers, self.falsifiers =
  self.find_proposition()` in `__init__`).

**Relation to `Sentence` and `interpret()`**: `Sentence` is the *syntactic* object created at
stage 1 with `proposition = None` (`syntactic/sentence.py:103`). `ModelDefaults.interpret`
(`structure.py:347-372`) is stage 5: it no-ops if `z3_model is None` (363), recurses into
`sent_obj.arguments` first (bottom-up, so subformula propositions exist before parents'),
then calls `sent_obj.update_proposition(self)`, which is one line:
`self.proposition = model_structure.proposition_class(self, model_structure)`
(`sentence.py:283-285`). Proposition construction is therefore *eager per sentence node* and
happens exactly once per solved model — but nothing prevents calling `interpret` twice
(second call overwrites the propositions with fresh equal ones).

## 4. `SemanticDefaults`: the Base Semantics Contract

`models/semantic.py:47-417`. What the base class **provides for free**:

- **State space construction** (`semantic.py:110-139`): if `'N'` in settings — validated by
  `_validate_N` (141-179): must be `int` (bool excluded), `1 <= N <= MAX_N` where
  `MAX_N = 20` (`semantic.py:44`; the comment at 31-43 documents measured memory blow-up:
  the eager `all_states = [BitVecVal(i, N) for i in range(1 << N)]` list costs 275MB at N=16,
  3.5GB at N=20). Sets `full_state` (all ones), `null_state` (zero), `all_states`
  (all `2^N` BitVecVals). If `'M'` present and not None: `M`, `all_times = [IntVal(i) for i
  in range(M)]` (127-129).
- **Mereology over bitvectors**: `fusion` = bitwise OR (209-223); `is_part_of(s,t)` ⇔
  `fusion(s,t) == t` (282-293); `is_proper_part_of` (295-307); `non_null_part_of` (309-321);
  `total_fusion` (fold of fusion, 262-280); `product` (pairwise fusion of two sets, 323-341);
  `coproduct` (union closed under fusion, 343-359); Z3-set conversion helpers `z3_set` /
  `z3_set_to_python_set` (225-260).
- **Class-level general settings**: `DEFAULT_GENERAL_SETTINGS` (`semantic.py:78-86`):
  `print_impossible, print_constraints, print_z3, save_output, sequential, maximize` (all
  False) and `solver: "z3"`.
- **Global-state reset hook**: `_reset_global_state` (181-207), called first thing in
  `__init__` (113); base resets `_cached_values = {}`; subclasses MUST override and chain.
- **Iterator support**: `initialize_with_state(verify_falsify_state, sentence_letters)`
  (361-388) monkey-patches `self.verify`/`self.falsify` with closures that return pinned
  `BoolVal`s for known `(state, letter)` pairs and fall back to the originals otherwise
  (390-417).
- **Concurrency guard**: `__init_subclass__` (88-108) wraps every subclass `__init__` in
  `guard_construction` so the whole constructor (including theory-side Z3 work after
  `super().__init__()`) runs under the process-global single-thread guard (see §4.1).

What a **theory subclass must supply** (abstract-by-absence — nothing is declared abstract;
the base just sets `None` placeholders at `semantic.py:131-139` and other code dereferences
them):

| Member | Required shape | Consumed at |
|---|---|---|
| `DEFAULT_EXAMPLE_SETTINGS` | class dict, must include `N`, `max_time`, `expectation`, ... | `settings/settings.py:84` |
| `main_point` | dict, e.g. `{"world": w}` | `structure.py:99`, `proposition.py:60`; base sets `None` (semantic.py:132) |
| `frame_constraints` | list of Z3 BoolRef | `constraints.py:80`; base sets `None` (135) |
| `premise_behavior` | callable `Sentence -> BoolRef` | `constraints.py:89-92`; base sets `None` (138) |
| `conclusion_behavior` | callable `Sentence -> BoolRef` | `constraints.py:93-96` |
| `verify(state, letter)` / `falsify(state, letter)` | `-> BoolRef` | `semantic.py:383-388`, `structure.py:919-925` |
| `true_at` / `false_at` etc. | theory-specific | operators, propositions |
| `ADDITIONAL_GENERAL_SETTINGS` | optional class dict | `settings/settings.py:78-81` |

Reference implementation of the behaviors (`theory_lib/logos/semantic/core.py:107-108`):
`self.premise_behavior = lambda p: self.true_at(p, self.main_point)`;
`self.conclusion_behavior = lambda c: self.false_at(c, self.main_point)`.

Note: `ModelDefaults.__init__` reads `self.semantics.all_states` and `.N` unconditionally
(`structure.py:100-101`), so although `SemanticDefaults` treats `N` as optional
(`semantic.py:119`), **every theory usable with `ModelDefaults` must have `N`** — the
optionality is illusory in practice.

### 4.1 Concurrency contract (`models/concurrency.py`, 153 lines)

Model construction is single-threaded-only because all classes build Z3 AST nodes against the
one process-global Z3 context. `_ConstructionGuard` (`concurrency.py:61-116`) is a
process-global, thread-reentrant, fail-fast lock: same-thread re-entry increments a depth
counter; a second thread raises `ConcurrentConstructionError` (`concurrency.py:40`,
subclass of `RuntimeError`) immediately instead of segfaulting. Exposed as context manager
`single_threaded_construction` (119) and decorator `guard_construction` (138), applied to
`SemanticDefaults.__init__` (semantic.py:110), `ModelConstraints.__init__`
(constraints.py:51), `ModelDefaults.__init__` (structure.py:74), and — via
`__init_subclass__` on both base classes — every concrete subclass `__init__`. Process-level
parallelism (one model per process) is the sanctioned alternative. A port to a runtime with
real immutable terms can drop this entirely, but must preserve the *semantic* invariant it
protects: construction of one model is a single serialized transaction.

## 5. Settings System

### 5.1 Declaration and defaults

Settings are declared in **three places**:
1. `SemanticDefaults.DEFAULT_GENERAL_SETTINGS` (`models/semantic.py:78-86`) — base general
   settings shared by all theories.
2. Each theory's `DEFAULT_EXAMPLE_SETTINGS` class attribute (e.g.
   `theory_lib/logos/semantic/core.py:39-50`) and optional `ADDITIONAL_GENERAL_SETTINGS`
   (e.g. `theory_lib/imposition/semantic/core.py:104-106`).
3. A module-level fallback `DEFAULT_GENERAL_SETTINGS` in `settings/settings.py:414-421`
   (differs from #1 — see Divergences).

`SettingsManager.__init__` (`settings/settings.py:51-88`) composes: base general settings
copy + `ADDITIONAL_GENERAL_SETTINGS` overlay (75-81); `DEFAULT_EXAMPLE_SETTINGS` taken
directly from `semantic_theory["semantics"].DEFAULT_EXAMPLE_SETTINGS` (84). The
`global_defaults` constructor parameter is **accepted but never read** — dead (51-88; callers
pass it at `builder/example.py:154-160` and `builder/module.py:119`).

### 5.2 Precedence chain

`get_complete_settings(user_general, user_example, module_flags)`
(`settings/settings.py:385-411`), lowest to highest:

1. `DEFAULT_GENERAL_SETTINGS` (base + theory additional).
2. User module-level `general_settings` (only keys already in the general defaults are
   merged, 114-117).
3. `DEFAULT_EXAMPLE_SETTINGS` (theory).
4. User per-example settings (only keys in example defaults merged, 144-146).
5. Example settings dict **wholesale overwrites** general on key collisions (405-406:
   `combined = general.copy(); combined.update(example)`).
6. CLI flag overrides — highest (409, `apply_flag_overrides` 163-189).

Flag override subtleties (`settings/settings.py:191-274`): a real argparse namespace is
distinguished from a test mock by the presence of `_parsed_args` (200); only flags the user
*actually typed* override (extracted by re-scanning raw argv, 222-238); clustered short flags
(`-cn`) are parsed by argparse but **not detected** as user-provided, so they silently fail to
override — documented as a known gap in the comment at 214-220. Non-setting standard args
(`load_theory, upgrade, version, save, interactive, output_mode, sequential_files, z3, cvc5,
subtheory`) are whitelisted from warnings (253-255).

### 5.3 Unknown settings and validation

- Unknown setting: **printed warning, not an error** (`_warn_unknown_setting`,
  `settings/settings.py:276-301`) — unless `strict_mode=True`, then `UnknownSettingError`
  with a did-you-mean suggestion (286-292; error class `settings/errors.py:142-167`).
  Comparison mode suppresses warnings unless env `MODELCHECKER_VERBOSE=true`
  (`settings.py:31-34`, 294-297).
- `solver` must be `'z3'` or `'cvc5'` else `ValidationError` (`settings.py:148-155`).
- `N` validated twice: at settings layer (`_validate_n_setting`, `settings.py:338-364`,
  raising `ValidationError`/`RangeError`) and again at semantics construction
  (`models/semantic.py:141-179`, raising `SemanticError`); both import the single ceiling
  `MAX_N` from `models/semantic.py:44`.
- Settings error hierarchy (`settings/errors.py`): `SettingsError` base carrying
  `setting`/`suggestion`/`context` and formatting them into `__str__` (14-49); subclasses
  `ValidationError` (52), `TypeConversionError` (61), `RangeError` (86),
  `MissingRequiredError` (122), `UnknownSettingError` (142), `TheoryCompatibilityError` (170).
  `_validate_setting_type` (settings.py:303-336) exists but no caller in the merge path uses
  it (values are merged untyped except `solver` and `N`).

### 5.4 Setting inventory (name → meaning, defaults per theory)

General (base, `models/semantic.py:78-86`): `print_impossible` (show impossible states in
output), `print_constraints` (print constraint list), `print_z3` (dump raw Z3 model/core;
read at `structure.py:683`), `save_output`, `sequential`, `maximize` (compare theories),
`solver` (`"z3"`|`"cvc5"` backend). Fallback module set adds `align_vertically`
(`settings/settings.py:420`). Theory additional: `derive_imposition`
(imposition, `theory_lib/imposition/semantic/core.py:104-106`).

Example settings (union across shipped theories; per-theory defaults in parentheses as
logos / bimodal / exclusion / imposition, from `theory_lib/*/semantic/core.py`):

| Name | Meaning | Defaults |
|---|---|---|
| `N` | bit-width; state space is `2^N` | 16 / 2 / 3 / 3 |
| `M` | number of time points (temporal) | None / 2 / – / – |
| `contingent` | force atomic propositions contingent | True / False / False / False |
| `non_empty` | verifier/falsifier sets non-empty | True / – / False / False |
| `non_null` | null state not a verifier/falsifier | True / – / False / False |
| `disjoint` | distinct letters get disjoint subject-matter | True / False / False / False |
| `possible` | require possible states (exclusion only) | – / – / False / – |
| `fusion_closure` | closure constraint (exclusion only) | – / – / False / – |
| `max_time` | Z3 timeout in **seconds** (`structure.py:94, 262`) | 10 / 1 / 1 / 1 |
| `iterate` | number of models to find | False / 1 / 1 / 1 |
| `expectation` | expected result for tests (`check_result`, structure.py:332-345) | None / True / None / None |
| `solver` | backend override per example | 'z3' (logos only lists it in example settings) |

## 6. Utilities Inventory (`utils/`, module by module)

- **`utils/__init__.py` (64 lines)** — re-export hub; `__all__` at 36-65. Docstring still
  says "This package will replace the original utils.py module" (stale; migration done).
- **`parsing.py` (119 lines)** — genuinely core. `parse_expression(tokens) ->
  (prefix_list, complexity)` (`parsing.py:11-45`): recursive-descent over a token list;
  parenthesized ⇒ binary via `op_left_right` (48-119) which splits left/right around the
  main operator with a hand-rolled parenthesis counter; `token.isalnum()` ⇒ atom; `\`-prefixed
  ⇒ LaTeX operator, with `\top`/`\bot` special-cased as nullary (27-33). Mutates its input
  list (pop from both ends). Complexity = operator count. Consumed by
  `syntactic/sentence.py` (import at sentence.py:12).
- **`bitvector.py` (166 lines)** — core display glue for states.
  `binary_bitvector(bit, N)` (20); `int_to_binary(i, n) -> '#b...'` (42);
  `index_to_substate(i)` — bit index → letter name `a..z, aa, bb...` (49);
  `bitvec_to_substates(bv, N)` (68-122) — bitvector → fusion string like `"a.b"`, `"□"` for
  the null state, with layered fallbacks (`<z3-obj>`, `<unknown-...>`) for non-bitvector
  inputs (73-82); `bitvec_to_worldstate(bv)` (125-166) — value → letter label. Parsing is
  stringly (works off `sexpr()` text in hex/binary/decimal forms, 84-97). Reusable
  infrastructure, but the defensive fallbacks are incidental glue.
- **`z3_helpers.py` (104 lines)** — semantically load-bearing, not glue.
  `ForAll(bvs, formula)` / `Exists(bvs, formula)` (16-49, 52-85) implement quantification by
  **explicit expansion**: substitute every one of the `2^N` values for each variable and
  conjoin/disjoin. This is a core design decision (finite-domain grounding instead of Z3
  quantifiers) with exponential formula growth in the number of bound variables; used
  pervasively by theory constraint generators (e.g.
  `theory_lib/logos/semantic/proposition.py`). `safe_getattr` (88-104) — trivial getattr
  wrapper, glue.
- **`context.py` (65 lines)** — `isolated_z3_context()` (20-65): context manager that swaps
  the private `z3.z3._main_ctx` to a fresh `z3.Context()` and clears the cached `AtomSort`
  on entry and exit. C-level isolation between examples; prevents learned-lemma leakage
  (docstring cites 2-10x slowdowns). Reaches into Z3 private internals — a porting hazard to
  document, not an API to reproduce.
- **`formatting.py` (80 lines)** — `pretty_set_print` (12, sorted `{a, b}` rendering),
  `not_implemented_string` (35, canned abstract-class messages keyed on class name strings),
  `flatten` (60, recursive list flatten). Glue.
- **`version.py` (128 lines)** — `get_model_checker_version` (16-22): reads installed
  package metadata, bare `except:` → `"0.0.0-dev"` (24); `get_license_template` (29-128):
  returns GPL-3.0 license text, with a derivative-work variant. Incidental (project
  scaffolding for `builder/project.py`), not runtime infrastructure.
- **`api.py` (57 lines)** — theory-*unaware* lookups. `get_example(name, example_range)`
  (15-30): dict lookup with KeyError listing available names.
  `get_theory(name, semantic_theories)` (33-57): **if the mapping has exactly one entry,
  returns it regardless of the requested name** (51-52) — a surprising special case; else
  keyed lookup with KeyError. Deliberately never imports `theory_lib` (layering, docstring
  1-9).
- **`testing.py` (203 lines)** — `run_test` (12-71): the canonical pipeline in miniature
  (see §1.1), returns `model_structure.check_result()`. `TestResultData` (58-83): plain
  mutable record with `is_valid_countermodel()` (premises all true, conclusions all false).
  `run_enhanced_test` (85-203): same pipeline with detailed evaluation capture; wraps
  everything in broad `except Exception` handlers that stash the message instead of raising
  (194-198). Test infrastructure, reusable.
- **`types.py` (40 lines)** — aliases; at runtime Z3 types degrade to
  `solver.types.SolverExpr` / `Any` to stay backend-agnostic (13-22).

## 7. Registry / Theory Discovery

`registry.py` (218 lines) is a **generic mechanism with zero theory names in it** (module
docstring 1-19); the catalog lives in `theory_lib/__init__.py:63-69`
(`_THEORY_NAMES = ['bimodal', 'logos', 'exclusion', 'imposition']`).

- **Data model**: `TheoryEntry` (`registry.py:37-100`), `__slots__` of `name`, `module_path`,
  `adapter`, `_loaders`, `_resolved`. Each of `semantics/proposition/model/operators` may be
  a direct value or a zero-arg thunk; `_resolve` (64-72) calls plain callables once and
  memoizes, explicitly *not* invoking classes (`callable(value) and not isinstance(value,
  type)`). `as_theory_dict()` (90-97) returns the classic 4-key dict shape.
- **Module state**: `_REGISTRY: Dict[str, TheoryEntry]`, `_ORDER: List[str]`,
  `_DEFAULT_THEORY` (`registry.py:103-105`) — global mutable module-level state, with a
  test-only `_reset_registry_for_testing` (213-218).
- **Registration**: `register_theory(name, *, module_path, semantics, ..., adapter=None)`
  (108-151); duplicate name ⇒ `ValueError`, fail-fast (136-138). `set_adapter` (173-187) is
  deliberately *not* fail-fast on repeat (upper layers like `jupyter/` re-register display
  adapters). `set_default_theory`/`get_default_theory` (190-204); `iter_theories` (207-210).
- **Bootstrap**: importing `model_checker` imports `theory_lib` for side effect
  (`__init__.py:66`). `theory_lib._register_theories()`
  (`theory_lib/__init__.py:452-478`) registers each name with four thunks built by
  `_make_component_loader` (438-450); the four thunks of one theory share a cache dict so the
  theory module's `get_theory()` runs at most once. Registration is idempotent against
  re-execution (already-registered names skipped, 462-465). `AVAILABLE_THEORIES` is a view
  over `get_registered()` (482), and `'logos'` is marked default (486-490).
- **Lazy import machinery**: attribute access `theory_lib.logos` goes through module-level
  `__getattr__` (`theory_lib/__init__.py:~400-426`), which `importlib.import_module`s the
  subpackage on demand and caches it in `_theory_modules`.
- **Failure modes**: unknown name ⇒ `ValueError: Unknown theory 'x'. Available theories: ...`
  (`registry.py:159-170`). A *registered but broken* theory raises nothing at registration
  time (thunks are lazy); the `ImportError` surfaces re-wrapped as `AttributeError("Failed to
  import theory ...")` at the first `entry.semantics` access
  (`theory_lib/__init__.py:419-424`) — i.e. discovery errors are deferred to first use.
- **Consumers** (registry, not direct imports): `__main__.py:75`, `builder/runner.py:877`,
  `builder/project.py:118`, `jupyter/interactive.py:36-41`, `jupyter/utils.py:31`,
  `jupyter/unicode.py:286`.

## 8. Public API Surface

**`__init__.py` (67 lines)** — intended public contract per `__all__` (27-33):
modules `model`, `syntactic`; functions `ForAll`, `Exists`, `bitvec_to_substates`,
`get_example`, `get_theory`, `run_test`; classes `ModelConstraints`, `Syntax`.
`__version__` from installed metadata (22-24). Two problems: `"model"` names a module that no
longer exists (renamed to `models/` — `from model_checker import *` would raise
`AttributeError`), and `get_theory` in `__all__` is the *upper-layer* `api.get_theory`
(imported at 56), while `utils.get_theory` is a different function with a different
signature — same name, two contracts.

**`api.py` (90 lines)** — the "upper layer" module explicitly permitted to import
`theory_lib` (docstring 1-13; layering contract in
`theory_lib/docs/THEORY_ARCHITECTURE.md`). Exports (`__all__`, api.py:19): `get_theory(name,
semantic_theories=None)` (22-62; auto-loads the theory's `semantic_theories` mapping via a
function-local `theory_lib` import, then delegates to the pure `utils.api.get_theory`;
wraps `ImportError` into `ValueError` listing available theories, 50-58),
`get_semantic_theories(theory_name)` (65-79), `get_available_theories()` (82-90).

**What leaks**: everything, in practice. There is no `_`-prefixing discipline at package
boundaries — `model_checker.models.structure.ModelDefaults`, `model_checker.registry.*`,
`model_checker.settings.SettingsManager` are all imported directly by `builder/`, `iterate/`,
`jupyter/`, and theory code, and `models/__init__.py`/`settings/__init__.py`/
`utils/__init__.py` re-export their full contents with `__all__` lists
(`models/__init__.py:34-47`, `settings/__init__.py:13-17`, `utils/__init__.py:36-65`). The
*de facto* API is the four-class pipeline (§1.1) + `SettingsManager` + registry + the
`get_theory()` dict shape `{semantics, proposition, model, operators}`
(`registry.py:90-97`).

## 9. Error Handling Philosophy

**Custom hierarchies** exist per package: `models/errors.py` — `ModelError` root with
`ModelConstraintError`, `ModelSolverError`, `ModelInterpretationError`, `ModelStateError`,
`SemanticError`, `PropositionError` (errors.py:8-79; plain classes, no extra fields);
`settings/errors.py` — richer, with `setting`/`suggestion`/`context` fields (see §5.3);
`ConcurrentConstructionError` (`models/concurrency.py:40`).

**Fail-fast, as practiced** (genuine examples):
- `SemanticDefaults._validate_N` raises *before* the memory-exhausting allocation
  (`models/semantic.py:141-179`), with an explanatory message; duplicated defensively at the
  settings layer (`settings/settings.py:338-364`).
- Registry duplicate registration ⇒ immediate `ValueError` (`registry.py:136-138`).
- `extract_verify_falsify_state` raises `ModelStateError` when no model exists
  (`structure.py:906-912`).
- `solve()` wraps solver `RuntimeError` into `ModelSolverError` with cause chaining
  (`structure.py:287-289`); construction guard raises instead of racing
  (`concurrency.py:82-94`).
- `PropositionDefaults`/direct instantiation ⇒ `NotImplementedError` (`proposition.py:43-45`);
  `ModelConstraints._load_sentence_letters` type-checks letters (`constraints.py:118-138`,
  though the error message has an unformatted f-string bug: line 136 lacks the `f` prefix, so
  it prints the literal `{letter}`).

**Where errors are swallowed or softened** (also genuine, contradicting the stated
philosophy):
- `utils/version.py:24` — bare `except:` returning `"0.0.0-dev"`.
- `utils/testing.py:194-198, 197-203` — `run_enhanced_test` catches `Exception` broadly twice
  and converts to a stored message.
- `utils/bitvector.py:73-82, 162-166` — unparseable inputs become placeholder strings
  (`"<z3-obj>"`, `"<unknown-...>"`) rather than errors.
- Unknown settings ⇒ `print()` warning by default (`settings/settings.py:294-301`); unknown
  CLI flags ⇒ `print()` warning (`settings.py:274`). Warnings go to stdout, not `warnings`/
  `logging`.
- `ModelDefaults.interpret` silently returns when there is no model (`structure.py:362-364`);
  `ModelConstraints.inject_z3_values` silently no-ops if the theory lacks the hook
  (`constraints.py:203-206`).
- `check_result` reads `self.settings["expectation"]` raw (`structure.py:345`) — KeyError if
  a caller bypassed the settings pipeline, even though line 95 computed a defaulted
  `self.expectation` that this method then ignores.

Summary for a port: errors that would produce *wrong logical verdicts* are handled strictly
(UNKNOWN-as-timeout, N validation, state extraction); errors in *presentation and metadata*
are absorbed with fallbacks; configuration errors are warnings by default with an opt-in
strict mode.

## Doc/Source Divergences

1. **`models/types.py:16`**: `from .semantic import Semantics` (TYPE_CHECKING) — no class
   `Semantics` exists in `models/semantic.py` (only `SemanticDefaults`); the annotation
   `'Semantics'` used in `constraints.py:56` and `types.py` names a phantom type. Silent at
   runtime; breaks strict type checking.
2. **`__init__.py:28`**: `__all__` lists module `"model"` — removed/renamed to `models/`
   (`ls model.py` ⇒ no such file); `from model_checker import *` fails. Comment at line 29
   also still says "utils.py".
3. **`SemanticDefaults` docstring** (`models/semantic.py:73-74`) declares
   `premise_behavior (str)` / `conclusion_behavior (str)`; in reality they are callables
   applied to sentences (`constraints.py:89-96`;
   `theory_lib/logos/semantic/core.py:107-108`).
4. **`ModelConstraints.instantiate` docstring** (`constraints.py:171-173`): "should only be
   called after a valid Z3 model has been found" — false; it is called from
   `ModelConstraints.__init__` (line 77) *before any solving*. Copy-paste from
   `ModelDefaults.interpret`, where the statement is true.
5. **`models/README.md` usage example**: calls `semantics.generate_constraints()` — no such
   method exists anywhere in `models/`; shows `{"N": 3, "max_time": 5000}` suggesting
   milliseconds, but `max_time` is seconds (`structure.py:94, 262`). Also
   `SemanticDefaults(settings)` is instantiable in the example, which is fine, but
   `ModelDefaults(model_constraints, settings)` there uses an undefined variable.
6. **`utils/README.md`** header links to `../syntactic.py`; `syntactic` is a package.
7. **`builder/example.py:198-215`**: `get_result` annotated `-> Tuple[bool, Optional[Any],
   str]` and docstring says tuple; it returns a dict.
8. **`utils/bitvector.py:42-43`**: `int_to_binary` docstring says "Converts a hexadecimal
   string to a binary string"; it converts an `int` to a `#b`-prefixed padded binary string.
9. **Two divergent "general settings" default sets**: `models/semantic.py:78-86` (has
   `sequential`, `solver`; no `align_vertically`) vs `settings/settings.py:414-421` (has
   `align_vertically`; no `sequential`/`solver`). The settings-module one is only a fallback
   passed as the dead `global_defaults` parameter, so the divergence is currently latent.
10. **`ModelDefaults` class docstring** (`structure.py:44-55`) documents attribute `result
    (tuple)` and `solver` as if stable; omits `stored_solver`, `unsat_core`,
    `constraint_dict`, and the fact that `solver` is always `None` post-construction.

## Improvement Opportunities

1. **`stored_solver` holds the wrong solver (likely bug)**. `solve()` assigns
   `stored_solver` at `structure.py:255` *before* `_setup_solver` creates a second,
   constraint-loaded solver at 259 (via a second `create_solver` at 179). After cleanup nulls
   `self.solver` (228), the only surviving handle — `stored_solver` — is the solver that
   never received any assertions. `iterate/constraints.py:52-58` falls back to exactly this
   handle. Either `_setup_solver` should reuse the already-created solver, or
   `stored_solver` should be assigned *after* setup.
2. **Solving in the constructor**. `ModelDefaults.__init__` performs the entire solve
   (`structure.py:126`), so object construction can take `max_time` seconds and a
   "constructed" object may represent failure (`timeout`/`z3_model is None`). Ports should
   separate `build : Constraints -> Problem` from `solve : Problem -> Result` and make the
   result a sum type (SAT model / unsat core / timeout) instead of the 10-field mutable flag
   cluster of §2 (`structure.py:113-123` plus the raw positional 4-tuple `result`).
3. **Four-phase in-place mutation of `Sentence`** (`syntactic/sentence.py:30-34`,
   fields flipped from `None` by `update_types`/`update_objects`/`update_proposition`) is the
   deepest temporal coupling in the system: the *type* of `original_operator` changes from
   `str` to operator-class to operator-instance across stages. A port should model the stages
   as distinct immutable types (ParsedSentence → TypedSentence → BoundSentence →
   InterpretedSentence).
4. **`proposition_constraints` self-substitution** (§1.4, `constraints.py:82-88`): an
   instance method invoked with a foreign object as `self`, sound only because
   `ModelConstraints` and `PropositionDefaults` share attribute names. Should be a
   classmethod/static function taking an explicit context object.
5. **God object `ModelDefaults`** (933 lines): solver lifecycle, result state, ANSI color
   management (in the constructor, `structure.py:77-85`), five print methods, test-file
   generation (508-572), and diff presentation (693-792) in one class. The printing layer
   also duplicates the group-membership logic three ways using O(n²) `in`-list scans
   (`structure.py:432-435, 458-466`) when `constraint_dict` already has the grouping.
6. **Monkey-patching as an iteration mechanism**: `initialize_with_state` replaces bound
   `verify`/`falsify` attributes with closures (`semantic.py:383-388`); combined with
   `inject_z3_values`' optional hook (`constraints.py:180-206`), the semantics object's
   behavior depends on hidden call history. Model this as an explicit
   `ConstrainedSemantics` wrapper/value.
7. **Abstract-by-`None` contract**: the theory contract of §4 is enforced nowhere
   (`main_point = None`, `frame_constraints = None` at `semantic.py:131-139`; failures
   surface as `TypeError: 'NoneType' is not callable` deep in `ModelConstraints`). An ABC or
   protocol check at `ModelConstraints.__init__` would fail at the boundary.
8. **Dead/vestigial code**: `SettingsManager.__init__`'s unused `global_defaults` parameter
   (`settings/settings.py:51`); `ModelDefaults.expectation` computed then bypassed
   (`structure.py:95` vs 345); `safe_getattr` (`utils/z3_helpers.py:88`) not exported in
   `utils/__init__.__all__`; commented-out `self.old_z3_models` (`constraints.py:65`);
   `_validate_setting_type` with no production caller (`settings.py:303`).
9. **Stringly-typed seams**: unsat-core mapping keys by `str(constraint_label)`
   (`structure.py:420`); `not_implemented_string` dispatching on class-name strings
   (`formatting.py:35-57`); `bitvec_to_substates` parsing `sexpr()` text (`bitvector.py:
   84-97`); proposition equality by formula name only (`proposition.py:74-80`), which
   conflates same-named propositions across models.
10. **Settings merge silently drops unknown-but-typed keys**: valid-key intersection filters
    (`settings.py:114, 144`) mean a misspelled setting is warned about *and discarded*, so
    runs proceed with defaults — combined with print-based warnings, misconfiguration is
    easy to miss. Strict mode exists (`settings.py:61, 286-292`) but nothing in the
    production path enables it (only `builder` tests); a port should make strictness the
    default per the project's own fail-fast principle.
11. **Explicit-expansion quantifiers** (`utils/z3_helpers.py:16-85`) generate `2^(N·k)`-leaf
    formulas for k bound variables. This is a deliberate semantic choice (decidable,
    model-completion-friendly) that a port must preserve *as a semantics*, but the
    representation invites sharing/memoization; today every call re-expands.
12. **`utils/api.get_theory` single-entry bypass** (`utils/api.py:51-52`): with exactly one
    registered variant, any requested name — including a wrong one — silently returns it.
    Fail-fast would check the name always.
