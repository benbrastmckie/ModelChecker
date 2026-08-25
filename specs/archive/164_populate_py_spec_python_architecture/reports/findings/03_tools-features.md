# Tools & Features: Iteration, Output, Comparison (post-first-model machinery)

Scope: everything that happens after a first Z3 model is found — the model iterator
(`code/src/model_checker/iterate/`), the output subsystem (`code/src/model_checker/output/`),
the display/printing contract, saving, `--maximize` comparison, and progress feedback.
All paths below are relative to `code/src/model_checker/` unless otherwise noted.
Line numbers verified against source on 2026-08-18.

---

## 1. Model iteration algorithm (finding the *next distinct* model)

### Top-level flow

The live iteration loop is `BaseModelIterator.iterate_generator()` in `iterate/core.py:140-481`.
Per attempt it does, in order:

1. **Constraint generation** — `self.constraint_generator.create_extended_constraints(self.found_models)`
   (`iterate/core.py:249`), which calls `_create_difference_constraint([model])` once **per previous
   model** and returns a list of constraints (`iterate/constraints.py:86-103`).
2. **Satisfiability check** — `check_satisfiability(extended_constraints)` *permanently adds* the
   constraints to a persistent solver and calls `solver.check()`
   (`iterate/constraints.py:105-125`). There is **no push/pop**; exclusion constraints accumulate
   monotonically in the solver across the whole iteration session.
3. **Model extraction** — `constraint_gen.get_model()` (`iterate/constraints.py:127-136`).
4. **Structure rebuild** — `ModelBuilder.build_new_model_structure(new_model)` (`iterate/models.py:34`),
   see §2.
5. **Validity filter** — a structure with `len(z3_world_states) == 0` is rejected as invalid
   (`iterate/core.py:312-323`).
6. **Isomorphism check** — `IsomorphismChecker.check_isomorphism(...)` (`iterate/core.py:326-328`),
   see §3. If isomorphic, the model is *not* yielded; a "stronger constraint" is requested and the
   loop retries (`iterate/core.py:330-343`).
7. **Accept** — model appended to `found_models`/`model_structures`, differences computed, yielded
   (`iterate/core.py:358-400`).

### The exact difference constraint

"Distinct" at the constraint level is **theory-defined**. Two layers exist:

**Generic layer** (`ConstraintGenerator._create_difference_constraint`,
`iterate/constraints.py:149-185` → `_create_state_difference_constraints`, lines 187-232):
for each state `s` in `range(N)` — note: `range(N)`, not `range(2**N)`, see Divergence D6 — it
evaluates `semantics.is_world(s)` in the previous model and builds the flipped literal:

```python
prev_value = prev_model.eval(is_world_expr, model_completion=True)
if is_true(prev_value):
    constraints.append(z3.Not(is_world_expr))   # was world -> must not be
else:
    constraints.append(is_world_expr)            # was not world -> must be
```

The per-model constraint is the **disjunction** `z3.Or(valid_constraints)`
(`iterate/constraints.py:184`): "at least one state flips its is-world status relative to
previous model M". This is a structured *difference-on-designated-predicates* constraint, not a
negation of the full Z3 model.

**Theory layer** — each theory subclass overrides `_create_difference_constraint`. The important
fact: **the generic layer is what actually runs.** `ConstraintGenerator` is a standalone class,
and `create_extended_constraints` calls `self._create_difference_constraint`, i.e., the
*generic* one — the theory subclass methods on `BaseModelIterator`
(`iterate/core.py:709-758`, all `raise NotImplementedError`) are **never invoked by the live
loop**, because `BaseModelIterator` delegates to its `constraint_generator` component, not to
`self`. The theory overrides in e.g. `theory_lib/logos/iterate.py:215-258` are reachable only if
a theory calls them itself. See Improvement I2.

For reference, the logos theory's (currently bypassed) constraint policy
(`theory_lib/logos/iterate.py:215-258`) is a smart-ordered disjunction per previous model:
1. world-count differs — `z3.Sum([z3.If(semantics.is_world(s),1,0) for s in range(2**N)]) != prev_count`
   (`theory_lib/logos/iterate.py:260-274`);
2. any `verify(s, atom)`/`falsify(s, atom)` value differs (`lines 276-309`);
3. capped at 5 disjuncts, structural `is_part_of` differences fill the remainder (`lines 311-327`);
then `z3.And` over per-model `z3.Or`s (`line 257`).

Imposition adds ternary `imposition(x,y,z) != prev` disjuncts over all `(2**N)**3` triples
(`theory_lib/imposition/iterate.py:369-428`). Exclusion subclasses `LogosModelIterator` and adds
witness-structure constraints (`theory_lib/exclusion/iterate.py:19-232`).

### Definition of "distinct"

Two-tier: (a) *syntactic difference* on designated semantic predicates (`is_world`, and in theory
subclasses `verify`/`falsify`/`is_part_of`/`imposition`) enforced by solver constraints;
(b) *semantic distinctness up to isomorphism* enforced post-hoc by the NetworkX graph check (§3).
A model that satisfies (a) but fails (b) is counted as "isomorphic skipped" and never yielded.

There is also an unused generic utility `create_difference_constraint(old_model, variables)` in
`iterate/z3_utils.py:10-46` (`z3.Or(*[var != old_value ...])`) with `find_next_model` using
`solver.push()/pop()` (`iterate/z3_utils.py:78-116`) — a cleaner pattern than the live
accumulate-forever approach, but not called anywhere in the live path.

---

## 2. Iterator architecture

### Class inventory in `iterate/`

| Class | File | Role |
|---|---|---|
| `BaseModelIterator` (live) | `iterate/core.py:46` | Orchestrator; owns component objects; hosts `iterate()`/`iterate_generator()` |
| `IteratorCore` | `iterate/iterator.py:26` | Init-time validation, settings, stats containers; its own `iterate()` (line 93) is dead/broken (see I4) |
| `BaseModelIterator` (abstract) | `iterate/base.py:15` | **Dead code** — never imported anywhere (`iterate/__init__.py:37` exports the `core.py` one) |
| `ConstraintGenerator` | `iterate/constraints.py:22` | Persistent solver + difference constraints |
| `ModelBuilder` | `iterate/models.py:23` | Rebuilds a `ModelStructure` from a raw Z3 model |
| `DifferenceCalculator` | `iterate/models.py:320` | Generic diff dict between two structures |
| `ModelGraph`, `IsomorphismChecker` | `iterate/graph.py:36, 357` | Graph encoding + isomorphism detection |
| `IterationStatistics`, `TerminationManager`, `ResultFormatter` | `iterate/metrics.py:15, 90, 179` | Stats, stopping conditions, (mostly unused) formatting |
| `SearchStatistics`, `IterationReportGenerator` | `iterate/statistics.py:10, 72` | Per-search records + final "ITERATION REPORT" |
| `IteratorBuildExample` + `create_with_z3_model` | `iterate/build_example.py` | **Dead code** — no callers outside its own module |
| errors hierarchy | `iterate/errors.py` | `IterateError` base with `context` dict; 7 subclasses |
| `types.py` | `iterate/types.py` | Large aspirational type/protocol vocabulary (`IterationStrategy`, `StrategyType`, `IterationConfig` …) — nothing in `iterate/` implements or consumes the protocols |

`BaseModelIterator.__init__` (`iterate/core.py:61-118`) wraps an `IteratorCore` (which validates
that `build_example.model_structure.z3_model_status` and `z3_model` exist,
`iterate/iterator.py:35-57`), aliases its state (`found_models`, `model_structures`, counters),
then instantiates the components. Progress: it picks up `build_example._unified_progress` if the
runner attached one (`iterate/core.py:104`), else installs a `NoOpProgress` stub (lines 108-113).

### What a theory must provide

Each theory ships an `iterate.py` module (canonical structure per project CLAUDE.md) exposing:

- A subclass of `BaseModelIterator` implementing:
  - `_calculate_differences(new, prev)` — theory-aware diff dict (e.g. `theory_lib/logos/iterate.py:52`)
  - `_create_difference_constraint(previous_models)` (`logos/iterate.py:215`)
  - `_create_non_isomorphic_constraint(z3_model)` (`logos/iterate.py:329` — stub `z3.BoolVal(True)`)
  - `_create_stronger_constraint(isomorphic_model)` (`logos/iterate.py:345` — stub `z3.BoolVal(True)`)
  - optionally an `iterate_generator()` override that post-processes yielded models
    (logos merges theory diffs into `model.model_differences`, `logos/iterate.py:361-412`)
- Module-level functions:
  - `iterate_example(example, max_iterations=None) -> List[ModelStructure]` (`logos/iterate.py:414`)
  - `iterate_example_generator(example, max_iterations=None)` marked with the attribute
    `iterate_example_generator.returns_generator = True` (`logos/iterate.py:470`) — the runner
    detects this flag to choose the incremental display path.

Discovery: `ModelRunner._discover_iteration_function` imports the theory package and prefers
`iterate_example_generator` over `iterate_example` (`builder/runner.py:885-891`); raises
`ImportError` if neither exists.

Subclass hierarchy in practice: `LogosModelIterator` (`logos/iterate.py:36`),
`ExclusionModelIterator(LogosModelIterator)` (`exclusion/iterate.py:19`),
`ImpositionModelIterator(BaseModelIterator)` (`imposition/iterate.py:34`),
`BimodalModelIterator(BaseModelIterator)` (`bimodal/iterate.py:31`).

### Model rebuild for MODEL 2+ (`ModelBuilder.build_new_model_structure`, `iterate/models.py:34-179`)

The next Z3 model cannot simply be wrapped: propositions/constraints must be *re-solved* under
the concrete values the iterator found. The builder:

1. creates a fresh `Syntax(premises, conclusions, operators)` and a fresh semantics instance
   `semantics_class(settings)` — explicitly **no state transfer** (`iterate/models.py:57-66`);
2. builds fresh `ModelConstraints(settings, syntax, semantics, proposition_class)` (lines 68-75);
3. creates a `temp_solver`, adds all base constraints, then **pins the new model's concrete
   values as constraints**: for every state in `range(2**semantics.N)` it asserts
   `is_world(state)` / `Not(is_world(state))` and (if present) `possible(state)` to match
   `z3_model.eval(..., model_completion=True)` (lines 89-106); likewise pins
   `verify(state, atom)` / `falsify(state, atom)` for every sentence letter (lines 108-128);
4. replaces `model_constraints.all_constraints = list(temp_solver.assertions())` (line 131) and
   constructs `model_structure_class(model_constraints, settings)`, which re-solves (now trivially
   sat, forced to the intended model) (lines 133-141);
5. calls `model_structure.interpret(premises + conclusions)` (lines 143-145).

Failures raise `ModelExtractionError` (`iterate/models.py:149-179`).

---

## 3. Isomorphism / graph handling

Library: **NetworkX** (`import networkx as nx`, `iterate/graph.py:8`), guarded by a `try/except
ImportError` setting `HAS_NETWORKX` (`iterate/graph.py:29-33`) — though note the *unconditional*
top-level `import networkx as nx` at line 8 makes the guard at 29-33 unreachable-as-fallback: if
networkx is missing the module import itself fails (Divergence D7).

### Graph encoding (`ModelGraph._create_graph`, `iterate/graph.py:61-165`)

- Nodes: one per entry of `model_structure.z3_world_states`, keyed by enumeration index `i`,
  with attributes `world_index`, `state`, plus a stringified truth value per sentence letter,
  computed via `z3_model.eval(semantics.true_at(letter_sentence, world))` (lines 96-121).
- Edges: for each world pair `(i, j)`, `semantics.accessible(i, j)` evaluated in the model adds a
  directed edge `relation='accessible'` (lines 130-149); bimodal `earlier` relation handled via
  `_add_theory_specific_edges` (lines 167-189, 240-258).
- Note the encoding indexes worlds by list position (`G.add_node(i, ...)`) and calls
  `accessible(i, j)` with *indices*, not the actual state bitvectors — correctness relies on
  world-state == index alignment (see I8).

### The check (`IsomorphismChecker`, `iterate/graph.py:357-543`)

`check_isomorphism(new_structure, new_model, previous_structures, previous_models)`
(`iterate/graph.py:365`) builds a `ModelGraph` for the candidate, lazily builds/caches graphs for
all previous models (`self.model_graphs`), and compares pairwise:

1. cache lookup keyed by pair of invariant hashes (`_generate_graph_cache_key`, line 502;
   `get_invariant_hash` at line 191 hashes node/edge counts, degree sequences, node-property
   distribution, triangle counts via sha256 of sorted JSON);
2. quick structural filter: node count, edge count, degree sequence (`_graphs_structurally_compatible`,
   lines 452-480);
3. full check: `nx.is_isomorphic(g1, g2)` (`iterate/graph.py:494`) — **called with no
   `node_match`/`edge_match`**, so proposition truth-value node attributes and relation edge labels
   are ignored in the definitive check; two models with identical shape but different proposition
   valuations are declared isomorphic (see I7).

All exceptions in checking degrade to "not isomorphic" (`iterate/graph.py:467-470, 447-450`).

### Escape hatches / performance limits

- If isomorphic, the loop requests `create_stronger_constraint(isomorphic_model)`
  (`iterate/core.py:340`), which delegates to the generic `_create_non_isomorphic_constraint`
  (`iterate/constraints.py:138-147` → 234-294): same is-world-flip disjunction, evaluated
  against the isomorphic model. The constraint is appended to `extended_constraints` and (via the
  next `check_satisfiability`) added to the persistent solver.
- Budget caps: per-model-search timeout `max_time` (§5); `max_invalid_attempts` (default 20)
  consecutive invalid models (`iterate/core.py:182`); `TerminationManager.should_terminate` adds a
  lack-of-progress rule — stop when `checked > 10 * max_iterations` with fewer than half the
  models found (`iterate/metrics.py:137-138`).
- Settings named `iteration_attempts` / `escape_attempts` exist **only in documentation**, not in
  code (see Divergence D3).

---

## 4. Model differences

### Computation

Two computations run for each accepted model:

1. **Generic**: `DifferenceCalculator.calculate_differences(new, prev)`
   (`iterate/models.py:323-356`, called at `iterate/core.py:378-383`) produces:

```python
{
  "world_changes":    {"added": [...], "removed": [...], "total_change_count": int},
  "possible_changes": {"added": [...], "removed": [...], "total_change_count": int},
  "atomic_changes":   {...},        # placeholder — always empty (models.py:451-463)
  "impossible_state_changes": {...} # only if changed (models.py:476-490)
}
```

   computed by set difference over `z3_world_states` / `z3_possible_states`
   (`iterate/models.py:373-405`). The result is stored on the structure:
   `new_structure.model_differences = differences` (`iterate/core.py:386`).

2. **Theory-specific**: the theory's `iterate_generator` override recomputes and *merges*. Logos
   (`theory_lib/logos/iterate.py:85-212, 361-412`) produces:

```python
{
  "worlds":          {"added": [...], "removed": [...]},
  "possible_states": {"added": [...], "removed": [...]},
  "verify":   {"A": {"a.b": {"old": False, "new": True}, ...}, ...},
  "falsify":  {...},
  "parthood": {"a ⊑ a.b": {"old": ..., "new": ...}, ...},
  "atomic_changes": {"verify": {...}, "falsify": {...}}  # display-shaped copy, lines 368-399
}
```

   State keys are human-readable fusion names via `bitvec_to_substates(state, N)`
   (`logos/iterate.py:160-183`). Theories may instead implement
   `detect_model_differences(previous)` on the structure, which `_calculate_differences` prefers
   (`logos/iterate.py:73-80`); the base `ModelDefaults.calculate_model_differences` returns `None`
   ("use generic") (`models/structure.py:693-710`).

### Display

The runner calls `structure.print_model_differences()` before printing each new model
(`builder/runner.py:643-644`). Base implementation (`models/structure.py:712-798`) prints
sections keyed `sentence_letters` / `semantic_functions` / `model_structure` — **a key schema
that neither the generic nor the theory calculators produce** (they produce
`world_changes`/`worlds`/`verify`/…); only theory overrides like
`LogosModelStructure.print_model_differences` (`theory_lib/logos/semantic/model.py:176`) match
the real schema, with ANSI colors when `output is sys.stdout`. Imposition/bimodal instead attach
a closure at `iterate_example` time that binds the *iterator's* `display_model_differences`
method onto each structure (`theory_lib/imposition/iterate.py:490-501`) — three different
mechanisms for the same job (see I5).

---

## 5. Termination and budgets

Settings actually read by the live path:

| Setting | Read at | Default | Meaning |
|---|---|---|---|
| `iterate` | `iterate/iterator.py:67` (`settings.get('iterate', 1)`) | theory-specific (`logos: False` at `theory_lib/logos/semantic/core.py:47`; imposition: `1` at `theory_lib/imposition/semantic/core.py:99`) | total models requested (`max_iterations`) |
| `max_time` | `iterate/core.py:209`; also solver timeout ms at `iterate/constraints.py:60-62`; progress at `builder/runner_utils.py:117-119` | 300 in iterator; 60 in runner_utils; theory defaults 1-10s | **per-model-search** wall clock AND Z3 `timeout` |
| `max_invalid_attempts` | `iterate/core.py:182` | 20 | consecutive invalid models (sat-but-no-model, structure build failure, zero worlds) |
| `expectation` | `iterate/models.py:659-701` (validators; not consulted by loop) | None | countermodel/theorem expectation |

Validation of `iterate >= 1` and `timeout > 0` in `IteratorCore._get_iteration_settings`
(`iterate/iterator.py:375-411`), which also seeds unused defaults `timeout: 300`,
`max_consecutive_invalid: 20`, `enable_progress`, `enable_statistics`.

**Stopping conditions** of `iterate_generator` (`iterate/core.py:193-230` + `metrics.py:109-140`):

1. `current_iteration >= max_iterations` — success.
2. Per-search timeout: `time.time() - current_search_start > settings.get('max_time', 300)` —
   records a `SearchStatistics(found=False, termination_reason=f"timeout after {timeout}s")` with
   `search_duration` clamped to exactly `timeout` (`iterate/core.py:210-230`), completes the
   progress bar as not-found, `break`s. **Timeout mid-iteration abandons only the current search;
   all previously yielded models are kept** (they were yielded incrementally).
3. Solver returns non-`sat` — "exhausted search space" (`iterate/core.py:260-278`).
4. `consecutive_invalid_count >= max_invalid_attempts` (three trigger sites,
   `iterate/core.py:282-323`).
5. Lack-of-progress heuristic (`iterate/metrics.py:137-138`).
6. `KeyboardInterrupt` caught → clean finish (`iterate/core.py:414-415`).

After the loop the `finally`/tail code prints the **ITERATION REPORT**
(`iterate/core.py:451-478`; generator: `iterate/statistics.py:75-113`), e.g.:

```
ITERATION REPORT
    Model 1: Initial model (0.42s)
    Model 2: Found after skipping 3 isomorphic models (1.07s)
    Model 3: Not found - timeout after 10s after checking 12 models (10.00s)

Total: 2/3 models found, 3 isomorphic models skipped, 11.49s elapsed
```

Note the report is written by the *iterator* directly to `sys.stdout`
(`iterate/core.py:477-478`) — output-layer logic living inside the search engine (see I1).

---

## 6. Output subsystem: formats and architecture

Package `output/` — exports at `output/__init__.py:7-24`: `MarkdownFormatter`, `JSONFormatter`,
`ANSIToMarkdown`, `OutputManager`, `OutputConfig`, `create_output_config`, `ModelDataCollector`.

### Supported output modes (exhaustive, as implemented)

1. **Terminal (default)**: ANSI-colored text printed by the model structures themselves
   (colors gated on `output is sys.__stdout__` / `sys.stdout`; e.g.
   `models/structure.py:664`, `theory_lib/logos/semantic/model.py:187-193`).
2. **Markdown file** (`--save` / `--save markdown`): captured terminal output, ANSI converted to
   markdown, one combined `EXAMPLES.md`.
3. **JSON file** (`--save json`): structured model data plus raw text, combined `MODELS.json`.
4. That's all. `FORMAT_NOTEBOOK = 'notebook'` and `NOTEBOOK.ipynb`/`DEFAULT_NOTEBOOK_FILE`
   constants exist (`output/constants.py:5-21`) but **no notebook formatter exists** in
   `output/formatters/` (only `base.py`, `markdown.py`, `json.py`). No LaTeX output exists
   anywhere in `output/`. (Jupyter display lives in the separate `jupyter/` package — another
   agent's territory.)
5. **Sequential per-model saving** is scaffolded (`OutputConfig.sequential`,
   `OutputManager.save_prompted_model` at `output/manager.py:122-153`) but **hard-disabled**:
   `BuildModule` raises `NotImplementedError` when `sequential` is requested because
   `SequentialSaveManager`/`ConsoleInputProvider` were deliberately deleted
   (`builder/module.py:139-153`).

### CLI wiring

`--save` is `nargs='*'`, `choices=['markdown', 'json']`, `default=None`
(`__main__.py:121-129`); `create_output_config(args, settings)` maps: flag absent → saving off;
`--save` bare → both formats; `--save json` → subset (`output/config.py:42-89`).

### Architecture: capture-then-format, not data-then-render

The dispatch is `BuildModule._capture_and_save_output` (`builder/module.py:185-218`):

- Saving disabled → just `example.print_model(...)` to stdout (line 202).
- Saving enabled → `_capture_model_output` redirects `sys.stdout` into a `StringIO`, calls
  `example.print_model(...)`, restores stdout, **re-prints the raw capture to the console**, and
  runs `ANSIToMarkdown().convert(raw)` (`builder/module.py:226-260`). So the markdown artifact is
  *post-processed terminal text*, not independently rendered data.
- Structured data comes separately from `ModelDataCollector.collect_model_data`
  (`output/collectors.py:14-50`) which duck-types four extraction hooks on the structure:
  `extract_states()`, `extract_evaluation_world()`, `extract_propositions()`,
  `extract_relations()` (`output/collectors.py:52-115`), yielding:

```python
{"example": ..., "theory": ..., "has_model": bool, "evaluation_world": str|None,
 "states": {"possible": [...], "impossible": [...], "worlds": [...]},
 "relations": {...}, "propositions": {...},
 "premises": [...], "conclusions": [...], "settings": {...}}   # added in module.py:286-289
```

- `_format_and_save_output` (`builder/module.py:312-343`) runs
  `MarkdownFormatter(use_colors=True).format_example(model_data, converted_output)` — which for
  non-empty output is just `model_output.strip()` (`output/formatters/markdown.py:33-42`) — then
  `OutputManager.save_example`.

Formatter "pattern": a `Protocol` interface `IOutputFormatter` (`output/formatters/base.py:6-55`,
methods `format_example`, `format_batch`, `get_file_extension`) with two implementations,
selected by a dict `self.formatters[format_name]` built in `OutputManager._initialize_formatters`
(`output/manager.py:60-68`). `ANSIToMarkdown.convert` regex-rewrites `\033[31m…\033[0m` → bold
and green → italic, then strips remaining codes (`output/formatters/markdown.py:100-140`).

---

## 7. Printing / display contract (what a theory must implement)

Call chain for one example: `BuildExample.print_model(example_name, theory_name, output)`
(`builder/example.py:244-271`) → `model_structure.print_to(settings, example_name, theory_name,
output=...)`. `print_to` is **theory-provided** — e.g.
`theory_lib/logos/semantic/model.py:147-174`, which prints a TIMEOUT banner when
`z3_model_runtime >= max_time` and no model, then calls `print_all`, then optionally
`print_grouped_constraints` when `print_constraints` is set.

Theory `print_all` (`theory_lib/logos/semantic/model.py:118-145`) sequence:

1. `print_info(model_status, settings, example_name, theory_name, output)`
   (`models/structure.py:794-825`) — `========` separator, `EXAMPLE NAME: there is a
   countermodel.`, `Atomic States: N`, `Semantic Theory: …`, premises/conclusions via
   `model_constraints.print_enumerate`, `Solver Run Time` footer.
2. `print_states(output)` (`logos/semantic/model.py:273`) — state inventory with colors/labels
   (world/possible/impossible).
3. `print_evaluation(output)` (`logos/semantic/model.py:260`) — the designated evaluation world.
4. `print_input_sentences(output)` (`models/structure.py:602-641`) — the interpreted
   premises/conclusions, numbered continuously.
5. `print_model(output)` (`models/structure.py:668-691`) — raw Z3 model or unsat core, only when
   setting `print_z3` is true.

Note the base class also defines its own, *differently-signatured* `print_all(output)`
(`models/structure.py:871-892`) — see D5.

### Recursive truth-tree printing

`ModelDefaults.recursive_print(sentence, eval_point, indent_num, use_colors)`
(`models/structure.py:574-600`):

- atomic sentence (`sentence.sentence_letter is not None`) →
  `sentence.proposition.print_proposition(eval_point, indent_num, use_colors)` — **proposition
  contract**: every theory's proposition class implements `print_proposition` (e.g.
  `theory_lib/logos/semantic/proposition.py:320`), printing the formula, its
  verifier/falsifier sets, and truth value at the eval point with ANSI colors.
- complex sentence → `sentence.original_operator.print_method(sentence, eval_point, indent_num,
  use_colors)` — **operator contract**: each operator exposes `print_method`, normally one of the
  base helpers in `syntactic/operators.py`: `general_print` (line 77 — print own proposition,
  recurse into `original_arguments` with `indent_num+1`), `print_over_worlds` (line 103 — modal
  and counterfactual operators: print antecedent at eval world, consequent at each alternative
  world), `print_over_times` (line 200 — temporal analog).

Recursion re-enters via `model_structure.recursive_print(arg, ...)`
(`syntactic/operators.py:100`), so the operator/structure pair form mutual recursion producing
the indented evaluation tree. Colors are enabled only when `output is sys.__stdout__`
(`models/structure.py:664`), and `_print_sentence_group` wraps recursion in
`redirect_stdout(output)` because `print_proposition`/`print_method` print to bare stdout
(`models/structure.py:653-666`) — a global side channel (see I6).

`print_grouped_constraints` (`models/structure.py:374`) and `print_constraints`
(`models/structure.py:483`) dump Z3 constraints grouped by origin; a heredoc template at
`models/structure.py:540-572` regenerates a runnable snippet with the example's inputs.

---

## 8. Model saving / exporting (disk layout)

Directory: `OutputManager.create_output_directory` — `output_{YYYYMMDD_HHMMSS}` under the CWD
(`output/manager.py:88-100`, constants `output/constants.py:24-25`), created once per run in
`BuildModule` when saving is on (`builder/module.py:166`).

**Batch mode (the only live mode)** — outputs accumulate per example
(`output/manager.py:102-120`) and `finalize()` (called from `builder/runner.py:758,767`,
including on Ctrl-C) writes:

```
output_20260818_143012/
├── EXAMPLES.md   # all examples' captured markdown joined by "\n\n---\n\n"  (manager.py:198-215)
└── MODELS.json   # {"metadata": {"timestamp", "version": "1.0"}, "models": [ ... ]}  (manager.py:217-227)
```

Iterated models are saved through the same path with `display_name =
f"{example_name}_model{model_num}"` (`builder/module.py:212-213`;
`builder/runner.py:656` passes `model_num=distinct_count`).

**Sequential mode (dead)** would write `output_dir/{example}/MODEL_{n}.md|.json` plus a
`summary.json` (`output/manager.py:122-153, 229-263`) — unreachable per
`builder/module.py:145-153`.

**No persisted/re-loadable model exists.** The JSON is a human/analysis export (states,
relations, propositions as strings, plus raw text under `"output"`,
`output/formatters/json.py:24-43`); nothing in the codebase reads MODELS.json back into a
`ModelStructure`. `BuildExample.save_or_append` (`builder/example.py:273+`) appends printed text
to a user-named file — again text, not a model.

---

## 9. Comparison features (`--maximize`)

CLI: `--maximize` / `-m`, "Compare multiple semantic theories on same examples"
(`__main__.py:113-117`); general setting default `False` (`settings/settings.py:419`,
`DEFAULT_GENERAL_SETTINGS`). Dispatch in `main()`: if `module.general_settings["maximize"]`,
run `module.comparison.run_comparison()` **instead of** `runner.run_examples()`
(`__main__.py:301-303`).

`ModelComparison` (`builder/comparison.py:78`):

- `run_comparison` (`:140-186`): for each example in `example_range`, prints the premises/
  conclusions header, translates operators per theory via each theory's `dictionary`
  (`builder/comparison.py:160-166` — this is how *the same example* runs under multiple
  semantics), calls `compare_semantics`, sorts by result descending, prints
  `"  {theory}: Maximum N = {max_N}"`.
- `compare_semantics` (`:91-137`): the metric is **maximum model size N reachable within the
  time limit**, *not* validity agreement. Each theory is serialized
  (`serialize_semantic_theory`, `builder/serialize.py`) and submitted to a
  `ProcessPoolExecutor` (`max_workers = min(cpu_count, len(theories))`); worker
  `_find_max_N_static` (`builder/comparison.py:20-75`) loops `N = settings.N, N+1, N+2, …`
  calling `try_single_N_static` (from `builder/runner.py`) until a run fails/times out, returning
  the last successful N. Per-future collection timeout 300s → result 0 (`:129-134`).

Aggregation/report is plain stdout text; comparison results are **not** routed through the
output-saving subsystem (a `# TODO: create print/save class` sits right above the dispatch,
`__main__.py:300`).

Cross-theory *semantic* comparison (same example under several theories with countermodel
display) is just the normal non-maximize path: `semantic_theories` with translation dictionaries
runs each example under every theory sequentially (`builder/runner.py` main loop).

---

## 10. Progress / feedback

Subsystem `output/progress/`:

| Piece | File | Notes |
|---|---|---|
| `ProgressBar` (abstract), `UnifiedProgress` | `output/progress/core.py:12, 47` | facade owning per-model bars; counters for checked/skipped |
| `TimeBasedProgress`, `AnimatedProgressBar` | `output/progress/animated.py:271, 234` | daemon-thread animation, 0.1s frames, 20-char bar that fills as a **time fraction elapsed/timeout**, orange 256-color ANSI (constants lines 16-18) |
| `Spinner` | `output/progress/spinner.py:14` | `-\|/` spinner for unmeasurable waits |
| `TerminalDisplay`, `BatchDisplay`, `ProgressDisplay` | `output/progress/display.py:44, 112, 13` | `\r`-rewrite with width clamp vs. no-op for CI |

Wiring: `ModelRunner._process_with_iterations` creates `UnifiedProgress(total_models=iterate_count,
max_time=settings.max_time)` via `create_progress_tracker_for_iteration`
(`builder/runner.py:417`, `builder/runner_utils.py:104-124`), runs the model-1 search under bar 1,
then attaches the tracker as `example._unified_progress` (`builder/runner.py:448-449`), which
`BaseModelIterator.__init__` picks up (`iterate/core.py:104`). During iteration the iterator calls
`start_model_search(n, start_time=...)`, `model_checked()`, `model_skipped_isomorphic()`,
`complete_model_search(found)` (`iterate/core.py:240-343`).

Display format: `Finding non-isomorphic models: [████████░░░░░░░░░░░░] 2/4 (1 skipped) 1.1s`
(`output/progress/animated.py:385-391`).

**Deferred-completion protocol** (documented at `output/progress/core.py:156-191` and
`builder/runner.py:599-607`): when a model is found the iterator calls `stop_animation_only()`
which freezes fill fraction + elapsed at that instant (`TimeBasedProgress.freeze_at_current`,
`animated.py:240-273`); the runner then prints the frozen bar (`complete_model_search(found=True)`),
the differences, the `MODEL k/n` header and the model output, in that order
(`builder/runner.py:626-666`), so bars and model blocks interleave correctly and the printed
elapsed time matches the bar fill.

Timing reports: per-model search durations in the ITERATION REPORT (§5); `Solver Run Time`
(`models/structure.py:824`) and `Total Run Time` (`logos/semantic/model.py:138-140`) per example.
The interactive "find another model?" prompt is `ModelRunner.prompt_for_iterations`
(`builder/runner.py:822-843`), used when a `prompt_manager` exists — i.e., currently never
(`builder/module.py:144`).

---

## Doc/Source Divergences

- **D1 — `iterate/README.md` settings block is fictional.** It documents `max_iterations`,
  `timeout`, `use_isomorphism`, `debug` settings (`iterate/README.md:183-192`) — the code reads
  `iterate`, `max_time`, `max_invalid_attempts` only (§5). It also shows
  `iterator.get_iteration_summary()` returning `models_found`/`total_checked`/`success_rate`/
  `avg_time_per_model` (`iterate/README.md:237-244`); actual keys are `total_models`,
  `avg_worlds`, `world_diversity`, `avg_differences`, `max_differences`
  (`iterate/metrics.py:49-67`). Its usage example constructs `BuildExample(semantics_module_name=…)`
  and `LogosIterator` — neither API exists (`LogosModelIterator` is the real name,
  `theory_lib/logos/iterate.py:36`).
- **D2 — `output/README.md` documents deleted components as present.** Directory listing includes
  `sequential_manager.py`, `prompts.py`, `input_provider.py`, `formatters/notebook.py`, and a
  `notebook/` subsystem with `streaming_generator.py` (`output/README.md:17-27`), and a whole
  `SequentialSaveManager` API section (`:62-66, 200+`). None of these files exist (verified by
  `ls output/ output/formatters/`), and sequential mode raises `NotImplementedError`
  (`builder/module.py:145-153`). `OutputManager`'s docstring still advertises the
  `SequentialSaveManager` parameter (`output/manager.py:36`).
- **D3 — `docs/architecture/ITERATE.md` documents settings that don't exist.** `iteration_attempts`
  ("try escape after 5 isomorphic models") and `escape_attempts` (`docs/architecture/ITERATE.md:171-172,
  867-868`) appear nowhere in `code/src/` (grep over `*.py`: zero hits). `iteration_timeout`
  exists only in the dead `IteratorCore.iterate` (`iterate/iterator.py:131`); the live loop uses
  `max_time` (`iterate/core.py:209`).
- **D4 — `iterate/README.md` module description stale.** Claims `metrics.py` contains
  `IterationProgress: Real-time progress bars` (`iterate/README.md:124-128`); progress lives in
  `output/progress/` and `metrics.py` has no such class. Header line counts (`core.py … 729
  lines`, `README.md:12`) are stale (actual 759).
- **D5 — Print-contract signature split.** `ModelDefaults.print_all(self, output)`
  (`models/structure.py:871`) vs theory `print_all(self, default_settings, example_name,
  theory_name, output)` (`theory_lib/logos/semantic/model.py:118`) — same name, incompatible
  arity; the base version is effectively dead for theories and misleads readers of the base class.
- **D6 — Generic difference constraints iterate `range(N)`, not `range(2**N)`.**
  `_create_state_difference_constraints` uses `N = settings.get('N', 3)` then
  `self._generate_input_combinations(1, N)` → states `0..N-1` (`iterate/constraints.py:200-205,
  296-312`), whereas everywhere else the state space is `range(2**N)` bitvectors
  (`iterate/models.py:89`, `theory_lib/logos/iterate.py:263`). The generic exclusion constraint
  therefore only forces differences among the first N of 2**N states — under-constraining (relies
  on the isomorphism check to reject duplicates, at CPU cost). Same bug in
  `_create_non_isomorphic_constraint` (`iterate/constraints.py:246-252`) and in
  `ModelBuilder._initialize_z3_dependent_attributes` (`iterate/models.py:227-235` uses
  `range(N)`; note that helper is itself dead — the live rebuild path at `models.py:89` uses
  `2**N` correctly).
- **D7 — Fake NetworkX fallback.** `iterate/graph.py:8` imports networkx unconditionally; the
  `try/except ImportError` guard at lines 29-33 and all `HAS_NETWORKX` messaging
  (`iterate/graph.py:434-440`, `iterate/core.py:167-175`) imply graceful degradation that cannot
  actually occur (missing networkx crashes the module import).

## Improvement Opportunities

- **I1 — Iteration engine performs terminal I/O.** `iterate_generator` writes the ITERATION
  REPORT and spacing newlines directly to `sys.stdout` (`iterate/core.py:396-397, 466-478`) and
  reaches into progress-bar internals (`self.search_progress.model_progress_bars[-1]`,
  `iterate/core.py:442-446`). A port should make the iterator yield/return data
  (`SearchStatistics` list is already a clean value type, `iterate/statistics.py:10-49`) and let
  a renderer own presentation.
- **I2 — Theory constraint hooks are disconnected from the live loop.** `BaseModelIterator`
  delegates constraint generation to `ConstraintGenerator`, whose `_create_difference_constraint`
  is the generic is-world-flip (`iterate/constraints.py:149`); the theory overrides on the
  iterator subclass (`iterate/core.py:709-758`, `theory_lib/logos/iterate.py:215`) and the
  abstract stubs are never called by `iterate_generator`. Either wire
  `ConstraintGenerator` to call back into the iterator, or delete the override surface. The
  triple `z3.BoolVal(True)` stubs for `_create_non_isomorphic_constraint` /
  `_create_stronger_constraint` in every theory (`logos/iterate.py:329-359`,
  `imposition/iterate.py:430-438`) show the seam was never finished.
- **I3 — Dead code to drop or resurrect:** `iterate/base.py` (never imported),
  `iterate/build_example.py` (`IteratorBuildExample`/`create_with_z3_model` — zero callers, and it
  represents the *cleaner* injection design via `ModelConstraints.inject_z3_values`,
  `models/constraints.py:180`), `iterate/z3_utils.py` (push/pop difference search, zero callers),
  `iterate/types.py` protocols/enums (`StrategyType`, `IterationStrategy`, `IterationConfig` —
  no implementations), `ResultFormatter` (`iterate/metrics.py:179` — superseded by
  `IterationReportGenerator`), `IteratorCore.iterate` (`iterate/iterator.py:93-332`; would crash:
  `self.progress` is `None` at `iterator.py:73` yet dereferenced at line ~124 `self.progress.update`),
  `BaseModelIterator._orchestrated_iterate` (`iterate/core.py:483-661`, unreferenced third copy
  of the loop).
- **I4 — Triplicated iteration loop.** `IteratorCore.iterate`, `BaseModelIterator.iterate_generator`,
  and `_orchestrated_iterate` are ~200-line near-clones differing in progress plumbing
  (`iterate/iterator.py:93`, `iterate/core.py:140, 483`). One loop parameterized by an observer
  interface suffices.
- **I5 — Three difference-display mechanisms.** (a) structure method override
  (`logos/semantic/model.py:176`), (b) closure monkey-patched onto structures at
  `iterate_example` time (`imposition/iterate.py:490-501`, `bimodal/iterate.py:519-530`),
  (c) base-class printer expecting a schema nobody produces (`models/structure.py:712-798`),
  plus an unused fourth in `ResultFormatter.format_difference_report`
  (`iterate/metrics.py:212-246`). The difference *data shapes* also differ per mechanism
  (`world_changes` vs `worlds`). A port should fix one canonical diff datatype and one renderer.
- **I6 — Printing is side-effecting and stdout-coupled.** Truth-tree printing relies on
  `redirect_stdout` because propositions/operators print to global stdout
  (`models/structure.py:653-666`); color choice tests object identity `output is sys.__stdout__`
  (`models/structure.py:664`), which silently disables colors under capture and breaks under
  stream wrapping; saving re-parses ANSI codes out of captured text
  (`builder/module.py:226-260`, `output/formatters/markdown.py:100-140`). The clean design is
  pure data (the collector schema in §6 is a start) → renderer per format; currently the markdown
  "formatter" is `model_output.strip()` (`output/formatters/markdown.py:33-42`).
- **I7 — Isomorphism check ignores labels.** `nx.is_isomorphic(g1, g2)` without
  `node_match`/`edge_match` (`iterate/graph.py:494`) treats proposition valuations and relation
  names as irrelevant, so genuinely distinct models can be skipped as "isomorphic"; conversely
  the graph only encodes worlds + `accessible`/`earlier`, so hyperintensional structure
  (verify/falsify, parthood) is invisible to the check. Use
  `nx.is_isomorphic(g1, g2, node_match=..., edge_match=...)` over a theory-declared signature.
- **I8 — `ModelGraph` construction is fragile and side-effecting.** Unconditional appends to a
  hard-coded `/tmp/graph_debug.log` on every graph build (`iterate/graph.py:70-78, 118-127,
  156-163, 183-188, 257-258`) — a production hot path doing debug file I/O; nodes/edges keyed by
  list index rather than the state value with `accessible(i, j)` called on indices
  (`iterate/graph.py:86-121, 133-149`); broad `except Exception` blocks swallow encoding errors
  leaving empty graphs that then compare equal.
- **I9 — Solver constraint accumulation is monotone and unscoped.** `check_satisfiability`
  permanently `add`s every batch (`iterate/constraints.py:117-121`); `extended_constraints` are
  regenerated from *all* previous models each pass and re-added (duplicates), and stronger
  constraints appended to the local list are only added on the *next* pass. `push()`/`pop()`
  discipline (as in dead `iterate/z3_utils.py:100-116`) or incremental single-model exclusion
  would be cleaner and cheaper.
- **I10 — `iterate=False` default is type-unsound.** Logos defaults `'iterate': False`
  (`theory_lib/logos/semantic/core.py:47`) while `IteratorCore` validates `iterate` as a positive
  int (`iterate/iterator.py:375-411`) and the runner compares `iterate_count == 1`
  (`builder/runner.py:293`) — `False` slips through as 0-ish. Works only because examples set an
  explicit integer; a port should type this as `Nat` (>=1).
- **I11 — Output subsystem carries a dead mode.** `sequential` threads through `OutputConfig`,
  `OutputManager.save_prompted_model`, `_save_immediately`, `_create_summary`
  (`output/config.py`, `output/manager.py:114-153, 229-263`) yet is unreachable
  (`builder/module.py:145-153`). Decide: delete or reimplement; don't port the scaffold.
- **I12 — Comparison metric is narrow.** `--maximize` reports only max-N-within-timeout per
  theory (`builder/comparison.py:91-137`) and bypasses the saving subsystem entirely
  (`__main__.py:300-303`); no validity-agreement matrix, no shared result datatype with the
  normal path. The mock `MockBuildModule` inside `_find_max_N_static`
  (`builder/comparison.py:42-53`) signals the comparison path was bolted on around the runner
  rather than sharing an engine API.
