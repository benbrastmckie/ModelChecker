# Research Report: Task #220

**Task**: 220 - Unicode operator characters
**Started**: 2026-09-29T00:00:00Z
**Completed**: 2026-09-29T00:00:00Z
**Effort**: Medium (2-4 phases: core alias mechanism, theory-file adoption, validation hardening, docs)
**Dependencies**: None
**Sources/Inputs**: Codebase exploration only (`code/src/model_checker/syntactic/`, `code/src/model_checker/utils/parsing.py`, `code/src/model_checker/theory_lib/*/operators.py`, `code/src/model_checker/jupyter/unicode.py`, `docs/usage/OPERATORS.md`)
**Artifacts**: - This report (specs/220_unicode_operator_characters/reports/01_unicode-operator-characters.md)
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The low-level parser (`utils/parsing.py`, `syntactic/collection.py`, `syntactic/sentence.py`,
  `syntactic/syntax.py`) is **already fully generic** with respect to operator-name spelling: it
  never special-cases the LaTeX-escape convention (`\wedge`, `\neg`, ...) except for the two
  hardcoded nullary constants `\top`/`\bot`. Arbitrary Unicode strings work today as `Operator.name`
  values for both infix (arity-2, parsed via `utils/parsing.py::op_left_right`) and prefix
  (arity-1, parsed via the fallback branch of `parse_expression`) forms. This is independently
  confirmed by `code/src/model_checker/syntactic/tests/unit/test_operators.py` and
  `test_syntax.py`, which already build and parse operators literally named `"∧"`, `"∨"`, `"¬"`.
- What is genuinely missing — and is the real content of this task — is a way for a theory's
  `operators.py` to give ONE operator class **more than one name simultaneously** (its canonical
  LaTeX identifier plus a user-chosen Unicode glyph), so existing examples/tests/docs that use
  `\wedge` keep working while a user can also type `∧`. `syntactic.Operator.name` is a single
  class attribute and `OperatorCollection.add_operator` derives its dictionary key strictly from
  that one attribute (`self.operator_dictionary[operator.name] = operator`) — there is no alias
  concept anywhere in `syntactic/collection.py` today.
- A parallel, pre-existing but functionally disconnected mechanism already solves *display*, not
  *input*: `jupyter/unicode.py` (`latex_to_unicode`/`unicode_to_latex`) plus the theory extension
  point `UNICODE_OPERATOR_EXTENSIONS` (implemented only by `exclusion/__init__.py`) do naive
  string substitution for Jupyter notebook pretty-printing. It is never consulted by
  `model_checker.syntactic` or by the `model-checker`/`dev_cli.py` CLI parsing path, so it does
  not satisfy "in theory operators.py files" — it lives in `jupyter/`, not `operators.py`, and it
  only affects notebook rendering.
- A second existing mechanism, `semantic_theory["dictionary"]` (consumed by
  `builder/translation.py::OperatorTranslation.translate`), does pre-parse raw `str.replace()`
  substitution on whole formula strings. It is currently used only for theory-to-theory operator
  translation (e.g. exclusion syntax → logos syntax for `--maximize`), lives in each theory's
  `examples.py` (not `operators.py`), and is naive (unscoped substring replace, not
  tokenization-aware) — a plausible but weaker alternative to an in-`Operator`-class alias
  mechanism.
- Recommended approach: add an optional `aliases: List[str] = []` class attribute to
  `syntactic.Operator` and extend `OperatorCollection.add_operator` to additionally register the
  class under each alias string (alongside the canonical `.name` key). Binary (arity=2) operators
  parse their aliases in infix position automatically (already generic); unary (arity=1) operators
  parse their aliases in prefix position automatically (already generic) — no changes needed to
  `utils/parsing.py`, `syntactic/sentence.py`, or `syntactic/syntax.py` for the arity-1/arity-2
  case. Nullary (`\top`/`\bot`) aliasing is explicitly out of scope (see Risks).

## Context & Scope

Task 220's description: "Implement user-specifiable unicode characters for operators in theory
operators.py files with infix or prefix form." No further task context, roadmap entry, or prior
research/plan artifact exists for this task (confirmed via `specs/state.json` and `specs/TODO.md`
— task 220 has no dependencies and this is its first research round). The phrase "in theory
operators.py files" was read as: theory authors (and, since `model-checker` project generation
copies a theory's files into a user's own project directory, end users maintaining their own copy
of an operators.py file) should be able to declare, directly in `operators.py`, which Unicode
glyph represents a given operator — not through a separate settings file, environment variable, or
runtime CLI flag. "Infix or prefix form" was read as scoping this to arity-2 (binary, written
between arguments, parenthesized per this repo's formatting convention) and arity-1 (unary,
written before its single argument, unparenthesized) operators specifically — i.e. excluding the
two nullary operators `\top`/`\bot`, which are neither infix nor prefix.

## Findings

### Codebase Patterns

**Parser is operator-name-agnostic already** (verified by tracing the full pipeline):

- `code/src/model_checker/utils/parsing.py::parse_expression` — for a top-level token that is
  not `"("`, not alphanumeric, and does not start with `"\\"`, it falls through to the generic
  final branch (`arg, comp = parse_expression(tokens); return [token, arg], comp + 1`), treating
  *any* such token as a unary prefix operator. This is exactly how `\neg`/backslash-prefixed
  unary operators are already handled one branch earlier — the fallback branch means a bare
  Unicode glyph like `¬` works identically, today, with zero code changes.
- `code/src/model_checker/utils/parsing.py::op_left_right` (used for the `"("`-initiated binary
  case) extracts whatever token follows the left operand as `operator`, with no restriction on
  its spelling (`extract_arguments`'s `else: left.append(token)` branch accumulates any
  non-paren, non-alnum token, then `process_operator` just pops the very next token) — so a
  Unicode infix operator inside parens (`"(p ∧ q)"`) parses identically to `"(p \\wedge q)"`.
- `code/src/model_checker/syntactic/collection.py::OperatorCollection.apply_operator` — its own
  docstring example already documents this: `["∧", ["p"], ["q"]] -> [AndOperator, Const("p",
  AtomSort), Const("q", AtomSort)]`. The only two literal string checks in this method are for
  `"\\top"`/`"\\bot"` (nullary) and `atom.isalnum()` (sentence letters); operator heads with
  arguments are looked up generically via `self[op]` regardless of spelling.
- `code/src/model_checker/syntactic/tests/unit/test_operators.py` and `test_syntax.py` **already
  exercise this exact feature** as their default test fixtures: operator classes are defined with
  `name = "∧"`, `name = "∨"`, `name = "¬"` and parsed via `Syntax(["(p ∧ q)"], [], collection)` /
  prefix formulas like `"¬ p"` — proving the parsing layer supports Unicode operator names for
  both infix and prefix forms today, independent of this task.
- `code/src/model_checker/syntactic/sentence.py::Sentence.infix` (and `_compute_infix_from_prefix`)
  reconstruct sub-formula strings from the raw token captured at tokenize time (`prefix_sentence`
  entries), not from the operator class's canonical `.name`. This means whatever glyph the user
  actually typed is what gets echoed back in `Sentence.name` / printed output — so an aliasing
  mechanism does not require any change to display/printing code; the round-trip already "just
  works" once a name resolves to an operator class at all.

**The single-name bottleneck** — everything funnels through one attribute:

- `code/src/model_checker/syntactic/operators.py::Operator` declares `name: Optional[OperatorName]
  = None` as a single class attribute (no list/alias slot).
- `code/src/model_checker/syntactic/collection.py::OperatorCollection.add_operator` (the *only*
  code path that populates `operator_dictionary`, used uniformly by every theory —
  `logos/operators.py`'s `LogosOperatorRegistry.load_subtheory` (`self.operator_collection.add_operator(op_class)`),
  `exclusion/operators.py::create_operators` (`OperatorCollection(UniNegationOperator, ...)`),
  `bimodal/operators.py` (`syntactic.OperatorCollection(NegationOperator, AndOperator, ...)`),
  `imposition/operators.py` (`imposition_operators.add_operator(op_class)`), and
  `builder/serialize.py::deserialize_operators` (`collection.add_operator(op_class)`)) always
  keys the dictionary entry from `operator.name`: `self.operator_dictionary[operator.name] =
  operator`. Every `get_operators()` function across every theory returns a `{name_string:
  op_class}` dict, but **that dict's own string keys are discarded** the moment the values are
  fed through `add_operator` (e.g. `logos/operators.py::load_subtheory`: `for op_class in
  operators.values(): self.operator_collection.add_operator(op_class)`), confirming the class's
  own `.name` attribute — not any dict key a caller chose — is the single source of truth for
  what string parses to that operator.
- Consequence: there is currently no way to make one operator class answer to two different
  spellings. A theory cannot both keep `AndOperator.name == "\\wedge"` (needed for backward
  compatibility with every existing `examples.py`/test formula and every doc reference) and also
  accept `"∧"` at the same time, without a new alias concept.

**Existing but disconnected precedent for Unicode operator glyphs**:

- `code/src/model_checker/jupyter/unicode.py`: `unicode_to_latex`/`latex_to_unicode` are static
  dicts (`'∧': '\\wedge'`, etc.) used only by `normalize_formula`, itself called only from
  `jupyter/interactive.py` (3 call sites, all notebook widget code). `get_theory_operators`
  additionally merges in a theory's own `UNICODE_OPERATOR_EXTENSIONS` module constant (discovered
  generically via `model_checker.registry.get_theory_entry` + `importlib`, not a hardcoded
  theory-name string) — currently implemented only by
  `code/src/model_checker/theory_lib/exclusion/__init__.py` (`⦻`→`\exclude`, `⊓`→`\uniwedge`,
  `⊔`→`\univee`, `≔`→`\uniequiv`). None of this is reachable from `model_checker.syntactic`,
  `builder/`, or `dev_cli.py` — it is Jupyter-notebook-display-only.
- `code/src/model_checker/builder/translation.py::OperatorTranslation.translate` performs raw
  `sentence.replace(old, new)` substitution over premise/conclusion strings using a
  `dictionary: Dict[str, str]` drawn from `semantic_theory["dictionary"]` in each theory's
  `examples.py` (e.g. `exclusion/examples.py:991`: `"dictionary": exclusion_to_logos`,
  `imposition/examples.py:988`: `"dictionary": imposition_to_logos`). This is a working,
  general pre-parse substitution mechanism, but (a) it lives in `examples.py`, not
  `operators.py`, so it does not match the task's stated location; (b) it is unscoped substring
  replacement with no tokenization awareness (a naive Unicode-to-Unicode or Unicode-to-LaTeX
  dictionary entry could accidentally match inside an unrelated token); and (c) it is currently
  used exclusively for theory-to-theory operator-name translation in `--maximize` comparisons,
  not for user-facing notation choice.

**Validation / hardening gaps relevant to this task's exact scope (arity-1/arity-2 only)**:

- `code/src/model_checker/syntactic/formulas.py::is_syntactically_wff` accepts *any* string head
  that does not start with `"\\"` as a valid "atomic sentence letter" (`isinstance(head, str) and
  not head.startswith('\\')` → `return True, ""`), **without checking `len(prefix) == 1`**. This
  means a 3-element prefix list like `["∧", ["p"], ["q"]]` is currently accepted by this function
  through the wrong branch (mislabeled as "atomic sentence letter", not "binary connective") —
  functionally harmless today (it still returns `True`), but it means this function currently
  provides no real arity/well-formedness discrimination for non-backslash operator heads. A
  correct implementation adding Unicode aliases should decide whether to tighten this (recognize
  registered aliases explicitly, keyed off complexity/length) or leave the existing permissive
  behavior — either is viable, but the planner should decide deliberately rather than by
  accident, since the current pass-through is coincidental, not designed.
- `code/src/model_checker/syntactic/collection.py` imports `DuplicateOperatorError` and
  `UnknownOperatorError` from `.errors` but **never raises either** — duplicate names are
  silently skipped (`if operator.name in self.operator_dictionary.keys(): return`) and an unknown
  operator lookup (`self[op]` → `self.operator_dictionary[value]`) raises a plain `KeyError`
  rather than the purpose-built `UnknownOperatorError` (which already supports an
  `available_operators` suggestion list). This existing, unwired infrastructure is directly
  useful for surfacing a clear error when a user's chosen alias collides with another operator's
  name/alias, or when a typo'd alias is used in a formula — worth wiring up as part of this task
  rather than leaving silent skip/bare `KeyError` behavior in place for the new alias path.
- `docs/usage/OPERATORS.md` currently states, as an explicit **Best Practice** and
  **Troubleshooting** item: "**Always use LaTeX notation** - never use Unicode in code" / "LaTeX
  parsing errors: Ensure you're using LaTeX notation (`\\wedge`, not `∧`) in operator names."
  This doc will need updating alongside the implementation so it does not contradict the new
  capability; it is the canonical developer-facing reference for `operators.py` conventions.

**Nullary operators are a separate, larger blast radius — confirmed out of scope**:

- Only two nullary (`arity = 0`) operator classes exist in the whole `theory_lib` tree today:
  `TopOperator`/`BotOperator`, each defined twice (once in
  `logos/subtheories/extensional/operators.py`, once in `bimodal/operators.py`), always named
  literally `"\\top"`/`"\\bot"`.
  These two literal strings are hardcoded (string-literal `==`/`in` comparisons, not
  collection lookups) at 8 call sites across the core module:
  `utils/parsing.py` (×2: `parse_expression`, `op_left_right::extract_arguments`),
  `syntactic/formulas.py::is_syntactically_wff`,
  `syntactic/sentence.py` (×2: `__init__`, `Sentence.from_prefix`),
  `syntactic/syntax.py::initialize_sentences::build_sentence`,
  `syntactic/collection.py::apply_operator`,
  plus theory-local consumers `bimodal/semantic/formula.py:354` and
  `logos/subtheories/counterfactual/frame_oracle.py:1186,1188`.
  Renaming/aliasing `\top`/`\bot` would require touching all of the above; since the task
  explicitly scopes to "infix or prefix form" (arity 2 / arity 1), this is out of scope and
  should be called out as a deliberate non-goal in the plan, not silently expanded into.

### External Resources

No external web research was performed for this task; it is a pure codebase-internal
architecture question. The behavior described above (parser genericity, single-name bottleneck)
was verified directly against the running source, including the pre-existing unit tests that
already exercise Unicode operator names at the `syntactic` layer.

### Recommendations

1. **Add `aliases: List[str] = []`** as a new optional class attribute on
   `code/src/model_checker/syntactic/operators.py::Operator` (default empty list; documented
   alongside `name`/`arity`/`primitive`).
2. **Extend `OperatorCollection.add_operator`** (`code/src/model_checker/syntactic/collection.py`)
   to, after registering the canonical `operator.name` key, additionally register the same class
   under each string in `operator.aliases`, using the same duplicate-key policy as the canonical
   name today (skip-silently vs. raise `DuplicateOperatorError` — recommend switching both paths
   to raise `DuplicateOperatorError`, since silent collision is a latent footgun for a
   user-editable alias and the error class already exists unused).
3. **No changes needed** to `utils/parsing.py`, `syntactic/sentence.py`, or `syntactic/syntax.py`
   for arity-1/arity-2 operators — confirmed generic today.
4. **Decide deliberately** (planner-level decision, not silently inherited) whether
   `is_syntactically_wff` should be tightened to recognize aliased/Unicode operator heads
   explicitly (by consulting a known-operator-name set or arity/shape rather than the
   `not head.startswith('\\')` heuristic), or left as-is (functionally passes today, but for the
   wrong stated reason).
5. **Wire `UnknownOperatorError`** into `OperatorCollection.__getitem__`/`apply_operator`'s
   `self[op]` lookup so a mistyped or unregistered alias produces a helpful message
   (`available_operators` list) instead of a bare `KeyError`.
6. **Update `docs/usage/OPERATORS.md`** to replace the blanket "never use Unicode" guidance with
   the new alias convention and a worked example (e.g. `AndOperator` with `name = "\\wedge"`,
   `aliases = ["∧"]`).
7. Treat `jupyter/unicode.py`'s `UNICODE_OPERATOR_EXTENSIONS` precedent and
   `builder/translation.py`'s `dictionary` field as **prior art to learn from, not to build on** —
   both are pre-parse string-substitution mechanisms living outside `operators.py`, whereas this
   task asks for the choice to live in `operators.py` itself and be resolved by the real parser/
   operator-collection lookup, which the `aliases` attribute achieves directly.
8. Explicitly exclude `\top`/`\bot` (nullary) aliasing from this task's scope; if wanted later, it
   is a separate, larger task touching 8+ call sites.

## Decisions

- Scope is arity-1 (prefix) and arity-2 (infix) operators only, per the task description's own
  "infix or prefix form" phrasing; nullary extremal constants are explicitly excluded.
- The recommended mechanism is a new `Operator.aliases` class attribute plus an
  `OperatorCollection.add_operator` extension, not the pre-existing Jupyter-only
  `UNICODE_OPERATOR_EXTENSIONS`/`unicode.py` pathway and not the `examples.py`-level `dictionary`/
  `OperatorTranslation` pathway — both existing mechanisms were evaluated and are the wrong layer
  (display-only, or theory-to-theory translation of whole formula strings) for "user-specifiable
  ... in theory operators.py files."

## Risks & Mitigations

- **Risk**: Alias collisions across operators/theories (e.g. two operators wanting the same
  glyph) currently fail silently (duplicate name is a no-op skip). **Mitigation**: switch to
  raising `DuplicateOperatorError` for both the canonical-name and new alias registration paths
  (recommendation 2 above) so a collision is caught at theory-load time, not silently masked.
- **Risk**: `is_syntactically_wff`'s current accidental permissiveness for non-backslash operator
  heads could mask genuine malformed-formula bugs once Unicode aliases are common (recommendation
  4). **Mitigation**: flag as a planner-level decision rather than an accidental side effect;
  not a blocker for a minimal implementation, but should not be silently left as "works by
  coincidence."
- **Risk**: Scope creep into nullary (`\top`/`\bot`) aliasing given their prominent role in
  `examples.py` files (e.g. `EXT_TH_11_conclusions = ['\\top']`). **Mitigation**: explicit
  non-goal statement in the plan (finding above); nullary aliasing is a separate follow-up task
  if desired.
- **Risk**: Updating `docs/usage/OPERATORS.md`'s "never use Unicode" guidance without updating it
  consistently (Best Practices section, Troubleshooting section, and the "LaTeX Notation
  Requirements" table all currently assert the LaTeX-only convention) could leave contradictory
  guidance. **Mitigation**: the plan should treat all three locations in that one file as a single
  edit, not three independent edits.

## Context Extension Recommendations

- **Topic**: Operator-name aliasing convention for theory `operators.py` files.
- **Gap**: `docs/usage/OPERATORS.md` (and any `.claude/context/` project docs mirroring it) has no
  section on defining a Unicode alias for an operator; the file currently states the opposite
  convention.
- **Recommendation**: once implemented, add a new subsection to `docs/usage/OPERATORS.md` (e.g.
  "Unicode Aliases") showing the `aliases = [...]` pattern, and update the "LaTeX Notation
  Requirements" / "Best Practices" / "Troubleshooting" sections identified above so they no longer
  contradict it.

## Appendix

### Search queries / exploration used

- `find code/src/model_checker/theory_lib -iname 'operators.py'`
- `grep -rn -i "unicode" code/src/model_checker --include='*.py'`
- Full reads: `theory_lib/logos/subtheories/extensional/operators.py`,
  `syntactic/operators.py`, `syntactic/formulas.py`, `utils/parsing.py`, `syntactic/sentence.py`,
  `syntactic/syntax.py`, `syntactic/collection.py`, `jupyter/unicode.py`,
  `theory_lib/exclusion/__init__.py`, `builder/translation.py`, `docs/usage/OPERATORS.md`,
  `syntactic/errors.py`.
- Traced the "operators" dict flow end-to-end: `logos_registry.get_operators()` →
  `LogosOperatorRegistry.get_operators` (returns the live `OperatorCollection`, not a plain
  dict — verified by reading the actual method body, correcting an initial mis-read of a
  same-named but different method, `list_available_operators`) → `Syntax(premises, conclusions,
  operators)` in `builder/example.py`/`builder/runner.py` → `Sentence.update_types` →
  `OperatorCollection.apply_operator`.
- Confirmed via `grep -rn "arity = 0"` that `\top`/`\bot` are the only nullary operators in
  `theory_lib`.
- Confirmed via `code/src/model_checker/syntactic/tests/unit/test_operators.py` and
  `test_syntax.py` that Unicode-named operator classes (`name = "∧"`, `"∨"`, `"¬"`) are already
  used as first-class test fixtures for the parsing pipeline, independent of this task.
