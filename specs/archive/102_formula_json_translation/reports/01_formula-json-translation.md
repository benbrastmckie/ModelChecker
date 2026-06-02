# Research Report: Formula JSON Translation with Enriched Operator Support

**Task**: 102 — Formula JSON translation with enriched operator support
**Status**: Researched
**Session**: sess_1780336357_1a2c03
**Date**: 2026-06-01

---

## 1. Summary of Findings

Task 102 requires implementing `bimodal_logic/translation.py` with two primary capabilities:
1. `json_to_prefix(formula_json) -> list` — translate a JSON formula dict (17 tags) into ModelChecker prefix-list format
2. `temporal_depth(formula_json) -> int` — recursively compute the temporal nesting depth of a formula

A secondary concern is whether `Sentence.from_prefix()` or a `Syntax` programmatic constructor is needed, or whether the existing `Syntax(infix_premises, infix_conclusions, operator_collection)` can consume the translated formula. The research shows that `Syntax` currently accepts only infix strings; a programmatic bypass is needed.

---

## 2. Current Formula Translation Infrastructure

### 2.1 Existing Translation File (Stub)

`/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/translation.py` is a stub with only:
```python
"""bimodal_logic.translation - Formula translation utilities stub.
NOTE: Placeholder stub - full implementation in task 102 (translation/serialization).
"""
from __future__ import annotations
```

### 2.2 Unrelated Translation Utility

`/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/translation.py` contains `OperatorTranslation.translate()` — a simple string-replacement utility for swapping operator symbols in infix formulas. This is NOT related to JSON translation; it is used for multi-theory comparisons (now dead code after task 100).

### 2.3 No Existing JSON Translation

There is zero existing JSON-to-formula translation in the ModelChecker codebase. The task is new implementation, not a refactor.

---

## 3. Formula Structure: Infix, Prefix, and Sentence

### 3.1 The Parsing Pipeline

The ModelChecker represents formulas in two forms:
- **Infix string** (human-readable): `"(p \\wedge q)"`, `"\\next A"`, `"\\Bot"`
- **Prefix list** (machine-processable): `['\\wedge', 'p', 'q']`, `['\\next', 'A']`, `['\\bot']`

`Sentence.__init__(infix_sentence)` drives the conversion:
1. Calls `self.prefix(infix_sentence)` to produce a `prefix_sentence` list
2. The `prefix()` method calls `parse_expression(tokens)` (propositional parser)
3. On `Syntax.initialize_sentences()`, `sentence.update_types(operator_collection)` is called to replace string operator names with actual operator classes

### 3.2 Operator Names in Prefix Lists

The prefix format uses operator `name` attributes as string keys:
- `BotOperator.name = "\\bot"` → prefix token `"\\bot"`
- `NegationOperator.name = "\\neg"` → prefix token `"\\neg"`
- `AndOperator.name = "\\wedge"` → prefix token `"\\wedge"`
- `OrOperator.name = "\\vee"` → prefix token `"\\vee"`
- `TopOperator.name = "\\top"` → prefix token `"\\top"`
- `NecessityOperator.name = "\\Box"` → prefix token `"\\Box"`
- `DefPossibilityOperator.name = "\\Diamond"` → prefix token `"\\Diamond"`
- `FutureOperator.name = "\\Future"` → prefix token `"\\Future"`
- `PastOperator.name = "\\Past"` → prefix token `"\\Past"`
- `UntilOperator.name = "\\Until"` → prefix token `"\\Until"`
- `SinceOperator.name = "\\Since"` → prefix token `"\\Since"`
- `DefFutureOperator.name = "\\future"` → prefix token `"\\future"`
- `DefPastOperator.name = "\\past"` → prefix token `"\\past"`
- `DefNextOperator.name = "\\next"` → prefix token `"\\next"`
- `DefPrevOperator.name = "\\prev"` → prefix token `"\\prev"`

Atoms are bare alphanumeric strings (e.g., `"p"`, `"q"`).

### 3.3 Prefix List Format

The prefix list structure follows these rules:
- Atom: `["p"]` (single-element list with bare string)
- Nullary operator: `["\\bot"]` or `["\\top"]`
- Unary operator: `["\\neg", argument_list]`
- Binary operator: `["\\wedge", left_list, right_list]`
- Until (binary): `["\\Until", event_list, guard_list]`

Example: `(p \\wedge \\neg q)` → `["\\wedge", ["p"], ["\\neg", ["q"]]]`

### 3.4 Syntax Constructor Takes Infix Strings Only

`Syntax.__init__(infix_premises, infix_conclusions, operator_collection)` currently only accepts infix strings. It calls `Sentence(infix_string)` which calls the infix parser. There is no `Sentence.from_prefix()` classmethod.

**Resolution**: Task 102 must add a `Sentence.from_prefix(prefix_list, _internal=False)` classmethod that bypasses the infix parser and directly sets `prefix_sentence` and `complexity`. This is the lowest-risk approach and avoids changes to `Syntax` itself.

Alternatively (and more cleanly), `json_to_prefix()` can return infix strings directly using `Sentence.infix()` — but this loses structural fidelity and requires care with operator symbol quoting.

**Recommended approach**: Implement `json_to_prefix(formula_json) -> list` that produces a prefix list directly, then add `Sentence.from_prefix(prefix_list)` to create Sentence objects without the infix round-trip. This preserves structural precision for nested formulas.

---

## 4. JSON Tags: 6 Primitive + 11 Enriched

### 4.1 The 6 Primitive JSON Tags

From `BimodalHarness/src/bimodal_harness/formula/ast.py` and `oracle/_mock.py`:

| JSON Tag | Fields | Operator | Operator Name |
|----------|--------|----------|---------------|
| `"atom"` | `"name": str` | (atom) | bare string |
| `"bot"` | (none) | `BotOperator` | `"\\bot"` |
| `"imp"` | `"left"`, `"right"` | (none — primitive BimodalLogic op) | See note |
| `"box"` | `"child"` | `NecessityOperator` | `"\\Box"` |
| `"untl"` | `"event"`, `"guard"` | `UntilOperator` | `"\\Until"` |
| `"snce"` | `"event"`, `"guard"` | `SinceOperator` | `"\\Since"` |

**Important note on `"imp"`**: BimodalLogic uses `imp` as a primitive (Formula.imp in Lean). In ModelChecker, implication is `ConditionalOperator` (a `DefinedOperator` with `name = "\\rightarrow"`) defined as `[OrOperator, [NegationOperator, left], right]`. Task 102 description says "6 primitive tags map directly to primitive operator prefix-list format" — however `ConditionalOperator` is a defined operator in operators.py. The translation should use `ConditionalOperator` (name `"\\rightarrow"`) and let `update_types` expand it via `derived_definition`. This matches the task description: "imp→\\rightarrow (fields: left, right)".

### 4.2 The 11 Enriched JSON Tags

From the task 102 description:

| JSON Tag | Field(s) | Operator Class | Operator Name |
|----------|----------|----------------|---------------|
| `"neg"` | `"arg"` | `NegationOperator` | `"\\neg"` |
| `"top"` | (none) | `TopOperator` | `"\\top"` |
| `"and"` | `"left"`, `"right"` | `AndOperator` | `"\\wedge"` |
| `"or"` | `"left"`, `"right"` | `OrOperator` | `"\\vee"` |
| `"diamond"` | `"arg"` | `DefPossibilityOperator` | `"\\Diamond"` |
| `"next"` | `"arg"` | `DefNextOperator` | `"\\next"` |
| `"prev"` | `"arg"` | `DefPrevOperator` | `"\\prev"` |
| `"some_future"` | `"arg"` | `DefFutureOperator` | `"\\future"` |
| `"some_past"` | `"arg"` | `DefPastOperator` | `"\\past"` |
| `"all_future"` | `"arg"` | `FutureOperator` | `"\\Future"` |
| `"all_past"` | `"arg"` | `PastOperator` | `"\\Past"` |

**Field name clarification**: The task description says to "confirm exact field names from BimodalLogic Formula.toJson output or BimodalHarness schema." For primitive tags, the BimodalHarness schema is confirmed from `ast.py`: `imp` uses `"left"`/`"right"`, `box` uses `"child"`, `untl`/`snce` use `"event"`/`"guard"`. For enriched tags, there is no BimodalHarness schema yet (these are new). The task description specifies: unary enriched operators use `"arg"`, binary enriched operators use `"left"` and `"right"`.

---

## 5. Enriched Operator Classes (Tasks 100 and 111)

All enriched operator classes are implemented and registered in `bimodal_operators`:

### 5.1 Primitive Operators
- `BotOperator` (arity=0) — extremal falsity
- `NecessityOperator` (arity=1) — modal necessity
- `FutureOperator` (arity=1) — all-future (`\\Future`, all_past maps here for `\\Past`)
- `PastOperator` (arity=1) — all-past
- `UntilOperator` (arity=2) — until temporal
- `SinceOperator` (arity=2) — since temporal
- `NegationOperator` (arity=1) — extensional negation
- `AndOperator` (arity=2) — extensional conjunction
- `OrOperator` (arity=2) — extensional disjunction

### 5.2 Defined Operators
- `ConditionalOperator` (`\\rightarrow`, arity=2) — `[OrOperator, [NegationOperator, left], right]`
- `BiconditionalOperator` (`\\leftrightarrow`, arity=2) — defined via ConditionalOperator
- `TopOperator` (`\\top`, arity=0) — `[NegationOperator, [BotOperator]]`
- `DefPossibilityOperator` (`\\Diamond`, arity=1) — `[NegationOperator, [NecessityOperator, [NegationOperator, arg]]]`
- `DefFutureOperator` (`\\future`, arity=1) — `[NegationOperator, [FutureOperator, [NegationOperator, arg]]]`
- `DefPastOperator` (`\\past`, arity=1) — `[NegationOperator, [PastOperator, [NegationOperator, arg]]]`
- `DefNextOperator` (`\\next`, arity=1) — `[UntilOperator, arg, [BotOperator]]` — Added in task 111
- `DefPrevOperator` (`\\prev`, arity=1) — `[SinceOperator, arg, [BotOperator]]` — Added in task 111

All are registered in `bimodal_operators = syntactic.OperatorCollection(...)` at the bottom of `operators.py`.

---

## 6. temporal_depth Function Design

The `temporal_depth()` function must recursively walk the JSON formula AST and compute the maximum temporal nesting depth. Rules from the task description:

| Tag | temporal_depth rule |
|-----|---------------------|
| `"atom"`, `"bot"`, `"top"` | 0 |
| `"neg"`, `"imp"`, `"and"`, `"or"` | max of children |
| `"box"`, `"diamond"` | max of children (modal does NOT increment temporal depth) |
| `"untl"`, `"snce"` | 1 + max of children |
| `"next"`, `"prev"` | 1 + depth(arg) — since Next(φ) = U(φ, ⊥), temporal depth increments |
| `"some_future"`, `"some_past"` | 1 + depth(arg) — since F(φ) = U(φ, ⊤), increments |
| `"all_future"`, `"all_past"` | 1 + depth(arg) — since G(φ) = ¬F(¬φ), increments |

This matches the `temporal_depth()` function already implemented in `BimodalHarness/src/bimodal_harness/formula/ast.py` (which operates only on the 6 primitives). For enriched tags, we must account for their primitive expansions.

---

## 7. The `Sentence.from_prefix()` Gap

The task description requires `Sentence.from_prefix(prefix_list, operators)` — a classmethod that constructs `Sentence` objects programmatically, bypassing the infix parser. Currently:

- `Sentence.__init__()` always calls `self.prefix(infix_sentence)` to parse an infix string
- There is no way to initialize a `Sentence` from a pre-built prefix list
- `Syntax.__init__()` takes `infix_premises` and `infix_conclusions` (lists of strings)

**Options**:

1. **Add `Sentence.from_prefix(prefix_list)` classmethod** — creates a Sentence with the given prefix_list directly, sets `name` to an infix string derived via `Sentence.infix(prefix_list)`, sets `complexity` appropriately. This is the cleanest approach.

2. **Convert prefix to infix then use existing pipeline** — call `Sentence.infix(prefix_list)` to get a canonical infix string, then pass to `Syntax()` normally. Risk: infix conversion may produce strings that the parser cannot re-parse (operator symbol escaping issues).

3. **Add a programmatic overload to `Syntax`** — accept `Sentence` objects directly alongside infix strings. More invasive but more robust for the full pipeline.

**Recommended for task 102**: Option 1 — add `Sentence.from_prefix()` that sets internal state directly without calling the parser. This keeps changes isolated to `sentence.py` and does not affect `Syntax`.

The key insight from examining `Sentence.__init__()`: the `_internal=True` flag already bypasses WFF validation for subformulas. A `from_prefix()` method would also skip the infix-parser step.

---

## 8. Existing Tests and Test Patterns

### 8.1 Relevant Test Files

- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py` — tests for DefNextOperator/DefPrevOperator; shows patterns for:
  - `BimodalSemantics(settings)` construction
  - `run_test(example_case, ...)` equivalence verification
  - `Syntax(["formula_string"], [], bimodal_operators)` parsing

- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_until_since.py` — shows Until/Since test patterns

- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` — the main 43-example correctness test suite

### 8.2 Test Pattern for Equivalence

From `test_next_prev.py`, equivalence tests use `run_test`:
```python
result = run_test(
    [["\\next A"], ["\\Until A \\bot"], {}],
    BimodalSemantics,
    BimodalProposition,
    bimodal_operators,
    Syntax,
    ModelConstraints,
    BimodalStructure,
)
```

For task 102, the equivalence test would be:
1. Take a formula JSON dict with an enriched tag (e.g., `{"tag": "next", "arg": {"tag": "atom", "name": "p"}}`)
2. Translate to prefix list using `json_to_prefix()`
3. Convert to infix string (via `Sentence.infix()`) for use with `Syntax`
4. Run Z3 solving
5. Compare against the primitive-tag equivalent

---

## 9. Key Implementation Plan

### 9.1 Files to Modify

1. **`code/src/bimodal_logic/translation.py`** (primary file to implement):
   - `json_to_prefix(formula_json: dict) -> list` — 17-tag dispatcher
   - `temporal_depth(formula_json: dict) -> int` — depth calculator
   - Internal helper `_prefix_to_infix(prefix_list: list) -> str` — for Syntax compatibility

2. **`code/src/model_checker/syntactic/sentence.py`** (minor addition):
   - `Sentence.from_prefix(prefix_list, _internal=False) -> Sentence` classmethod

3. **New test file** (TDD-first):
   - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py` — tests for json_to_prefix, temporal_depth, and equivalence

### 9.2 Implementation of `json_to_prefix`

```python
def json_to_prefix(formula_json: dict) -> list:
    """Translate a formula JSON dict (17 tags) to ModelChecker prefix list."""
    tag = formula_json.get("tag")
    if tag == "atom":
        return [formula_json["name"]]
    elif tag == "bot":
        return ["\\bot"]
    elif tag == "top":
        return ["\\top"]
    elif tag == "imp":
        return ["\\rightarrow", json_to_prefix(formula_json["left"]),
                                json_to_prefix(formula_json["right"])]
    elif tag == "box":
        return ["\\Box", json_to_prefix(formula_json["child"])]
    elif tag == "untl":
        return ["\\Until", json_to_prefix(formula_json["event"]),
                           json_to_prefix(formula_json["guard"])]
    elif tag == "snce":
        return ["\\Since", json_to_prefix(formula_json["event"]),
                           json_to_prefix(formula_json["guard"])]
    # Enriched tags
    elif tag == "neg":
        return ["\\neg", json_to_prefix(formula_json["arg"])]
    elif tag == "and":
        return ["\\wedge", json_to_prefix(formula_json["left"]),
                           json_to_prefix(formula_json["right"])]
    elif tag == "or":
        return ["\\vee", json_to_prefix(formula_json["left"]),
                         json_to_prefix(formula_json["right"])]
    elif tag == "diamond":
        return ["\\Diamond", json_to_prefix(formula_json["arg"])]
    elif tag == "next":
        return ["\\next", json_to_prefix(formula_json["arg"])]
    elif tag == "prev":
        return ["\\prev", json_to_prefix(formula_json["arg"])]
    elif tag == "some_future":
        return ["\\future", json_to_prefix(formula_json["arg"])]
    elif tag == "some_past":
        return ["\\past", json_to_prefix(formula_json["arg"])]
    elif tag == "all_future":
        return ["\\Future", json_to_prefix(formula_json["arg"])]
    elif tag == "all_past":
        return ["\\Past", json_to_prefix(formula_json["arg"])]
    else:
        raise ValueError(f"Unknown formula tag: {tag!r}")
```

### 9.3 Infix Conversion for Syntax Pipeline

The `Sentence.infix(prefix_list)` method can convert a prefix list back to an infix string. This method already exists on Sentence instances. The translation module can use it by creating a temporary Sentence or using the static conversion logic.

However, there is a subtlety: `Sentence.infix()` is an instance method that calls `self.infix(prefix)` recursively. The cleanest solution is to extract infix conversion as a standalone function `prefix_to_infix(prefix_list) -> str`.

### 9.4 Pipeline Integration

The full pipeline for `OracleProvider.find_countermodel(formula_json)` will be:
1. `prefix_list = json_to_prefix(formula_json)` — in `translation.py`
2. `infix_str = prefix_to_infix(prefix_list)` — in `translation.py`
3. `syntax = Syntax([infix_str], [], bimodal_operators)` — existing infrastructure
4. Continue with `BimodalSemantics` → `ModelConstraints` → `BimodalStructure` → Z3

---

## 10. Downstream Consumer Requirements

### 10.1 Task 103 (OracleProvider)
Needs `json_to_prefix()` and `temporal_depth()` from `translation.py`. The `temporal_depth()` result determines `M = max(temporal_depth + 2, 3)`.

### 10.2 Task 112 (fold/unfold normalization)
Needs the enriched-to-primitive expansion rules and the reverse. Since `json_to_prefix()` preserves enriched operator names (e.g., `"\\next"` for the `"next"` tag), and `Syntax.update_types()` calls `derive_type()` to expand defined operators to primitives, the fold direction requires a separate JSON-level traversal that maps primitive patterns back to enriched tags.

### 10.3 Task 107 (boundary effect analysis)
Needs `temporal_depth(formula_json)` to work correctly for all 17 tags including enriched operators.

### 10.4 Task 113 (enriched operator equivalence tests)
Needs both enriched-tag translation path and primitive-expansion path to produce identical Z3 results. The equivalence verification should be built into task 102's test suite as the acceptance gate.

---

## 11. Open Questions Resolved

1. **Does `Syntax.__init__()` accept Sentence objects?** No, it accepts only infix strings. The fix is to add `Sentence.from_prefix()` or use infix conversion.

2. **What are the exact field names for enriched tags?** Unary enriched operators use `"arg"`, binary use `"left"` / `"right"`. This is specified in the task description and consistent with Lean naming conventions.

3. **Does `"imp"` map to a primitive or defined operator?** In ModelChecker, `ConditionalOperator` is defined (not primitive). But `update_types()` with `derive_type()` will expand it automatically. Using `"\\rightarrow"` in the prefix list is correct — the OperatorCollection handles expansion.

4. **What is the temporal_depth for enriched operators?** All temporal operators (next, prev, some_future, some_past, all_future, all_past) increment temporal depth by 1. Modal operators (box, diamond) do NOT increment temporal depth. This is because enriched temporal operators are defined in terms of untl/snce (which are depth-1 operators).

---

## 12. Test Strategy

### 12.1 Test File Structure
Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py`

### 12.2 Test Categories (TDD order)

**Phase 1: json_to_prefix tests (all 17 tags)**
- `test_atom_translation` — `{"tag": "atom", "name": "p"}` → `["p"]`
- `test_bot_translation` — `{"tag": "bot"}` → `["\\bot"]`
- `test_imp_translation` — `{"tag": "imp", "left": atom_p, "right": atom_q}` → `["\\rightarrow", ["p"], ["q"]]`
- `test_box_translation` — `{"tag": "box", "child": atom_p}` → `["\\Box", ["p"]]`
- `test_untl_translation` — `{"tag": "untl", "event": atom_p, "guard": atom_q}` → `["\\Until", ["p"], ["q"]]`
- `test_snce_translation` — similar
- `test_neg_translation` — `{"tag": "neg", "arg": atom_p}` → `["\\neg", ["p"]]`
- `test_top_translation` — `{"tag": "top"}` → `["\\top"]`
- `test_and_translation`, `test_or_translation`
- `test_diamond_translation`, `test_next_translation`, `test_prev_translation`
- `test_some_future_translation`, `test_some_past_translation`
- `test_all_future_translation`, `test_all_past_translation`
- `test_nested_translation` — e.g., `{"tag": "neg", "arg": {"tag": "next", "arg": atom_p}}`
- `test_unknown_tag_raises` — `{"tag": "invalid"}` raises `ValueError`

**Phase 2: temporal_depth tests**
- Leaf nodes: atom, bot, top → 0
- Modal: box, diamond → propagate (no increment)
- Extensional: neg, imp, and, or → max of children
- Temporal primitive: untl, snce → 1 + max children
- Temporal enriched: next, prev, some_future, some_past, all_future, all_past → 1 + depth(arg)
- Nested: `{"tag": "next", "arg": {"tag": "untl", ...}}` → 2

**Phase 3: Syntax integration tests**
- Translate JSON to prefix, convert to infix, verify Syntax parsing works
- Verify `update_types()` correctly expands defined operators

**Phase 4: Z3 equivalence tests (acceptance gate)**
- For each of the 11 enriched operators, verify:
  - Translating via enriched tag produces identical SAT/UNSAT result as primitive expansion
  - Use `run_test()` pattern from `test_next_prev.py`
  - At least 2 test cases per operator (SAT and UNSAT)

---

## 13. Key Files

| File | Purpose | Action |
|------|---------|--------|
| `/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/translation.py` | Primary implementation target | Implement `json_to_prefix`, `temporal_depth`, `prefix_to_infix` |
| `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/sentence.py` | Sentence class | Add `Sentence.from_prefix()` classmethod |
| `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` | Operator classes | Read-only reference; all 17 operators present |
| `/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/__init__.py` | Public API | May need to export `json_to_prefix`, `temporal_depth` |
| `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/formula/ast.py` | Reference implementation | `temporal_depth` for 6 primitives; enriched operators need extending |
| `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/_mock.py` | JSON schema examples | Confirmed primitive tag format |
| `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py` | Test pattern reference | `run_test()` equivalence pattern |

---

## 14. Risk Assessment

| Risk | Likelihood | Mitigation |
|------|------------|------------|
| `prefix_to_infix()` produces strings that the parser cannot parse | Medium | Test round-trip: `infix → prefix → infix → prefix` must be identical |
| Enriched operators produce different Z3 constraints than primitives due to `derive_type()` expansion path | Low | Covered by equivalence tests in Phase 4 |
| G/H boundary issue with ForAllTime guard | Medium | `temporal_depth` mitigation in task 103; task 102 just needs correct depth values |
| `"imp"` mapping to `ConditionalOperator` (defined) vs primitive | Low | `update_types` + `derive_type` handles this transparently |
| Unknown tags silently accepted | Low | Fail-fast validation: raise ValueError for unknown tags |
