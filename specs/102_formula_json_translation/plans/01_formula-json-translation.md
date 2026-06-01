# Implementation Plan: Formula JSON Translation with Enriched Operator Support

- **Task**: 102 - Formula JSON translation with enriched operator support
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: 100 (completed), 111 (completed)
- **Research Inputs**: specs/102_formula_json_translation/reports/01_formula-json-translation.md
- **Artifacts**: plans/01_formula-json-translation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Implement the JSON-to-internal formula translation layer in `bimodal_logic/translation.py`, supporting all 17 JSON formula tags (6 primitive + 11 enriched). The implementation includes three core functions: `json_to_prefix()` for converting JSON formula dicts to ModelChecker prefix-list format, `temporal_depth()` for computing temporal nesting depth, and `prefix_to_infix()` as a standalone infix converter. A `Sentence.from_prefix()` classmethod is added to `sentence.py` to enable programmatic Sentence construction without the infix parser round-trip. TDD methodology is followed throughout: tests are written before implementation in each phase.

### Research Integration

From the research report (01_formula-json-translation.md):
- The `translation.py` stub is empty -- this is greenfield implementation, not refactoring.
- All 17 operator classes are implemented and registered in `bimodal_operators` (including DefNextOperator and DefPrevOperator from task 111).
- Prefix list format: atoms as `["p"]`, nullary as `["\\bot"]`, unary as `["\\neg", ["p"]]`, binary as `["\\wedge", ["p"], ["q"]]`.
- `Sentence.__init__()` only accepts infix strings -- the `from_prefix()` classmethod is needed to bypass parsing.
- Field names confirmed: primitive tags use `"child"`, `"event"`/`"guard"`, `"left"`/`"right"`; enriched unary uses `"arg"`, enriched binary uses `"left"`/`"right"`.
- `temporal_depth` increments by 1 for all temporal operators (untl, snce, next, prev, some_future, some_past, all_future, all_past) but NOT for modal operators (box, diamond).
- The pipeline integration path: `json_to_prefix()` -> `prefix_to_infix()` -> `Syntax([infix_str], [], operators)` -- OR -- `json_to_prefix()` -> `Sentence.from_prefix()` for direct construction.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Implement `json_to_prefix(formula_json)` supporting all 17 JSON tags
- Implement `temporal_depth(formula_json)` with correct depth rules for all tags
- Implement `prefix_to_infix(prefix_list)` as a standalone function
- Add `Sentence.from_prefix(prefix_list)` classmethod to `sentence.py`
- Export public API from `bimodal_logic/__init__.py`
- Verify enriched operator equivalence via Z3 solving tests
- Full TDD: tests written before each implementation component

**Non-Goals**:
- Reverse direction (sentence-to-JSON serialization) -- deferred to later tasks
- `fold_formula()` / `unfold_formula()` normalization -- task 112
- OracleProvider integration -- task 103
- Property-based / fuzz testing -- task 113

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `prefix_to_infix()` produces strings the parser cannot re-parse | H | M | Round-trip tests: infix -> prefix -> infix -> prefix must be identical |
| `Sentence.from_prefix()` breaks existing Sentence lifecycle | H | L | Isolate changes to a classmethod; do not modify `__init__`; test existing 171 tests pass |
| Field name mismatch between task description and BimodalHarness schema | M | M | Research report resolved field names; add validation that raises on unknown fields |
| Enriched operators produce different Z3 results than primitives | H | L | Explicit equivalence tests using `run_test()` for each enriched operator |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Write Tests for json_to_prefix and temporal_depth [COMPLETED]

**Goal**: Create the test file with comprehensive tests for both `json_to_prefix()` and `temporal_depth()`, covering all 17 tags, nested formulas, and error cases. Tests will fail initially (RED phase of TDD).

**Tasks**:
- [x] Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py`
- [x] Write test class `TestJsonToPrefixPrimitives` with tests for all 6 primitive tags:
  - `test_atom_translation`: `{"tag": "atom", "name": "p"}` -> `["p"]`
  - `test_bot_translation`: `{"tag": "bot"}` -> `["\\bot"]`
  - `test_imp_translation`: `{"tag": "imp", "left": ..., "right": ...}` -> `["\\rightarrow", [...], [...]]`
  - `test_box_translation`: `{"tag": "box", "child": ...}` -> `["\\Box", [...]]`
  - `test_untl_translation`: `{"tag": "untl", "event": ..., "guard": ...}` -> `["\\Until", [...], [...]]`
  - `test_snce_translation`: `{"tag": "snce", "event": ..., "guard": ...}` -> `["\\Since", [...], [...]]`
- [x] Write test class `TestJsonToPrefixEnriched` with tests for all 11 enriched tags:
  - `test_neg_translation`, `test_top_translation`, `test_and_translation`, `test_or_translation`
  - `test_diamond_translation`, `test_next_translation`, `test_prev_translation`
  - `test_some_future_translation`, `test_some_past_translation`
  - `test_all_future_translation`, `test_all_past_translation`
- [x] Write test class `TestJsonToPrefixNested` with tests for nested/complex formulas:
  - `test_nested_neg_next`: `neg(next(atom))` -> `["\\neg", ["\\next", ["p"]]]`
  - `test_nested_binary`: `and(atom, or(atom, atom))` -> nested prefix
  - `test_deeply_nested`: 3+ levels of nesting
- [x] Write test class `TestJsonToPrefixErrors`:
  - `test_unknown_tag_raises_value_error`
  - `test_missing_tag_raises`
  - `test_missing_required_field_raises`
- [x] Write test class `TestTemporalDepth` covering all depth rules:
  - Leaf nodes: atom -> 0, bot -> 0, top -> 0
  - Extensional: neg -> max children, imp -> max children, and -> max children, or -> max children
  - Modal: box -> max children (no increment), diamond -> max children (no increment)
  - Temporal primitive: untl -> 1 + max children, snce -> 1 + max children
  - Temporal enriched: next -> 1 + depth(arg), prev -> 1 + depth(arg), some_future/some_past/all_future/all_past -> 1 + depth(arg)
  - Nested temporal: `next(untl(atom, atom))` -> 2
  - Mixed modal-temporal: `box(next(atom))` -> 1 (box does not increment)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py` - NEW: comprehensive test suite

**Verification**:
- Test file exists and is syntactically valid Python
- All tests fail with ImportError or similar (functions not yet implemented)

---

### Phase 2: Implement json_to_prefix, temporal_depth, and prefix_to_infix [NOT STARTED]

**Goal**: Implement the three core translation functions in `translation.py` so that all Phase 1 tests pass (GREEN phase of TDD).

**Tasks**:
- [ ] Implement `json_to_prefix(formula_json: dict) -> list` in `translation.py`:
  - 17-tag dispatcher mapping JSON tags to prefix lists
  - Recursive descent for nested formulas
  - Fail-fast: raise `ValueError` for unknown tags or missing required fields
- [ ] Implement `temporal_depth(formula_json: dict) -> int` in `translation.py`:
  - Recursive walker with correct depth rules per tag category
  - Atom/bot/top -> 0
  - neg/imp/and/or -> max of children
  - box/diamond -> max of children (NO increment)
  - untl/snce -> 1 + max of children
  - next/prev/some_future/some_past/all_future/all_past -> 1 + depth(arg)
- [ ] Implement `prefix_to_infix(prefix_list: list) -> str` in `translation.py`:
  - Standalone function (not Sentence method) for converting prefix to infix
  - Handle atoms, nullary, unary, and binary operators
  - Produce parenthesized infix strings compatible with the existing parser
- [ ] Update `bimodal_logic/__init__.py` to export `json_to_prefix`, `temporal_depth`, `prefix_to_infix`
- [ ] Run Phase 1 tests: all must pass

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/bimodal_logic/translation.py` - implement three functions
- `code/src/bimodal_logic/__init__.py` - add exports

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py -v` -- all tests pass
- Existing tests unaffected: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` -- no regressions

---

### Phase 3: Implement Sentence.from_prefix and Syntax Integration Tests [NOT STARTED]

**Goal**: Add the `Sentence.from_prefix()` classmethod to `sentence.py` and write+run integration tests verifying the full pipeline from JSON through Syntax to Z3 solving.

**Tasks**:
- [ ] Write test class `TestSentenceFromPrefix` in `test_json_translation.py`:
  - `test_from_prefix_creates_sentence`: Verify Sentence object is created
  - `test_from_prefix_preserves_prefix_list`: `sentence.prefix_sentence` matches input
  - `test_from_prefix_sets_name`: `sentence.name` is a valid infix string
  - `test_from_prefix_sets_complexity`: `sentence.complexity` is correct
  - `test_from_prefix_with_operator`: Verify operator-bearing formulas have `original_operator`
- [ ] Write test class `TestSyntaxIntegration` in `test_json_translation.py`:
  - `test_prefix_to_infix_round_trip`: json_to_prefix -> prefix_to_infix -> Syntax parses
  - `test_syntax_with_enriched_operator`: Full pipeline with enriched tag formula
  - `test_update_types_works_with_from_prefix`: Sentence.from_prefix -> update_types succeeds
- [ ] Implement `Sentence.from_prefix(cls, prefix_list)` classmethod in `sentence.py`:
  - Create Sentence instance without calling the infix parser
  - Set `prefix_sentence` directly from input
  - Compute `name` via `self.infix(prefix_list)` for display
  - Compute `complexity` from prefix list structure
  - Set `original_arguments`, `original_operator` from prefix structure
  - Initialize remaining attributes (arguments, operator, sentence_letter, proposition) to None
- [ ] Run integration tests: all must pass

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/syntactic/sentence.py` - add `from_prefix()` classmethod
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py` - add integration tests

**Verification**:
- All new tests pass
- All existing 171+ bimodal tests still pass (no regressions)
- `PYTHONPATH=code/src pytest code/tests/ -v` -- full suite passes

---

### Phase 4: Enriched Operator Z3 Equivalence Tests [NOT STARTED]

**Goal**: Verify that translating via enriched tags and solving with Z3 produces identical results as translating via primitive expansions. This is the acceptance gate for the translation layer.

**Tasks**:
- [ ] Write test class `TestEnrichedEquivalence` in `test_json_translation.py`:
  - For each of 11 enriched operators, write a test verifying semantic equivalence using `run_test()`:
    - `test_neg_equivalence`: `\\neg A` <-> `(A \\rightarrow \\bot)` is a theorem
    - `test_top_equivalence`: `\\top` <-> `(\\bot \\rightarrow \\bot)` is a theorem (or `\\neg \\bot`)
    - `test_and_equivalence`: `(A \\wedge B)` <-> `\\neg (A \\rightarrow \\neg B)` is a theorem
    - `test_or_equivalence`: `(A \\vee B)` <-> `(\\neg A \\rightarrow B)` is a theorem
    - `test_diamond_equivalence`: `\\Diamond A` <-> `\\neg \\Box \\neg A` is a theorem
    - `test_next_equivalence`: `\\next A` <-> `(A \\Until \\bot)` is a theorem
    - `test_prev_equivalence`: `\\prev A` <-> `(A \\Since \\bot)` is a theorem
    - `test_some_future_equivalence`: `\\future A` <-> `\\neg \\Future \\neg A` is a theorem
    - `test_some_past_equivalence`: `\\past A` <-> `\\neg \\Past \\neg A` is a theorem
    - `test_all_future_equivalence`: `\\Future A` exists as primitive -- test G(A) via infix
    - `test_all_past_equivalence`: `\\Past A` exists as primitive -- test H(A) via infix
  - Each test uses `isolated_z3_context()` and the `run_test()` pattern from `test_next_prev.py`
- [ ] Write test class `TestJsonToZ3Pipeline` verifying full JSON-to-Z3 pipeline:
  - `test_json_atom_through_pipeline`: JSON atom -> prefix -> infix -> Syntax -> parse succeeds
  - `test_json_compound_through_pipeline`: JSON compound formula -> solve -> correct result
  - `test_json_temporal_depth_matches_prefix`: temporal_depth from JSON matches prefix complexity
- [ ] Run all tests: full test suite must pass

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py` - add equivalence and pipeline tests

**Verification**:
- All equivalence tests pass (11 enriched operators verified)
- Full pipeline tests pass
- Full test suite: `PYTHONPATH=code/src pytest code/tests/ -v` -- all pass
- No regressions in existing 171+ tests

---

## Testing & Validation

- [ ] All 17 JSON tags translate correctly to prefix lists
- [ ] `temporal_depth()` returns correct values for all tag categories
- [ ] `prefix_to_infix()` produces strings the parser can re-parse
- [ ] `Sentence.from_prefix()` creates valid Sentence objects
- [ ] Enriched operator Z3 equivalence verified for all 11 enriched operators
- [ ] Existing 171+ bimodal tests show no regressions
- [ ] Full test suite: `PYTHONPATH=code/src pytest code/tests/ -v`

## Artifacts & Outputs

- `specs/102_formula_json_translation/plans/01_formula-json-translation.md` (this file)
- `code/src/bimodal_logic/translation.py` - `json_to_prefix`, `temporal_depth`, `prefix_to_infix`
- `code/src/model_checker/syntactic/sentence.py` - `Sentence.from_prefix()` classmethod
- `code/src/bimodal_logic/__init__.py` - updated exports
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py` - comprehensive test suite

## Rollback/Contingency

- `translation.py` is currently an empty stub -- revert to stub if implementation fails
- `Sentence.from_prefix()` is additive (classmethod) -- remove if it causes regressions
- `__init__.py` export additions are additive -- revert by removing import lines
- Git history preserves all prior states; `git checkout` of individual files sufficient
