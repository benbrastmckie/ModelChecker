# Implementation Plan: Fold/Unfold Formula Normalization Utilities

- **Task**: 112 - Fold/unfold formula normalization utilities
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: 102 (completed)
- **Research Inputs**: specs/112_fold_unfold_formula_normalization/reports/01_fold-unfold-normalization.md
- **Artifacts**: plans/01_fold-unfold-normalization.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Implement three formula JSON-to-JSON transformation functions in `code/src/bimodal_logic/translation.py`: `unfold_formula` (expand enriched tags to primitives), `fold_formula` (recognize primitive patterns as enriched tags), and `normalize_formula` (fold/unfold to a specific operator level). The functions operate entirely in the formula dict domain, building on the existing tag classification infrastructure from task 102. The primary challenge is the fold algorithm's overlapping pattern disambiguation -- five enriched operators share the outer `imp(_, bot)` structure and must be checked in specificity order (Level 3 before Level 1).

### Research Integration

Key findings from the research report:
1. The 11 enriched operators form a 3-level dependency hierarchy: Level 1 (neg, top, next, prev), Level 2 (and, or, diamond, some_future, some_past), Level 3 (all_future, all_past).
2. Unfold is a straightforward recursive descent dispatching on tags, building primitive nodes from already-unfolded children.
3. Fold requires outside-in pattern matching with Level 3 to Level 1 ordering. Within `imp(_, bot)`, the discriminant is the left child's structure: untl/snce with top guard = all_future/all_past, box = diamond, imp with neg-right = and, anything else = neg.
4. `top` (imp(bot, bot)) must be checked before `neg` since both are Level 1 but `top` is more specific.
5. The correct round-trip property is `unfold(fold(unfold(f))) == unfold(f)`, not `fold(unfold(f)) == f`.
6. Field naming conventions: `arg` for enriched unary, `left`/`right` for binary, `child` for box, `event`/`guard` for untl/snce.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Implement `unfold_formula` that recursively reduces all 11 enriched tags to the 6 primitives
- Implement `fold_formula` that greedily replaces primitive patterns with enriched tags using outside-in Level 3 to Level 1 matching
- Implement `normalize_formula` that fold/unfolds to a specified operator level (0-3)
- Export all three functions from `bimodal_logic/__init__.py`
- Achieve 100% coverage of all 17 tags in both directions
- Pass round-trip property test for 100+ randomly generated formulas

**Non-Goals**:
- Modifying the existing `json_to_prefix`, `temporal_depth`, or `prefix_to_infix` functions
- Implementing formula simplification or algebraic reduction
- Supporting any formula representation other than JSON dicts

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fold pattern ordering error in `imp(_, bot)` family | H | M | Explicit test for each of the 11 enriched patterns, plus targeted overlapping-pattern tests |
| `top` vs `neg bot` ambiguity | M | L | Check `top` pattern (both sides bot) before `neg` pattern (any left, right=bot) |
| Random formula generator producing malformed formulas | L | L | Validate generator output matches JSON schema before using in property tests |
| Deep recursion on large formulas | L | L | Python default recursion limit (1000) is sufficient for test formulas with max_depth 4-5 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: unfold_formula with TDD [COMPLETED]

**Goal**: Implement `unfold_formula` that recursively expands all 11 enriched tags to the 6 primitive tags, with comprehensive unit tests written first.

**Tasks**:
- [ ] Create test file `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py`
- [ ] Write `TestUnfoldFormula` test class with tests for:
  - [ ] Primitive passthrough: atom, bot, imp, box, untl, snce are returned unchanged (structurally)
  - [ ] Level 1 expansions: neg -> imp(phi, bot), top -> imp(bot, bot), next -> untl(phi, bot), prev -> snce(phi, bot)
  - [ ] Level 2 expansions: and -> imp(imp(phi, imp(psi, bot)), bot), or -> imp(imp(phi, bot), psi), diamond -> imp(box(imp(phi, bot)), bot), some_future -> untl(phi, imp(bot, bot)), some_past -> snce(phi, imp(bot, bot))
  - [ ] Level 3 expansions: all_future -> imp(untl(imp(phi, bot), imp(bot, bot)), bot), all_past -> imp(snce(imp(phi, bot), imp(bot, bot)), bot)
  - [ ] Nested formula: unfold(neg(and(p, q))) produces only primitive tags
  - [ ] Idempotency: unfold(unfold(f)) == unfold(f) for several examples
- [ ] Write `test_unfold_produces_only_primitives` helper that walks a result and asserts all tags are in {atom, bot, imp, box, untl, snce}
- [ ] Add private helpers to `translation.py`: `_make_bot()`, `_make_top_expanded()`
- [ ] Implement `unfold_formula(formula_json: dict) -> dict` in `translation.py` using recursive dispatch on all 17 tags
- [ ] Run tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py::TestUnfoldFormula -v`
- [ ] Verify all unfold tests pass

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/bimodal_logic/translation.py` -- add `_make_bot`, `_make_top_expanded`, `unfold_formula`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` -- create with `TestUnfoldFormula`

**Verification**:
- All `TestUnfoldFormula` tests pass
- unfold of every enriched tag produces correct primitive expansion
- Nested formulas produce only primitive tags

---

### Phase 2: fold_formula with TDD [COMPLETED]

**Goal**: Implement `fold_formula` with outside-in pattern matching that correctly disambiguates all overlapping patterns, with unit tests for each of the 11 enriched patterns written first.

**Tasks**:
- [ ] Write `TestFoldFormula` test class with tests for:
  - [ ] Primitive passthrough: atom, bot, imp(p, q), box(p), untl(p, q), snce(p, q) are returned unchanged when they do not match any enriched pattern
  - [ ] Level 1 recognition: imp(p, bot) -> neg(p), imp(bot, bot) -> top, untl(p, bot) -> next(p), snce(p, bot) -> prev(p)
  - [ ] Level 2 recognition: imp(imp(p, imp(q, bot)), bot) -> and(p, q), imp(imp(p, bot), q) -> or(p, q), imp(box(imp(p, bot)), bot) -> diamond(p), untl(p, imp(bot, bot)) -> some_future(p), snce(p, imp(bot, bot)) -> some_past(p)
  - [ ] Level 3 recognition: imp(untl(imp(p, bot), imp(bot, bot)), bot) -> all_future(p), imp(snce(imp(p, bot), imp(bot, bot)), bot) -> all_past(p)
  - [ ] Children are recursively folded: fold(imp(imp(p, bot), bot)) -> neg(neg(p)) not neg(imp(p, bot))
- [ ] Write `TestOverlappingPatterns` test class with targeted ambiguity tests:
  - [ ] `top` preferred over `neg(bot)`: fold(imp(bot, bot)) -> top, not neg(bot)
  - [ ] `all_future` preferred over `neg`: fold(imp(untl(imp(p, bot), imp(bot, bot)), bot)) -> all_future(p), not neg(untl(neg(p), top))
  - [ ] `all_past` preferred over `neg`: fold(imp(snce(imp(p, bot), imp(bot, bot)), bot)) -> all_past(p), not neg(snce(neg(p), top))
  - [ ] `diamond` preferred over `neg`: fold(imp(box(imp(p, bot)), bot)) -> diamond(p), not neg(box(neg(p)))
  - [ ] `and` preferred over `neg`: fold(imp(imp(p, imp(q, bot)), bot)) -> and(p, q), not neg(imp(p, neg(q)))
  - [ ] `or` not confused with `neg`: fold(imp(imp(p, bot), q)) -> or(p, q) when q is not bot
- [ ] Add private helpers to `translation.py`: `_is_bot(node)`, `_is_top_pattern(node)`
- [ ] Implement `fold_formula(formula_json: dict) -> dict` in `translation.py` using outside-in pattern matching with Level 3 -> Level 2 -> Level 1 ordering
- [ ] Run tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py::TestFoldFormula -v`
- [ ] Run overlap tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py::TestOverlappingPatterns -v`
- [ ] Verify all fold and overlap tests pass

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/bimodal_logic/translation.py` -- add `_is_bot`, `_is_top_pattern`, `fold_formula`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` -- add `TestFoldFormula`, `TestOverlappingPatterns`

**Verification**:
- All `TestFoldFormula` tests pass (11 enriched patterns correctly identified)
- All `TestOverlappingPatterns` tests pass (disambiguation order correct)
- fold correctly recursively folds children

---

### Phase 3: normalize_formula and exports [COMPLETED]

**Goal**: Implement `normalize_formula` that fold/unfolds to a specific operator level, export all new functions from `__init__.py`, and verify level-based normalization.

**Tasks**:
- [ ] Write `TestNormalizeFormula` test class with tests for:
  - [ ] Level 0 equals unfold: normalize(f, 0) == unfold(f) for several enriched formulas
  - [ ] Level 1 allows neg/top/next/prev: normalize(and(p, q), 1) uses neg but not and
  - [ ] Level 2 allows all Level 1 + and/or/diamond/some_future/some_past: normalize(all_future(p), 2) uses neg and some_future but not all_future
  - [ ] Level 3 equals full fold of unfolded: normalize(f, 3) == fold(unfold(f)) for several formulas
  - [ ] Invalid level raises ValueError for level < 0 or level > 3
- [ ] Implement internal `_fold_at_level(formula_json: dict, max_level: int) -> dict` that restricts pattern matching to patterns at or below `max_level`
- [ ] Implement `normalize_formula(formula_json: dict, level: int) -> dict` as `_fold_at_level(unfold_formula(formula_json), level)`
- [ ] Update `code/src/bimodal_logic/__init__.py` to export `unfold_formula`, `fold_formula`, `normalize_formula`
- [ ] Run tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py::TestNormalizeFormula -v`
- [ ] Verify imports work: `PYTHONPATH=code/src python -c "from bimodal_logic import unfold_formula, fold_formula, normalize_formula; print('OK')"`

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `code/src/bimodal_logic/translation.py` -- add `_fold_at_level`, `normalize_formula`
- `code/src/bimodal_logic/__init__.py` -- add exports for `unfold_formula`, `fold_formula`, `normalize_formula`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` -- add `TestNormalizeFormula`

**Verification**:
- All `TestNormalizeFormula` tests pass
- Imports from `bimodal_logic` work for all three new functions
- Level 0 produces only primitives, Level 3 maximizes enriched usage

---

### Phase 4: Property-based tests and gate validation [COMPLETED]

**Goal**: Implement random formula generator, run round-trip property tests on 100+ formulas, verify all gate criteria, and run the full test suite to confirm no regressions.

**Tasks**:
- [ ] Write `random_formula(atoms, max_depth, rng)` helper function in the test file that generates random formula JSON using all 17 tags
- [ ] Write `TestRoundTrip` test class with property-based tests:
  - [ ] `test_unfold_fold_roundtrip_100`: for 100+ random formulas, assert `unfold(fold(unfold(f))) == unfold(f)`
  - [ ] `test_fold_idempotent_after_unfold`: for 100+ random formulas, assert `fold(fold(unfold(f))) == fold(unfold(f))`
  - [ ] `test_unfold_idempotent`: for 100+ random formulas, assert `unfold(unfold(f)) == unfold(f)`
  - [ ] `test_unfold_produces_only_primitives`: for 100+ random formulas, assert all tags in unfold result are in {atom, bot, imp, box, untl, snce}
  - [ ] `test_normalize_level0_equals_unfold`: for 50+ random formulas, assert `normalize(f, 0) == unfold(f)`
  - [ ] `test_normalize_level3_equals_fold_unfold`: for 50+ random formulas, assert `normalize(f, 3) == fold(unfold(f))`
- [ ] Write `TestAllEnrichedPatternsFoldable` to verify fold recognizes all 11 enriched patterns from their primitive expansions (gate requirement)
- [ ] Run full test file: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py -v`
- [ ] Run full bimodal test suite for regression check: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] Run all project tests: `PYTHONPATH=code/src pytest code/tests/ -v`

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` -- add `random_formula`, `TestRoundTrip`, `TestAllEnrichedPatternsFoldable`

**Verification**:
- Round-trip property holds for 100+ randomly generated formulas
- fold correctly identifies all 11 enriched operator patterns from their primitive expansions
- All existing bimodal tests still pass (no regressions)
- All project tests pass

## Testing & Validation

- [ ] All `TestUnfoldFormula` tests pass (11 enriched + 6 primitive + nested + idempotency)
- [ ] All `TestFoldFormula` tests pass (11 enriched patterns recognized from primitive form)
- [ ] All `TestOverlappingPatterns` tests pass (disambiguation order verified)
- [ ] All `TestNormalizeFormula` tests pass (levels 0-3 produce correct operator sets)
- [ ] Round-trip property `unfold(fold(unfold(f))) == unfold(f)` holds for 100+ random formulas
- [ ] Fold idempotency `fold(fold(unfold(f))) == fold(unfold(f))` holds for 100+ random formulas
- [ ] All 11 enriched patterns are foldable from their primitive expansions (gate)
- [ ] `normalize(f, 0) == unfold(f)` for all test formulas
- [ ] Full bimodal test suite passes (no regressions)
- [ ] Full project test suite passes

## Artifacts & Outputs

- `code/src/bimodal_logic/translation.py` -- extended with `unfold_formula`, `fold_formula`, `normalize_formula`, and private helpers
- `code/src/bimodal_logic/__init__.py` -- updated exports
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` -- new test file with 5 test classes
- `specs/112_fold_unfold_formula_normalization/plans/01_fold-unfold-normalization.md` -- this plan
- `specs/112_fold_unfold_formula_normalization/summaries/01_fold-unfold-normalization-summary.md` -- implementation summary (post-implementation)

## Rollback/Contingency

All changes are additive -- no existing code is modified, only extended. Rollback consists of removing the three new functions from `translation.py`, reverting the `__init__.py` export additions, and deleting the test file. The existing `json_to_prefix`, `temporal_depth`, and `prefix_to_infix` functions are untouched.
