# Implementation Summary: Fold/Unfold Formula Normalization Utilities

- **Task**: 112 - Fold/unfold formula normalization utilities
- **Status**: COMPLETED
- **Date**: 2026-06-01
- **Duration**: 4 phases, approximately 2 hours
- **Session**: sess_1748820000_u112

## What Was Implemented

Three new public functions in `code/src/bimodal_logic/translation.py`:

### 1. `unfold_formula(formula_json: dict) -> dict`

Recursively expands all 11 enriched formula tags to the 6 primitive tags. Uses a straightforward recursive dispatch on all 17 tags. Primitive tags (atom, bot, imp, box, untl, snce) are passed through with their children recursively unfolded. The 11 enriched tags are replaced by their primitive-only definitions (e.g., `neg φ -> imp(φ, bot)`, `top -> imp(bot, bot)`, `all_future φ -> imp(untl(imp(φ, bot), imp(bot, bot)), bot)`).

### 2. `fold_formula(formula_json: dict) -> dict`

Greedily folds primitive patterns into enriched tags using outside-in pattern matching with Level 3 before Level 2 before Level 1 ordering. Handles the critical disambiguation within the `imp(_, bot)` family by checking specificity in order: all_future (untl with top guard + neg event), all_past (snce with top guard + neg event), diamond (box with neg child), and (imp with neg right), top (bot, bot), neg (fallback).

### 3. `normalize_formula(formula_json: dict, level: int) -> dict`

Composes unfold and level-restricted fold. First calls `unfold_formula` to get a primitive-only formula, then applies `_fold_at_level(unfolded, level)` which restricts pattern matching to patterns at or below the specified level (0=no enriched, 1=neg/top/next/prev, 2=Level 1 + and/or/diamond/some_future/some_past, 3=all 11 enriched). Raises `ValueError` for levels outside [0, 3].

### Private helpers added

- `_make_bot()` - creates a bot node
- `_make_top_expanded()` - creates imp(bot, bot)
- `_is_bot(node)` - predicate for bot nodes
- `_is_top_pattern(node)` - predicate for imp(bot, bot) nodes
- `_is_neg_pattern(node)` - predicate for imp(_, bot) nodes
- `_fold_at_level(formula_json, max_level)` - internal level-restricted fold

### Exports updated

`code/src/bimodal_logic/__init__.py` updated to export `unfold_formula`, `fold_formula`, `normalize_formula`.

## Test Coverage

New file: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py`

Contains 5 test classes with 90 total tests:

| Test Class | Tests | Coverage |
|------------|-------|----------|
| `TestUnfoldFormula` | 35 | All 17 tags, idempotency, nesting |
| `TestFoldFormula` | 18 | All 11 enriched patterns, passthrough, recursion |
| `TestOverlappingPatterns` | 10 | Disambiguation order verification |
| `TestNormalizeFormula` | 10 | Levels 0-3, error cases |
| `TestRoundTrip` | 6 | Property-based, 60-120 random formulas each |
| `TestAllEnrichedPatternsFoldable` | 11 | Gate: all enriched round-trip |

**All 90 new tests pass. All 451 pre-existing bimodal unit tests pass (no regressions).**

Key properties verified for 120 random formulas:
- `unfold(unfold(f)) == unfold(f)` (idempotency)
- `unfold(fold(unfold(f))) == unfold(f)` (round-trip)
- `fold(fold(unfold(f))) == fold(unfold(f))` (fold idempotency post-unfold)
- `normalize(f, 0) == unfold(f)`
- `normalize(f, 3) == fold(unfold(f))`

## Plan Deviations

- None (implementation followed plan exactly)

## Files Modified

- `code/src/bimodal_logic/translation.py` - Added 3 public functions, 6 private helpers
- `code/src/bimodal_logic/__init__.py` - Added exports for new functions
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` - Created (new file)
