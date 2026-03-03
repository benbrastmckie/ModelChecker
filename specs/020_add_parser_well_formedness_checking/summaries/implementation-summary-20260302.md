# Implementation Summary: Task #20

**Completed**: 2026-03-02
**Duration**: ~2 hours

## Changes Made

Added well-formedness checking to the parser to reject term-only sentences and other syntactically ill-formed inputs at parse time. The implementation follows a two-level validation approach from the Logos Theory manual:

1. **Syntactic category check**: Verifies the input is a well-formed formula (WFF) according to the grammar. Rejects bare terms (variables, constants, function applications) and bare lambda abstractions.

2. **Closedness check**: Verifies the formula has no free variables. Open formulas like `P[v_x]` are WFFs but not valid sentences.

## Files Created

- `code/src/model_checker/syntactic/formulas.py` - New module with:
  - `compute_formula_free_variables(prefix)`: Computes free variables of a formula in prefix notation
  - `is_syntactically_wff(prefix)`: Checks if a prefix structure is a well-formed formula

- `code/tests/unit/syntactic/test_formulas.py` - Unit tests for formula operations (44 tests)

- `code/tests/unit/syntactic/test_well_formedness.py` - Comprehensive well-formedness tests (36 tests)

## Files Modified

- `code/src/model_checker/syntactic/__init__.py` - Export new functions
- `code/src/model_checker/syntactic/sentence.py` - Added `_validate_well_formedness()` method and `_internal` flag for subformula construction
- `code/src/model_checker/syntactic/syntax.py` - Updated `build_sentence()` to use `_internal=True` for subformulas
- `code/src/model_checker/models/structure.py` - Removed Task 19 workaround (`_is_nonpropositional_sentence` method), simplified `interpret()` to only skip lambda abstractions
- `code/tests/unit/syntactic/test_first_order_parsing.py` - Updated tests to use closed formulas (constants instead of open variables)

## Verification

- All syntactic unit tests pass: 257 tests
- Pre-existing failures: 1 test (`test_update_types_atomic` - unrelated mock issue)
- New tests cover:
  - Rejection of bare terms (variables, constants, function applications)
  - Rejection of bare lambda abstractions
  - Rejection of open formulas with free variables
  - Acceptance of closed formulas (quantified, with constants, propositional)
  - Helpful error messages with suggestions

## Test Results

```bash
PYTHONPATH=code/src pytest code/tests/unit/syntactic/ -v
# 257 passed, 1 warning
```

## Notes

- The implementation adds an `_internal` flag to `Sentence.__init__()` to allow subformula construction without validation. This is necessary because lambda bodies inside quantifiers are internal structures that don't need to be valid standalone sentences.

- The `Syntax` class now passes `is_subformula=True` when recursively building subformulas, which sets `_internal=True` on the sentence to skip validation.

- Error messages include helpful suggestions:
  - For bare variables/constants: Suggests using a predicate like `P[v_x]`
  - For open formulas: Suggests quantifying with `\forall v_x. ...`
  - For bare lambdas: Explains they must be applied or inside a quantifier
