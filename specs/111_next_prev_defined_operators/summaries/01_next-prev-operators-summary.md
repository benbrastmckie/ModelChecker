# Implementation Summary: Add Next/Prev (X/Y) Defined Operator Classes

- **Task**: 111
- **Status**: COMPLETED
- **Date**: 2026-06-01
- **Phases**: 2 of 2 completed

## What Was Implemented

Added `DefNextOperator` and `DefPrevOperator` as `DefinedOperator` subclasses to the bimodal operator collection in `code/src/model_checker/theory_lib/bimodal/operators.py`.

### DefNextOperator

- `name = "\\next"`, `arity = 1`
- `derived_definition(argument)` returns `[UntilOperator, argument, [BotOperator]]`
- Semantics: Next(phi) = U(phi, bot) — phi holds at the immediately next time (since bot never holds, the guard interval is empty, forcing the witness to be the immediate next time)
- `print_method` delegates to `print_over_times` (identical pattern to DefFutureOperator/DefPastOperator)

### DefPrevOperator

- `name = "\\prev"`, `arity = 1`
- `derived_definition(argument)` returns `[SinceOperator, argument, [BotOperator]]`
- Semantics: Prev(phi) = S(phi, bot) — phi held at the immediately previous time
- `print_method` delegates to `print_over_times`

Both operators were registered in the `bimodal_operators` OperatorCollection after `DefPastOperator`.

## Tests Written

Created `code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py` with 34 tests:

- `TestDefNextOperatorSignature` (7 tests): class existence, arity, name, DefinedOperator subclass, derived_definition method, print_method, not primitive
- `TestDefPrevOperatorSignature` (7 tests): same for DefPrevOperator
- `TestDefNextDefinition` (5 tests): full derived_definition structure — returns list, UntilOperator outer, argument as event, [BotOperator] as guard, complete structure check
- `TestDefPrevDefinition` (5 tests): same for DefPrevOperator with SinceOperator
- `TestOperatorRegistration` (4 tests): "\\next" and "\\prev" in operator_dictionary, resolve to correct classes
- `TestPrefixConstruction` (4 tests): Syntax can parse "\\next A", "\\prev A", and compound formulas
- `TestSemanticEquivalence` (2 tests): Next(A) <-> U(A, bot) is a theorem; Prev(A) <-> S(A, bot) is a theorem

## Test Results

- New tests: 34/34 passed (green phase)
- Full bimodal test suite: 218/219 passed
  - The 1 failure (BM_CM_1) is a pre-existing Z3 non-determinism issue that existed before this task

## Plan Deviations

- None (implementation followed plan exactly)
- The plan referenced "171 existing tests" but the suite had grown to 218 by implementation time due to work on tasks 106, 109, and 110. No deviation in approach.

## Files Modified

- `code/src/model_checker/theory_lib/bimodal/operators.py` — added 2 classes (~50 lines) and 2 registrations
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py` — new test file (34 tests)
