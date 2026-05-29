# Research Report: Temporal Operator Display Incorrectly Assumes Arguments FALSE Outside Interval

- **Task**: 95 - fix_temporal_display_truth_outside_interval
- **Status**: [COMPLETED]
- **Type**: z3

## Problem

BM_CM_4 (`\Diamond A |= \past A`) finds a countermodel where the conclusion `\past A` is displayed as **True**. By definition, a countermodel must have all premises true and at least one conclusion false. The solver correctly finds a valid countermodel, but the display code computes the wrong truth value for the conclusion.

## Root Cause

`FutureOperator.find_truth_condition()` and `PastOperator.find_truth_condition()` in `code/src/model_checker/theory_lib/bimodal/operators.py` hardcode the assumption that the argument is FALSE at times outside the world's time interval. This is correct for atomic propositions but wrong for negated or complex arguments.

### The bug (PastOperator, lines 806-810):

```python
else:
    # Time is outside world's interval: atoms are FALSE
    # So argument (if it contains atoms) is FALSE
    past_false = True
    break
```

### The bug (FutureOperator, lines 640-644):

```python
else:
    # Time is outside world's interval: atoms are FALSE
    # So argument (if it contains atoms) is FALSE
    future_false = True
    break
```

### Why this is wrong

The code assumes: "atoms are FALSE outside interval, therefore argument is FALSE." This holds for atoms and positive formulas, but fails for negated arguments:

- `\past A` is defined as `\neg \Past \neg A`
- The argument to `\Past` is `\neg A`
- Outside the interval, atoms are FALSE, so `A` is FALSE, so `\neg A` is **TRUE**
- The code incorrectly says `\neg A` is FALSE (treating it as if it were an atom)

### Concrete trace for BM_CM_4

The solver finds: `\Diamond A` true (premise), `\past A` false (conclusion) — a valid countermodel.

The display code computes `\past A = \neg \Past \neg A`:
1. Evaluates `\Past \neg A`: checks times outside interval, assumes `\neg A` is FALSE there
2. Since `\Past` finds its argument "false" at some past time, `\Past \neg A` is marked FALSE
3. `\past A = \neg \Past \neg A = \neg FALSE = TRUE`

The display shows the conclusion as True, contradicting the solver's (correct) result.

### Same bug pattern in UntilOperator

`UntilOperator.find_truth_condition()` at line 1016 has the same assumption:

```python
# ProofChecker alignment: times outside world's interval have guard FALSE
```

This will produce incorrect display results when the guard argument is a negation or complex formula.

## Affected Files

| File | Lines | Operator |
|------|-------|----------|
| `code/src/model_checker/theory_lib/bimodal/operators.py` | 640-644 | `FutureOperator.find_truth_condition()` |
| `code/src/model_checker/theory_lib/bimodal/operators.py` | 806-810 | `PastOperator.find_truth_condition()` |
| `code/src/model_checker/theory_lib/bimodal/operators.py` | 1016-1026 | `UntilOperator.find_truth_condition()` |

## Fix Directions

### Option A: Evaluate argument against Z3 model at out-of-interval times (recommended)

Instead of assuming the argument is FALSE, actually evaluate it:

```python
else:
    # Time is outside world's interval: evaluate argument properly
    # Atoms are FALSE, but complex formulas (negations, etc.) may be TRUE
    arg_truth = semantics.evaluate_at_time(argument, world_id, past_time)
    if not arg_truth:
        past_false = True
        break
```

This requires access to the semantics object and the Z3 model to properly evaluate the argument's truth value at out-of-interval times.

### Option B: Recursive truth computation

Build a local evaluator that computes truth values at out-of-interval times by:
1. Setting all atoms to FALSE (the interval assumption)
2. Recursively evaluating the argument's truth based on its operator structure
3. Handling negation, conjunction, disjunction, etc. correctly

This avoids needing the Z3 model but requires implementing a mini-evaluator.

### Option C: Check argument structure before assuming FALSE

Add a check: if the argument is a positive formula (atoms, conjunctions/disjunctions of atoms), assume FALSE. If it contains negation or other operators that can flip truth values, evaluate properly.

## Impact

- **BM_CM_4**: Currently shows conclusion as True (display bug only — the solver result is correct)
- **Any example using `\past`, `\future`, `\Past`, `\Future`, `\Until`, `\Since` with negated or complex arguments**: May show incorrect truth values in the display output
- The solver's constraint generation is NOT affected — only the display/printing code is wrong

## Verification

After fixing, BM_CM_4 should display:
- Premise `\Diamond A`: True (unchanged)
- Conclusion `\past A`: **False** (corrected from True)

## References

- `code/src/model_checker/theory_lib/bimodal/operators.py`
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (for `true_at` evaluation)
- BM_CM_4 example definition at `examples.py:365-378`
