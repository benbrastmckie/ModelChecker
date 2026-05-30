# Research Report: Refined Temporal Operator Bug Analysis

- **Task**: 95 - fix_temporal_display_truth_outside_interval
- **Started**: 2026-05-29
- **Completed**: 2026-05-29
- **Effort**: 2h
- **Dependencies**: Report 01_temporal-display-truth.md (prior research)
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/operators.py` (1509 lines)
  - `code/src/model_checker/theory_lib/bimodal/semantic.py` (2697 lines)
  - `code/src/model_checker/theory_lib/bimodal/examples.py` (BM_CM_4 definition)
  - `code/src/model_checker/models/proposition.py` (PropositionDefaults base class)
  - `code/src/model_checker/syntactic/sentence.py` (Sentence structure)
- **Artifacts**: `specs/095_fix_temporal_display_truth_outside_interval/reports/02_refined-temporal-analysis.md`
- **Standards**: `report-format.md`

---

## Executive Summary

- The bug is confirmed in four operators: `FutureOperator.find_truth_condition()` (lines 640-644), `PastOperator.find_truth_condition()` (lines 807-810), `UntilOperator.find_truth_condition()` (lines 1025-1028), and `SinceOperator.find_truth_condition()` (lines 1244-1247). All share identical logic: assume the argument is FALSE for times outside the world's interval.
- The `argument` objects passed to `find_truth_condition` are `Sentence` objects. Their `.proposition` attribute (a `BimodalProposition`) has both `.extension` (precomputed truth table covering only the world's interval) and `.z3_model` (the concrete Z3 model for out-of-interval evaluation).
- The correct fix (Option A from prior research) is to call `z3_model.evaluate(semantics.true_at(argument.sentence, {"world": world_id, "time": out_time}))` for any time outside the world's interval, since `semantics.true_at` already correctly handles atoms (false outside interval via `is_valid_time_for_world`) and complex formulas (recursively).
- The `NegationOperator.find_truth_condition()` at line 85 shows the right pattern: it reads `argument.proposition.extension` directly and swaps true/false times. But temporal operators cannot use this alone — they need truth at out-of-interval times, which is NOT in the extension.
- `DefPastOperator` (`\past`) is defined as `\neg \Past \neg A`. When evaluated, `NegationOperator.find_truth_condition` correctly swaps the `\Past \neg A` extension. But `PastOperator.find_truth_condition` for `\neg A` is where the bug occurs — it incorrectly treats times outside the interval as FALSE for the `\neg A` argument.
- Fix complexity is LOW: replace the 2-line "assume FALSE" block in each of the four operators with a single `z3_model.evaluate(...)` call using the already-available `argument.proposition.z3_model` and `argument.proposition.model_structure.semantics`.

---

## Context and Scope

### The Call Chain for `\past A`

`\past A` is defined as `DefPastOperator` (line 1467-1471):
```python
def derived_definition(self, argument):
    return [NegationOperator, [PastOperator, [NegationOperator, argument]]]
```

So `\past A` expands to `\neg \Past \neg A`. The display-time evaluation of `\past A` is handled by `find_extension()` in `BimodalProposition` (semantic.py:1690), which recursively calls `find_truth_condition()` for each operator in the expanded formula tree:

1. `NegationOperator.find_truth_condition(\Past \neg A)` — reads extension of `\Past \neg A`, swaps true/false
2. `PastOperator.find_truth_condition(\neg A)` — reads extension of `\neg A`, iterates over D
3. `NegationOperator.find_truth_condition(A)` — reads extension of `A`, swaps true/false
4. `A` is a sentence letter — `find_extension()` evaluates with `z3_model.evaluate(semantics.true_at(A, ...))` for each in-interval time

### What `argument.proposition.extension` Contains

For a sentence letter `A`, extension covers only in-interval times:
```
world 0, interval [1, 3]: extension = ([2], [1, 3])  # A true at t=2, false at t=1,3
```

For `\neg A`, extension is computed by `NegationOperator.find_truth_condition` — also only covering in-interval times (swaps from A's extension):
```
world 0, interval [1, 3]: extension = ([1, 3], [2])  # \neg A true at t=1,3, false at t=2
```

There is NO extension entry for out-of-interval times. The extension dict maps world_ids to (true_times, false_times), where both lists contain only times within the world's interval.

### The Bug Site in PastOperator (lines 797-811)

```python
past_false = False
for past_time in all_D_times:
    if past_time < time_point:
        if past_time in time_interval:
            # Time is in world's interval: check argument extension
            if past_time in false_times:
                past_false = True
                break
        else:
            # Time is outside world's interval: atoms are FALSE
            # So argument (if it contains atoms) is FALSE
            past_false = True   # <-- BUG: this is wrong for \neg A
            break
```

`false_times` comes from `argument.proposition.extension[current_world]` — so it correctly encodes `\neg A`'s truth within the interval. But when `past_time` is outside the interval, the code assumes the argument is FALSE without actually evaluating it. For `\neg A`, the correct answer is TRUE (since A is false outside the interval, \neg A is true).

---

## Findings

### Finding 1: All Four Temporal Operators Have the Same Bug

| Operator | Lines | Bug Location | What It Checks |
|----------|-------|--------------|----------------|
| `FutureOperator.find_truth_condition` | 640-644 | `future_time` not in `time_interval` | "argument is FALSE at future out-of-interval times" |
| `PastOperator.find_truth_condition` | 807-811 | `past_time` not in `time_interval` | "argument is FALSE at past out-of-interval times" |
| `UntilOperator.find_truth_condition` | 1025-1028 | `r` not in `time_interval` (guard check) | "guard is FALSE at out-of-interval intermediate times" |
| `SinceOperator.find_truth_condition` | 1244-1247 | `r` not in `time_interval` (guard check) | "guard is FALSE at out-of-interval intermediate times" |

For `UntilOperator` and `SinceOperator`, there is an additional subtlety: the event argument uses `event_true_times = event_extension[world_id][0]` to find witnesses, but only searches within the world's interval (lines 1013 and 1232). The guard check at out-of-interval times is where the bug manifests.

### Finding 2: The Extension Architecture

`BimodalProposition.find_extension()` (semantic.py:1690) is the root computation:
- For sentence letters: calls `z3_model.evaluate(semantics.true_at(sentence, {"world": world_id, "time": time}))` for each in-interval time
- For complex formulas: calls `operator.find_truth_condition(*arguments, eval_point)`

The `find_truth_condition` methods receive `argument` objects that are `Sentence` instances. Each `Sentence` has a `.proposition` attribute (set by `update_proposition()` in `sentence.py:422`) which is a `BimodalProposition` with:
- `.extension`: dict mapping world_id -> (true_times, false_times) covering only in-interval times
- `.z3_model`: the concrete Z3 model (attribute of `BimodalProposition`, set at line 1603)
- `.model_structure`: the model structure (inherited from `PropositionDefaults`)
- `.sentence`: the original `Sentence` object (inherited from `PropositionDefaults`, `proposition.py:55`)

### Finding 3: Option A Is the Correct and Minimal Fix

`semantics.true_at(sentence, eval_point)` correctly handles atoms with the `is_valid_time_for_world` check (line 1126). For out-of-interval times, atoms evaluate to FALSE via this check. Complex formulas recurse through their operator's `true_at` method, which correctly propagates.

The fix for each operator's out-of-interval branch:

```python
else:
    # Time is outside world's interval: evaluate argument properly
    # Atoms are FALSE (handled by semantics.true_at via is_valid_time_for_world)
    # Complex formulas (negations, etc.) are evaluated correctly by recursion
    z3_model = argument.proposition.z3_model
    semantics_obj = argument.proposition.model_structure.semantics
    truth_expr = semantics_obj.true_at(
        argument.proposition.sentence,
        {"world": current_world, "time": past_time}  # or future_time, r, etc.
    )
    arg_is_true = is_true(z3_model.evaluate(truth_expr))
    if not arg_is_true:
        past_false = True
        break
```

Note: `is_true` is imported from `model_checker.solver` in semantic.py; operators.py does NOT currently import it. The fix can instead use the simpler pattern: `if not z3_model.evaluate(truth_expr)` since Z3's `BoolRef.evaluate` returns a Python-truthiness-compatible value, or can check against z3's true literal. The cleanest approach is to compare with the Z3 true value.

### Finding 4: Why `NegationOperator.find_truth_condition` Does Not Have This Bug

`NegationOperator.find_truth_condition` (line 85) only deals with swapping truth/false within the extension:
```python
for world_id, temporal_profile in argument.proposition.extension.items():
    true_times, false_times = temporal_profile
    new_truth_condition[world_id] = (false_times, true_times)
```

This is correct because: the extension already contains the correctly computed truth values for in-interval times. For times NOT in the extension, they simply don't appear in the output — which is correct because `find_truth_condition` only needs to cover in-interval evaluation points. The problem only occurs in temporal operators that need to CHECK argument truth at out-of-interval times as part of their quantification logic.

### Finding 5: Concrete BM_CM_4 Trace

BM_CM_4: premises `[\Diamond A]`, conclusions `[\past A]`.

Suppose Z3 finds a countermodel where world 0 has interval `[1, 2]`, and A is false at t=1, true at t=2, and D = [-1, 0, 1, 2] (M=3, so D = {-2, -1, 0, 1, 2}... depends on settings with M=5 giving D = {-4, -3, ..., 4}).

Evaluating `\past A` at t=1 in world 0 (the main evaluation point):
1. `\past A` expands to `\neg \Past \neg A`
2. `PastOperator.find_truth_condition(\neg A)` runs for world 0
3. `\neg A`'s extension for world 0: true at t=1 (A=F), false at t=2 (A=T) — only in-interval
4. At time_point=1, looking for past times < 1 in D: e.g., times -4, -3, -2, -1, 0
5. Time 0 is NOT in time_interval [1,2] -> the code sets `past_false = True`
6. So `\Past \neg A` is computed as False at t=1
7. `\neg \Past \neg A` = `\neg False` = True at t=1
8. Display shows `\past A` = True -> WRONG (solver says False)

The CORRECT evaluation at t=1:
- Times -4, -3, -2, -1, 0 are out of interval
- For `\neg A` at those times: A is FALSE outside interval (by atom_false_of_not_domain), so `\neg A` is TRUE
- So `\Past \neg A` is NOT falsified at t=1 by those out-of-interval times
- It would only be falsified if there existed a past time where `\neg A` is false (i.e., where A is true)
- But A is false outside the interval and false at t=1 (in-interval) — so `\Past \neg A` is vacuously/actually TRUE at t=1
- Thus `\past A = \neg \Past \neg A = \neg True = False` at t=1 -> CORRECT

### Finding 6: How to Get `z3_model` in the Operators' `find_truth_condition` Methods

The `argument` parameter in `PastOperator.find_truth_condition(self, argument, eval_point)` is a `Sentence` object. After `update_proposition()` is called during model display, `argument.proposition` is a `BimodalProposition` with `argument.proposition.z3_model` available.

Evidence: in `find_truth_condition` methods, `argument.proposition.model_structure` and `argument.proposition.extension` are already accessed (lines 599, 767). Adding `argument.proposition.z3_model` follows the exact same pattern.

### Finding 7: Alternative Simpler Approach Using Extension Lookup

There is a simpler approach that avoids Z3 evaluation entirely: use the ARGUMENT's extension for in-interval times and compute truth for out-of-interval times directly by calling `find_extension`-style logic recursively on the argument's operator tree with all atoms forced to False.

However, this "mini-evaluator" approach (Option B) is significantly more complex and duplicates Z3 model evaluation logic. The `z3_model.evaluate()` call (Option A) is cleaner and reuses the existing `semantics.true_at` machinery that is already tested and correct.

---

## Recommendations

### Priority 1: Fix All Four Temporal Operators Using Option A

Modify the out-of-interval branch in `FutureOperator.find_truth_condition`, `PastOperator.find_truth_condition`, `UntilOperator.find_truth_condition`, and `SinceOperator.find_truth_condition`.

The pattern for each operator:

**Before (buggy)**:
```python
else:
    # Time is outside world's interval: atoms are FALSE
    # So argument (if it contains atoms) is FALSE
    past_false = True
    break
```

**After (correct)**:
```python
else:
    # Time is outside world's interval: evaluate argument properly
    # semantics.true_at handles atoms correctly (FALSE via is_valid_time_for_world)
    # and complex formulas correctly (recursive evaluation through operators)
    z3_model = argument.proposition.z3_model
    semantics_obj = argument.proposition.model_structure.semantics
    truth_expr = semantics_obj.true_at(
        argument.proposition.sentence,
        {"world": current_world, "time": past_time}
    )
    evaluated = z3_model.evaluate(truth_expr)
    # z3.BoolVal(True).as_bool() -> True; z3.BoolVal(False).as_bool() -> False
    if not evaluated:
        past_false = True
        break
```

For `UntilOperator` and `SinceOperator`, the `argument` is `guard_arg`, and the variable names differ (`r` instead of `past_time`/`future_time`). The pattern is identical.

### Priority 2: Variable Name Mapping for Each Operator

| Operator | Argument variable | Out-of-interval time variable | World variable |
|----------|-------------------|-------------------------------|----------------|
| `FutureOperator` | `argument` | `future_time` | `current_world` |
| `PastOperator` | `argument` | `past_time` | `current_world` |
| `UntilOperator` | `guard_arg` | `r` | `world_id` |
| `SinceOperator` | `guard_arg` | `r` | `world_id` |

For `UntilOperator` and `SinceOperator`, the semantics object and z3_model come from `guard_arg.proposition`, not `event_arg.proposition` — both should yield the same model, but using `guard_arg` is correct.

### Priority 3: Add Test Coverage for BM_CM_4

After fixing, verify:
1. BM_CM_4 displays `\past A` as False (not True)
2. BM_CM_4 is moved from the "excluded" test list (line 43 in test_bimodal.py) to the active countermodel tests
3. Add similar tests for `\future`, `\Until` and `\Since` with negated arguments

### Priority 4: Verify `z3_model.evaluate()` Return Value Handling

The `z3_model.evaluate()` method returns a Z3 expression (e.g., `BoolVal(True)` or `BoolVal(False)`). The check `if not evaluated` may not work reliably with Z3 expressions. The safe pattern is:

```python
from model_checker.solver import is_true
# ...
evaluated = z3_model.evaluate(truth_expr)
if not is_true(evaluated):
    past_false = True
    break
```

`is_true` is already used in semantic.py (line 1726) for this exact pattern. Operators.py imports from `model_checker` but not `is_true` specifically — this import would need to be added, or the check can use `z3.is_true(evaluated)` which is available via the existing `z3_shim` import.

---

## Appendix

### File Locations

- Bug locations: `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py`
  - FutureOperator: lines 578-655
  - PastOperator: lines 746-822
  - UntilOperator: lines 968-1040
  - SinceOperator: lines 1187-1259
- Model evaluation: `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py`
  - `BimodalSemantics.true_at`: lines 1097-1136
  - `BimodalProposition.find_extension`: lines 1690-1742
  - `BimodalProposition.__init__`: lines 1589-1625
- BM_CM_4 definition: `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/examples.py:364-378`
- Test file: `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py:43` (BM_CM_4 excluded)

### DefPastOperator Definition

`\past` is not `PastOperator` — it is `DefPastOperator` at line 1465:
```python
class DefPastOperator(syntactic.DefinedOperator):
    name = "\\past"
    arity = 1
    def derived_definition(self, argument):
        return [NegationOperator, [PastOperator, [NegationOperator, argument]]]
```

`\Past` (capital P) IS `PastOperator`. The user's example `\past A` expands at parse time to `\neg \Past \neg A`, so the bug is in `PastOperator.find_truth_condition` receiving `\neg A` as argument.

### Architecture Note on find_truth_condition

The `find_truth_condition` methods implement display-time evaluation, separate from the Z3 constraint-generation used by the solver. This is why the solver finds the correct countermodel (the Z3 `true_at`/`false_at` constraint expressions are correct) but the display shows the wrong value (the Python-side `find_truth_condition` logic is incorrect). Fixing `find_truth_condition` does NOT affect solver correctness.
