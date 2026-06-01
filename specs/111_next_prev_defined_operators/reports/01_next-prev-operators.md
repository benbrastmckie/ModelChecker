# Research Report: DefNextOperator and DefPrevOperator

**Task**: 111 - Add Next/Prev (X/Y) defined operator classes
**Date**: 2026-06-01
**Status**: Research complete

---

## 1. DefinedOperator Base Class Analysis

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/operators.py`

### Class Definition (line 263)

```python
class DefinedOperator(Operator):
    primitive = False

    def derived_definition(self, *args: Any) -> List[Any]:
        raise NotImplementedError(...)

    def __init__(self, semantics: SemanticDefaults) -> None:
        super().__init__(semantics)
        self._validate_arity()

    def _validate_arity(self) -> None:
        # Validates that declared arity == number of params in derived_definition
        # Uses inspect.signature on derived_definition
        # Raises ValueError if mismatch
```

### Key Interface Requirements

1. **Class attributes** (inherited from `Operator`):
   - `name: str` - LaTeX-style operator name (e.g. `"\\future"`)
   - `arity: int` - number of arguments
   - `primitive = False` - set automatically by `DefinedOperator`

2. **`derived_definition(self, *args)`** - Must be implemented with exactly `arity` parameters (excluding `self`). Returns a **nested list in prefix notation**: `[OperatorClass, arg1_or_sublist, arg2_or_sublist, ...]`. For arity-0: `[OperatorClass]`. For arity-1: `[OperatorClass, argument]`.

3. **`_validate_arity()`** - Called in `__init__`; uses `inspect.signature` to count parameters of `derived_definition` and verifies they match `arity`. **The `# type: ignore` comment on `derived_definition` signatures is a pattern in the codebase** (used by all existing defined operators) to suppress type checking for the overriding signature.

4. **`print_method()`** - Must be implemented (abstract in spirit). Delegates to one of:
   - `self.general_print(...)` - for extensional operators
   - `self.print_over_times(...)` - for temporal operators
   - `self.print_over_worlds(...)` - for modal operators

---

## 2. UntilOperator Analysis

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 872)

```python
class UntilOperator(syntactic.Operator):
    name = "\\Until"
    arity = 2
```

### Semantic Signature
```python
def true_at(self, event_arg, guard_arg, eval_point):
    # exists s > t: event(s) AND forall r in (t,s): guard(r)

def false_at(self, event_arg, guard_arg, eval_point):
    # forall s > t: event is false at s OR exists r in (t,s): guard is false at r

def find_truth_condition(self, event_arg, guard_arg, eval_point):
    # Returns dict: world_id -> (true_times, false_times)
```

**Convention (Burgess)**: `U(event, guard)` - first arg is the **event** (what eventually holds at witness time), second arg is the **guard** (what holds in between).

For `Next(φ) = U(φ, ⊥)`:
- `event_arg` = φ (the formula we're looking for at the next time)
- `guard_arg` = ⊥ (the guard - always false, so the interval (t, s) must be empty, forcing s = t+1)

---

## 3. SinceOperator Analysis

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 1099)

```python
class SinceOperator(syntactic.Operator):
    name = "\\Since"
    arity = 2
```

### Semantic Signature
```python
def true_at(self, event_arg, guard_arg, eval_point):
    # exists s < t: event(s) AND forall r in (s,t): guard(r)

def false_at(self, event_arg, guard_arg, eval_point):
    # forall s < t: event was false at s OR exists r in (s,t): guard was false at r

def find_truth_condition(self, event_arg, guard_arg, eval_point):
    # Returns dict: world_id -> (true_times, false_times)
```

For `Prev(φ) = S(φ, ⊥)`:
- `event_arg` = φ (what held at the previous time)
- `guard_arg` = ⊥ (the guard - always false, so the interval (s, t) must be empty, forcing s = t-1)

---

## 4. BotOperator Analysis

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 298)

```python
class BotOperator(syntactic.Operator):
    name = "\\bot"
    arity = 0
```

The `derived_definition` for arity-0 operators must have **no arguments** (besides `self`). For referencing `BotOperator` in a `derived_definition` return value, the pattern from `TopOperator` (line 1419) is:

```python
def derived_definition(self):  # type: ignore
    return [NegationOperator, [BotOperator]]
```

Note: arity-0 operators are wrapped as `[BotOperator]` (a single-element list) when used as a subformula in the definition.

---

## 5. Existing DefinedOperator Examples (Templates)

### DefFutureOperator (best template for temporal defined operators)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 1479)

```python
class DefFutureOperator(syntactic.DefinedOperator):
    name = "\\future"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [FutureOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
```

### DefPastOperator

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 1516)

```python
class DefPastOperator(syntactic.DefinedOperator):
    name = "\\past"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [PastOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
```

### DefPossibilityOperator (modal analogue)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 1433)

```python
class DefPossibilityOperator(syntactic.DefinedOperator):
    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        # Uses print_over_worlds instead of print_over_times
        model_structure = sentence_obj.proposition.model_structure
        all_worlds = list(model_structure.world_arrays.keys())
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)
```

### ConditionalOperator (binary defined)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 1331)

```python
class ConditionalOperator(syntactic.DefinedOperator):
    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)
```

---

## 6. The Correct derived_definition Pattern for Next/Prev

Based on the definition `Next(φ) = U(φ, ⊥)`:
- UntilOperator is binary: `U(event, guard)`
- BotOperator is 0-ary: referenced as `[BotOperator]`
- So: `[UntilOperator, argument, [BotOperator]]`

Based on the definition `Prev(φ) = S(φ, ⊥)`:
- SinceOperator is binary: `S(event, guard)`
- BotOperator is 0-ary: referenced as `[BotOperator]`
- So: `[SinceOperator, argument, [BotOperator]]`

**This is exactly what the task description specifies.**

---

## 7. bimodal_operators Collection Registration

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (line 1534)

```python
bimodal_operators = syntactic.OperatorCollection(
    # extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,
    # extremal operators
    TopOperator,
    # modal operators
    NecessityOperator,
    # tense operators
    FutureOperator,
    PastOperator,
    UntilOperator,
    SinceOperator,
    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    BotOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
)
```

`OperatorCollection.__init__` accepts operator classes as positional arguments (via `*input`). Registration is simply adding the class to the `operator_dictionary` using `operator.name` as key.

**New classes must be added** after `DefPastOperator` (or in the `defined operators` section):
```python
    DefNextOperator,
    DefPrevOperator,
```

---

## 8. print_over_times Function Details

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/operators.py` (line 200)

```python
def print_over_times(self, sentence_obj, eval_point, other_times, indent_num, use_colors):
```

- For **unary operators** (like Next/Prev): iterates through `other_times` and calls `recursive_print` for the argument at each time point.
- `other_times` = the keys of `eval_world_history` (all time points in the current world).

The `print_method` pattern for temporal defined operators:
```python
def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
    eval_world = eval_point["world"]
    eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
    eval_world_times = eval_world_history.keys()
    self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
```

---

## 9. from_prefix Construction (How Prefix Parsing Works)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/collection.py` (line 85)
**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/sentence.py` (line 389)

The `apply_operator` method in `OperatorCollection` is the key function. It converts prefix notation to operator class instances:

```python
def apply_operator(self, prefix_sentence):
    # ["\\next", ["p"]] -> [DefNextOperator, Const("p", AtomSort)]
```

The system resolves an operator string like `"\\next"` by looking it up in `operator_dictionary`. Since `DefNextOperator.name = "\\next"` and it's registered in `bimodal_operators`, the string `"\\next"` in a formula like `"\\next A"` will correctly resolve to `DefNextOperator`.

**Prefix construction from formula string** (via `Sentence.prefix(infix_sentence)` in `sentence.py` line 72): The parser converts infix strings like `"\\next A"` into a prefix list `["\\next", ["A"]]`, which `apply_operator` then resolves.

For test purposes, the `from_prefix` construction can be tested by:
1. Creating a `Syntax` instance with formulas containing `\\next` or `\\prev`
2. Running `run_test` with those formulas
3. Verifying the operator is recognized and produces correct results

---

## 10. Test Infrastructure for Bimodal Operators

### Unit Test Pattern (for operator signature/structure tests)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_until_since.py`

Key patterns:
- Use `@pytest.fixture` for `BimodalSemantics` with settings
- Test class name: `TestXxxOperatorSignature`, `TestXxxOperatorZ3Structure`
- Test registration: `from model_checker.theory_lib.bimodal.operators import bimodal_operators`
- Check operator name and arity as class attributes (no instantiation needed)
- For Z3 expression tests: use mock arguments and mock `semantics.true_at`/`false_at`

### Integration Test Pattern (for semantic equivalence tests)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`

Key pattern for end-to-end testing:
```python
from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.bimodal import (
    BimodalStructure, BimodalProposition, BimodalSemantics, bimodal_operators
)
result = run_test(
    [premises, conclusions, settings],
    BimodalSemantics,
    BimodalProposition,
    bimodal_operators,
    Syntax,
    ModelConstraints,
    BimodalStructure,
)
```

For testing **semantic equivalence** (Next(p) same as U(p, ⊥)):
- Use `run_test` with equivalence formula: `\\next A \\leftrightarrow (A \\Until \\bot)` as a theorem (expect=True, no countermodel found)
- Use `run_test` with `\\prev A \\leftrightarrow (A \\Since \\bot)` as a theorem

For testing **from_prefix construction**:
- Simply construct a `Syntax` instance: `Syntax(["\\next A"], [], bimodal_operators)` - if it doesn't throw, the operator was found and parsed correctly.

---

## 11. Complete Implementation Recipe

### Step 1: Add DefNextOperator (after DefPastOperator, line ~1530)

```python
class DefNextOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula holds at the immediately next time.

    Defined as: Next(φ) = U(φ, ⊥)
    U(event, guard) with guard=⊥: Since ⊥ is always false, the open interval
    (t, s) must be empty, forcing s = t+1. So Next(φ) is true at t iff φ holds
    at t+1 (the immediately next time).

    Corresponds to Lean definition: next phi := untl phi bot
    """

    name = "\\next"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [UntilOperator, argument, [BotOperator]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
```

### Step 2: Add DefPrevOperator (after DefNextOperator)

```python
class DefPrevOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula held at the immediately previous time.

    Defined as: Prev(φ) = S(φ, ⊥)
    S(event, guard) with guard=⊥: Since ⊥ is always false, the open interval
    (s, t) must be empty, forcing s = t-1. So Prev(φ) is true at t iff φ held
    at t-1 (the immediately previous time).

    Corresponds to Lean definition: prev phi := snce phi bot
    """

    name = "\\prev"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [SinceOperator, argument, [BotOperator]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
```

### Step 3: Register in bimodal_operators (add to the collection at line 1534)

```python
bimodal_operators = syntactic.OperatorCollection(
    # ... existing operators ...
    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    BotOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
    DefNextOperator,    # NEW
    DefPrevOperator,    # NEW
)
```

---

## 12. Recommended Tests

### Test File: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py`

**Test categories to implement**:

1. **Signature tests** (`TestDefNextOperatorSignature`, `TestDefPrevOperatorSignature`):
   - `test_operator_exists` - class exists and is importable
   - `test_operator_arity` - arity == 1
   - `test_operator_name` - name == `"\\next"` / `"\\prev"`
   - `test_has_required_methods` - instantiation, methods exist
   - `test_is_defined_operator` - `issubclass(DefNextOperator, syntactic.DefinedOperator)`

2. **derived_definition structure tests** (`TestDefNextDefinition`, `TestDefPrevDefinition`):
   - `test_derived_definition_returns_list` - `isinstance(result, list)`
   - `test_derived_definition_uses_until` - `result[0] is UntilOperator`
   - `test_derived_definition_uses_bot` - `result[2] == [BotOperator]`
   - `test_derived_definition_uses_since` - `result[0] is SinceOperator`

3. **Registration tests** (`TestOperatorRegistration`):
   - `test_next_in_bimodal_operators` - `"\\next" in bimodal_operators.operator_dictionary`
   - `test_prev_in_bimodal_operators` - `"\\prev" in bimodal_operators.operator_dictionary`

4. **Semantic equivalence tests** (integration-style, via `run_test`):
   - `test_next_equiv_until_bot` - `\\next A ↔ (A \\Until \\bot)` is a theorem
   - `test_prev_equiv_since_bot` - `\\prev A ↔ (A \\Since \\bot)` is a theorem

5. **From-prefix construction tests**:
   - `test_next_from_prefix` - `Syntax(["\\next A"], [], bimodal_operators)` succeeds
   - `test_prev_from_prefix` - `Syntax(["\\prev A"], [], bimodal_operators)` succeeds

---

## 13. Key Notes for Implementation

1. **`# type: ignore` comment on `derived_definition`**: All existing defined operators use this to suppress type checker complaints about narrowing the `*args` signature.

2. **BotOperator is wrapped in list**: `[BotOperator]` not just `BotOperator` in the returned list structure.

3. **The `argument` parameter** in `derived_definition` is passed through as-is (not in a list). In the derived definition for binary use `[UntilOperator, argument, [BotOperator]]`, the `argument` is a sentence/formula object that will be used directly.

4. **No `find_truth_condition` needed**: `DefinedOperator` subclasses do NOT need to implement `true_at`, `false_at`, or `find_truth_condition` — these are inherited and computed by expanding the definition via `derived_definition`.

5. **The `print_over_times` call convention**: `sentence_obj` (not `argument`!) is the first arg — it's the sentence for the defined operator itself, not the inner formula.

6. **Equivalence formulas use `\\bot` not `\\top`**: In examples, `\top` is sometimes expressed as `\\neg \\bot` to avoid potential bugs with `TopOperator`. For the test formulas, use `\\bot` directly since we specifically want U/S with bottom as guard.

---

## 14. Reference File Locations

| Item | File | Lines |
|------|------|-------|
| DefinedOperator base class | `code/src/model_checker/syntactic/operators.py` | 263-344 |
| print_over_times | `code/src/model_checker/syntactic/operators.py` | 200-260 |
| UntilOperator | `code/src/model_checker/theory_lib/bimodal/operators.py` | 872-1096 |
| SinceOperator | `code/src/model_checker/theory_lib/bimodal/operators.py` | 1099-1324 |
| BotOperator | `code/src/model_checker/theory_lib/bimodal/operators.py` | 298-353 |
| DefFutureOperator (template) | `code/src/model_checker/theory_lib/bimodal/operators.py` | 1479-1513 |
| DefPastOperator (template) | `code/src/model_checker/theory_lib/bimodal/operators.py` | 1516-1529 |
| bimodal_operators collection | `code/src/model_checker/theory_lib/bimodal/operators.py` | 1534-1559 |
| OperatorCollection class | `code/src/model_checker/syntactic/collection.py` | 16-158 |
| Test: unit/test_until_since.py | `code/src/model_checker/theory_lib/bimodal/tests/unit/` | full file |
| Test: unit/test_bimodal.py | `code/src/model_checker/theory_lib/bimodal/tests/unit/` | full file |
| run_test utility | `code/src/model_checker/utils/testing.py` | 12-55 |

---

## Summary

`DefNextOperator` and `DefPrevOperator` are straightforward 1-arity `DefinedOperator` subclasses. The key insight is:

- `Next(φ) = U(φ, ⊥)`: `derived_definition` returns `[UntilOperator, argument, [BotOperator]]`
- `Prev(φ) = S(φ, ⊥)`: `derived_definition` returns `[SinceOperator, argument, [BotOperator]]`

The `print_method` follows the exact same pattern as `DefFutureOperator` and `DefPastOperator` — `print_over_times` with the world's time history. Both operators must be added to the `bimodal_operators` collection. No additional methods (`true_at`, `false_at`, `find_truth_condition`) need to be implemented since `DefinedOperator` handles these by expanding the definition.

The implementation is minimal: ~25 lines of code for both classes plus 2 registrations. The test suite should cover signatures, `derived_definition` structure, registration, semantic equivalence (via `run_test`), and from-prefix construction.
