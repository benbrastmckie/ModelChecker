# Research Report: Pre-existing Test Failures

## Summary

Three pre-existing test failures require fixes. Root cause analysis reveals:

1. **FO_CM_4**: Example uses open formula with free variable - needs universal closure
2. **test_exists_uses_validation**: Test checks for removed implementation detail - update test
3. **test_semantic_method_calls_dont_crash**: Error whitelist missing 'parser error' - update test

---

## Failure 1: FO_CM_4 (test_first_order_examples.py)

### Location
- Test file: `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/test_first_order_examples.py`
- Example file: `code/src/model_checker/theory_lib/logos/subtheories/first-order/examples.py`

### Error Message
```
ParseError: Invalid sentence '(F[v_x] \equiv G[v_x])': formula has free variable(s): v_x.
Sentences must be closed formulas.
```

### Root Cause
The example `FO_CM_4` (Hyperintensional Collapse) uses an open formula as a premise:
```python
FO_CM_4_premises = ['(F[v_x] \\equiv G[v_x])']  # Has free variable v_x
FO_CM_4_conclusions = ['\\forall v_y. (F[v_y] \\equiv G[v_y])']
```

The Sentence class now validates that all sentences must be closed formulas (no free variables). This is correct behavior - open formulas are not valid sentences.

### Recommended Fix
**Update the example** to use a properly closed formula. The logical point of FO_CM_4 remains valid - constitutive equivalence at one point doesn't generalize:

```python
# Change premise to use existential closure:
FO_CM_4_premises = ['\\exists v_x. (F[v_x] \\equiv G[v_x])']
# OR use universal closure (different logical claim):
FO_CM_4_premises = ['\\forall v_x. (F[v_x] \\equiv G[v_x])']
```

The existential version preserves the countermodel intention: "Something being F-equivalent-to-G doesn't entail everything is F-equivalent-to-G" (which is actually valid, so we'd need to reconsider the example's purpose).

**Alternative**: Change to demonstrate the actual hyperintensional collapse:
```python
# Premise: F and G are constitutively identical at a specific individual
FO_CM_4_premises = ['(F[a<>] \\equiv G[a<>])']  # Using constant 'a'
FO_CM_4_conclusions = ['\\forall v_y. (F[v_y] \\equiv G[v_y])']
```

This version correctly tests: "F being constitutively identical to G at constant a does not entail they are identical everywhere."

### File to Modify
`code/src/model_checker/theory_lib/logos/subtheories/first-order/examples.py` lines 303-304

---

## Failure 2: test_exists_uses_validation (test_exists_duality.py)

### Location
- Test file: `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_exists_duality.py`

### Error Message
```
AssertionError: ExistsOperator.true_at should use validate_lambda_argument
assert 'validate_lambda_argument' in source
```

### Root Cause
The test inspects the source code of `ExistsOperator.true_at` looking for `validate_lambda_argument`:
```python
source = inspect.getsource(ExistsOperator.true_at)
assert 'validate_lambda_argument' in source
```

However, the implementation now uses `extract_lambda_term` directly instead of calling `validate_lambda_argument`:
```python
def true_at(self, property_arg, eval_point):
    lambda_term = extract_lambda_term(property_arg, "\\exists")  # Validates AND extracts
    ...
```

The `extract_lambda_term` function already validates the argument internally, making the separate `validate_lambda_argument` call redundant. This is a design improvement.

### Recommended Fix
**Update the test** to check for `extract_lambda_term` instead, which performs the same validation:

```python
def test_exists_uses_validation(self):
    """Test that ExistsOperator validates lambda arguments."""
    import inspect
    source = inspect.getsource(ExistsOperator.true_at)
    # extract_lambda_term validates the argument and extracts components
    assert 'extract_lambda_term' in source, (
        "ExistsOperator.true_at should use extract_lambda_term for validation"
    )
```

### File to Modify
`code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_exists_duality.py` lines 120-128

---

## Failure 3: test_semantic_method_calls_dont_crash (test_semantic_coverage.py)

### Location
- Test file: `code/src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py`

### Error Message
```
Z3Exception: b'parser error'
...
AssertionError: Unexpected error: ...
```

### Root Cause
The test calls semantic methods with minimal/empty arguments:
```python
method_tests = [
    ('compatible', [[], []]),  # Empty state lists
    ('maximal', [[]]),         # Empty state list
    ('is_world', [[]]),        # Empty state
]
```

When these empty lists are passed to Z3 operations (via `fusion` which uses bitwise OR), Z3 raises a `Z3Exception` with message `b'parser error'` because it cannot coerce an empty list to a BitVec.

The test's error handling checks for expected error patterns:
```python
valid_errors = ["required", "missing", "invalid", "setup", "state", "model",
                "argument", "parameter", "bitvector", "z3", "operand", "type",
                "unsupported"]
```

But `"parser error"` is not in this list, and `"parser"` alone is not present.

### Recommended Fix
**Update the valid_errors whitelist** to include `"parser"`:

```python
valid_errors = ["required", "missing", "invalid", "setup", "state", "model",
                "argument", "parameter", "bitvector", "z3", "operand", "type",
                "unsupported", "parser"]
```

This acknowledges that Z3 may raise parser errors when given malformed input, which is an expected failure mode for this edge case testing.

### File to Modify
`code/src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py` line 115

---

## Implementation Plan

| Priority | Failure | Fix Type | Effort | Risk |
|----------|---------|----------|--------|------|
| 1 | test_exists_uses_validation | Update test | Low | Low |
| 2 | test_semantic_method_calls_dont_crash | Update test | Low | Low |
| 3 | FO_CM_4 | Update example | Medium | Medium |

### Detailed Steps

#### Phase 1: Simple Test Fixes

1. **test_exists_uses_validation**:
   - Edit line 126 to check for `extract_lambda_term` instead of `validate_lambda_argument`
   - Update assertion message

2. **test_semantic_method_calls_dont_crash**:
   - Add `"parser"` to `valid_errors` list on line 115

#### Phase 2: Example Fix

3. **FO_CM_4**:
   - Change premise from open formula `(F[v_x] \\equiv G[v_x])` to closed formula `(F[a<>] \\equiv G[a<>])`
   - Verify the countermodel still demonstrates the intended hyperintensional collapse
   - Run the full first-order test suite to confirm no regressions

---

## Verification Commands

```bash
# After fixes, verify all three tests pass:
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/test_first_order_examples.py -k "FO_CM_4" -v

PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_exists_duality.py::TestLambdaValidation::test_exists_uses_validation -v

PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::TestLogosSemanticsCalls::test_semantic_method_calls_dont_crash -v
```
