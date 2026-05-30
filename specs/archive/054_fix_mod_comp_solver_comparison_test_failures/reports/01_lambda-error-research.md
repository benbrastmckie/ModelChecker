# Research Report: Task #54

**Task**: 54 - fix_mod_comp_solver_comparison_test_failures
**Started**: 2026-03-30T12:00:00Z
**Completed**: 2026-03-30T12:15:00Z
**Effort**: Small (straightforward fix)
**Dependencies**: None
**Sources/Inputs**: Codebase exploration, test execution
**Artifacts**: This report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Root cause identified: MOD_COMP examples use `\forall` operator (first-order) but test only loads `['extensional', 'modal']` subtheories
- The `\lambda` KeyError occurs because `\forall` internally uses lambda abstraction, and the `\lambda` operator is only registered with `first_order` subtheory
- Fix: Update `get_required_subtheories` in test_solver_comparison.py to include `first_order` when modal subtheory is loaded
- Alternative: Move MOD_COMP examples to first_order subtheory where they semantically belong

## Context & Scope

All 6 MOD_COMP tests (z3 and cvc5 backends) fail with error `'\\lambda'`, indicating a missing operator registration. Task requested investigation of:
1. Where MOD_COMP examples are defined
2. What operator uses `\lambda` and where it's defined
3. The error flow - where the KeyError is raised
4. How other subtheory examples handle similar operators
5. The operator registry/lookup mechanism

## Findings

### 1. MOD_COMP Examples Location

**File**: `code/src/model_checker/theory_lib/logos/subtheories/modal/examples.py`

Three MOD_COMP examples are defined (lines 529-590):
- `MOD_COMP_1`: Barcan Formula - `\forall v_x. \Box F[v_x] |- \Box \forall v_x. F[v_x]`
- `MOD_COMP_2`: Modal+First-Order Identity - `|- \Box \forall v_x. (F[v_x] -> F[v_x])`
- `MOD_COMP_3`: Nested Modal+Forall - `\Box \Box \forall v_x. F[v_x] |- \Box \forall v_x. F[v_x]`

All three use `\forall v_x` syntax requiring the first-order subtheory.

### 2. Lambda Operator Definition

**File**: `code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py`

The `LambdaOperator` class (line 58-173) with `name = "\\lambda"` is defined in the first_order subtheory. It is exposed via `get_operators()` (line 754-766):

```python
def get_operators():
    return {
        "\\lambda": LambdaOperator,
        "\\forall": ForAllOperator,
        "=": IdentityOperator,
        "\\exists": ExistsOperator,
    }
```

### 3. Error Flow Analysis

1. Test calls `get_required_subtheories('modal')` which returns `['extensional', 'modal']`
2. `get_theory(['extensional', 'modal'])` is called
3. Only extensional and modal operators are registered (no `\lambda`, `\forall`)
4. When parsing `\forall v_x. \Box F[v_x]`, the parser desugars to `\forall(\lambda v. ...)`
5. When looking up the `\lambda` operator, a KeyError is raised

### 4. Subtheory Dependency Mismatch

**Test file** (`test_solver_comparison.py`, lines 86-105):
```python
subtheory_deps = {
    'extensional': ['extensional'],
    'modal': ['extensional', 'modal'],  # MISSING first_order
    'constitutive': ['extensional', 'modal', 'constitutive'],
    'counterfactual': ['extensional', 'modal', 'counterfactual'],
    'relevance': ['extensional', 'modal', 'constitutive', 'relevance'],
    'first_order': ['extensional', 'constitutive', 'first_order'],
}
```

**Modal examples file** (`modal/examples.py`, line 647):
```python
# Create operator registry for modal theory (includes extensional, counterfactual, and first-order dependencies)
modal_registry = LogosOperatorRegistry()
modal_registry.load_subtheories(['extensional', 'modal', 'counterfactual', 'first_order'])
```

The modal examples module knows it needs `first_order`, but the test's `get_required_subtheories` doesn't include this dependency.

### 5. How Other Subtheories Handle This

Looking at the test's dependency map:
- `first_order` examples require `['extensional', 'constitutive', 'first_order']`
- Modal examples at `modal/examples.py` internally load `['extensional', 'modal', 'counterfactual', 'first_order']`

The MOD_COMP examples were added in Task 42 for "Modal + First-Order interaction" testing, but the test_solver_comparison.py wasn't updated to reflect this dependency.

## Decisions

1. The MOD_COMP examples are intentionally in the modal subtheory to test modal+first-order compositionality
2. The fix should be in the test file rather than moving examples, as the examples represent legitimate modal logic theorems

## Recommendations

### Primary Fix (Recommended)

Update `get_required_subtheories` in `test_solver_comparison.py`:

```python
subtheory_deps = {
    'extensional': ['extensional'],
    'modal': ['extensional', 'modal', 'first_order'],  # Add first_order
    'constitutive': ['extensional', 'modal', 'constitutive'],
    'counterfactual': ['extensional', 'modal', 'counterfactual'],
    'relevance': ['extensional', 'modal', 'constitutive', 'relevance'],
    'first_order': ['extensional', 'constitutive', 'first_order'],
}
```

### Alternative Fix

If adding `first_order` to all modal tests is undesirable (performance concerns), create example metadata to specify per-example dependencies:

```python
# In modal/examples.py
MOD_COMP_1_settings = {
    'N': 2,
    ...
    'expectation': False,
    'required_subtheories': ['extensional', 'modal', 'first_order'],  # New field
}
```

Then update the test to check for this field and use it when available.

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Adding first_order to modal deps increases test time | Low | Low | first_order only adds 4 operators; negligible overhead |
| Other modal tests may break with first_order | Low | Medium | Run full modal test suite after fix |
| Future compositionality examples need same fix | Medium | Low | Document the pattern in test file |

## Verification Steps

After implementing the fix:
1. Run `pytest test_solver_comparison.py -k "MOD_COMP" -v` - all 6 tests should pass
2. Run `pytest test_solver_comparison.py -k "modal" -v` - all modal tests should pass
3. Run full test suite to ensure no regressions

## Appendix

### Test Command Used
```bash
cd /home/benjamin/Projects/Logos/ModelChecker/code
python -m pytest src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py -k "MOD_COMP" -v
```

### Key Files
- Test file: `code/src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py`
- MOD_COMP examples: `code/src/model_checker/theory_lib/logos/subtheories/modal/examples.py` (lines 529-631)
- Lambda operator: `code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py` (lines 58-173)
- Theory loader: `code/src/model_checker/theory_lib/logos/__init__.py` (`get_theory` function)
