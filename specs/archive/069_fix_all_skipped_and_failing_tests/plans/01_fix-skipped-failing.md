# Implementation Plan: Fix All Skipped and Failing Tests

## Phase 1: Fix failing test_push_pop_sat_transitions [NOT STARTED]

**File**: `code/src/model_checker/solver/tests/unit/test_equivalence.py`

Change test values from `x > 200` / `x < 100` to `x > 50` / `x < 10` for both z3 and cvc5 blocks. These are contradictory under both signed and unsigned 8-bit comparison.

Update the comment to explain the signed comparison issue.

**Verification**: Run `pytest code/src/model_checker/solver/tests/unit/test_equivalence.py -q`

## Phase 2: Fix bimodal skipped tests [NOT STARTED]

### 2a: test_bimodal.py
**File**: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`

- Remove the module-level `@pytest.mark.skip` decorator from `test_example_cases`
- Remove the TODO comment about removing skip
- Add individual `pytest.mark.skip` for the 5 failing examples (TN_CM_1, TN_CM_2, BM_CM_2, BM_CM_3, BM_CM_4) using a separate parametrize exclusion or xfail marker

Implementation approach: Use `pytest.mark.xfail` for the 5 problematic examples rather than skip, so they're tracked as known issues. Create a set of known-failing example names and conditionally mark them.

### 2b: test_iterate.py  
**File**: `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`

- Remove the `pytestmark = pytest.mark.skip(...)` line
- Remove the TODO comment
- Update `import z3` to `from model_checker.z3_shim import z3` for consistency
- Run tests to verify they pass

### 2c: test_cli_execution.py
**File**: `code/src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution.py`

- Remove the `pytestmark = pytest.mark.skip(...)` line
- Remove the TODO comment
- Run test to verify it works

**Verification**: Run all bimodal test files individually

## Phase 3: Delete legacy builder test file [NOT STARTED]

**File**: `code/src/model_checker/builder/tests/test_refactoring_current_behavior.py`

Delete this file entirely. The skip message says "Tests document legacy behavior that has been removed."

**Verification**: Verify no other files import from this module.

## Phase 4: Fix solver test_validate_missing_cvc5_raises [NOT STARTED]

**File**: `code/src/model_checker/solver/tests/unit/test_registry.py`

Replace:
```python
@pytest.mark.skipif(detect_cvc5(), reason="cvc5 is installed")
def test_validate_missing_cvc5_raises(self):
    """Validating cvc5 when not installed should raise ImportError."""
    with pytest.raises(ImportError, match="cvc5 not installed"):
        validate_backend("cvc5")
```

With:
```python
def test_validate_missing_cvc5_raises(self):
    """Validating cvc5 when not installed should raise ImportError."""
    with patch("model_checker.solver.registry.detect_cvc5", return_value=False):
        with pytest.raises(ImportError, match="cvc5 not installed"):
            validate_backend("cvc5")
```

Add `from unittest.mock import patch` at top of file.

**Verification**: Run `pytest code/src/model_checker/solver/tests/unit/test_registry.py -q`

## Phase 5: Final verification [NOT STARTED]

Run targeted test suites to confirm zero unexpected skips:
- `pytest code/src/model_checker/solver/tests/ -q`
- `pytest code/src/model_checker/theory_lib/bimodal/tests/ -q --timeout=30`
- `pytest code/src/model_checker/builder/tests/ -q`
- `pytest code/src/model_checker/iterate/tests/ -q`

Expected: 0 failures, 0 unexpected skips (only xfail markers on 5 bimodal examples).
