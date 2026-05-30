# Research Report: Fix All Skipped and Failing Tests

## Summary

Investigated all skipped and failing tests. Current state: 1 failing, ~56 skipped across 8 files. Most issues are straightforward to fix.

## 1. Failing Test: test_push_pop_sat_transitions

**File**: `solver/tests/unit/test_equivalence.py:127`
**Root Cause**: Test uses `z3_x > 200` and `z3_x < 100` on 8-bit BitVec expecting unsat, but `>` and `<` are signed comparisons. Signed 8-bit 200 = -56, so `x > -56 AND x < 100` is satisfiable.
**Fix**: Change test values to be contradictory under signed comparison: use `x > 50` and `x < 10` (both positive, clearly contradictory).
**Risk**: Low — test-only change.

## 2. Bimodal Unit Tests (test_bimodal.py) — 21 tests

**File**: `theory_lib/bimodal/tests/unit/test_bimodal.py`
**Skip**: Module-level `@pytest.mark.skip` decorator on `test_example_cases`.
**Tested without skip**: 16 pass, 5 fail (TN_CM_1, TN_CM_2, BM_CM_2, BM_CM_3, BM_CM_4). Failures are timeout-related (5+ seconds each) — these are genuine countermodel examples that the solver struggles with.
**Fix**: Remove skip decorator. For the 5 failing examples, mark them individually with `@pytest.mark.skip(reason="Known solver timeout")` or increase timeout. These are real semantic issues outside task 69 scope.
**Risk**: Medium — the 5 failures need individual skip markers or exclusion.

## 3. Bimodal Integration Tests (test_iterate.py) — 3 tests

**File**: `theory_lib/bimodal/tests/integration/test_iterate.py`
**Skip**: Module-level `pytestmark = pytest.mark.skip`.
**Analysis**: Tests use `import z3` directly (line 3) instead of z3_shim. Tests mock heavily and should work once unskipped, but the imports need updating.
**Fix**: Remove pytestmark skip. Update `import z3` to use z3_shim or keep z3 for mock-only usage.
**Risk**: Low — mostly mock-based tests.

## 4. Bimodal E2E Tests (test_cli_execution.py) — 1 test

**File**: `theory_lib/bimodal/tests/e2e/test_cli_execution.py`
**Skip**: Module-level `pytestmark = pytest.mark.skip`.
**Analysis**: Test modifies source files (examples.py) during execution, runs subprocess. This is fragile and potentially dangerous.
**Fix**: Remove skip. The test should work if dev_cli.py path is correct. But the file-modification approach is fragile.
**Risk**: Medium — mutates source files during test.

## 5. Builder Legacy Tests (test_refactoring_current_behavior.py) — 14 tests

**File**: `builder/tests/test_refactoring_current_behavior.py`
**Skip**: Module-level `pytestmark = pytest.mark.skip(reason="Tests document legacy behavior that has been removed")`.
**Analysis**: Tests document old ModuleLoader behavior. The class still exists and most tests probably pass. However, these tests verify "current behavior before refactoring" — if the refactoring is done, they're obsolete.
**Fix**: Delete the file. The skip message says "legacy behavior that has been removed."
**Risk**: Low — file explicitly documents removed behavior.

## 6. Builder TDD Tests — 3 files, 31 tests total

**Files**:
- `builder/tests/unit/test_runner.py` (9 tests) — `skipIf(not RUNNER_EXISTS)`
- `builder/tests/unit/test_translation.py` (12 tests) — `skipIf(not TRANSLATION_EXISTS)`  
- `builder/tests/unit/test_comparison.py` (10 tests) — `skipIf(not COMPARISON_EXISTS)`

**Current state**: ALL PASS. ModelRunner, OperatorTranslation, and ModelComparison classes now exist. The `skipIf` guards import successfully, so `RUNNER_EXISTS=True`, `TRANSLATION_EXISTS=True`, `COMPARISON_EXISTS=True`. No tests are actually skipped anymore.
**Fix**: None needed — these are already running and passing.
**Risk**: None.

## 7. Solver test_validate_missing_cvc5_raises (test_registry.py) — 1 test

**File**: `solver/tests/unit/test_registry.py:96-100`
**Skip**: `@pytest.mark.skipif(detect_cvc5(), reason="cvc5 is installed")`
**Analysis**: Test verifies that `validate_backend("cvc5")` raises ImportError when cvc5 is not installed. Skipped because cvc5 IS installed in this env.
**Fix**: Mock `detect_cvc5` to return False, then call `validate_backend("cvc5")`. This makes the test work regardless of whether cvc5 is installed.
**Risk**: Low — test-only change with mocking.

## 8. Graph Utils (test_graph_utils.py) — 3 tests

**File**: `iterate/tests/integration/test_graph_utils.py`
**Skip**: `skipif(not HAS_DEPENDENCIES)` where HAS_DEPENDENCIES checks for networkx import.
**Current state**: ALL PASS. NetworkX is installed (it's in pyproject.toml dependencies). The `skipif` guard evaluates to False, so tests run normally.
**Fix**: None needed — tests are already running and passing.
**Risk**: None.

## Implementation Plan Summary

| Issue | Action | Tests Affected |
|-------|--------|---------------|
| test_push_pop_sat_transitions | Change test values to signed-compatible | 1 |
| test_bimodal.py | Remove skip, add individual skips for 5 failing | 21 (16 pass, 5 skip) |
| test_iterate.py | Remove module-level skip | 3 |
| test_cli_execution.py | Remove module-level skip | 1 |
| test_refactoring_current_behavior.py | Delete file | 14 (removed) |
| test_runner/translation/comparison.py | No action needed | 31 (already passing) |
| test_validate_missing_cvc5_raises | Mock detect_cvc5 | 1 |
| test_graph_utils.py | No action needed | 3 (already passing) |

**Net result**: 0 failing, ideally 5 skipped (the genuinely problematic bimodal examples), down from 1 failing + ~56 skipped.
