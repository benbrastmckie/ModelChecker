# Implementation Plan: Fix Pre-existing Test Failures

- **Task**: 43 - fix_preexisting_test_failures
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: reports/01_test-failures-research.md
- **Artifacts**: plans/01_test-failures-fix.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: python

## Overview

Three pre-existing test failures need resolution. The research report identified root causes and provided specific fixes for each failure. The fixes are straightforward test updates that align the test expectations with the current implementation behavior. All fixes preserve the original testing intent while updating assertions to match refactored code.

### Research Integration

The research report (01_test-failures-research.md) provided:
- Root cause analysis for each failure
- Specific file locations and line numbers
- Recommended code changes
- Verification commands

## Goals & Non-Goals

**Goals**:
- Fix FO_CM_4 example to use closed formula instead of open formula with free variable
- Update test_exists_uses_validation to check for `extract_lambda_term` instead of `validate_lambda_argument`
- Add `"parser"` to valid_errors whitelist in test_semantic_method_calls_dont_crash
- Ensure all three tests pass after fixes

**Non-Goals**:
- Changing the core implementation behavior
- Modifying other tests not mentioned in the task
- Refactoring the test structure

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| FO_CM_4 countermodel behavior changes | Medium | Low | Verify countermodel still demonstrates intended hyperintensional collapse |
| Other tests depend on changed code | Medium | Low | Run full test suite after each fix |
| Misidentified root cause | High | Low | Research already verified causes with code inspection |

## Implementation Phases

### Phase 1: Fix Simple Test Assertions [NOT STARTED]

**Goal**: Fix the two test assertion issues that require only minor test file edits.

**Tasks**:
- [ ] Edit `test_exists_duality.py` line ~126 to check for `extract_lambda_term` instead of `validate_lambda_argument`
- [ ] Update the assertion message to reflect the new function name
- [ ] Edit `test_semantic_coverage.py` line ~115 to add `"parser"` to the `valid_errors` list
- [ ] Run both tests to verify fixes

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_exists_duality.py` - Change assertion to check for `extract_lambda_term`
- `code/src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py` - Add `"parser"` to valid_errors whitelist

**Verification**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_exists_duality.py::TestLambdaValidation::test_exists_uses_validation -v

PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::TestLogosSemanticsCalls::test_semantic_method_calls_dont_crash -v
```

---

### Phase 2: Fix FO_CM_4 Example [NOT STARTED]

**Goal**: Update FO_CM_4 example to use a closed formula with constant instead of open formula with free variable.

**Tasks**:
- [ ] Edit `examples.py` line ~303-304 to change premise from `(F[v_x] \equiv G[v_x])` to `(F[a<>] \equiv G[a<>])`
- [ ] Verify the example still demonstrates the intended countermodel (constitutive equivalence at one individual does not entail universal equivalence)
- [ ] Run FO_CM_4 test to verify fix

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/examples.py` - Change FO_CM_4 premises to use constant `a<>` instead of free variable `v_x`

**Verification**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/test_first_order_examples.py -k "FO_CM_4" -v
```

---

### Phase 3: Full Test Suite Verification [NOT STARTED]

**Goal**: Confirm all fixes work together and no regressions introduced.

**Tasks**:
- [ ] Run the full first-order test suite
- [ ] Run the full logos integration test suite
- [ ] Verify no new failures introduced

**Timing**: 15 minutes

**Files to modify**: None (verification only)

**Verification**:
```bash
# First-order test suite
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/ -v

# Logos integration tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/integration/ -v
```

## Testing & Validation

- [ ] test_exists_uses_validation passes with updated assertion
- [ ] test_semantic_method_calls_dont_crash passes with expanded whitelist
- [ ] FO_CM_4 test passes with closed formula
- [ ] No regressions in first-order test suite
- [ ] No regressions in logos integration test suite

## Artifacts & Outputs

- plans/01_test-failures-fix.md (this file)
- summaries/01_test-failures-fix-summary.md (after implementation)
- Modified test files with passing tests

## Rollback/Contingency

All changes are confined to test files and one example file. If any fix causes unexpected issues:
1. Revert the specific file change using git
2. Re-investigate the root cause with additional context
3. Consult the original implementation for intended behavior

Since these are test fixes rather than implementation changes, rollback risk is minimal.
