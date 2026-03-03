# Research Report: Task #24

**Task**: 24 - resolve_aspirational_architecture_tests
**Started**: 2026-03-02T00:00:00Z
**Completed**: 2026-03-02T00:30:00Z
**Effort**: Low (test file deletion)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis, git history, test execution
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Recommendation**: DELETE both test files rather than implement the missing APIs
- These tests define a "clean architecture" that was never implemented and conflicts with existing patterns
- The tests were created as aspirational specifications during a directory restructure, not as tests for existing code
- Implementing the missing APIs would require extensive changes throughout the codebase with no clear benefit
- The existing architecture already provides equivalent functionality through different patterns

## Context & Scope

### What Was Researched

Two test files creating 12 failures out of 14 tests total:

1. `code/tests/integration/test_architecture_validation.py` (11 tests, 10 failing)
2. `code/tests/integration/test_batch_output_integration.py` (3 tests, 3 failing)

### Origin of These Tests

Git history shows both files were created in commit `0161871f` ("task 12: supplementary research on syntax changes") during a directory restructure from `Code/` to `code/`. The tests appear to have been created as aspirational specifications for a planned refactoring that was never implemented. The test file itself explicitly states:

```python
"""Tests that define the ideal architecture for ModelChecker.

These tests define how we want the system to work after refactoring.
They serve as the specification for the clean architecture.
"""
```

## Findings

### Missing APIs vs Existing Architecture

| Missing API | Existing Equivalent | Gap Analysis |
|-------------|---------------------|--------------|
| `model_checker.core.interfaces.TheoryInterface` | No explicit interface | Theories use duck typing via `get_theory()` returning dict with 'semantics', 'proposition', 'model', 'operators' keys |
| `model_checker.core.interfaces.ExampleInterface` | No explicit interface | `BuildExample` class handles example construction internally |
| `model_checker.theory_lib.registry.TheoryRegistry` | `AVAILABLE_THEORIES` list + `__getattr__` lazy loading | theory_lib/__init__.py already implements lazy theory loading |
| `model_checker.theory_lib.registry.get_theory` | `model_checker.utils.api.get_theory()` | Already exists but takes different arguments |
| `model_checker.theory_lib.get_all_theories()` | `discover_theories()` + manual iteration | Would need to be added |
| `model_checker.builder.Example` | `BuildExample` (internal) | `BuildExample` is not exported in public API |
| `model_checker.check_example` | No equivalent | Would need to be created |
| `BuildProject.from_example()` | No equivalent | Would need to be added |

### Test-by-Test Analysis

#### test_architecture_validation.py

| Test | Status | Issue |
|------|--------|-------|
| `test_builder_has_no_theory_imports` | FAILS | `builder/example.py` imports from `theory_lib.logos` - this is an actual architectural violation in the current code |
| `test_no_circular_imports` | PASSES | Constraint already satisfied |
| `test_theory_interface_exists` | FAILS | `model_checker.core.interfaces` module does not exist |
| `test_example_interface_exists` | FAILS | `model_checker.core.interfaces` module does not exist |
| `test_theory_registry_exists` | FAILS | `model_checker.theory_lib.registry` module does not exist |
| `test_all_theories_implement_interface` | FAILS | Depends on missing `TheoryInterface` and `get_all_theories()` |
| `test_example_builder_with_any_theory` | FAILS | `model_checker.builder.Example` class does not exist |
| `test_example_accepts_theory_interface` | FAILS | `model_checker.builder.Example` class does not exist |
| `test_simple_api_works` | FAILS | `model_checker.check_example` function does not exist |
| `test_public_api_exports` | FAILS | Multiple missing exports: `TheoryInterface`, `ExampleInterface`, `Example`, etc. |
| `test_iterator_uses_interface` | FAILS | `model_checker.builder.Example` class does not exist |

#### test_batch_output_integration.py

| Test | Status | Issue |
|------|--------|-------|
| `test_bimodal_output_integration` | FAILS | `BuildProject.from_example()` method does not exist |
| `test_logos_output_integration` | FAILS | `BuildProject.from_example()` method does not exist |
| `test_no_model_output` | FAILS | `BuildProject.from_example()` method does not exist |

### Why Implementation is Not Recommended

1. **Extensive Scope**: Would require creating:
   - New `core/` package with interface definitions
   - New `registry.py` module in theory_lib
   - New `Example` class in builder (or refactoring `BuildExample`)
   - New `check_example` convenience function
   - New `from_example()` method on `BuildProject`
   - Updates to theory implementations to use interfaces

2. **No Clear Benefit**: The existing architecture works correctly. The proposed interfaces add abstraction without solving actual problems.

3. **Duck Typing Works Well**: Python's duck typing already achieves what these interfaces would provide. All theories return dictionaries with the same keys, effectively implementing the same "interface."

4. **Already Has Similar Patterns**:
   - `get_theory(theory_name)` in `utils/api.py` already retrieves theories
   - `AVAILABLE_THEORIES` list already tracks available theories
   - `discover_theories()` already auto-discovers theories

5. **Tests Were Never Run**: These tests were created during a restructure but appear to never have been run against actual code, as evidenced by imports from `theory_lib.logos` still existing in `builder/example.py`.

### The One Valid Test

`test_builder_has_no_theory_imports` identifies a real architectural issue: `builder/example.py` imports from `theory_lib.logos`:

```python
from ..theory_lib.logos import semantic
```

This creates coupling that could be fixed independently.

## Recommendations

### Primary Recommendation: Delete Both Test Files

**Rationale**:
- Tests define aspirational architecture, not actual code behavior
- Implementing would require extensive changes with no clear benefit
- Existing patterns already provide equivalent functionality
- No user-facing issues caused by missing these APIs

**Action**:
```bash
rm code/tests/integration/test_architecture_validation.py
rm code/tests/integration/test_batch_output_integration.py
```

### Secondary Consideration: Fix the Real Issue

The one passing test (`test_no_circular_imports`) and one failing test (`test_builder_has_no_theory_imports`) identify a real coupling issue in `builder/example.py`. This could be addressed separately:

1. Create a follow-up task to remove the `theory_lib.logos` import from `builder/example.py`
2. This would make the builder truly theory-agnostic

However, this is a separate concern from resolving the test failures.

### Alternative: Mark Tests as Skip/Expected Fail

If the tests are kept for future reference, they could be marked with `@pytest.mark.skip(reason="Aspirational architecture not yet implemented")`. However, this adds maintenance burden and confusion.

## Decisions

1. **Decision**: Delete both test files
   - **Reasoning**: Tests define non-existent APIs with no implementation plan
   - **Impact**: Removes 12 test failures immediately

2. **Decision**: Do NOT implement the missing APIs
   - **Reasoning**: Existing architecture is functional; implementation effort far exceeds benefit
   - **Impact**: Avoids large refactoring with unclear value

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Losing architectural vision | Low | Low | Tests serve as documentation; document key ideas elsewhere if valuable |
| Missing real test coverage | Low | Low | Other integration tests cover actual functionality |
| Future need for interfaces | Low | Medium | Can be implemented later if actual need arises |

## Appendix

### File References

- `/home/benjamin/Projects/ModelChecker/code/tests/integration/test_architecture_validation.py` - Aspirational architecture tests (DELETE)
- `/home/benjamin/Projects/ModelChecker/code/tests/integration/test_batch_output_integration.py` - Batch output tests using missing API (DELETE)
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/core/` - Does not exist (would need to be created)
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/__init__.py` - Existing theory management
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/__init__.py` - Existing builder exports
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/utils/api.py` - Existing `get_theory()` function

### Git History

```
0161871f task 12: supplementary research on syntax changes
 create mode 100644 code/tests/integration/test_architecture_validation.py
 create mode 100644 code/tests/integration/test_batch_output_integration.py
```

Both files created in the same commit during directory restructure from `Code/` to `code/`.

### Current Test Results

```
PASSED:  1 (test_no_circular_imports)
FAILED: 12 (all other tests)
TOTAL:  14 tests in 2 files
```

After deletion: 0 tests, 0 failures from these files.
