# Test Failures Analysis

Date: 2025-08-05

## Overview

This document analyzes the test failures found when running `./run_tests.py --package`. The failures are concentrated in two components:

1. **Builder Component**: Interactive mode tests failing due to `input()` calls during testing
2. **Output Component**: Integration tests expecting different markdown formatting

## Root Cause Analysis

### 1. Builder Component Failures (5 tests)

**Affected Tests**:
- `test_build_module_interactive.py::TestBuildModuleInteractive` (5 failures)
- `test_cli_interactive_integration.py::TestCLIInteractiveIntegration` (1 failure)

**Root Cause**: 
The tests are failing because they're attempting to call `input()` during test execution, which is not allowed by pytest. The issue occurs in `InteractiveSaveManager.prompt_save_mode()` which uses `input()` directly instead of being properly mocked.

**Code Path**:
```python
# src/model_checker/output/interactive.py:39
response = input("Save all examples (a) or run in sequence (s)? ").strip().lower()
```

**Problem**: The tests mock `prompt_choice` but not the direct `input()` call in `prompt_save_mode()`.

### 2. Output Component Failures (6 tests)

**Affected Tests**:
- `test_interactive.py::TestInteractiveSaveManager` (2 failures)
- `test_output_integration.py::TestOutputIntegration` (4 failures)

**Root Causes**:

#### A. Interactive Tests (2 failures)
Same issue as builder component - direct `input()` calls in `prompt_save_mode()`.

#### B. Integration Tests (4 failures)
The `MarkdownFormatter.format_example()` method has been simplified to only return the raw model output, but the tests expect structured markdown with headers and sections.

**Current Implementation**:
```python
# src/model_checker/output/formatters.py:34-43
def format_example(self, example_data: Dict[str, Any], 
                  model_output: str) -> str:
    # Just return the model output without any headers or emoji sections
    if model_output:
        return model_output.strip()
    else:
        # If no model output, return a simple message
        example = example_data.get("example", "Unknown")
        if not example_data.get("has_model", False):
            return f"EXAMPLE {example}: there is no countermodel."
        else:
            return f"EXAMPLE {example}: model found but no output available."
```

**Test Expectations**:
- Tests expect markdown headers like `## Example: test_bimodal`
- Tests expect structured sections like `### States`, `### Relations`
- Tests expect formatted state listings like `s7 [EVALUATION]`

## Impact Assessment

### Builder Component
- 6 tests failing due to unmocked `input()` calls
- Tests are correctly identifying an issue with test isolation
- The actual functionality works but tests need proper mocking

### Output Component
- 2 tests failing due to unmocked `input()` calls (same as builder)
- 4 tests failing due to simplified markdown formatter
- The formatter has been intentionally simplified but tests weren't updated

## Solution Options

### Option 1: Fix Tests Only (Quick Fix)
**Approach**: Update tests to match current implementation behavior
- Mock `input()` calls in interactive tests
- Update integration tests to expect simplified output
- **Pros**: Fast implementation, maintains current behavior
- **Cons**: May hide design issues, tests become less meaningful

### Option 2: Restore Formatter Functionality (Medium Effort)
**Approach**: Restore the structured markdown formatting
- Keep the simplified output as default
- Add a flag or method for structured output
- Update tests accordingly
- **Pros**: Maintains test coverage, preserves formatting capabilities
- **Cons**: More complex, may not align with current design goals

### Option 3: Refactor Interactive Input (Recommended)
**Approach**: Abstract input mechanism for better testability
- Create an InputProvider interface
- Use dependency injection for input mechanism
- Mock at the interface level in tests
- **Pros**: Better design, fully testable, maintains functionality
- **Cons**: Requires refactoring, more complex initial implementation

## Recommendation

I recommend **Option 3** (Refactor Interactive Input) combined with updating the integration tests to match the current simplified formatter output. This approach:

1. Fixes the root cause of input-related test failures
2. Makes the code more testable and maintainable
3. Accepts the design decision to simplify markdown output
4. Maintains proper test coverage

The refactoring would involve:
1. Creating an `InputProvider` abstraction
2. Updating `InteractiveSaveManager` to use the abstraction
3. Properly mocking the abstraction in tests
4. Updating integration tests to expect simplified output