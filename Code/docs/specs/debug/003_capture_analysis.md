# Debug Report: Save Output Capture Issue

## Problem Statement

The `-s` flag is correctly parsed and sets `save_output=True`, but the OutputCapture buffer remains empty (0 chars) after running examples, despite output being displayed on the terminal.

## Investigation Results

### 1. Flag Processing - WORKING
- `-s` flag correctly maps to `save_output` in `__main__.py`
- Settings are properly merged and passed to OutputManager
- OutputCapture instance is created when `save_output=True`

### 2. OutputCapture Implementation - WORKING
- Refactored to remove `@contextmanager` decorator
- Implements `__enter__` and `__exit__` methods correctly
- Minimal test shows capture works in isolation
- TeeOutput correctly writes to both streams

### 3. Integration Issue - PROBLEM IDENTIFIED

The issue appears to be in how output is generated within the model checker. Testing shows:
- OutputCapture enters and exits correctly
- Buffer remains at 0 chars despite visible output
- This suggests output is being written to a different stdout

## Root Cause Hypothesis

The model structure's `print_to()` method accepts an `output` parameter that defaults to `sys.__stdout__` (the original stdout), not `sys.stdout` (the current stdout which may be captured).

Looking at the error trace from earlier:
```
File "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/logos/semantic.py", line 782:
    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
```

The use of `sys.__stdout__` bypasses any stdout redirection!

## Solution

1. Change all `print_to()` methods to use `output=None` and `output or sys.stdout`
2. Ensure all print statements within model checking use the current `sys.stdout`
3. Never use `sys.__stdout__` unless explicitly bypassing capture

## Implementation Plan

### Phase 1: Audit print_to Methods
- Search for all uses of `sys.__stdout__`
- Replace with proper runtime evaluation pattern

### Phase 2: Fix Model Output
- Update all theory implementations
- Ensure consistent output handling

### Phase 3: Verify Capture
- Test with -s flag
- Ensure save prompt appears with content

## Lessons Learned

1. **Default Parameter Anti-Pattern**: `sys.__stdout__` in defaults captures the original stdout at import time
2. **Bypassed Redirection**: Using `sys.__stdout__` explicitly avoids capture mechanisms
3. **Systemic Issue**: This pattern likely exists in multiple places

This is another instance of the default parameter evaluation issue we identified earlier!