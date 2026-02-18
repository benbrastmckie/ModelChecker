# Example Report System - Detailed Implementation Plan

## Executive Summary

This document provides a detailed implementation plan for fixing the example report printing system in ModelChecker. The solution eliminates duplicate printing, removes the need for guard clauses, and provides a clean, maintainable architecture.

## Current Architecture Analysis

### How Examples Are Run

1. **Direct CLI Execution**:
   ```
   model-checker src/model_checker/theory_lib/logos/examples.py
   ```
   - `__main__.py` creates a `BuildModule` instance
   - `BuildModule` loads the module and extracts `example_range`
   - `ModelRunner.run_examples()` iterates through examples
   - Module-level `atexit.register()` causes report to print at exit

2. **Project Creation and Execution**:
   ```
   model-checker -l logos
   cd project_logos
   model-checker logos/examples.py
   ```
   - Project builder generates theory-specific examples.py
   - Subprocess runs `model-checker logos/examples.py`
   - In subprocess, module is imported fresh
   - `atexit.register()` happens in subprocess context
   - Report prints when subprocess exits

3. **Theory as Dependency**:
   ```python
   # In exclusion/examples.py
   from ..logos import semantic as logos_semantic
   ```
   - Importing exclusion causes logos modules to be imported
   - Logos' `atexit.register()` runs on import
   - Both exclusion and logos reports print at exit

### Core Problems Identified

1. **Multiple Import Paths**: Same module imported via different paths triggers multiple registrations
2. **Dependency Chain**: Theory dependencies cause unwanted report printing
3. **Subprocess Isolation**: Each subprocess gets fresh Python interpreter, making guards ineffective
4. **Module-Level Side Effects**: `atexit.register()` at module level causes unpredictable behavior

## Proposed Solution Architecture

### Design Principles

1. **Explicit Over Implicit**: Reports are explicitly called, not implicitly registered
2. **Single Responsibility**: Runner controls when reports print, not the modules themselves
3. **Zero Side Effects**: Importing a module should not register any callbacks
4. **Context Awareness**: Only the primary theory being tested should print its report

### Implementation Strategy

#### Phase 1: Add Report Infrastructure

**File: `src/model_checker/builder/runner.py`**

Add a method to call theory-specific report functions after examples complete:

```python
def run_examples(self):
    """Process and execute each example case with all semantic theories."""
    try:
        # ... existing example running code ...
        
        # After all examples complete successfully
        self._print_theory_report()
        
    except KeyboardInterrupt:
        # ... existing interrupt handling ...
```

Add the report printing method:

```python
def _print_theory_report(self):
    """Print theory-specific example report if available.
    
    This method checks if the loaded module has a print_example_report
    function and calls it. This ensures reports are printed exactly once,
    only for the primary theory being tested.
    """
    if hasattr(self.build_module.module, 'print_example_report'):
        # Check if it's a callable function
        report_func = getattr(self.build_module.module, 'print_example_report')
        if callable(report_func):
            try:
                report_func()
            except Exception as e:
                # Don't let report errors break the run
                print(f"\nWarning: Could not print example report: {e}")
```

#### Phase 2: Update Theory Example Files

**For each theory (`logos`, `exclusion`, `imposition`, `bimodal`):**

1. **Remove all `atexit` registrations**
2. **Remove all guard logic** 
3. **Keep `print_example_report()` function as-is**

Example transformation for `logos/examples.py`:

```python
# BEFORE:
import atexit

def print_example_report():
    """Print report of examples run."""
    # ... report implementation ...

# Guard against multiple registrations
if not hasattr(print_example_report, '_atexit_registered'):
    atexit.register(print_example_report)
    print_example_report._atexit_registered = True

# AFTER:
def print_example_report():
    """Print report of examples run."""
    # ... report implementation stays exactly the same ...

# NO atexit registration
# NO guards needed
# Function is available for runner to call
```

#### Phase 3: Handle Direct Execution

For cases where examples.py is run directly (not via model-checker CLI):

```python
# At the end of each theory's examples.py file:
if __name__ == '__main__':
    # This block only runs for direct execution: python examples.py
    # Not when imported or run via model-checker
    print_example_report()
```

#### Phase 4: Project Generation Compatibility

The current project generation already creates proper examples.py files that would work with this system. No changes needed to project generation.

When a generated project runs its examples, the flow is:
1. `model-checker logos/examples.py` runs in subprocess
2. BuildModule loads the module
3. ModelRunner.run_examples() executes examples
4. ModelRunner._print_theory_report() calls print_example_report()
5. Report prints exactly once

### Implementation Locations

#### Files to Modify

1. **`src/model_checker/builder/runner.py`**:
   - Add `_print_theory_report()` method
   - Call it at the end of `run_examples()`
   - Location: After line 736, before output finalization

2. **`src/model_checker/theory_lib/logos/examples.py`**:
   - Remove lines 366-374 (atexit registration and guard)
   - Keep `print_example_report()` function unchanged
   - Add direct execution support in `__main__` block if needed

3. **`src/model_checker/theory_lib/exclusion/examples.py`**:
   - Remove atexit registration
   - Keep `print_example_report()` function

4. **`src/model_checker/theory_lib/imposition/examples.py`**:
   - Remove atexit registration
   - Keep `print_example_report()` function

5. **`src/model_checker/theory_lib/bimodal/examples.py`**:
   - Remove atexit registration
   - Keep `print_example_report()` function

### Error Handling

1. **Missing Report Function**: Silently skip if module doesn't have `print_example_report`
2. **Report Function Errors**: Catch and warn, but don't fail the run
3. **Partial Execution**: Reports should handle incomplete example_range gracefully

### Testing Plan

1. **Direct CLI Execution**:
   ```bash
   model-checker src/model_checker/theory_lib/logos/examples.py
   # Should print report exactly once at the end
   ```

2. **Project Generation and Execution**:
   ```bash
   model-checker -l logos
   cd project_logos
   model-checker logos/examples.py
   # Should print report exactly once
   ```

3. **Theory with Dependencies**:
   ```bash
   model-checker src/model_checker/theory_lib/exclusion/examples.py
   # Should print ONLY exclusion report, NOT logos report
   ```

4. **Direct Python Execution**:
   ```bash
   python src/model_checker/theory_lib/logos/examples.py
   # Should still print report via __main__ block
   ```

5. **Interrupted Execution**:
   ```bash
   model-checker src/model_checker/theory_lib/logos/examples.py
   # Ctrl-C during execution
   # Should not print report (execution incomplete)
   ```

## Benefits of This Design

1. **Predictable Behavior**: Reports print exactly once, always at the same point
2. **No Guards Needed**: Eliminates all guard clauses and state tracking
3. **Clean Imports**: No side effects from importing modules
4. **Dependency Isolation**: Only primary theory reports, not dependencies
5. **Maintainable**: Clear responsibility - runner controls reporting
6. **Backwards Compatible**: Works with existing project structure
7. **Testable**: Easy to unit test report printing logic

## Implementation Timeline

1. **Step 1** (5 minutes): Implement `_print_theory_report()` in runner.py
2. **Step 2** (10 minutes): Remove atexit from all theory examples.py files
3. **Step 3** (5 minutes): Test all execution scenarios
4. **Step 4** (5 minutes): Verify no regressions

Total estimated time: 25 minutes

## Risk Mitigation

1. **Risk**: Some execution paths might not call the report
   - **Mitigation**: Comprehensive testing of all execution scenarios

2. **Risk**: Report function might have errors
   - **Mitigation**: Wrap in try-except to prevent breaking the run

3. **Risk**: Legacy code might depend on atexit behavior
   - **Mitigation**: Search codebase for any dependencies on report timing

## Success Metrics

1. Each theory prints its report exactly once when run as primary
2. No reports print when theory is imported as dependency
3. No guard clauses or flags in any examples.py file
4. All existing functionality continues to work
5. Clean, understandable code without complex state management

## Conclusion

This implementation plan provides a robust, elegant solution to the report printing problem. By moving control to the runner and eliminating module-level side effects, we achieve predictable, maintainable behavior without the need for guard clauses or complex state tracking.

The solution respects the principle of least surprise - reports print when and only when you run that theory's examples, never as a side effect of imports or dependencies.