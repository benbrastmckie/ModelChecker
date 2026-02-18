# Example Report System Design

## Executive Summary

This document outlines the design for a robust and elegant example reporting system for ModelChecker theories. The goal is to provide informative end-of-run reports without requiring guard clauses or complex state management.

## Design Objectives

1. **Single Report Per Run**: Each theory should print its report exactly once when its examples are run
2. **No Guards Required**: The design should not need flags or guards to prevent duplicate printing
3. **Theory Independence**: The solution should work for any theory without hardcoding theory names
4. **Project Compatibility**: Reports should work correctly both in theory_lib and in generated projects
5. **Clean Separation**: Reports from dependencies should not interfere with the main theory's report

## Current Problems

### Problem 1: Multiple Module Imports
When model-checker loads a theory's examples.py file, the module may be imported multiple times through different import paths:
- Direct import as the main module
- Import as a dependency by other theories
- Re-imports during module reloading

### Problem 2: Subprocess Execution
When project creation runs examples via subprocess, the module lifecycle is different:
- The subprocess starts fresh with its own Python interpreter
- atexit handlers are registered in the subprocess context
- The parent process doesn't see the subprocess's atexit handlers

### Problem 3: Dependency Chain Printing
Theories that depend on other theories (e.g., exclusion depends on logos) cause both reports to print:
- exclusion imports logos modules
- This triggers logos' atexit registration
- Both reports print at exit

### Problem 4: Timing Issues
Reports may print at different times:
- During module import (if called directly)
- At program exit (via atexit)
- Multiple times if module is re-imported

## Current Implementation Analysis

### What's Working
- Reports contain useful information about examples run
- Attribution and documentation links are helpful
- Subtheory breakdown in logos is informative

### What's Not Working
- `atexit.register()` at module level causes multiple registrations
- Guards using function attributes don't work reliably across imports
- Module-level registration happens even when theory is just a dependency
- Multiple reports print when one theory depends on another

## Proposed Solution: Context-Aware Reporting

### Core Principle
**Reports should only print when the theory is the PRIMARY theory being tested, not when imported as a dependency.**

### Implementation Strategy

#### 1. Runner-Controlled Reporting
Instead of using atexit at module level, have the model-checker runner explicitly call the report function:

```python
# In examples.py
def print_example_report():
    """Print report of examples run."""
    # Report implementation
    pass

# NO atexit registration at module level
# NO guards or flags needed
```

#### 2. BuildModule Integration
The BuildModule class should be responsible for calling the report after running examples:

```python
# In builder/module.py
class BuildModule:
    def run_examples(self):
        # Run the examples
        results = self._execute_examples()
        
        # If the module has a report function, call it
        if hasattr(self.module, 'print_example_report'):
            self.module.print_example_report()
        
        return results
```

#### 3. Project Compatibility
For generated projects, include a small wrapper that calls the report:

```python
# In generated project's __main__ section
if __name__ == '__main__':
    # Run examples through model-checker
    # ... existing code ...
    
    # Print report if available
    if 'print_example_report' in locals():
        print_example_report()
```

#### 4. Clean Command-Line Support
For direct command-line execution:

```python
# In examples.py
if __name__ == '__main__':
    # Run examples
    # ... existing code ...
    
    # Print report at the end
    print_example_report()
```

### Benefits of This Design

1. **No Guards Needed**: Report is called exactly once by the runner
2. **No atexit Complexity**: Avoids all atexit registration issues
3. **Clear Responsibility**: The runner (BuildModule) controls when reports print
4. **No Dependency Conflicts**: Only the primary theory's report prints
5. **Predictable Timing**: Report always prints after examples complete
6. **Easy to Test**: Can call print_example_report() directly in tests

### Migration Path

1. Remove all atexit registrations from theory examples.py files
2. Keep print_example_report() functions as-is
3. Update BuildModule to call print_example_report() after running examples
4. Update project generation to include report call in generated files
5. Test with each theory to ensure single report printing

## Alternative Approaches Considered

### 1. Environment Variable Approach
Set an environment variable to indicate the primary theory:
- **Rejected**: Too fragile, requires process-wide state

### 2. Import Hook Approach  
Use Python import hooks to control when reports are registered:
- **Rejected**: Too complex, hard to debug

### 3. Singleton Pattern
Use a singleton to ensure single registration:
- **Rejected**: Still requires guards, doesn't solve dependency issue

## Implementation Checklist

- [ ] Remove atexit.register() from all theory examples.py files
- [ ] Update BuildModule to call print_example_report() after example execution
- [ ] Modify project template to include report call
- [ ] Test each theory individually
- [ ] Test theories with dependencies (exclusion -> logos)
- [ ] Test project generation and example execution
- [ ] Document the new report system in theory development guide

## Success Criteria

1. Each theory prints its report exactly once when run as primary
2. No report prints when theory is imported as dependency
3. No guard clauses or flags in examples.py files
4. Reports work correctly in both theory_lib and generated projects
5. Clean, understandable code without complex state management