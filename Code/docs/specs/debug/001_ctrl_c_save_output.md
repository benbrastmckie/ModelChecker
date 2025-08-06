# Debugging Analysis: Ctrl+C with save_output=False

## Issue Description

When running the model checker with `"save_output": False` in general_settings and pressing Ctrl+C during execution, the system:
1. Continues to run all examples instead of stopping
2. Incorrectly prints "Output saved to: /path/to/output_directory" even though save_output is False

## Expected Behavior

When Ctrl+C is pressed:
1. Execution should stop immediately
2. No output directory should be created or mentioned when save_output=False

## Investigation Plan

### 1. Reproduce the Issue

Create a test file to reproduce:
```python
# test_ctrl_c.py
from model_checker.theory_lib.bimodal import *

semantic_theories = {
    "test": {
        "semantics": BimodalSemantics,
        "proposition": BimodalProposition,
        "model": BimodalModel,
        "operators": {"not": Negation, "box": Box},
        "dictionary": {"~": "not", "[]": "box"}
    }
}

example_range = {
    "EXAMPLE_1": [['p'], ['p'], {'N': 3}],
    "EXAMPLE_2": [['q'], ['q'], {'N': 3}],
    "EXAMPLE_3": [['r'], ['r'], {'N': 3}]
}

general_settings = {
    "save_output": False
}
```

### 2. Trace Execution Path

Key areas to investigate:
1. **BuildModule.run_examples()** - Main execution loop
2. **KeyboardInterrupt handling** - Where is it caught/handled?
3. **OutputManager initialization** - Why is it created when save_output=False?
4. **Finalization logic** - Why does it print output path?

### 3. Hypothesis

The issue likely stems from:
1. Keyboard interrupt being caught at the wrong level
2. Finalization code running regardless of save_output setting
3. Missing check for save_output before printing output path

## Debugging Steps

### Step 1: Analyze BuildModule Initialization

Check how OutputManager is initialized when save_output=False.

### Step 2: Trace Interrupt Handling

Find where KeyboardInterrupt is caught and how it's handled.

### Step 3: Examine Finalization Logic

Look at the code that prints "Output saved to:" message.

## Root Cause Analysis

### Issue 1: Output path printed when save_output=False

In `BuildModule.run_examples()` at line 990:
```python
# Get full path for display
import os
full_path = os.path.abspath(self.output_manager.output_dir)
```

This tries to get the absolute path of `output_dir`, but when `save_output=False`:
- `output_dir` is initialized to `None` in OutputManager
- `create_output_directory()` is never called
- `os.path.abspath(None)` returns the current working directory
- The message "Output saved to: [current_directory]" is printed incorrectly

### Issue 2: Ctrl+C doesn't stop execution

There's no KeyboardInterrupt handling in:
- `BuildModule.run_examples()` 
- The main entry point in `__main__.py`

When Ctrl+C is pressed, Python raises KeyboardInterrupt but since it's not caught, the default behavior depends on where in the code execution is.

## Solution

### Fix 1: Check output_dir before printing

In `BuildModule.run_examples()`, after line 985:
```python
# Finalize output saving if enabled
if self.output_manager.should_save():
    self.output_manager.finalize()
    
    # Only print path if output was actually saved
    if self.output_manager.output_dir is not None:
        # Get full path for display
        import os
        full_path = os.path.abspath(self.output_manager.output_dir)
        
        # Interactive mode - prompt for directory change
        if self.interactive_manager and self.interactive_manager.is_interactive():
            self.interactive_manager.prompt_change_directory(full_path)
        else:
            print(f"\nOutput saved to: {full_path}")
```

### Fix 2: Add KeyboardInterrupt handling

Wrap the main loop in run_examples() with try/except:
```python
try:
    for example_name, example_case in self.example_range.items():
        # ... existing code ...
except KeyboardInterrupt:
    print("\n\nExecution interrupted by user.")
    # Still finalize if we saved any output
    if self.output_manager.should_save() and self.output_manager.output_dir is not None:
        self.output_manager.finalize()
        print(f"\nPartial output saved to: {os.path.abspath(self.output_manager.output_dir)}")
    sys.exit(1)
```

## Testing Plan

1. Create automated test for Ctrl+C behavior
2. Test with save_output=True and save_output=False
3. Verify proper cleanup in both cases

## Testing Results

Successfully implemented fixes:
1. ✓ Added check for `output_dir is not None` before printing path
2. ✓ Added KeyboardInterrupt handling with proper cleanup
3. ✓ Verified with manual testing using real example files

The automated tests revealed additional complexity with mocking settings, but manual testing confirmed the fixes work correctly.

## Lessons Learned

1. **Always check for None**: When dealing with optional features (like output saving), always verify that resources were actually created before using them.

2. **Consistent error handling**: KeyboardInterrupt should be handled at the appropriate level - in this case, the main example processing loop.

3. **Test with real examples**: While unit tests are valuable, testing with actual example files can reveal issues that mocked tests might miss.

4. **Clean exit on interrupt**: When handling KeyboardInterrupt, ensure partial results are saved if applicable and provide clear feedback to the user.