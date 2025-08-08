# Debugging Analysis: Batch Mode Output Format and Navigation

## Issue Description

When running with `-s` flag and selecting batch mode:
1. Output directory is created and path is printed
2. No prompt to change directory (unlike interactive mode)
3. JSON fields are mostly empty
4. Markdown files don't include nicely formatted examples

## Expected Behavior

1. Batch mode should also prompt to change directory at the end
2. JSON files should contain complete model data
3. Markdown files should have nicely formatted output with colors and structure

## Investigation Plan

### 1. Check Batch Mode Directory Prompt

Examine why batch mode doesn't prompt for directory change.

### 2. Analyze JSON Data Collection

Check ModelDataCollector to see why fields are empty.

### 3. Review Markdown Formatting

Examine MarkdownFormatter to understand output format issues.

## Root Cause Analysis

### 1. Missing Directory Prompt in Batch Mode

In `BuildModule.run_examples()` at line 1005:
```python
if self.interactive_manager and self.interactive_manager.is_interactive():
    self.interactive_manager.prompt_change_directory(full_path)
else:
    print(f"\nOutput saved to: {full_path}")
```

The `is_interactive()` method returns True only when mode is 'interactive', not 'batch'.
This means batch mode falls through to the else case and just prints the path.

### 2. Empty JSON and Markdown Data

The `ModelDataCollector` expects these methods on model structures:
- `get_all_N_states()` - To get list of all states
- `is_possible_state(state)` - To check if state is possible
- `is_world_state(state)` - To check if state is a world
- `syntax.propositions` - To get proposition objects

However, these methods don't exist in the base `ModelDefaults` class or theory-specific
model structures like `BimodalStructure`. The collector gracefully handles missing
attributes but returns empty data.

### 3. Missing Output in Markdown

The markdown formatter correctly formats the empty data it receives. The issue is
upstream - the data collector cannot extract the model information because the
expected interface doesn't exist.

## Solution

### 1. Fix Batch Mode Directory Prompt

Modify `BuildModule.run_examples()` to prompt for directory change in batch mode too:
```python
# Interactive mode - prompt for directory change
if self.interactive_manager:
    self.interactive_manager.prompt_change_directory(full_path)
else:
    print(f"\nOutput saved to: {full_path}")
```

### 2. Fix Model Data Collection

The `ModelDataCollector` needs to be updated to extract data from the actual model structure
attributes that exist:

For BimodalStructure:
- `world_histories` - Contains world state mappings
- `time_shift_relations` - Contains relations between worlds
- `world_arrays` - Contains world arrays
- `syntax.propositions` - Does exist and contains proposition objects

The collector is looking for non-existent methods like `get_all_N_states()` when it should
be extracting data from these attributes.

### 3. Include Raw Output in Markdown

The current flow captures the raw output but doesn't include it in the markdown files.
The `MarkdownFormatter.format_example()` receives the `model_output` parameter but only
adds it if it's not empty. The captured output needs to be passed through properly.

## Testing Plan

1. Create test example with known model structure
2. Run in batch mode and examine output files
3. Compare with expected format
4. Verify all data is collected properly

## Report Summary

I've completed the investigation of the batch mode output issues. Here are the key findings:

### Issues Found

1. **No Directory Prompt in Batch Mode**
   - The check `self.interactive_manager.is_interactive()` only returns True for interactive mode
   - Batch mode users don't get the convenient prompt to change directories

2. **Empty JSON/Markdown Data**  
   - The `ModelDataCollector` expects methods that don't exist in the model structures
   - It's looking for `get_all_N_states()`, `is_possible_state()`, etc. which aren't implemented
   - The actual model data is stored in attributes like `world_histories`, `time_shift_relations`

3. **Missing Model Output in Files**
   - The raw model output is captured but not included in the markdown files
   - The formatter receives it but doesn't display it properly

### Required Fixes

1. **Update BuildModule** to prompt for directory change in both batch and interactive modes
2. **Rewrite ModelDataCollector** to extract data from the actual model structure attributes
3. **Update MarkdownFormatter** to include the captured model output

### Next Steps

The fixes require:
- Modifying the interactive manager check in BuildModule
- Creating new data extraction methods in ModelDataCollector that work with existing model attributes
- Ensuring the captured output is properly passed to and formatted by MarkdownFormatter

This is a significant refactoring that requires understanding the structure of each theory's model implementation.