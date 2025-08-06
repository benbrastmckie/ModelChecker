# Implementation Plan: Save Output Feature

## Selected Approach
**Stream-Based Capture with End-of-Session Prompt**

This approach captures output during execution while preserving real-time display, then prompts the user once at the end to save the complete session output.

## Test-Driven Development Strategy
- **Test categories**: Unit tests for capture system, integration tests for save flow
- **Testing framework**: Following existing pytest patterns
- **Success criteria**: Output captured correctly, user prompts work, files saved properly

## Implementation Phases

### Phase 1: Fix Print Output Defaults (Priority: High)
**Objective**: Fix sys.__stdout__ usage to enable output capture

**Tests to Write First**:
- `test_print_to_uses_current_stdout.py`: Verify print_to respects sys.stdout
- `test_output_redirection.py`: Test output can be redirected

**Implementation Tasks**:
1. Update all print_to() method signatures to use `output=None`
2. Add `if output is None: output = sys.stdout` checks
3. Update color detection to use `hasattr(output, 'isatty')`
4. Verify all theories follow consistent pattern

**Success Criteria**:
- [ ] All print_to methods use current stdout by default
- [ ] Output redirection tests pass
- [ ] No regression in normal output display

### Phase 2: Output Capture Infrastructure (Priority: High)
**Objective**: Build core output capture system

**Tests to Write First**:
- `test_output_capture.py`: Test OutputCapture class functionality
- `test_tee_output.py`: Test simultaneous stdout and buffer writing

**Implementation Tasks**:
1. Create `src/model_checker/output/capture.py`:
   - OutputCapture class with context manager support
   - TeeOutput class for dual writing
   - Thread-safe implementation
2. Add capture initialization to BuildModule
3. Integrate capture with run_examples flow

**Success Criteria**:
- [ ] OutputCapture captures all output
- [ ] Real-time display still works
- [ ] Context manager properly restores stdout

### Phase 3: Save Prompt System (Priority: High)
**Objective**: Implement user prompt and file saving

**Tests to Write First**:
- `test_save_prompt.py`: Test prompt behavior and user input
- `test_file_save.py`: Test output file creation

**Implementation Tasks**:
1. Create `src/model_checker/output/save.py`:
   - prompt_save_output() function
   - Default filename generation
   - File writing with proper encoding
2. Add prompt call after run_examples
3. Handle user input validation

**Success Criteria**:
- [ ] Prompt appears only when save_output=True
- [ ] User can save or skip
- [ ] Files saved with correct content

### Phase 4: Integration and Edge Cases (Priority: Medium)
**Objective**: Handle special cases and ensure robustness

**Tests to Write First**:
- `test_empty_output.py`: Test behavior with no output
- `test_large_output.py`: Test with very large outputs
- `test_special_characters.py`: Test Unicode handling

**Implementation Tasks**:
1. Add size limits and warnings for large outputs
2. Handle empty output gracefully
3. Ensure Unicode characters preserved
4. Add error handling for file operations

**Success Criteria**:
- [ ] All edge cases handled gracefully
- [ ] No memory issues with large outputs
- [ ] Unicode content preserved correctly

### Phase 5: Documentation Updates (Priority: Medium)
**Objective**: Update all documentation for new feature

**Implementation Tasks**:
1. Update TOOLS.md with detailed save_output examples
2. Add section to user guides
3. Update CLI help text
4. Add examples showing saved output files

**Success Criteria**:
- [ ] Documentation complete and accurate
- [ ] Examples demonstrate feature usage
- [ ] Help text explains behavior clearly

## Integration Points

### Modified Components
- **All semantic.py files**: Update print_to() signatures
- **BuildModule**: Add output capture initialization
- **__main__.py**: No changes needed (flag already parsed)

### New Components
- **src/model_checker/output/**: New package for output management
  - `capture.py`: Output capture functionality
  - `save.py`: Save prompt and file operations
  - `__init__.py`: Package exports

### Configuration Changes
- No new settings needed (save_output already exists)
- No breaking changes to existing configs

## Breaking Changes
- **None**: All changes are backward compatible

## Post-Implementation Tasks
- [ ] Run full test suite to ensure no regressions
- [ ] Test with various example files
- [ ] Verify Unicode handling in saved files
- [ ] Check performance impact is minimal