# Feature Research: Save Output Functionality

## Current State Analysis

### Existing Functionality
- **Flag Parsing**: The `-s` flag is properly parsed in `__main__.py` and sets `save_output = True`
- **Settings Management**: The `save_output` setting is included in `DEFAULT_GENERAL_SETTINGS` 
- **Documentation**: The flag is documented in TOOLS.md as prompting the user to save output
- **No Implementation**: There is no actual implementation that uses the `save_output` flag

### Output Flow Analysis
1. **Output Generation**: Models print to stdout via `print_to()` methods in semantic.py files
2. **Default Parameter Issue**: All `print_to()` methods use `output=sys.__stdout__` as default
3. **Print Flow**: 
   - `BuildExample.print_model()` calls `model_structure.print_to()`
   - Output goes directly to stdout (or sys.__stdout__ by default)
   - No capture or save mechanism is triggered

### Integration Points
- **BuildModule.run_examples()**: Main execution loop for examples
- **BuildExample.print_model()**: Where model output is generated
- **SemanticTheory.print_to()**: Where actual printing happens
- **BuildExample.save_model()**: Existing method for saving models (but requires manual filename)

### Dependencies
- **sys.stdout**: Standard output stream
- **io.StringIO**: For capturing output
- **No external dependencies needed**

### Limitations
- **No automatic capture**: Output goes directly to stdout
- **Manual save only**: `save_model()` exists but requires user to provide filename
- **No prompt system**: No infrastructure for prompting user during execution

## Alternative Approaches

### Approach A: Minimal Prompt Integration
**Description**: Add a simple prompt after each example to ask if user wants to save

**Pros**:
- Low risk, minimal code changes
- Easy to implement
- Preserves existing output behavior

**Cons**:
- Interrupts flow for multiple examples
- No batch save option
- Limited user experience

### Approach B: Output Capture with Batch Save
**Description**: Capture all output and prompt once at the end

**Pros**:
- Better user experience
- Allows reviewing all output before saving
- Single interruption point

**Cons**:
- Higher memory usage for large outputs
- Requires output capture infrastructure
- More complex implementation

### Approach C: Stream-Based Capture (Recommended)
**Description**: Capture output to both stdout and buffer, prompt at end of execution

**Pros**:
- Preserves real-time output display
- Allows saving complete session output
- Clean separation of concerns
- Follows stdout redirection patterns

**Cons**:
- Requires implementing output capture system
- Need to handle the sys.__stdout__ issue

## Recommended Approach

### Approach C: Stream-Based Capture

This approach best aligns with the existing architecture and user expectations:

1. **Output Capture System**:
   - Create OutputCapture class that tees output to both stdout and StringIO
   - Replace sys.stdout during execution
   - Preserve real-time display

2. **Integration Points**:
   - Initialize capture in BuildModule when save_output=True
   - Capture during run_examples()
   - Prompt user after all examples complete

3. **User Experience**:
   - User sees output in real-time as normal
   - Single prompt at end: "Save output to file? (y/n)"
   - If yes, prompt for filename or use default
   - Save complete session output

## Risk Assessment

### Technical Risks
- **sys.__stdout__ usage**: Need to fix print_to() methods to use sys.stdout
- **Thread safety**: Ensure capture works correctly if any parallel execution
- **Memory usage**: Large outputs could consume memory

### Mitigation Strategies
- Fix print_to() defaults before implementing capture
- Use context managers for clean stdout restoration
- Add size limits or streaming to file for very large outputs