# Interactive Save Output Implementation Plan

## Overview

This document provides a comprehensive implementation plan for adding interactive save output functionality to the ModelChecker. The feature will prompt users for save decisions at runtime and provide convenient directory navigation options.

## Requirements

### User Flow

1. **Initial Mode Selection**
   - On startup with `-s` flag, prompt user to choose:
     - Batch mode: Run all examples, then save everything
     - Interactive mode: Prompt after each example
   
2. **Interactive Mode Flow**
   - After each model is found:
     - Prompt: "Save this model? (y/n)"
     - If yes: Create directory and save current model
     - Prompt: "Find additional models? (y/n)" (if iterate > 1)
     - Continue until no more models or user declines
   
3. **Final Directory Navigation**
   - Display full absolute path of output directory
   - Prompt: "Change to output directory? (y/n)"
   - If yes: Print cd command for user to execute

### Technical Requirements

- Maintain backwards compatibility with existing `-s` flag
- Support both batch and interactive modes
- Create separate directories for each saved example in interactive mode
- Provide clear, user-friendly prompts
- Handle invalid input gracefully
- Support keyboard interrupts (Ctrl+C)

## Implementation Phases

### Phase 1: Interactive Prompt Infrastructure

**Goal**: Create reusable prompt utilities for user interaction

**Tasks**:
1. Create `src/model_checker/output/prompts.py`
2. Implement prompt functions:
   - `prompt_yes_no(message: str, default: bool = False) -> bool`
   - `prompt_choice(message: str, choices: List[str]) -> str`
3. Add input validation and error handling
4. Support default values and timeout (optional)

**Tests** (`test_prompts.py`):
- Test yes/no prompts with various inputs (y, yes, Y, YES, n, no, N, NO)
- Test invalid input handling
- Test default value behavior
- Test choice prompts with valid/invalid selections

### Phase 2: Interactive Mode Manager

**Goal**: Create a manager to handle interactive save workflow

**Tasks**:
1. Create `src/model_checker/output/interactive.py`
2. Implement `InteractiveSaveManager` class:
   - `prompt_save_mode() -> str` (returns 'batch' or 'interactive')
   - `prompt_save_model(example_name: str) -> bool`
   - `prompt_find_more_models() -> bool`
   - `prompt_change_directory(path: str) -> bool`
3. Integrate with existing `OutputManager`

**Tests** (`test_interactive.py`):
- Test mode selection prompts
- Test save model prompts
- Test directory change prompts
- Test workflow sequences

### Phase 3: Modify OutputManager for Interactive Support

**Goal**: Extend OutputManager to support interactive mode

**Tasks**:
1. Modify `src/model_checker/output/manager.py`:
   - Add `interactive_mode: bool` parameter
   - Add `create_example_directory(example_name: str) -> str`
   - Modify save methods to support per-example directories
2. Update directory structure for interactive mode:
   ```
   MODELS_YYYYMMDD_HHMMSS/
   ├── IM_CM_0/
   │   ├── MODEL_1.md
   │   ├── MODEL_1.json
   │   ├── MODEL_2.md  (if multiple iterations)
   │   └── MODEL_2.json
   ├── IM_CM_1/
   │   ├── MODEL_1.md
   │   └── MODEL_1.json
   └── summary.json
   ```

**Tests** (`test_output_manager_interactive.py`):
- Test interactive mode initialization
- Test per-example directory creation
- Test model numbering for iterations
- Test summary file generation

### Phase 4: Integrate with BuildModule

**Goal**: Add interactive prompting to the model checking workflow

**Tasks**:
1. Modify `src/model_checker/builder/module.py`:
   - Add interactive mode detection
   - Prompt for save mode at startup
   - Add prompts after each model
   - Support iteration prompts
   - Display full path at end
2. Modify `_capture_and_save_output` to support interactive saves
3. Add iteration-aware prompting

**Tests** (`test_build_module_interactive.py`):
- Test interactive workflow integration
- Test batch vs interactive mode selection
- Test iteration prompting
- Mock user input for various scenarios

### Phase 5: CLI Integration

**Goal**: Add command-line support for interactive mode

**Tasks**:
1. Modify `src/model_checker/__main__.py`:
   - Add `--interactive` flag (implies `-s`)
   - Add `--no-prompt` flag to disable prompts (batch mode)
   - Update help text
2. Handle flag combinations:
   - `-s` alone: Prompt for mode
   - `-s --interactive`: Force interactive mode
   - `-s --no-prompt`: Force batch mode

**Tests** (`test_cli_interactive.py`):
- Test flag parsing
- Test flag combinations
- Test help text updates

### Phase 6: Path Display and Navigation

**Goal**: Implement user-friendly path display and navigation prompts

**Tasks**:
1. Create `src/model_checker/output/navigation.py`:
   - `format_path_display(path: str) -> str`
   - `get_cd_command(path: str) -> str`
   - `display_final_prompt(output_dir: str) -> None`
2. Add OS-specific path formatting
3. Handle relative vs absolute paths

**Tests** (`test_navigation.py`):
- Test path formatting
- Test cd command generation
- Test OS-specific behavior

### Phase 7: Documentation Updates

**Goal**: Update documentation for interactive features

**Tasks**:
1. Update `docs/TOOLS.md`:
   - Add interactive mode section
   - Document prompt behavior
   - Add workflow examples
2. Update `CLAUDE.md` with interactive workflow notes
3. Create usage examples

## Test-Driven Development Approach

Following [TESTS.md](../../docs/TESTS.md) guidelines:

### Test Structure
```python
# test_interactive_save_e2e.py
class TestInteractiveSaveE2E(unittest.TestCase):
    """End-to-end tests for interactive save workflow."""
    
    def setUp(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.mock_input = MockInput()
        
    def test_interactive_save_single_model(self):
        """Test saving a single model interactively."""
        # Mock user inputs: interactive mode, save model, no iterations
        self.mock_input.queue_inputs(['i', 'y', 'n'])
        
        # Run workflow
        result = run_interactive_workflow(self.example)
        
        # Verify directory structure
        self.assertTrue(os.path.exists(result.output_dir))
        self.assertTrue(os.path.exists(
            os.path.join(result.output_dir, 'example_1/MODEL_1.md')
        ))
```

### Test Categories

1. **Unit Tests**: Individual components (prompts, managers, utilities)
2. **Integration Tests**: Component interactions
3. **End-to-End Tests**: Complete workflows with mocked input
4. **UI Tests**: Prompt formatting and display

## Implementation Order

1. **Week 1**: Phases 1-2 (Prompt infrastructure and interactive manager)
2. **Week 2**: Phases 3-4 (OutputManager and BuildModule integration)
3. **Week 3**: Phases 5-6 (CLI and navigation)
4. **Week 4**: Phase 7 (Documentation) and comprehensive testing

## Code Style Guidelines

Following [STYLE_GUIDE.md](../../docs/STYLE_GUIDE.md):

### Naming Conventions
- Functions: `snake_case` (e.g., `prompt_yes_no`)
- Classes: `PascalCase` (e.g., `InteractiveSaveManager`)
- Constants: `UPPER_SNAKE` (e.g., `DEFAULT_PROMPT_TIMEOUT`)

### Import Order
```python
# Standard library
import os
import sys
from typing import Optional, List

# Third-party
import colorama

# Local framework
from model_checker.output import OutputManager
from model_checker.output.prompts import prompt_yes_no
```

### Error Handling
- Use explicit error messages
- No silent failures
- Validate user input with clear feedback

## Example Usage

### Batch Mode
```bash
$ ./dev_cli.py -s --no-prompt examples.py
Running all examples...
[Output for all examples]
Output saved to: /absolute/path/to/output_20240315_143022

$ cd /absolute/path/to/output_20240315_143022
```

### Interactive Mode
```bash
$ ./dev_cli.py -s examples.py
Select save mode:
  b) Batch - Save all at end
  i) Interactive - Prompt after each model
Choice [b/i]: i

EXAMPLE IM_CM_0: Model found.
Save this model? (y/n): y
Saved to: output_20240315_143022/IM_CM_0/MODEL_1.md

Find additional models? (y/n): y
Finding model 2...
Model 2 found.
Save this model? (y/n): y
Saved to: output_20240315_143022/IM_CM_0/MODEL_2.md

Find additional models? (y/n): n

[Continue with next example...]

All models saved to: /absolute/path/to/output_20240315_143022
Change to output directory? (y/n): y
To change directory, run:
  cd /absolute/path/to/output_20240315_143022
```

## Success Criteria

1. All tests pass
2. Interactive prompts are clear and responsive
3. Directory structure is organized and navigable
4. Full paths are displayed for easy navigation
5. Backwards compatibility maintained
6. Documentation is comprehensive
7. Error handling is robust

## Risk Mitigation

1. **Input handling**: Use try/except for all input operations
2. **File system**: Check permissions before creating directories
3. **User experience**: Provide clear feedback for all actions
4. **Performance**: Don't block on prompts during model checking
5. **Compatibility**: Test on different terminals and OS

## TODOs

- [x] When I hit ctrl+c after running with "save_output": False", it runs all the examples anyways and then prints: Output saved to: /home/benjamin/Documents/Philosophy/Projects/ModelChecker/output_20250804_224825
- [x] I selected '1' for batch upon running with the '-s' flag and it printed the models and ended with "Output saved to: /home/benjamin/Documents/Philosophy/Projects/ModelChecker/output_20250804_230500" but it did not give me the option to run the command. However, when I opened those files, neither looks like what I want. The json fields were mostly empty and I want the markdown file to include nicely formatted and printed examples.
  

