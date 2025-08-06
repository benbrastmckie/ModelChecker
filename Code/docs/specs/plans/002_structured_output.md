# Implementation Plan: Structured Output Save Feature

## Overview
Implement a save output feature that creates a structured directory containing:
- `EXAMPLES.md`: Formatted example output with color support or clear state indicators
- `MODELS.json`: Machine-readable model data
- Support for batch vs sequential output modes
- Options for single vs multiple files in sequential mode

## Output Structure Example
```
output_20240305_143022/
├── EXAMPLES.md          # Human-readable formatted output
├── MODELS.json          # Machine-readable model data
└── sequential/          # (Optional) Individual example files
    ├── example1.md
    ├── example2.md
    └── ...
```

## Test-Driven Development Strategy
- **Test categories**: Unit tests for formatters, integration tests for output modes
- **Testing framework**: Following existing pytest patterns
- **Success criteria**: Correct file structure, proper formatting, mode switching works

## Implementation Phases

### Phase 1: Output Directory Structure (Priority: High)
**Objective**: Create directory management and output organization

**Tests to Write First**:
- `test_output_directory.py`: Test directory creation and structure
- `test_output_modes.py`: Test batch vs sequential mode selection

**Implementation Tasks**:
1. Create `src/model_checker/output/manager.py`:
   ```python
   class OutputManager:
       def __init__(self, save_output: bool, mode: str = 'batch'):
           self.save_output = save_output
           self.mode = mode  # 'batch' or 'sequential'
           self.output_dir = None
           self.models_data = []
           
       def create_output_directory(self):
           """Create timestamped output directory"""
           
       def should_save(self) -> bool:
           """Check if saving is enabled"""
   ```

2. Add output mode options to CLI:
   ```python
   parser.add_argument(
       '--output-mode',
       choices=['batch', 'sequential'],
       default='batch',
       help='Output mode: batch (single file) or sequential (multiple files)'
   )
   parser.add_argument(
       '--sequential-files',
       choices=['single', 'multiple'],
       default='multiple',
       help='For sequential mode: single file or multiple files'
   )
   ```

**Success Criteria**:
- [ ] Directory created with timestamp
- [ ] Output modes properly initialized
- [ ] Manager tracks output state

### Phase 2: Model Data Collection (Priority: High)
**Objective**: Collect model data in structured format for JSON export

**Tests to Write First**:
- `test_model_data_collection.py`: Test data extraction from models
- `test_json_serialization.py`: Test JSON format and structure

**Implementation Tasks**:
1. Create `src/model_checker/output/collectors.py`:
   ```python
   class ModelDataCollector:
       def collect_model_data(self, model_structure, example_name, theory_name):
           """Extract model data into structured format"""
           return {
               "example": example_name,
               "theory": theory_name,
               "has_model": model_structure.z3_model_status,
               "states": self._collect_states(model_structure),
               "evaluation_world": self._get_evaluation_world(model_structure),
               "relations": self._collect_relations(model_structure),
               "propositions": self._collect_propositions(model_structure)
           }
           
       def _collect_states(self, model_structure):
           """Collect state information with types"""
           # Return list of states with their properties:
           # - possible/impossible
           # - world state or not
           # - state number/name
   ```

2. Update model classes to expose necessary data

**Success Criteria**:
- [ ] Model data properly extracted
- [ ] JSON structure is complete and valid
- [ ] All state types identified correctly

### Phase 3: Markdown Formatter with Color Support (Priority: High)
**Objective**: Create formatted markdown output with color indicators

**Tests to Write First**:
- `test_markdown_formatter.py`: Test markdown generation
- `test_color_formatting.py`: Test ANSI color conversion to markdown

**Implementation Tasks**:
1. Create `src/model_checker/output/formatters.py`:
   ```python
   class MarkdownFormatter:
       def __init__(self, use_colors: bool = True):
           self.use_colors = use_colors
           
       def format_example(self, example_data, model_output):
           """Format example with proper markdown and color indicators"""
           # Convert ANSI colors to markdown indicators:
           # - 🟢 Possible states (green)
           # - 🔴 Impossible states (red)
           # - 🔵 World states (blue)
           # - ⭐ Evaluation world (special marker)
           
       def format_state_type(self, state, state_type):
           """Format state with type indicator"""
           if self.use_colors:
               return self._with_color_emoji(state, state_type)
           else:
               return f"{state} [{state_type.upper()}]"
   ```

2. Create ANSI to Markdown converter:
   ```python
   class ANSIToMarkdown:
       def convert(self, ansi_text):
           """Convert ANSI escape codes to markdown-friendly format"""
   ```

**Success Criteria**:
- [ ] Markdown properly formatted
- [ ] State types clearly indicated
- [ ] Color support works when available
- [ ] Fallback to text indicators works

### Phase 4: Output Mode Implementation (Priority: High)
**Objective**: Implement batch and sequential output modes

**Tests to Write First**:
- `test_batch_output.py`: Test single file output mode
- `test_sequential_output.py`: Test multiple file output mode
- `test_sequential_single.py`: Test sequential single file mode

**Implementation Tasks**:
1. Extend OutputManager with mode-specific logic:
   ```python
   class OutputManager:
       def save_example(self, example_name, example_data, formatted_output):
           """Save example based on current mode"""
           if self.mode == 'batch':
               self._append_to_batch(example_name, example_data, formatted_output)
           else:  # sequential
               self._save_sequential(example_name, example_data, formatted_output)
               
       def finalize(self):
           """Finalize output and save files"""
           if self.mode == 'batch':
               self._save_batch_files()
           self._save_models_json()
   ```

2. Implement sequential mode options:
   ```python
   def _save_sequential(self, example_name, example_data, formatted_output):
       if self.sequential_files == 'multiple':
           # Save to individual files in sequential/ subdirectory
       else:  # single
           # Append to single EXAMPLES.md with separators
   ```

**Success Criteria**:
- [ ] Batch mode creates single EXAMPLES.md
- [ ] Sequential mode creates appropriate file structure
- [ ] Mode switching works correctly
- [ ] All files properly formatted

### Phase 5: Integration with BuildModule (Priority: High)
**Objective**: Integrate new output system with existing execution flow

**Tests to Write First**:
- `test_build_integration.py`: Test integration with BuildModule
- `test_end_to_end_save.py`: Test complete save workflow

**Implementation Tasks**:
1. Update BuildModule to use OutputManager:
   ```python
   def __init__(self, module_flags):
       # ... existing code ...
       self.output_manager = OutputManager(
           save_output=self.save_output,
           mode=getattr(module_flags, 'output_mode', 'batch')
       )
   ```

2. Modify run_examples to collect output:
   ```python
   def run_examples(self):
       if self.output_manager.should_save():
           self.output_manager.create_output_directory()
           
       # ... existing example loop ...
       # In process_example:
       if self.output_manager.should_save():
           # Capture output and model data
           model_data = collector.collect_model_data(...)
           formatted_output = formatter.format_example(...)
           self.output_manager.save_example(...)
   ```

3. Add finalization after all examples:
   ```python
   # After example loop
   if self.output_manager.should_save():
       self.output_manager.finalize()
       print(f"\nOutput saved to: {self.output_manager.output_dir}")
   ```

**Success Criteria**:
- [ ] Integration doesn't break existing functionality
- [ ] Output saved correctly for all modes
- [ ] User informed of output location

### Phase 6: User Prompts and Interaction (Priority: Medium)
**Objective**: Add user interaction for save options

**Tests to Write First**:
- `test_user_prompts.py`: Test prompt flow and options
- `test_prompt_defaults.py`: Test default behavior

**Implementation Tasks**:
1. Create prompt system:
   ```python
   class SavePrompt:
       def prompt_save_options(self):
           """Prompt user for save options if not specified via CLI"""
           # Ask: Save output? (y/n)
           # If yes, ask: Batch or sequential? 
           # If sequential, ask: Single or multiple files?
           
       def get_directory_name(self, default):
           """Allow user to customize directory name"""
   ```

2. Integrate prompts when -s flag used without mode specification

**Success Criteria**:
- [ ] Prompts appear when appropriate
- [ ] Defaults work correctly
- [ ] User can customize options

### Phase 7: Documentation and Examples (Priority: Medium)
**Objective**: Complete documentation updates

**Implementation Tasks**:
1. Update TOOLS.md with new save options
2. Create example output directories showing structure
3. Add usage examples for different modes
4. Update CLI help text

**Success Criteria**:
- [ ] Documentation complete and clear
- [ ] Examples demonstrate all modes
- [ ] Help text accurate

## Configuration Options

### New CLI Arguments
```bash
# Save with defaults (batch mode)
./dev_cli.py examples/test.py -s

# Save in sequential mode with multiple files
./dev_cli.py examples/test.py -s --output-mode sequential

# Save in sequential mode with single file
./dev_cli.py examples/test.py -s --output-mode sequential --sequential-files single

# Batch mode (explicit)
./dev_cli.py examples/test.py -s --output-mode batch
```

### Output Format Examples

#### EXAMPLES.md (Batch Mode)
```markdown
# Model Checking Results

## Example: example1 (Theory: logos)

### Evaluation
- **Evaluation World**: w1 ⭐
- **Model Found**: Yes

### States
- 🟢 s1 (Possible)
- 🔴 s2 (Impossible)
- 🔵 w1 (World State, Evaluation)
- 🔵 w2 (World State)

### Relations
...

---

## Example: example2 (Theory: bimodal)
...
```

#### MODELS.json
```json
{
  "metadata": {
    "timestamp": "2024-03-05T14:30:22",
    "version": "1.0"
  },
  "models": [
    {
      "example": "example1",
      "theory": "logos",
      "has_model": true,
      "evaluation_world": "w1",
      "states": {
        "possible": ["s1", "w1", "w2"],
        "impossible": ["s2"],
        "worlds": ["w1", "w2"]
      },
      "relations": {...},
      "propositions": {...}
    }
  ]
}
```

## Breaking Changes
- **None**: Feature is additive, existing behavior unchanged without -s flag

## Risk Assessment
- **File I/O errors**: Handle gracefully with error messages
- **Large outputs**: Implement streaming for very large models
- **Unicode handling**: Ensure proper encoding throughout