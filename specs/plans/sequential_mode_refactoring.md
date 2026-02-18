# Sequential Mode Refactoring Plan - CLEAN BREAK

**Date**: 2025-01-15  
**Author**: Claude  
**Status**: Revised for Review  
**Impact**: Breaking changes for cleaner, simpler architecture  

## Core Principle: NO BACKWARDS COMPATIBILITY

Following `Code/maintenance/CODE_STANDARDS.md`:
> **NEVER** maintain backwards compatibility. This principle ensures:
> - Clean architecture without legacy cruft
> - Simplified interfaces without optional parameters  
> - Direct refactoring without compatibility layers

## Executive Summary

Complete removal of the confusing three-mode system. Replace with a single boolean flag that determines whether to prompt the user or not. Delete all legacy code, compatibility layers, and unnecessary abstractions.

## Problems to Eliminate

1. Three modes for two behaviors
2. Confusing "sequential" terminology  
3. MODE_INTERACTIVE constant that shouldn't exist
4. Complex strategy pattern for simple behavior
5. Redundant manager classes
6. Overly complex configuration

## NEW ARCHITECTURE (Final State)

### Core Design: One Simple Boolean

```python
# The ENTIRE configuration model
class OutputConfig:
    def __init__(self, 
                 formats: List[str] = None,
                 prompt_for_saves: bool = False,  # That's it!
                 save_output: bool = True):
        self.formats = formats or ['markdown', 'json']
        self.prompt_for_saves = prompt_for_saves
        self.save_output = save_output
```

### Simplified Manager

```python
class OutputManager:
    def __init__(self, config: OutputConfig, prompt_manager=None):
        self.config = config
        self.prompt_manager = prompt_manager
        self.output_dir = None
        self.accumulated_outputs = []  # For non-prompted mode
        self.saved_models = {}  # For prompted mode
        
    def save_example(self, example_name: str, model_data: Dict, output: str):
        """Save an example - either immediately or accumulate."""
        if self.config.prompt_for_saves and self.prompt_manager:
            # Ask user and save immediately if yes
            if self.prompt_manager.should_save(example_name):
                self._save_immediately(example_name, model_data, output)
                self.saved_models[example_name] = True
        else:
            # Accumulate for batch save at end
            self.accumulated_outputs.append((example_name, model_data, output))
    
    def finalize(self):
        """Save accumulated outputs (batch mode only)."""
        if not self.config.prompt_for_saves:
            for example_name, model_data, output in self.accumulated_outputs:
                self._save_immediately(example_name, model_data, output)
```

### Single Prompt Manager (Renamed)

```python
class SavePromptManager:
    """Manages user prompting for save decisions."""
    
    def __init__(self, input_provider=None):
        self.input_provider = input_provider or StandardInputProvider()
        
    def should_save(self, example_name: str) -> bool:
        """Ask user if they want to save this example."""
        response = self.input_provider.get_input(
            f"\nSave model for {example_name}? (y/n): "
        ).strip().lower()
        return response == 'y'
```

### Deleted Components

**COMPLETELY REMOVE:**
- `MODE_BATCH`, `MODE_SEQUENTIAL`, `MODE_INTERACTIVE` constants
- `IOutputStrategy` protocol and all strategy classes
- `SequentialOutputStrategy` class
- `BatchOutputStrategy` class  
- `PromptedOutputStrategy` class
- `sequential_files` configuration option
- All mode-checking code
- All strategy pattern infrastructure

### CLI Interface (Simplified)

```python
# In __main__.py
parser.add_argument(
    '--prompt', '-p',  # Changed from --sequential
    action='store_true',
    help='Prompt before saving each model'
)
```

### Settings (Simplified)

```python
# In theory semantic files
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "prompt_for_saves": False,  # Renamed from 'sequential'
}
```

## File Changes

### Files to DELETE

```
src/model_checker/output/strategies/        # DELETE entire directory
├── __init__.py                            # DELETE
├── base.py                                 # DELETE  
├── batch.py                                # DELETE
├── sequential.py                           # DELETE
└── prompted.py                             # DELETE
```

### Files to REWRITE (Not Refactor)

#### 1. `output/config.py` - COMPLETE REWRITE

```python
"""Simple output configuration."""

from typing import List, Optional

class OutputConfig:
    """Output configuration with two behaviors: batch or prompted."""
    
    def __init__(self,
                 formats: List[str] = None,
                 prompt_for_saves: bool = False,
                 save_output: bool = True):
        self.formats = formats or ['markdown', 'json']
        self.prompt_for_saves = prompt_for_saves
        self.save_output = save_output

def create_output_config(args, settings=None) -> OutputConfig:
    """Create config from CLI args."""
    # Determine formats
    formats = []
    if hasattr(args, 'save') and args.save:
        formats = args.save if args.save else ['markdown', 'json']
    
    # Check prompt flag
    prompt = False
    if settings and settings.get('prompt_for_saves', False):
        prompt = True
    if hasattr(args, 'prompt') and args.prompt:
        prompt = True
        
    return OutputConfig(
        formats=formats,
        prompt_for_saves=prompt,
        save_output=bool(formats)
    )
```

#### 2. `output/manager.py` - HEAVY SIMPLIFICATION

Remove:
- All strategy initialization code
- All mode checking
- Complex conditional logic
- _initialize_components method
- Multiple save tracking dictionaries

Add:
- Simple accumulation list
- Direct save logic
- Clear prompted vs batch behavior

#### 3. `output/constants.py` - MASSIVE REDUCTION

```python
"""Output constants."""

# Output formats (keep these)
FORMAT_MARKDOWN = 'markdown'
FORMAT_JSON = 'json'
FORMAT_NOTEBOOK = 'notebook'

DEFAULT_FORMATS = [FORMAT_MARKDOWN, FORMAT_JSON]

EXTENSIONS = {
    FORMAT_MARKDOWN: 'md',
    FORMAT_JSON: 'json',
    FORMAT_NOTEBOOK: 'ipynb'
}

# DELETE all mode constants
# DELETE all strategy constants
```

#### 4. `output/prompt_manager.py` - RENAME from sequential.py

Simplified to just handle prompting logic, no mode management.

### Test Updates

**DELETE tests for:**
- Strategy pattern behavior
- Mode interactions
- Sequential file options
- Compatibility layers

**ADD tests for:**
- Simple prompt vs batch behavior
- Direct save functionality
- Clear user interaction flow

## Implementation Steps

### Step 1: Delete Strategy Infrastructure
```bash
rm -rf src/model_checker/output/strategies/
```

### Step 2: Rewrite Core Files
1. New `config.py` with simple boolean
2. New `manager.py` without strategies
3. Clean `constants.py`
4. Rename `sequential.py` to `prompt_manager.py`

### Step 3: Update Integration Points
1. Update `__main__.py` for new CLI flag
2. Update `builder/module.py` for simple integration
3. Update all theory files for new setting name

### Step 4: Fix All Tests
1. Delete strategy tests
2. Update remaining tests for new simple behavior
3. Add new focused tests

## Benefits of This Approach

### Massive Simplification
- **~500 lines deleted** (all strategy code)
- **One boolean** instead of three modes
- **Direct code flow** without abstraction layers
- **No compatibility cruft**

### Better User Experience  
- Clear `--prompt` flag
- Simple mental model
- Predictable behavior
- No mode confusion

### Maintainability
- Less code to maintain
- Clear, direct logic
- Easy to test
- Simple to modify

## Metrics

### Before
- 3 mode constants
- 5 strategy classes  
- ~800 lines of strategy code
- Complex configuration logic
- Multiple abstraction layers

### After
- 0 mode constants
- 0 strategy classes
- 1 boolean flag
- ~200 lines total
- Direct, simple logic

## No Migration Path

**This is a clean break.** Users will need to:
1. Change `--sequential` to `--prompt` in scripts
2. Change `sequential: true` to `prompt_for_saves: true` in settings
3. That's it!

## Risk Assessment

**High Impact, Low Risk:**
- Tests will catch integration issues
- Simpler code has fewer bugs
- Clear behavior is easier to verify
- No complex interactions to break

## Success Criteria

1. ✅ All strategy code deleted
2. ✅ Single boolean configuration
3. ✅ Direct save logic without abstractions
4. ✅ Clear, simple code flow
5. ✅ No backwards compatibility code

## Code Standards Compliance

This plan follows `Code/maintenance/CODE_STANDARDS.md`:

✅ **No Backwards Compatibility** - Complete clean break  
✅ **No Decorators** - None used  
✅ **Fail-Fast Philosophy** - Clear, direct errors  
✅ **Single Responsibility** - Each component does one thing  
✅ **Test-Driven Development** - Write tests for new behavior first  

## Conclusion

This refactoring eliminates unnecessary complexity by:
1. **Deleting** the entire strategy pattern
2. **Replacing** three modes with one boolean
3. **Simplifying** to direct, obvious code
4. **Removing** all compatibility layers

The result is clean, maintainable code that does exactly what it needs to with no extra abstractions.

---

**Next Step**: Approve this aggressive simplification approach, then implement the clean break.