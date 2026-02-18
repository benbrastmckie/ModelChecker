# Interactive Setting Implementation Plan

## Summary
Add a general setting `interactive` (default: False) to enable interactive mode by default, with the `--interactive` CLI flag overriding all settings to maintain backward compatibility.

## Completed Implementation

### 1. Added 'interactive' Setting to All Theory Classes ✓
- Updated `DEFAULT_GENERAL_SETTINGS` in:
  - `theory_lib/exclusion/semantic.py` - Added `"interactive": False`
  - `theory_lib/imposition/semantic.py` - Added `"interactive": False`
  - `theory_lib/bimodal/semantic.py` - Added `"interactive": False`
  - `theory_lib/logos/examples.py` - Added `"interactive": False` to general_settings

### 2. Updated OutputConfig Logic ✓
- Modified `create_output_config_from_cli_args()` in `output/config.py`:
  - Added optional `general_settings` parameter
  - Implemented priority order:
    1. CLI flag `--interactive` (highest priority)
    2. CLI flag `--output-mode` (overrides settings but not --interactive)
    3. Setting `interactive: True` in general_settings
    4. Default to batch mode

### 3. Updated BuildModule Initialization ✓
- Modified `_initialize_output_management()` in `builder/module.py`:
  - Pass `self.general_settings` to `create_output_config_from_cli_args()`
  - Only create InteractiveSaveManager when mode is 'interactive'
  - Removed redundant mode setting logic

### 4. Added Comprehensive Tests ✓
- Created `output/tests/unit/test_config_interactive_setting.py`:
  - 11 test cases covering all priority scenarios
  - Tests for setting true/false behavior
  - Tests for CLI flag override behavior
  - Tests for complete priority order
  - All tests passing

### 5. Updated Documentation ✓
- `output/README.md`:
  - Added interactive setting information
  - Documented priority order for interactive mode
- `settings/README.md`:
  - Added 'interactive' to general settings list
  - Updated settings categories description
- `Docs/architecture/OUTPUT.md`:
  - Added priority order to Interactive Strategy section
  - Clarified activation methods

### 6. Test Results ✓
- All 270 output tests passing
- New interactive setting tests: 11/11 passing
- No regression in existing functionality

## Priority Order

The implementation follows this priority order for interactive mode:
1. **CLI flag `--interactive`** - Always wins (highest priority)
2. **CLI flag `--output-mode`** - Overrides settings but not --interactive
3. **Setting `interactive: True`** - Enables interactive by default
4. **Default** - Batch mode if nothing specified

## Usage Examples

### Using Settings to Enable Interactive Mode
```python
# In examples.py
general_settings = {
    "interactive": True,  # Enable interactive mode by default
    "save_output": False,
    # ... other settings
}
```

### CLI Override Behavior
```bash
# Setting has interactive: True, but CLI overrides to sequential
python -m model_checker examples.py --save --output-mode sequential

# Setting has interactive: False, but CLI forces interactive
python -m model_checker examples.py --save --interactive

# Setting has interactive: True, runs in interactive mode
python -m model_checker examples.py --save
```

## Benefits

1. **Backward Compatibility**: CLI flags maintain their override behavior
2. **Flexibility**: Users can set default behavior in code
3. **Clear Priority**: Documented and tested priority order
4. **Consistent Design**: Follows existing settings patterns

## Testing Coverage

- Unit tests: 11 new tests for interactive setting behavior
- Integration: Existing 259 tests continue to pass
- Total: 270 tests, 100% passing

## Implementation Notes

- The setting is added to all theory classes for consistency
- The logos theory uses `general_settings` dict instead of class constant
- Interactive manager is only created when mode is 'interactive'
- Documentation updated in three key locations for discoverability