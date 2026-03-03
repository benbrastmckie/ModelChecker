# Research Report: Task #25 - Fix CLI Interactive Mode Tests

**Task**: 25 - Fix CLI interactive mode tests
**Started**: 2026-03-02T12:00:00Z
**Completed**: 2026-03-02T12:30:00Z
**Effort**: Small-Medium (1-2 hours estimated implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis, git history, test execution
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The tests are **aspirational** - they test a partially implemented feature that was started but never completed
- An `--interactive/-I` flag was previously planned (commit `276f6ec1`) but the CLI argument was never added to argparse
- The `model_checker.output.interactive` module **did exist** (commit `819eae2d`) but was **renamed to `sequential_manager.py`** (commit `27e84720`)
- **Recommended approach**: Delete these tests, as the interactive mode functionality was intentionally refactored into sequential mode (`-q/--sequential` flag) which already works

## Context & Scope

### Problem Statement

21 tests are failing across two test files:
- `code/tests/integration/test_cli_interactive.py` (15+ tests)
- `code/tests/integration/test_build_module_interactive.py` (6 tests)

The tests expect:
1. An `--interactive/-I` CLI flag in `ParseFileFlags` that doesn't exist
2. A `model_checker.output.interactive` module that doesn't exist
3. An `InteractiveManager` class with methods like `prompt_choice`, `prompt_save_model`
4. `BuildModule.interactive_manager` attribute and `BuildModule.output_manager.interactive_manager`

### Research Scope

1. Determine if these are planned features or orphaned tests
2. Trace git history to understand when/why divergence occurred
3. Recommend fix approach (implement vs delete)

## Findings

### Git History Analysis

The feature was **partially implemented** across multiple commits in August 2025:

| Commit | Date | Action |
|--------|------|--------|
| `819eae2d` | 2025-08-04 | Created `output/interactive.py` with `InteractiveSaveManager` class |
| `cf894249` | 2025-08-04 | Added BuildModule integration with interactive save |
| `276f6ec1` | 2025-08-04 | Added CLI tests expecting `--interactive/-I` flag |
| `27e84720` | 2025-09-15 | **Refactored**: Renamed `interactive.py` to `sequential.py`, changed approach |

The September 15 refactor (`27e84720`) with message "created refactor for interactive mode" **intentionally** changed the approach:
- Renamed `output/interactive.py` to `output/sequential.py`
- Renamed strategy `interactive.py` to `prompted.py`
- The tests were **not updated** to reflect this change

### Current Implementation Analysis

**What Exists (Sequential Mode)**:

1. `--sequential/-q` flag in `__main__.py`:
   ```python
   output_group.add_argument(
       '--sequential',
       '-q',
       action='store_true',
       help='Prompt to save each model individually (interactive mode)'
   )
   ```

2. `SequentialSaveManager` class in `output/sequential_manager.py`:
   - `should_save(example_name)` - prompts to save model
   - `should_find_more()` - prompts for more models
   - `get_next_model_number(example_name)` - tracks model numbers
   - `prompt_directory_change(output_dir)` - prompts for cd

3. `OutputConfig` with `sequential: bool` parameter

4. `prompt_yes_no` and `prompt_choice` functions in `output/prompts.py` (exported in `__init__.py`)

**What's Missing (Tests Expect)**:

1. `--interactive/-I` flag - **Never added** to argparse
2. `model_checker.output.interactive` module - **Renamed** to `sequential_manager`
3. `InteractiveManager` class with:
   - `set_mode(mode)` method
   - `prompt_save_model(example_name)` method
   - `interactive_manager` property
4. `flags.interactive` attribute on parsed args
5. `_short_to_long['I'] == 'interactive'` mapping

### Test Content Analysis

**test_cli_interactive.py**:
- Tests parsing of `-I/--interactive` flag
- Tests `flags.interactive` attribute
- Tests `parser._short_to_long['I'] == 'interactive'` mapping
- Tests passing interactive flag to BuildModule
- Tests help text shows `--interactive` and `-I`
- Tests flag combinations with `--output-mode` (which also doesn't exist)

**test_build_module_interactive.py**:
- Patches `model_checker.output.interactive.prompt_choice` - module doesn't exist
- Expects `module.output_manager.interactive_manager` - attribute doesn't exist
- Expects `module.output_manager.mode` - attribute doesn't exist
- Expects `module.interactive_manager` - attribute doesn't exist
- Tests workflow with `prompt_save_model` method

### Protocol Analysis

The `IInteractiveManager` protocol in `builder/protocols.py` shows the **intended** interface:
```python
class IInteractiveManager(Protocol):
    def is_interactive(self) -> bool: ...
    def set_mode(self, mode: str) -> None: ...
    def prompt_save_mode(self) -> None: ...
```

This was part of the original design but implementation diverged.

## Recommendations

### Recommended Approach: Option B - Delete the Tests

**Rationale**:
1. The feature was **intentionally refactored** from "interactive" to "sequential" mode
2. The existing `--sequential/-q` flag already provides the functionality these tests describe
3. The `SequentialSaveManager` class already implements the prompting behavior
4. Implementing a separate `--interactive` mode would create redundant, confusing functionality

### Implementation Steps

1. **Delete test files**:
   - `code/tests/integration/test_cli_interactive.py`
   - `code/tests/integration/test_build_module_interactive.py`

2. **Clean up stale protocol** (optional):
   - Review `IInteractiveManager` protocol in `builder/protocols.py`
   - Either update to match `SequentialSaveManager` or remove if unused

3. **Verify sequential mode has test coverage**:
   - Check `code/src/model_checker/output/tests/unit/test_sequential_manager.py`
   - Check `code/src/model_checker/output/tests/integration/test_prompt_manager.py`

### Alternative Approach: Option A - Implement (Not Recommended)

If stakeholders prefer to keep the `-I` flag as an alias:

1. Add `--interactive/-I` as alias for `--sequential`:
   ```python
   output_group.add_argument(
       '--interactive', '-I',
       dest='sequential',  # Maps to same destination
       action='store_true',
       help='Alias for --sequential'
   )
   ```

2. Update `_short_to_long` mapping in `parse()` method

3. Still need to update tests to not expect `model_checker.output.interactive` module

This approach adds complexity for questionable value.

## Decisions

1. **Decision**: Recommend deleting tests rather than implementing feature
   - **Rationale**: Sequential mode already provides this functionality; tests are orphaned from a refactor

2. **Decision**: Keep `IInteractiveManager` protocol for potential future use
   - **Rationale**: Protocols are cheap, may be useful for dependency injection testing

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Deleting tests removes planned feature | Low | Medium | Git history preserves; can restore if needed |
| Sequential mode lacks coverage | Low | Medium | Verify existing tests cover same scenarios |
| Protocol divergence causes issues | Very Low | Low | Keep protocol aligned with current implementation |

## Appendix

### Files Examined

- `/home/benjamin/Projects/ModelChecker/code/tests/integration/test_cli_interactive.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/integration/test_build_module_interactive.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/__main__.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/output/__init__.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/output/sequential_manager.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/output/config.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/output/prompts.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/module.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/protocols.py`

### Git Commits Analyzed

- `276f6ec1` - "Phase 5: Add CLI flags for interactive mode"
- `cf894249` - "Phase 4: Complete BuildModule integration with interactive save"
- `819eae2d` - "Phase 2: InteractiveSaveManager implementation"
- `27e84720` - "created refactor for interactive mode"

### Test Error Summary

```
test_cli_interactive.py::test_interactive_flag_parsing - SystemExit: 2
  unrecognized arguments: -I

test_build_module_interactive.py::test_interactive_mode_initialization - ModuleNotFoundError
  No module named 'model_checker.output.interactive'
```
