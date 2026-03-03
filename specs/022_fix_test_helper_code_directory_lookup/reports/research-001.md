# Research Report: Task #22

**Task**: 22 - Fix test helper run_cli_command code directory lookup
**Started**: 2026-03-02T12:00:00Z
**Completed**: 2026-03-02T12:15:00Z
**Effort**: Small (< 30 min implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis, test execution
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Two files contain hardcoded `'Code'` (capital C) directory lookups that need to be changed to `'code'` (lowercase)
- The `pyproject.toml` marker approach is recommended over a simple case change for robustness
- This affects 5+ tests in `test_error_handling.py` and 3 skipped tests in `test_full_pipeline.py`
- Fix is straightforward: change lookup condition from directory name to `pyproject.toml` presence

## Context & Scope

Task 16 renamed the `Code/` directory to `code/` to standardize on lowercase directory names. The `run_cli_command()` function in `code/tests/utils/helpers.py` and `setUp()` in `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` both walk up the directory tree looking for a directory named `'Code'` (capital C). Since this directory no longer exists, the functions never find the project root and fail to set `PYTHONPATH` correctly, causing subprocess calls to fail with `No module named model_checker`.

## Findings

### Files Requiring Changes

1. **`code/tests/utils/helpers.py`** (line 29):
   ```python
   while current_dir.name != 'Code' and current_dir.parent != current_dir:
       current_dir = current_dir.parent
   ```

2. **`code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`** (line 22):
   ```python
   while current.name != 'Code' and current.parent != current:
       current = current.parent
   ```

### Test Impact

**Confirmed failing tests in `test_error_handling.py`**:
- `TestCLIErrorHandling::test_invalid_theory_name` - FAILED
- `TestCLIErrorHandling::test_malformed_module_syntax` - FAILED
- `TestCLIErrorHandling::test_invalid_cli_flags[--invalid-flag]` - FAILED
- `TestCLIErrorHandling::test_invalid_cli_flags[-X]` - FAILED
- `TestCLIErrorHandling::test_invalid_cli_flags[--nonexistent]` - FAILED

**Skipped tests in `test_full_pipeline.py`** (due to same issue):
- `TestFullPipeline::test_theory_library_execution` - SKIPPED
- `TestFullPipeline::test_iteration_workflow` - SKIPPED
- `TestFullPipeline::test_error_handling` - SKIPPED

The error output confirms the diagnosis:
```
No module named model_checker
```

### Available Fix Approaches

#### Approach 1: Simple Case Change (Not Recommended)
Change `'Code'` to `'code'`:
```python
while current_dir.name != 'code' and current_dir.parent != current_dir:
```

**Pros**: Minimal change
**Cons**: Fragile - breaks if directory is renamed again; not self-documenting

#### Approach 2: pyproject.toml Marker (Recommended)
Look for `pyproject.toml` as the project root marker:
```python
while not (current_dir / 'pyproject.toml').exists() and current_dir.parent != current_dir:
    current_dir = current_dir.parent
```

**Pros**:
- Robust against future directory renames
- Self-documenting (pyproject.toml is the standard Python project root marker)
- Works regardless of parent directory name

**Cons**: Slightly more I/O (file existence check)

#### Approach 3: dev_cli.py Marker (Alternative)
Look for `dev_cli.py` which is specific to this project:
```python
while not (current_dir / 'dev_cli.py').exists() and current_dir.parent != current_dir:
```

**Pros**: Even more specific to this project
**Cons**: Less standard; `dev_cli.py` is not a universal marker

### Recommendation

**Use Approach 2 (pyproject.toml marker)** for both files. This is the most robust and Pythonic approach:

1. `pyproject.toml` is the standard Python project configuration file
2. It exists at `code/pyproject.toml` and defines the package
3. This pattern is used by many Python tools (pytest, setuptools, etc.)
4. It won't break if the directory name changes again

### Implementation Notes

Both files need identical logic changes:

**In `code/tests/utils/helpers.py`** (run_cli_command function, lines 27-30):
```python
# Find the code directory (project root) by looking for pyproject.toml
current_dir = Path(__file__).parent
while not (current_dir / 'pyproject.toml').exists() and current_dir.parent != current_dir:
    current_dir = current_dir.parent
```

**In `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`** (setUp method, lines 20-23):
```python
# Navigate to the code directory by looking for pyproject.toml
current = Path(__file__)
while not (current / 'pyproject.toml').exists() and current.parent != current:
    current = current.parent
```

### Additional Observations

1. The conftest.py at `code/conftest.py` does not set up PYTHONPATH centrally - each test file handles its own path setup
2. The pytest configuration in `pyproject.toml` includes `pythonpath = "src"` but this only applies when running pytest from the code directory
3. There is only one `pyproject.toml` in the project at `code/pyproject.toml`, so there's no ambiguity

## Decisions

1. Use `pyproject.toml` marker instead of directory name matching
2. Apply the same fix pattern to both affected files
3. Update comment to explain the marker-based approach

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| pyproject.toml moved in future | Unlikely; this is a standard Python project file |
| Multiple pyproject.toml files | Currently only one exists; pattern finds nearest ancestor |
| I/O overhead | Negligible; only checked during test setup |

## Appendix

### Files Examined
- `/home/benjamin/Projects/ModelChecker/code/tests/utils/helpers.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`
- `/home/benjamin/Projects/ModelChecker/code/pyproject.toml`
- `/home/benjamin/Projects/ModelChecker/code/conftest.py`

### Search Queries
- Grep for `'Code'` case-sensitive references
- Grep for `current_dir.name` patterns
- Glob for `pyproject.toml` files

### Test Commands Used
```bash
PYTHONPATH=code/src pytest code/tests/integration/test_error_handling.py -v
PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/e2e/test_full_pipeline.py -v
```
