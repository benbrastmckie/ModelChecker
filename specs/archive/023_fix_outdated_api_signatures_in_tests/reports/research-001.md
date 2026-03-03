# Research Report: Task #23

**Task**: 23 - fix_outdated_api_signatures_in_tests
**Started**: 2026-03-02T00:00:00Z
**Completed**: 2026-03-02T00:30:00Z
**Effort**: Medium (22+ test failures across 8 test files)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis of src/ and tests/ directories
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- 5 distinct API signature mismatches identified across 8 test files
- `Syntax.__init__()` requires `(infix_premises, infix_conclusions, operator_collection)` but tests call it with no args or wrong args
- `ModelDefaults.__init__()` requires `(model_constraints, settings)` but tests pass only a dict
- `OutputManager.__init__()` requires `(config: OutputConfig, prompt_manager=None)` but tests pass `save_output=True`
- `STANDARD_SETTINGS` is not exported from `tests/fixtures/example_data.py` - needs to be added
- `builder/example.py` path reference uses incorrect relative path in test

## Context & Scope

This research investigates test failures caused by API signature changes in core classes. The tests were written against older APIs but the source implementations have evolved. The goal is to identify all affected locations and determine the correct current signatures.

## Findings

### 1. Syntax.__init__() Signature Mismatch

**Current Signature** (from `code/src/model_checker/syntactic/syntax.py:45-50`):
```python
def __init__(
    self,
    infix_premises: List[FormulaString],
    infix_conclusions: List[FormulaString],
    operator_collection: OperatorCollection,
) -> None:
```

**Affected Test Files**:

| File | Line(s) | Issue |
|------|---------|-------|
| `tests/integration/test_performance.py` | 284, 356 | Calls `Syntax()` with no args |
| `tests/integration/test_error_handling.py` | 90, 112, 259 | Calls `Syntax()` with no args |
| `tests/integration/test_model_building_sync.py` | 52, 60 | Calls `Syntax([], [], {})` - passes dict instead of OperatorCollection |

**Pattern for Fix**:
Tests that create Syntax for parsing should use:
```python
from model_checker.syntactic import Syntax
from model_checker.syntactic.collection import OperatorCollection

syntax = Syntax(
    infix_premises=['formula1'],
    infix_conclusions=['formula2'],
    operator_collection=OperatorCollection()  # or with operators
)
```

### 2. ModelDefaults.__init__() Signature Mismatch

**Current Signature** (from `code/src/model_checker/models/structure.py:47`):
```python
def __init__(self, model_constraints: 'ModelConstraints', settings: Dict[str, Any]) -> None:
```

This requires TWO arguments:
1. `model_constraints`: A `ModelConstraints` instance (not just settings)
2. `settings`: A dictionary of settings

**Affected Test Files**:

| File | Line(s) | Issue |
|------|---------|-------|
| `tests/utils/base.py` | 150 | `return ModelDefaults(settings)` - missing model_constraints |
| `tests/integration/test_performance.py` | 102, 124, 158, 247, 336 | Passes only settings dict |
| `tests/integration/test_error_handling.py` | 134, 148, 208 | Passes only settings dict |
| `tests/integration/test_timeout_resources.py` | 32, 86, 106, 128, 141, 195, 225, 252, 280 | Passes only settings dict |

**Pattern for Fix**:
Tests need to create the full model stack:
```python
from model_checker.syntactic import Syntax
from model_checker.syntactic.collection import OperatorCollection
from model_checker.models.constraints import ModelConstraints
from model_checker.models import ModelDefaults
from model_checker.theory_lib import logos

# Get theory components
theory = logos.get_theory()
semantics_class = theory['semantics']
proposition_class = theory['proposition']
operators = theory['operators']

# Create full model stack
op_collection = OperatorCollection(operators)
syntax = Syntax(premises, conclusions, op_collection)
semantics = semantics_class(N=settings.get('N', 3))
model_constraints = ModelConstraints(settings, syntax, semantics, proposition_class)
model = ModelDefaults(model_constraints, settings)
```

**Alternative**: The tests may need a factory function or test helper that encapsulates this complexity.

### 3. OutputManager.__init__() Signature Mismatch

**Current Signature** (from `code/src/model_checker/output/manager.py:31-46`):
```python
def __init__(self, config: OutputConfig, prompt_manager=None):
    """Initialize output manager.

    Args:
        config: Output configuration
        prompt_manager: Optional SequentialSaveManager for user prompting

    Raises:
        ValueError: If config is not provided
    """
```

**Affected Test Files**:

| File | Line | Issue |
|------|------|-------|
| `tests/e2e/test_simple_output_verify.py` | 42 | `OutputManager(save_output=True)` |
| `tests/integration/test_batch_output_integration.py` | 65, 137, 180 | `OutputManager(save_output=True, output_dir=...)` |

**Pattern for Fix**:
```python
from model_checker.output.config import OutputConfig
from model_checker.output.manager import OutputManager

config = OutputConfig(
    formats=['markdown', 'json'],
    sequential=False,
    save_output=True
)
output_manager = OutputManager(config)
```

### 4. STANDARD_SETTINGS Not Exported

**Location**: `tests/fixtures/example_data.py`

**Issue**: The test at `tests/integration/test_error_handling.py:221` imports `STANDARD_SETTINGS`:
```python
from tests.fixtures.example_data import STANDARD_SETTINGS
```

But `STANDARD_SETTINGS` is not defined in `example_data.py`. The file has `TEST_SETTINGS` dictionary with various configurations.

**Pattern for Fix**:
Add to `tests/fixtures/example_data.py`:
```python
# Standard settings for common test cases
STANDARD_SETTINGS = {
    'N': 3,
    'max_time': 10,
    'print_constraints': False
}
```

Or alias to existing:
```python
STANDARD_SETTINGS = TEST_SETTINGS['standard']
```

### 5. builder/example.py Path Reference Issue

**Location**: `tests/integration/test_model_building_sync.py:106-127`

**Issue**: The test uses relative path that doesn't resolve correctly:
```python
build_example_path = os.path.join(
    os.path.dirname(__file__),
    '../src/model_checker/builder/example.py'  # Line 108
)
```

From `tests/integration/`, the path `../src/model_checker/builder/example.py` tries to reach:
`tests/src/model_checker/builder/example.py` (does not exist)

**Actual location**: `code/src/model_checker/builder/example.py`

**Pattern for Fix**:
```python
# Option 1: Fix relative path
build_example_path = os.path.join(
    os.path.dirname(__file__),
    '../../src/model_checker/builder/example.py'
)

# Option 2: Use absolute path from project root
import model_checker.builder.example as example_module
build_example_path = example_module.__file__
```

## Recommendations

### Implementation Approach

1. **Create test helper functions** in `tests/utils/base.py` or a new `tests/utils/model_factory.py`:
   - `create_test_model(settings, theory='logos')` - handles full model stack creation
   - `create_test_syntax(premises, conclusions)` - handles Syntax creation with default operators

2. **Fix OutputManager tests** by using OutputConfig:
   - Update 4 test files to use proper OutputConfig initialization

3. **Add STANDARD_SETTINGS** to fixtures:
   - Simple one-line fix in example_data.py

4. **Fix path reference** in test_model_building_sync.py:
   - Use module introspection instead of relative paths

### Estimated Effort per Issue

| Issue | Files | Effort |
|-------|-------|--------|
| Syntax.__init__() | 3 files, ~10 calls | Medium |
| ModelDefaults.__init__() | 4 files, ~18 calls | High (needs helper) |
| OutputManager.__init__() | 2 files, 4 calls | Low |
| STANDARD_SETTINGS | 1 file, 1 add | Low |
| builder/example.py path | 1 file, 1 fix | Low |

### Suggested Order of Fixes

1. **STANDARD_SETTINGS** (quick win, unblocks test_error_handling.py)
2. **OutputManager** (straightforward config change)
3. **builder/example.py path** (simple path fix)
4. **Syntax.__init__()** (requires understanding usage patterns)
5. **ModelDefaults.__init__()** (most complex, may need helper function)

## Decisions

- Tests should be updated to match current API rather than reverting API changes
- A test helper function should be created to simplify model creation in tests
- The base test classes in `tests/utils/base.py` need updating

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Model creation complexity | Tests become verbose | Create helper functions |
| Breaking other tests | High | Run full test suite after each fix |
| Missing edge cases | Medium | Review each test's intent before fixing |

## Appendix

### Files Requiring Changes

1. `tests/fixtures/example_data.py` - Add STANDARD_SETTINGS
2. `tests/utils/base.py` - Fix BaseModelTest.create_model()
3. `tests/integration/test_performance.py` - Multiple Syntax and ModelDefaults fixes
4. `tests/integration/test_error_handling.py` - Multiple Syntax and ModelDefaults fixes
5. `tests/integration/test_timeout_resources.py` - Multiple ModelDefaults fixes
6. `tests/integration/test_model_building_sync.py` - Fix Syntax calls and path reference
7. `tests/e2e/test_simple_output_verify.py` - Fix OutputManager call
8. `tests/integration/test_batch_output_integration.py` - Fix OutputManager calls

### Current API Summary

| Class | Current Signature | Required Imports |
|-------|-------------------|------------------|
| `Syntax` | `(infix_premises, infix_conclusions, operator_collection)` | `from model_checker.syntactic import Syntax` |
| `ModelDefaults` | `(model_constraints, settings)` | `from model_checker.models import ModelDefaults` |
| `OutputManager` | `(config: OutputConfig, prompt_manager=None)` | `from model_checker.output.manager import OutputManager` |
| `OutputConfig` | `(formats, sequential, save_output)` | `from model_checker.output.config import OutputConfig` |
| `OperatorCollection` | `()` or `(operators_dict)` | `from model_checker.syntactic.collection import OperatorCollection` |
