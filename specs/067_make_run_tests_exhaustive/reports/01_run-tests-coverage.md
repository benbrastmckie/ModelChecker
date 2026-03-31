# Research Report: Make run_tests.py Exhaustive

## Task 67 | Session: sess_1774916194_468554

## Summary

`run_tests.py` has three gaps in test discovery, leaving 165 tests (across 3 test suites) unreachable from the unified test runner. Each gap has a distinct root cause and a straightforward fix.

## Current Test Discovery Mechanism

The `TestRunner` class (line 616) initializes three discovery methods:

1. **`_discover_theories()`** (line 651) -- Scans `theory_lib/` for directories containing both `tests/` and `examples.py`. Returns theory names like `exclusion`, `logos`.
2. **`_discover_components()`** (line 669) -- Scans `src/model_checker/` for top-level directories with `tests/` subdirs (excluding `theory_lib`). Returns names like `builder`, `iterate`, `output`, etc.
3. **`_discover_subtheories()`** (line 691) -- Returns a hardcoded dict mapping `logos` to its five subtheories.

Tests are then run via three runner classes:
- `ExampleTestRunner` -- runs `examples.py`-based integration tests per theory/subtheory
- `UnitTestRunner` -- runs pytest on `tests/` directories per theory/subtheory
- `PackageTestRunner` -- runs pytest on `tests/` directories per component

## Gap 1: Bimodal Theory Excluded (98 tests)

### Location
`_discover_theories()` at line 662:
```python
item.name != 'bimodal' and  # Exclude bimodal theory (not finished)
```

### Root Cause
Hardcoded exclusion filter. The bimodal theory directory has both `tests/` and `examples.py`, so it would be discovered if the filter were removed.

### Current State of Bimodal Tests
- Path: `src/model_checker/theory_lib/bimodal/tests/`
- Test structure: `e2e/`, `integration/`, `unit/` subdirectories
- pytest collect: **98 tests collected** successfully
- All tests appear to be properly structured

### Fix Required
Remove or conditionally relax the `item.name != 'bimodal'` exclusion. Options:
1. **Remove entirely** -- if bimodal tests are now passing
2. **Make configurable** -- add a `--include-wip` flag to optionally include work-in-progress theories
3. **Move to config** -- use a list of excluded theories that can be emptied

### Recommendation
First verify bimodal tests pass: `cd code && python -m pytest src/model_checker/theory_lib/bimodal/tests/ -v`. If they pass, remove the exclusion. If some fail, consider the `--include-wip` approach.

## Gap 2: first_order Subtheory Missing (53 tests)

### Location
`_discover_subtheories()` at line 691-696:
```python
def _discover_subtheories(self) -> Dict[str, List[str]]:
    return {
        'logos': ['modal', 'counterfactual', 'extensional', 'constitutive', 'relevance']
    }
```

### Root Cause
The subtheory list is hardcoded and `first_order` is simply not included. The `first_order` subtheory exists at `theory_lib/logos/subtheories/first_order/` with:
- `examples.py`
- `operators.py`
- `tests/` directory containing `test_first_order_examples.py` and `unit/` tests

### Impact
- **Example tests**: `_run_logos_example_tests()` (line 321) defaults to iterating only the five listed subtheories, so `first_order` example tests are never run.
- **Unit tests**: `_run_logos_unit_tests()` (line 486) runs pytest on `logos/tests/` only, not on subtheory test directories, so `first_order` unit tests are missed regardless of discovery.
- **Subtheory filter patterns** (line 500-505): No pattern exists for `first_order` either.

### Test Counts
- Path: `src/model_checker/theory_lib/logos/subtheories/first_order/tests/`
- pytest collect: **53 tests collected** (12 example tests + 41 unit tests)

### Fix Required
Two changes needed:

1. Add `'first_order'` to the subtheories list in `_discover_subtheories()`:
   ```python
   'logos': ['modal', 'counterfactual', 'extensional', 'constitutive', 'relevance', 'first_order']
   ```

2. Add a filter pattern for first_order in `_run_logos_unit_tests()` (line 500-505):
   ```python
   'first_order': '(first_order or FO_)',
   ```

### Better Approach: Dynamic Discovery
Replace the hardcoded list with filesystem scanning:
```python
def _discover_subtheories(self) -> Dict[str, List[str]]:
    subtheories = {}
    logos_subtheories_dir = self.code_dir / "src" / "model_checker" / "theory_lib" / "logos" / "subtheories"
    if logos_subtheories_dir.exists():
        subs = []
        for item in logos_subtheories_dir.iterdir():
            if (item.is_dir() and
                not item.name.startswith('__') and
                (item / "tests").exists()):
                subs.append(item.name)
        if subs:
            subtheories['logos'] = sorted(subs)
    return subtheories
```

Note: `spatial` subtheory exists in `logos/subtheories/` but has no `tests/` directory, so it would correctly be excluded by this check.

## Gap 3: output/notebook/tests/ Not Reachable (14 tests)

### Location
`_discover_components()` at line 669 and `PackageTestRunner.run_component_tests()` at line 572.

### Root Cause
Component discovery only scans direct children of `src/model_checker/`:
```python
for item in src_dir.iterdir():
    if (item.is_dir() and
        not item.name.startswith('__') and
        item.name != 'theory_lib' and
        (item / "tests").exists()):
        components.append(item.name)
```

This discovers `output` (which has `output/tests/` with 234 tests), but not `output/notebook` (which has `output/notebook/tests/` with 14 separate tests).

When `PackageTestRunner.run_component_tests('output', ...)` runs, it points pytest at `output/tests/`, which does NOT include `output/notebook/tests/` -- those are in a separate directory tree.

### Test Counts
- `output/tests/`: 234 tests (already discovered)
- `output/notebook/tests/`: **14 tests** (not discovered)

### Fix Required
Options:

1. **Nested component discovery** -- Extend `_discover_components()` to scan one level deeper for sub-components with their own `tests/` directories. Register them as `output.notebook` or similar.

2. **Run pytest on parent** -- Change `run_component_tests()` to run pytest on `output/` (the whole package) instead of just `output/tests/`, letting pytest discover all nested test directories via `conftest.py` chain. However, this might pick up non-test Python files.

3. **Explicit sub-component registration** -- Add `notebook` as a nested component under `output`:
   ```python
   # In _discover_components or run_component_tests
   for item in src_dir.iterdir():
       if item.is_dir() and not item.name.startswith('__') and item.name != 'theory_lib':
           if (item / "tests").exists():
               components.append(item.name)
           # Also check for sub-components with tests
           for sub_item in item.iterdir():
               if (sub_item.is_dir() and
                   not sub_item.name.startswith('__') and
                   (sub_item / "tests").exists()):
                   components.append(f"{item.name}.{sub_item.name}")
   ```

### Recommendation
Option 3 is cleanest. It requires also updating `run_component_tests()` to handle dotted component names:
```python
def run_component_tests(self, component: str, config: TestConfig) -> int:
    if component == "theory_lib":
        test_dir = self.src_dir / "model_checker" / "theory_lib" / "tests"
    elif '.' in component:
        parts = component.split('.')
        test_dir = self.src_dir / "model_checker" / parts[0] / parts[1] / "tests"
    else:
        test_dir = self.src_dir / "model_checker" / component / "tests"
```

## Summary of Changes Needed

| Gap | Location | Tests | Fix Complexity |
|-----|----------|-------|----------------|
| Bimodal exclusion | `_discover_theories()` L662 | 98 | Trivial (remove/gate filter) |
| first_order missing | `_discover_subtheories()` L694 | 53 | Small (add to list or make dynamic) |
| notebook unreachable | `_discover_components()` L669 | 14 | Small (nested discovery + dotted names) |
| **Total** | | **165** | **Small** |

## Effort Estimate

**Small** -- All three fixes are localized to the test runner's discovery methods. No changes to test files or project structure needed. Estimated implementation time: 1-2 hours including verification.

## Verification Plan

After implementation, verify:
1. `python run_tests.py` runs all 165 additional tests
2. `python run_tests.py logos first_order` works for targeted subtheory testing
3. `python run_tests.py --component output.notebook` works for targeted notebook testing
4. `python run_tests.py bimodal` works for bimodal theory testing (if tests pass)
5. No regressions in existing test counts
