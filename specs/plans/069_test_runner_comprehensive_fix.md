# Implementation Plan 069: Comprehensive Test Runner Fix

**Date:** 2025-01-09  
**Author:** Assistant  
**Priority:** High  
**Scope:** run_tests.py and test infrastructure  

## Executive Summary

The current test runner (`run_tests.py`) has critical issues causing test deselection and skipping:
1. **Deselection Problem**: When running tests, pytest deselects many tests because the runner selects specific test files instead of directories
2. **Skip Markers**: Several tests have skip markers that should be removed after refactoring completion
3. **Fragmented Test Selection**: The runner divides tests into "examples", "unit", and "package" categories, missing tests that don't fit these narrow definitions

This plan provides a comprehensive fix that maintains filtering flexibility while ensuring all tests run by default.

## Current Problems Analysis

### 1. Test Deselection Root Cause

**Current Behavior:**
```python
# ExampleTestRunner looks for specific files
command = ["pytest", "test_examples.py"]  # Only runs this file
# Result: Other tests in same directory are "deselected"
```

**Problem:** The runner targets specific test files (e.g., `test_examples.py`, `test_iterate.py`) instead of running entire directories, causing pytest to report deselection of other valid tests.

### 2. Skip Markers Still Present

**Found Skip Markers:**
- `src/model_checker/iterate/tests/e2e/test_edge_cases.py` - Module-level skip
- `src/model_checker/iterate/tests/unit/test_base_iterator.py` - Method-level skips
- `src/model_checker/iterate/tests/unit/test_simplified_iterator.py` - unittest.skipTest() calls
- Theory tests with `@pytest.mark.skip` for unimplemented features

### 3. Incomplete Test Discovery

**Current Categories:**
- `--examples`: Only runs `test_examples.py` files
- `--unit`: Only runs specific unit test files  
- `--package`: Only runs certain package test files

**Missing:** Integration tests, e2e tests, and any tests not matching the narrow file patterns.

## Proposed Solution Architecture

### Design Principles

1. **Directory-Based Selection**: Run entire test directories, not specific files
2. **Comprehensive Default**: With no flags, run ALL tests in all directories
3. **Smart Filtering**: Allow filtering by package, theory, or test type without deselection
4. **Proper Test Detection**: Detect test types by directory structure, not file names
5. **Clear Reporting**: Show what's being run and why

### New Test Runner Architecture

```python
class TestRunner:
    """Unified test runner with comprehensive coverage."""
    
    def run_all_tests(self):
        """Run ALL tests without any filtering."""
        test_dirs = [
            "src/model_checker",  # All package tests
            "tests",              # System-level tests
        ]
        return self._run_pytest(test_dirs)
    
    def run_filtered_tests(self, filters):
        """Run tests with smart filtering."""
        # Build directory list based on filters
        test_dirs = self._build_test_directories(filters)
        return self._run_pytest(test_dirs)
    
    def _run_pytest(self, directories):
        """Run pytest on directories, not specific files."""
        command = ["pytest"] + directories
        # No file selection = no deselection
```

## Implementation Plan

### Phase 1: Remove Skip Markers (Immediate)

#### 1.1 Remove Module-Level Skips
```python
# Files to fix:
# src/model_checker/iterate/tests/e2e/test_edge_cases.py
# Remove: pytestmark = pytest.mark.skip(...)
```

#### 1.2 Remove Method-Level Skips
```python
# Fix unittest.skipTest() calls by either:
# 1. Removing them if tests should run
# 2. Converting to pytest.mark.skipif() with clear conditions
# 3. Adding 'pass' statements where needed for syntax
```

#### 1.3 Conditional Skips Only
```python
# Keep only legitimate conditional skips:
@pytest.mark.skipif(not HAS_NETWORKX, reason="NetworkX required")
```

### Phase 2: Redesign Test Discovery (Core Fix)

#### 2.1 New Test Discovery Logic

```python
class TestDiscovery:
    """Discover tests based on directory structure."""
    
    def find_all_test_directories(self, root="src/model_checker"):
        """Find all directories containing tests."""
        test_dirs = []
        for path in Path(root).rglob("tests"):
            if path.is_dir() and not path.name.startswith("__"):
                test_dirs.append(path)
        return test_dirs
    
    def categorize_test_directory(self, test_dir):
        """Categorize based on subdirectories."""
        subdirs = {d.name for d in test_dir.iterdir() if d.is_dir()}
        
        # Modern structure (unit/integration/e2e)
        if subdirs & {"unit", "integration", "e2e"}:
            return "structured"
        # Flat structure (legacy)
        else:
            return "flat"
    
    def get_test_paths_for_filter(self, filter_type, target):
        """Get test paths based on filter."""
        if filter_type == "all":
            return self.find_all_test_directories()
        elif filter_type == "package":
            return [f"src/model_checker/{target}/tests"]
        elif filter_type == "theory":
            return [f"src/model_checker/theory_lib/{target}/tests"]
        elif filter_type == "type":
            # Return all dirs with specific subdirectory
            return self._find_by_test_type(target)
```

#### 2.2 Replace File-Specific Runners

**Current (Bad):**
```python
def run_example_tests(theory):
    test_file = find_test_examples_file(theory)
    command = ["pytest", test_file]  # Causes deselection
```

**New (Good):**
```python
def run_theory_tests(theory, test_type=None):
    test_dir = f"src/model_checker/theory_lib/{theory}/tests"
    
    if test_type:
        # Run specific type subdirectory
        test_path = f"{test_dir}/{test_type}"
    else:
        # Run entire test directory
        test_path = test_dir
    
    command = ["pytest", test_path]  # No deselection
```

### Phase 3: Update Command-Line Interface

#### 3.1 New Flag Structure

```python
parser.add_argument("targets", nargs="*", 
                   help="Specific packages/theories to test")

# Test type filters (can combine)
parser.add_argument("--unit", action="store_true",
                   help="Include unit tests")
parser.add_argument("--integration", action="store_true",
                   help="Include integration tests")
parser.add_argument("--e2e", action="store_true",
                   help="Include end-to-end tests")
parser.add_argument("--all", action="store_true",
                   help="Run ALL tests (default if no filters)")

# Target type hints
parser.add_argument("--package", action="store_true",
                   help="Targets are packages")
parser.add_argument("--theory", action="store_true",
                   help="Targets are theories")
```

#### 3.2 Intelligent Default Behavior

```python
def determine_test_scope(args):
    """Determine what to test based on arguments."""
    
    # No arguments = run everything
    if not args.targets and not any([args.unit, args.integration, args.e2e]):
        return TestScope(run_all=True)
    
    # Specific targets provided
    if args.targets:
        targets = classify_targets(args.targets)
        test_types = get_test_types(args)
        return TestScope(targets=targets, types=test_types)
    
    # Only test type flags = run those types everywhere
    if any([args.unit, args.integration, args.e2e]):
        test_types = get_test_types(args)
        return TestScope(run_all=True, types=test_types)
```

### Phase 4: Fix Test Organization Issues

#### 4.1 Standardize Test Imports

```python
# In each test file, ensure proper imports
import pytest  # Use pytest, not unittest.skipTest
from pathlib import Path
import sys

# Add src to path if needed
sys.path.insert(0, str(Path(__file__).parents[4] / "src"))
```

#### 4.2 Fix Pytest Configuration

```toml
# pyproject.toml
[tool.pytest.ini_options]
pythonpath = "src"
testpaths = [
    "src/model_checker",  # All package tests
    "tests",              # System tests
]
# Remove overly specific testpaths that cause deselection
```

### Phase 5: Implementation Steps

#### Step 1: Backup Current Runner
```bash
cp run_tests.py run_tests_backup.py
```

#### Step 2: Remove Skip Markers
```python
# Script to remove skip markers
def remove_skip_markers():
    skip_patterns = [
        "pytestmark = pytest.mark.skip",
        "self.skipTest(",
        "@pytest.mark.skip("
    ]
    # Process each file and remove/comment skips
```

#### Step 3: Rewrite Core Runner Logic
```python
class ImprovedTestRunner:
    def run(self, config):
        """Main entry point."""
        if config.run_all:
            return self._run_all_tests()
        else:
            return self._run_filtered_tests(config)
    
    def _run_all_tests(self):
        """Run everything without filters."""
        command = [
            "pytest",
            "src/model_checker",
            "tests",
            "-v"
        ]
        return subprocess.run(command)
    
    def _run_filtered_tests(self, config):
        """Run with smart filtering."""
        test_paths = self._build_test_paths(config)
        command = ["pytest"] + test_paths + config.pytest_args
        return subprocess.run(command)
```

#### Step 4: Test the New Runner
```bash
# Test various scenarios
./run_tests.py                      # Should run ALL tests
./run_tests.py --unit               # All unit tests
./run_tests.py iterate              # All iterate tests
./run_tests.py --theory logos       # All logos tests
./run_tests.py --unit iterate       # Only iterate unit tests
```

### Phase 6: Update Documentation

#### 6.1 Update run_tests.py Docstring
```python
"""Comprehensive test runner for ModelChecker.

Usage:
    run_tests.py              # Run ALL tests (no deselection)
    run_tests.py --unit       # Run all unit tests
    run_tests.py iterate      # Run all tests for iterate package
    run_tests.py logos modal  # Run tests for logos and modal
    
No more deselection! All tests in selected scope will run.
"""
```

#### 6.2 Update Test Documentation
- Update `tests/README.md` with new runner behavior
- Update `docs/TESTS.md` with comprehensive testing guide
- Document the test organization structure

#### 6.3 Update CLAUDE.md Testing Section
```markdown
## Testing
Run all tests without deselection:
```bash
./run_tests.py  # Runs everything
```
```

## Success Metrics

### Immediate Success (After Implementation)
- ✅ Running `run_tests.py` shows 0 deselected tests
- ✅ No tests skipped unless genuinely not applicable
- ✅ All test directories are discovered and run
- ✅ Clear output showing what's being tested

### Functional Success
- ✅ Can filter by package: `run_tests.py iterate`
- ✅ Can filter by theory: `run_tests.py --theory logos`
- ✅ Can filter by type: `run_tests.py --unit`
- ✅ Can combine filters: `run_tests.py --unit iterate logos`
- ✅ Default behavior runs everything

### Quality Metrics
- ✅ No hardcoded test file names in runner
- ✅ Directory-based discovery only
- ✅ Clear separation of concerns
- ✅ Maintainable and extensible

## Risk Mitigation

### Risk 1: Breaking Existing Workflows
**Mitigation:** Keep backup of original runner, test thoroughly

### Risk 2: Missing Tests
**Mitigation:** Use pytest collection to verify all tests found

### Risk 3: Performance Impact
**Mitigation:** Add parallel execution support with pytest-xdist

## Implementation Timeline

| Phase | Task | Duration |
|-------|------|----------|
| 1 | Remove skip markers | 30 mins |
| 2 | Redesign test discovery | 2 hours |
| 3 | Update CLI interface | 1 hour |
| 4 | Fix test organization | 1 hour |
| 5 | Implementation | 2 hours |
| 6 | Documentation | 1 hour |

**Total: ~7-8 hours**

## Code Changes Summary

### Files to Modify
1. `run_tests.py` - Complete rewrite of test discovery and execution
2. `pyproject.toml` - Fix pytest configuration
3. Skip marker removal in:
   - `src/model_checker/iterate/tests/e2e/test_edge_cases.py`
   - `src/model_checker/iterate/tests/unit/test_base_iterator.py`
   - `src/model_checker/iterate/tests/unit/test_simplified_iterator.py`
4. Documentation updates:
   - `tests/README.md`
   - `docs/TESTS.md`
   - `CLAUDE.md`

### New Capabilities
- Run all tests without deselection
- Smart filtering by package/theory/type
- Clear reporting of what's being tested
- No more mysterious deselection

## Conclusion

This plan fixes the fundamental issues with the test runner:
1. **Eliminates deselection** by running directories, not specific files
2. **Removes unnecessary skips** from completed refactoring
3. **Provides flexible filtering** while maintaining comprehensive coverage
4. **Improves clarity** in what tests are running and why

The new runner will be simpler, more maintainable, and actually run all tests as expected.

---

**Next Step:** Review this plan and approve for implementation