# Plan 062: Tests Package Refactor Implementation

**Status:** Planning Complete  
**Created:** 2025-01-09  
**Priority:** HIGH - Second Priority  
**Current Compliance:** 71%  
**Target Compliance:** 90%+  
**Estimated Effort:** 20 hours  
**Dependencies:** Plan 061 (Models Package) should be complete  

## Executive Summary

The tests/ package contains integration tests for the ModelChecker framework but lacks modern organization patterns. This refactor will modernize the test suite structure, implement proper isolation fixtures, and enhance test quality to serve as a reliable validation foundation for all other refactoring efforts.

## Current State Analysis

### Package Structure
```
tests/
├── __init__.py                    (1 line)
├── README.md                      (68 lines) - Basic documentation
├── test_cli_arguments.py          (170 lines) - CLI validation
├── test_import_structure.py       (44 lines) - Import testing
├── test_monadic_semantics.py      (74 lines) - Theory testing
├── test_noncontingent_semantics.py (101 lines) - Theory testing
├── test_project_creation.py       (164 lines) - Project generation
├── test_theory_interop.py         (98 lines) - Theory compatibility
└── test_z3_usage.py               (50 lines) - Z3 integration
```

### Issues Identified

#### Organization Issues
- **No separation by test type** (unit/integration/e2e)
- **Mixed concerns** within test files
- **No shared fixtures** or utilities
- **Missing conftest.py** for test configuration

#### Test Quality Issues
- **Limited isolation** - tests may affect each other
- **No cleanup patterns** - potential artifact accumulation
- **Minimal mocking** - hard dependencies on external components
- **Limited parameterization** - repetitive test patterns

#### Coverage Gaps
- **No performance tests**
- **Limited error condition testing**
- **Missing edge case coverage**
- **No regression test suite**

## Implementation Plan

### Phase 1: Foundation Cleanup (Day 1 - 5 hours)

#### Task 1.1: Create Test Organization Structure
**Priority:** CRITICAL  
**Effort:** 2 hours  

Create new directory structure:
```bash
tests/
├── unit/                    # Fast, isolated component tests
│   ├── __init__.py
│   ├── test_cli_parsing.py # Extract from test_cli_arguments.py
│   └── test_imports.py      # From test_import_structure.py
├── integration/             # Component interaction tests
│   ├── __init__.py
│   ├── test_cli_execution.py
│   ├── test_theory_interop.py
│   └── test_z3_integration.py
├── e2e/                     # Full workflow tests
│   ├── __init__.py
│   ├── test_project_creation.py
│   └── test_semantic_validation.py
├── fixtures/                # Shared test data
│   ├── __init__.py
│   ├── example_data.py
│   ├── mock_theories.py
│   └── test_modules.py
├── utils/                   # Test utilities
│   ├── __init__.py
│   ├── assertions.py
│   └── helpers.py
├── conftest.py             # Pytest configuration
└── README.md               # Enhanced documentation
```

#### Task 1.2: Create conftest.py with Isolation Fixtures
**Priority:** HIGH  
**File:** `tests/conftest.py`  
**Effort:** 1.5 hours  

```python
"""Pytest configuration for ModelChecker integration tests."""

import pytest
import tempfile
import shutil
import os
import sys
from pathlib import Path
from unittest.mock import Mock

# Add src to path for testing
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

@pytest.fixture(autouse=True)
def test_isolation():
    """Ensure test isolation with cleanup."""
    # Store initial state
    initial_cwd = os.getcwd()
    initial_path = sys.path.copy()
    initial_modules = set(sys.modules.keys())
    
    yield
    
    # Restore state
    os.chdir(initial_cwd)
    sys.path[:] = initial_path
    
    # Clean up imported modules
    current_modules = set(sys.modules.keys())
    new_modules = current_modules - initial_modules
    for module in new_modules:
        if module.startswith('model_checker'):
            sys.modules.pop(module, None)

@pytest.fixture(autouse=True)
def cleanup_test_artifacts():
    """Clean up any test artifacts."""
    import glob
    
    # Track artifacts created
    initial_artifacts = set(glob.glob('test_*'))
    initial_outputs = set(glob.glob('output_*'))
    
    yield
    
    # Clean up new artifacts
    for pattern, initial in [('test_*', initial_artifacts), 
                            ('output_*', initial_outputs)]:
        current = set(glob.glob(pattern))
        new_items = current - initial
        for item in new_items:
            try:
                if os.path.isdir(item):
                    shutil.rmtree(item)
                else:
                    os.remove(item)
            except (OSError, PermissionError):
                pass

@pytest.fixture
def temp_test_dir():
    """Provide temporary directory for test isolation."""
    with tempfile.TemporaryDirectory(prefix='test_mc_') as tmpdir:
        yield Path(tmpdir)

@pytest.fixture
def mock_theory():
    """Provide mock theory for testing."""
    from tests.fixtures.mock_theories import create_mock_theory
    return create_mock_theory()
```

#### Task 1.3: Create Shared Fixtures Module
**Priority:** MEDIUM  
**File:** `tests/fixtures/example_data.py`  
**Effort:** 1 hour  

```python
"""Shared test data for ModelChecker tests."""

# Standard test examples
VALID_FORMULAS = [
    "(A \\wedge B)",
    "\\Box (A \\rightarrow B)",
    "\\neg (A \\vee B)",
]

INVALID_FORMULAS = [
    "(A ∧ B)",  # Unicode instead of LaTeX
    "A \\wedge B",  # Missing parentheses
    "(A \\wedge)",  # Incomplete
]

TEST_SETTINGS = {
    'minimal': {'N': 2},
    'standard': {'N': 3, 'max_time': 10},
    'complex': {'N': 5, 'max_time': 30, 'print_constraints': True},
}

def get_test_example(name='basic'):
    """Get standardized test example."""
    examples = {
        'basic': [['A'], ['B'], {'N': 2}],
        'complex': [['A', 'B'], ['(A \\wedge B)'], {'N': 3}],
        'modal': [['\\Box A'], ['\\Diamond B'], {'N': 3}],
    }
    return examples.get(name, examples['basic'])
```

#### Task 1.4: Migrate Existing Tests to New Structure
**Priority:** HIGH  
**Effort:** 0.5 hours  

Move existing test files to appropriate directories:
```bash
# Unit tests (fast, isolated)
mv test_import_structure.py unit/test_imports.py

# Integration tests (component interaction)
mv test_cli_arguments.py integration/test_cli_execution.py
mv test_theory_interop.py integration/
mv test_z3_usage.py integration/test_z3_integration.py

# E2E tests (full workflows)
mv test_project_creation.py e2e/
mv test_monadic_semantics.py e2e/test_semantic_validation.py
mv test_noncontingent_semantics.py e2e/test_semantic_validation.py
```

### Phase 2: Method Refinement (Day 2 - 6 hours)

#### Task 2.1: Extract Test Utilities
**Priority:** HIGH  
**File:** `tests/utils/helpers.py`  
**Effort:** 2 hours  

Extract common patterns from existing tests:
```python
"""Test helper utilities."""

import subprocess
import sys
from pathlib import Path

def run_cli_command(args, capture_output=True):
    """Run ModelChecker CLI command and return result."""
    cmd = [sys.executable, '-m', 'model_checker'] + args
    
    result = subprocess.run(
        cmd,
        capture_output=capture_output,
        text=True,
        cwd=Path(__file__).parent.parent.parent
    )
    
    return result

def assert_theory_valid(theory_name):
    """Assert a theory can be loaded and used."""
    from model_checker.utils.api import get_theory
    
    theory = get_theory(theory_name)
    assert theory is not None
    assert 'semantics' in theory
    assert 'model' in theory
    
def create_test_module(content, tmp_path):
    """Create a test module file."""
    module_file = tmp_path / 'test_module.py'
    module_file.write_text(content)
    return str(module_file)

def capture_model_output(example_data, theory_name='logos'):
    """Capture model checking output for testing."""
    # Implementation to capture output
    pass
```

#### Task 2.2: Refactor Large Test Methods
**Priority:** MEDIUM  
**Files:** Various test files  
**Effort:** 2 hours  

Break down large test methods (example from `test_project_creation.py`):
```python
# Before: Large monolithic test
def test_project_creation_comprehensive():
    # 50+ lines of mixed setup, execution, validation
    
# After: Focused test methods
class TestProjectCreation:
    @pytest.fixture
    def project_setup(self, temp_test_dir):
        """Setup for project tests."""
        return {
            'path': temp_test_dir,
            'name': 'test_project',
            'theory': 'logos'
        }
    
    def test_project_directory_creation(self, project_setup):
        """Test project directory is created correctly."""
        # Focused test for directory creation
        
    def test_project_file_structure(self, project_setup):
        """Test all expected files are created."""
        # Focused test for file structure
        
    def test_project_imports_work(self, project_setup):
        """Test generated project can be imported."""
        # Focused test for imports
```

#### Task 2.3: Add Parameterized Tests
**Priority:** LOW  
**Effort:** 2 hours  

Convert repetitive tests to parameterized:
```python
import pytest

class TestFormulaValidation:
    @pytest.mark.parametrize("formula,expected", [
        ("(A \\wedge B)", True),
        ("\\Box A", True),
        ("A ∧ B", False),  # Unicode
        ("(A \\wedge", False),  # Incomplete
    ])
    def test_formula_validation(self, formula, expected):
        """Test formula validation with various inputs."""
        from model_checker.syntactic import validate_formula
        result = validate_formula(formula)
        assert result == expected

    @pytest.mark.parametrize("theory_name", [
        'logos', 'exclusion', 'bimodal', 'imposition'
    ])
    def test_theory_loading(self, theory_name):
        """Test all theories can be loaded."""
        assert_theory_valid(theory_name)
```

### Phase 3: Error Handling Enhancement (Day 3 - 4 hours)

#### Task 3.1: Add Error Condition Tests
**Priority:** HIGH  
**File:** `tests/integration/test_error_handling.py`  
**Effort:** 2 hours  

Create comprehensive error testing:
```python
"""Test error handling across the framework."""

import pytest
from tests.utils.helpers import run_cli_command

class TestCLIErrorHandling:
    """Test CLI error handling."""
    
    def test_invalid_file_path(self):
        """Test handling of non-existent file."""
        result = run_cli_command(['nonexistent.py'])
        assert result.returncode != 0
        assert 'not found' in result.stderr.lower()
    
    def test_invalid_theory(self):
        """Test handling of invalid theory name."""
        result = run_cli_command(['-l', 'invalid_theory', 'test'])
        assert result.returncode != 0
        assert 'theory' in result.stderr.lower()
    
    def test_malformed_module(self, temp_test_dir):
        """Test handling of malformed module file."""
        bad_module = temp_test_dir / 'bad.py'
        bad_module.write_text('import syntax error!')
        
        result = run_cli_command([str(bad_module)])
        assert result.returncode != 0
        assert 'syntax' in result.stderr.lower()

class TestFrameworkErrorHandling:
    """Test framework-level error handling."""
    
    def test_invalid_formula_handling(self):
        """Test invalid formula error messages."""
        from model_checker.syntactic import Syntax
        
        with pytest.raises(Exception) as exc_info:
            Syntax().parse("(A ∧ B)")  # Unicode
        
        assert 'unicode' in str(exc_info.value).lower()
        
    def test_z3_timeout_handling(self):
        """Test Z3 solver timeout handling."""
        # Test timeout scenarios
        pass
```

#### Task 3.2: Add Edge Case Tests
**Priority:** MEDIUM  
**File:** `tests/unit/test_edge_cases.py`  
**Effort:** 2 hours  

```python
"""Edge case testing for ModelChecker."""

import pytest

class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_empty_formula_list(self):
        """Test handling of empty formula lists."""
        from tests.fixtures.example_data import get_test_example
        example = get_test_example('basic')
        example[1] = []  # Empty conclusions
        
        # Should handle gracefully
        
    def test_maximum_n_value(self):
        """Test maximum N value (64)."""
        settings = {'N': 64}
        # Test handling
        
    def test_minimum_n_value(self):
        """Test minimum N value (1)."""
        settings = {'N': 1}
        # Test handling
        
    @pytest.mark.parametrize("n_value", [-1, 0, 65, 100])
    def test_invalid_n_values(self, n_value):
        """Test invalid N values are rejected."""
        settings = {'N': n_value}
        # Should raise appropriate error
```

### Phase 4: Architectural Improvements (Day 4 - 5 hours)

#### Task 4.1: Create Test Base Classes
**Priority:** LOW  
**File:** `tests/utils/base.py`  
**Effort:** 2 hours  

```python
"""Base classes for ModelChecker tests."""

import pytest
from abc import ABC, abstractmethod

class BaseTheoryTest(ABC):
    """Base class for theory testing."""
    
    @abstractmethod
    def get_theory_name(self):
        """Return theory name to test."""
        pass
    
    def test_theory_loads(self):
        """Test theory can be loaded."""
        from model_checker.utils.api import get_theory
        theory = get_theory(self.get_theory_name())
        assert theory is not None
    
    def test_theory_has_required_components(self):
        """Test theory has all required components."""
        from model_checker.utils.api import get_theory
        theory = get_theory(self.get_theory_name())
        
        required = ['semantics', 'model', 'proposition', 'operators']
        for component in required:
            assert component in theory

class BaseCLITest:
    """Base class for CLI testing."""
    
    def run_cli(self, *args):
        """Run CLI with arguments."""
        from tests.utils.helpers import run_cli_command
        return run_cli_command(list(args))
    
    def assert_cli_success(self, *args):
        """Assert CLI command succeeds."""
        result = self.run_cli(*args)
        assert result.returncode == 0
        return result
```

#### Task 4.2: Add Performance Tests
**Priority:** MEDIUM  
**File:** `tests/integration/test_performance.py`  
**Effort:** 1.5 hours  

```python
"""Performance testing for ModelChecker."""

import pytest
import time

class TestPerformance:
    """Test performance characteristics."""
    
    @pytest.mark.timeout(5)
    def test_simple_model_performance(self):
        """Test simple models complete quickly."""
        start = time.time()
        
        # Run simple model check
        from tests.fixtures.example_data import get_test_example
        example = get_test_example('basic')
        # Execute model check
        
        elapsed = time.time() - start
        assert elapsed < 1.0  # Should complete in under 1 second
    
    @pytest.mark.timeout(30)
    def test_complex_model_performance(self):
        """Test complex models complete within timeout."""
        # Test with N=10, multiple formulas
        pass
    
    def test_memory_usage(self):
        """Test memory usage stays reasonable."""
        import tracemalloc
        
        tracemalloc.start()
        # Run model checking
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        
        # Peak memory should be under 100MB for standard examples
        assert peak < 100 * 1024 * 1024
```

#### Task 4.3: Update Test Documentation
**Priority:** LOW  
**File:** `tests/README.md`  
**Effort:** 1.5 hours  

Enhanced documentation with:
- New test organization structure
- How to run specific test types
- Adding new tests guidelines
- Fixture documentation
- Performance testing notes

## Testing Strategy

### Test Execution Patterns
```bash
# Run all tests
pytest tests/

# Run only unit tests (fast)
pytest tests/unit/

# Run integration tests
pytest tests/integration/

# Run end-to-end tests
pytest tests/e2e/

# Run with coverage
pytest tests/ --cov=model_checker --cov-report=html

# Run specific test class
pytest tests/unit/test_imports.py::TestImportStructure

# Run with markers
pytest tests/ -m "not slow"
```

### Coverage Requirements
- Maintain overall coverage above 80%
- Critical paths must have 95%+ coverage
- Error handling paths must be tested
- Edge cases must be covered

## Risk Management

### Medium Risk Items
- **Test reorganization** might temporarily break CI/CD
- **New fixtures** might have unexpected interactions
- **Performance tests** might be flaky in different environments

### Mitigation Strategies
1. **Parallel structure** - Keep old tests while building new
2. **Incremental migration** - Move tests one at a time
3. **CI/CD updates** - Update test commands as needed
4. **Environment markers** - Mark environment-specific tests

## Success Metrics

### Quantitative Metrics
- **Compliance Score**: 71% → 90%+
- **Test Organization**: 100% categorized by type
- **Fixture Usage**: All tests use proper isolation
- **Coverage**: Maintain 80%+ overall

### Qualitative Metrics
- Tests are easy to understand and maintain
- New tests follow established patterns
- Test failures provide clear diagnostics
- Tests run reliably in all environments

## Implementation Schedule

| Day | Phase | Tasks | Hours |
|-----|-------|-------|-------|
| 1 | Phase 1 | Create structure, fixtures, migrate | 5 |
| 2 | Phase 2 | Extract utilities, refactor tests | 6 |
| 3 | Phase 3 | Add error and edge case tests | 4 |
| 4 | Phase 4 | Base classes, performance, docs | 5 |

**Total: 20 hours over 4 days**

## Validation Checklist

### Phase 1 Complete
- [ ] New directory structure created
- [ ] conftest.py with isolation fixtures
- [ ] Shared fixtures module created
- [ ] Existing tests migrated

### Phase 2 Complete
- [ ] Test utilities extracted
- [ ] Large tests refactored
- [ ] Parameterized tests added
- [ ] All tests still passing

### Phase 3 Complete
- [ ] Error condition tests added
- [ ] Edge case tests added
- [ ] Error handling validated
- [ ] Coverage improved

### Phase 4 Complete
- [ ] Base test classes created
- [ ] Performance tests added
- [ ] Documentation updated
- [ ] All tests categorized

### Final Validation
- [ ] Compliance score ≥90%
- [ ] All tests passing
- [ ] Test isolation verified
- [ ] Documentation complete

## Next Steps

1. **After models/ refactor**: Begin Phase 1 implementation
2. **During implementation**: Update Plan 060 progress
3. **After completion**: Proceed to jupyter/ package refactor

---

**Status**: Ready for implementation after models/ package complete
**Next Action**: Wait for models/ completion, then begin Phase 1