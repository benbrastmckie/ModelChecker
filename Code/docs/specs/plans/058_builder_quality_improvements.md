# Builder Package Quality Improvements Implementation Plan

**Specification ID**: 058_builder_quality_improvements  
**Author**: ModelChecker Development Team  
**Date**: September 2025  
**Priority**: High  
**Status**: Ready for Implementation  

[← Back to Plans](README.md) | [Related: Quality Audit →](../research/025_builder_package_quality_audit.md)

---

## 1. Executive Summary

This implementation plan addresses all quality issues identified in the builder package audit (research/025), providing a systematic approach to achieve 100% compliance with maintenance standards. The plan is organized into four phases with specific tasks, code examples, and validation criteria.

### Goals
- Achieve 100% import compliance (currently 20%)
- Reduce method complexity below 10 (currently up to 15)
- Improve test quality and reduce mocking overhead
- Enhance architectural clarity and maintainability

### Timeline
- **Phase 1**: 1 day (Critical fixes)
- **Phase 2**: 1 week (Code quality)
- **Phase 3**: 2 weeks (Structural improvements)
- **Phase 4**: 1 month (Architectural enhancements)

---

## 2. Phase 1: Critical Import Fixes (Day 1)

### 2.1 Convert Absolute to Relative Imports

**Priority**: P0 (Critical)  
**Effort**: 2 hours  
**Files**: 8 modules requiring changes

#### Task 1.1: Update example.py

```python
# BEFORE (Violates portability)
from model_checker.builder.validation import (
    validate_semantic_theory,
    validate_example_case,
)
from model_checker.builder.z3_utils import (
    create_difference_constraint,
    extract_model_values,
    find_next_model as find_next_z3_model
)

# AFTER (Compliant)
from .validation import (
    validate_semantic_theory,
    validate_example_case,
)
from .z3_utils import (
    create_difference_constraint,
    extract_model_values,
    find_next_model as find_next_z3_model
)
```

#### Task 1.2: Update module.py

```python
# BEFORE
from model_checker.builder.loader import ModuleLoader
from model_checker.builder.runner import ModelRunner
from model_checker.builder.comparison import ModelComparison
from model_checker.builder.project import BuildProject
from model_checker.builder.translation import OperatorTranslation
from model_checker.builder.validation import validate_module_structure
from model_checker.builder.serialize import serialize_semantic_theory

# AFTER
from .loader import ModuleLoader
from .runner import ModelRunner
from .comparison import ModelComparison
from .project import BuildProject
from .translation import OperatorTranslation
from .validation import validate_module_structure
from .serialize import serialize_semantic_theory
```

#### Task 1.3: Update remaining files

Apply same pattern to:
- `validation.py` (3 imports)
- `loader.py` (4 imports)
- `project.py` (2 imports)
- `translation.py` (3 imports)
- `z3_utils.py` (2 imports)
- `__init__.py` (6 imports)

#### Automated Fix Script

```bash
#!/bin/bash
# fix_imports.sh - Automated import correction

# Backup original files
find src/model_checker/builder -name "*.py" -exec cp {} {}.backup \;

# Fix imports in all Python files
find src/model_checker/builder -name "*.py" -type f | while read file; do
    # Skip test files
    if [[ "$file" == *"/tests/"* ]]; then
        continue
    fi
    
    # Replace absolute imports with relative
    sed -i 's/from model_checker\.builder\.\([a-z_]*\)/from .\1/g' "$file"
    
    # Fix multi-line imports
    perl -i -pe 's/from model_checker\.builder\./from ./g' "$file"
done

# Run tests to validate changes
python -m pytest src/model_checker/builder/tests/ -q

# If tests pass, remove backups
if [ $? -eq 0 ]; then
    find src/model_checker/builder -name "*.py.backup" -delete
    echo "Import fixes completed successfully"
else
    echo "Tests failed - restoring backups"
    find src/model_checker/builder -name "*.py.backup" | while read backup; do
        mv "$backup" "${backup%.backup}"
    done
fi
```

### 2.2 Fix Import Grouping

**Priority**: P0 (Critical)  
**Effort**: 30 minutes  
**Files**: 5 modules requiring blank line separation

#### Task 1.4: Standardize import groups

```python
# TEMPLATE for all files
"""Module docstring."""

# Standard library imports
import os
import sys
from typing import Dict, List, Optional

# Third-party imports
import z3
import numpy as np

# Local imports
from .validation import validate_semantic_theory
from .serialize import serialize_semantic_theory
```

#### Task 1.5: Configure isort

Create `.isort.cfg`:
```ini
[settings]
profile = black
import_heading_stdlib = Standard library imports
import_heading_thirdparty = Third-party imports  
import_heading_firstparty = Local imports
force_single_line = true
lines_after_imports = 2
known_third_party = z3,numpy,networkx
known_first_party = model_checker
```

Run isort:
```bash
isort src/model_checker/builder/ --check-only --diff
isort src/model_checker/builder/  # Apply fixes
```

### 2.3 Validation Criteria

- [ ] All imports use relative syntax for local modules
- [ ] All files have proper blank line separation
- [ ] Test suite passes without import errors
- [ ] No circular import errors
- [ ] Package can be imported from different locations

---

## 3. Phase 2: Code Quality Improvements (Week 1)

### 3.1 Refactor Long Methods

**Priority**: P1 (High)  
**Effort**: 4 hours  
**Methods**: 4 requiring refactoring

#### Task 2.1: Refactor runner.py::process_example (187 lines → ~40 lines each)

```python
# BEFORE - Monolithic method
def process_example(self, example_name, example_case, theory_name=None):
    """Process a single example through model checking."""
    # 187 lines of code...
    
# AFTER - Decomposed methods
def process_example(self, example_name, example_case, theory_name=None):
    """Process a single example through model checking."""
    # Step 1: Validate inputs
    validated_case = self._validate_example_inputs(example_name, example_case)
    
    # Step 2: Create build example
    build_example = self._create_build_example(
        validated_case, theory_name
    )
    
    # Step 3: Run model checking
    result = self._run_model_check(build_example)
    
    # Step 4: Handle iterations if requested
    if self.build_module.module_flags.iterations:
        result = self._process_iterations(build_example, result)
    
    # Step 5: Format and return output
    return self._format_example_output(
        example_name, result, theory_name
    )

def _validate_example_inputs(self, example_name, example_case):
    """Validate and normalize example inputs."""
    # ~30 lines
    
def _create_build_example(self, validated_case, theory_name):
    """Create BuildExample instance with proper configuration."""
    # ~35 lines
    
def _run_model_check(self, build_example):
    """Execute model checking and capture results."""
    # ~25 lines
    
def _process_iterations(self, build_example, initial_result):
    """Handle model iteration if requested."""
    # ~40 lines
    
def _format_example_output(self, example_name, result, theory_name):
    """Format result for output."""
    # ~20 lines
```

#### Task 2.2: Refactor module.py::__init__ (94 lines → ~25 lines each)

```python
# AFTER - Extracted initialization
def __init__(self, module_flags):
    """Initialize BuildModule with given flags."""
    self.module_flags = module_flags
    
    # Step 1: Load module
    self._load_module_file()
    
    # Step 2: Validate structure
    self._validate_module_structure()
    
    # Step 3: Initialize components
    self._initialize_components()
    
    # Step 4: Apply settings
    self._apply_settings()

def _load_module_file(self):
    """Load and validate module file."""
    # ~20 lines
    
def _validate_module_structure(self):
    """Validate required module attributes."""
    # ~25 lines
    
def _initialize_components(self):
    """Initialize runner, comparison, and other components."""
    # ~25 lines
    
def _apply_settings(self):
    """Apply general and flag-based settings."""
    # ~20 lines
```

#### Task 2.3: Refactor comparison.py::run_comparison (78 lines)

```python
# Split into:
def run_comparison(self):
    """Run comparison across theories."""
    results = self._collect_theory_results()
    comparison = self._compare_results(results)
    self._output_comparison(comparison)
    
def _collect_theory_results(self):
    """Run examples for each theory."""
    # ~25 lines
    
def _compare_results(self, results):
    """Compare results across theories."""
    # ~30 lines
    
def _output_comparison(self, comparison):
    """Format and output comparison."""
    # ~20 lines
```

### 3.2 Reduce Cyclomatic Complexity

**Priority**: P1 (High)  
**Effort**: 2 hours  
**Target**: All methods < 10 complexity

#### Task 2.4: Simplify conditional logic

```python
# BEFORE - Complex nested conditions
def validate_settings(self, settings):
    if settings:
        if 'N' in settings:
            if settings['N'] > 0:
                if settings['N'] <= 100:
                    return True
                else:
                    raise ValueError("N too large")
            else:
                raise ValueError("N must be positive")
        else:
            if 'default_N' in self.config:
                settings['N'] = self.config['default_N']
            else:
                settings['N'] = 2
    else:
        raise ValueError("Settings required")

# AFTER - Guard clauses and extracted methods
def validate_settings(self, settings):
    """Validate and normalize settings."""
    if not settings:
        raise ValueError("Settings required")
    
    if 'N' not in settings:
        settings['N'] = self._get_default_n()
        return True
    
    self._validate_n_value(settings['N'])
    return True

def _get_default_n(self):
    """Get default N value from config or use standard default."""
    return self.config.get('default_N', 2)

def _validate_n_value(self, n):
    """Validate N is within acceptable range."""
    if n <= 0:
        raise ValueError("N must be positive")
    if n > 100:
        raise ValueError(f"N too large: {n} > 100")
```

### 3.3 Standardize Error Handling

**Priority**: P1 (High)  
**Effort**: 2 hours

#### Task 2.5: Create consistent error patterns

```python
# error_types.py - Centralized error definitions
class BuilderError(Exception):
    """Base exception for builder package."""
    pass

class ModuleLoadError(BuilderError):
    """Raised when module cannot be loaded."""
    pass

class ValidationError(BuilderError):
    """Raised when validation fails."""
    pass

class ModelCheckError(BuilderError):
    """Raised during model checking."""
    pass

# Usage pattern
def load_module(self, path):
    """Load module from path."""
    if not os.path.exists(path):
        raise ModuleLoadError(
            f"Module not found: {path}\n"
            f"Working directory: {os.getcwd()}\n"
            f"Suggestion: Check file path and permissions"
        )
```

---

## 4. Phase 3: Structural Improvements (Weeks 2-3)

### 4.1 Split Oversized Modules

**Priority**: P2 (Medium)  
**Effort**: 8 hours  
**Target**: All modules < 500 lines

#### Task 3.1: Split runner.py (708 lines → 350 + 350)

Create `runner_utils.py`:
```python
"""Utility functions for ModelRunner."""

def format_model_output(model, settings, example_name):
    """Format model for display output."""
    # Move formatting logic here
    
def calculate_model_statistics(model):
    """Calculate statistics for model."""
    # Move statistics logic here
    
def validate_runner_state(runner):
    """Validate runner is in correct state."""
    # Move validation logic here
```

Update `runner.py`:
```python
from .runner_utils import (
    format_model_output,
    calculate_model_statistics,
    validate_runner_state,
)

class ModelRunner:
    """Simplified runner using utilities."""
    # Now ~350 lines
```

#### Task 3.2: Extract validation module components

Create `validation_rules.py`:
```python
"""Validation rule definitions."""

REQUIRED_THEORY_COMPONENTS = [
    'semantics', 'proposition', 'operators', 'model_structure'
]

REQUIRED_EXAMPLE_COMPONENTS = ['premises', 'conclusions', 'settings']

def validate_theory_structure(theory):
    """Validate theory has required components."""
    # Move from validation.py
    
def validate_example_structure(example):
    """Validate example has required components."""
    # Move from validation.py
```

### 4.2 Reduce Test Mocking

**Priority**: P2 (Medium)  
**Effort**: 6 hours

#### Task 3.3: Create test builders

```python
# tests/fixtures/builders.py
class ExampleBuilder:
    """Builder for test examples."""
    
    def __init__(self):
        self.premises = ["A"]
        self.conclusions = ["B"]
        self.settings = {"N": 2}
    
    def with_premises(self, *premises):
        self.premises = list(premises)
        return self
    
    def with_conclusions(self, *conclusions):
        self.conclusions = list(conclusions)
        return self
    
    def with_settings(self, **settings):
        self.settings.update(settings)
        return self
    
    def build(self):
        return [self.premises, self.conclusions, self.settings]

# Usage in tests
def test_example_validation():
    example = (ExampleBuilder()
               .with_premises("A", "B")
               .with_conclusions("C")
               .with_settings(N=3)
               .build())
    
    # No mocking needed
    result = validate_example_case(example)
    assert result is not None
```

#### Task 3.4: Use real components where possible

```python
# BEFORE - Over-mocked
def test_module_init():
    mock_loader = Mock()
    mock_runner = Mock()
    mock_comparison = Mock()
    # ... 20 more mocks
    
# AFTER - Real components
def test_module_init(tmp_path):
    # Create real test file
    test_file = tmp_path / "test_module.py"
    test_file.write_text("""
from model_checker.theory_lib.logos import get_theory
semantic_theories = {"Test": get_theory(['extensional'])}
example_range = {"EX1": [["A"], ["B"], {"N": 2}]}
general_settings = {}
""")
    
    # Use real BuildModule with test file
    flags = Mock(file_path=str(test_file), _parsed_args=[])
    module = BuildModule(flags)
    
    # Test with real components
    assert module.semantic_theories is not None
```

### 4.3 Add Performance Tests

**Priority**: P2 (Medium)  
**Effort**: 4 hours

#### Task 3.5: Create performance benchmarks

```python
# tests/performance/test_benchmarks.py
import time
import pytest
from statistics import mean, stdev

class TestPerformanceBenchmarks:
    """Performance regression tests."""
    
    @pytest.mark.benchmark
    def test_module_loading_performance(self, benchmark_module):
        """Module loading should complete in <100ms."""
        times = []
        for _ in range(10):
            start = time.perf_counter()
            BuildModule(benchmark_module)
            times.append(time.perf_counter() - start)
        
        avg_time = mean(times)
        std_dev = stdev(times)
        
        assert avg_time < 0.1, f"Loading too slow: {avg_time:.3f}s"
        assert std_dev < 0.02, f"High variance: {std_dev:.3f}s"
    
    @pytest.mark.benchmark
    def test_model_checking_performance(self, simple_example):
        """Simple model checking should complete in <500ms."""
        # Test implementation
```

---

## 5. Phase 4: Architectural Enhancements (Month 2)

### 5.1 Define Component Interfaces

**Priority**: P3 (Low)  
**Effort**: 12 hours

#### Task 4.1: Create protocol definitions

```python
# interfaces.py
from typing import Protocol, Dict, Any, List

class IBuilder(Protocol):
    """Interface for builders."""
    
    def build(self) -> Any:
        """Build the component."""
        ...

class IValidator(Protocol):
    """Interface for validators."""
    
    def validate(self, data: Any) -> bool:
        """Validate data."""
        ...
    
    def get_errors(self) -> List[str]:
        """Get validation errors."""
        ...

class IRunner(Protocol):
    """Interface for runners."""
    
    def run(self, example: Any) -> Dict[str, Any]:
        """Run example."""
        ...
    
    def get_status(self) -> str:
        """Get runner status."""
        ...
```

#### Task 4.2: Implement interfaces

```python
# module.py
from .interfaces import IBuilder

class BuildModule(IBuilder):
    """BuildModule implementing IBuilder interface."""
    
    def build(self) -> Dict[str, Any]:
        """Build module components."""
        return {
            'theories': self.semantic_theories,
            'examples': self.example_range,
            'settings': self.general_settings,
        }
```

### 5.2 Implement Dependency Injection

**Priority**: P3 (Low)  
**Effort**: 8 hours

#### Task 4.3: Create dependency container

```python
# container.py
class DependencyContainer:
    """Dependency injection container."""
    
    def __init__(self):
        self._services = {}
        self._singletons = {}
    
    def register(self, name: str, factory, singleton=False):
        """Register service factory."""
        self._services[name] = (factory, singleton)
    
    def resolve(self, name: str):
        """Resolve service by name."""
        if name not in self._services:
            raise KeyError(f"Service not registered: {name}")
        
        factory, singleton = self._services[name]
        
        if singleton:
            if name not in self._singletons:
                self._singletons[name] = factory()
            return self._singletons[name]
        
        return factory()

# Usage
container = DependencyContainer()
container.register('loader', ModuleLoader, singleton=True)
container.register('runner', ModelRunner)
container.register('validator', lambda: Validator(strict=True))

# In BuildModule
class BuildModule:
    def __init__(self, flags, container=None):
        self.container = container or DependencyContainer()
        self.loader = self.container.resolve('loader')
        self.runner = self.container.resolve('runner')
```

### 5.3 Break Circular Dependencies

**Priority**: P3 (Low)  
**Effort**: 8 hours

#### Task 4.4: Use dependency inversion

```python
# BEFORE - Circular dependency
# module.py imports runner.py
# runner.py imports example.py  
# example.py imports module.py

# AFTER - Dependency inversion
# interfaces.py - No imports
class IModule(Protocol):
    def get_theories(self) -> Dict: ...

class IRunner(Protocol):
    def run(self, example) -> Any: ...

class IExample(Protocol):
    def process(self) -> Any: ...

# module.py - Imports interfaces only
from .interfaces import IRunner, IExample

class BuildModule:
    def __init__(self, runner: IRunner):
        self.runner = runner

# runner.py - Imports interfaces only
from .interfaces import IModule, IExample

class ModelRunner:
    def __init__(self, module: IModule):
        self.module = module

# example.py - Imports interfaces only
from .interfaces import IModule

class BuildExample:
    def __init__(self, module: IModule):
        self.module = module
```

---

## 6. Validation and Testing

### 6.1 Phase 1 Validation

```bash
# Test import changes
python -c "from model_checker.builder import BuildModule"
python -m pytest src/model_checker/builder/tests/ -v

# Check for absolute imports
grep -r "from model_checker.builder" src/model_checker/builder/ \
  --exclude-dir=tests

# Verify import grouping
isort --check-only src/model_checker/builder/
```

### 6.2 Phase 2 Validation

```python
# test_complexity.py
import ast
import radon.complexity as radon

def test_method_complexity():
    """Ensure all methods have complexity < 10."""
    for filepath in Path('src/model_checker/builder').glob('*.py'):
        with open(filepath) as f:
            tree = ast.parse(f.read())
        
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                complexity = radon.cc_visit(node)
                assert complexity < 10, \
                    f"{filepath}::{node.name} complexity {complexity}"

def test_method_length():
    """Ensure all methods < 50 lines."""
    # Implementation
```

### 6.3 Phase 3 Validation

```bash
# Check module sizes
wc -l src/model_checker/builder/*.py | sort -n

# Test coverage
pytest --cov=model_checker.builder --cov-report=term-missing

# Performance benchmarks
pytest -m benchmark --benchmark-only
```

### 6.4 Phase 4 Validation

```python
# Test interfaces
def test_interface_compliance():
    """Verify all components implement interfaces."""
    assert isinstance(BuildModule(), IBuilder)
    assert isinstance(ModelRunner(), IRunner)
    assert isinstance(Validator(), IValidator)

# Test dependency injection
def test_dependency_injection():
    """Verify DI container works correctly."""
    container = DependencyContainer()
    container.register('test', lambda: "test_value")
    assert container.resolve('test') == "test_value"

# Test no circular imports
def test_no_circular_imports():
    """Verify no circular dependencies."""
    import importlib
    # Implementation to detect circular imports
```

---

## 7. Risk Mitigation

### 7.1 Rollback Plan

1. **Git branches**: Create feature branch for each phase
2. **Backup files**: Script creates .backup files
3. **Test suite**: Run after each change
4. **Incremental changes**: Small, tested commits

### 7.2 Testing Strategy

1. **Unit tests**: Run after each file change
2. **Integration tests**: Run after each phase
3. **Performance tests**: Run before/after optimization
4. **Manual testing**: Interactive CLI testing

### 7.3 Communication Plan

1. **Daily updates**: Progress on current phase
2. **Phase completion**: Review meeting
3. **Issues**: Immediate escalation
4. **Documentation**: Update as changes made

---

## 8. Success Metrics

### 8.1 Quantitative Metrics

| Metric | Current | Target | Measurement |
|--------|---------|--------|-------------|
| Import Compliance | 20% | 100% | Grep for absolute imports |
| Method Complexity | ≤15 | <10 | Radon complexity |
| Method Length | ≤187 | <50 | Line count |
| Module Size | ≤708 | <500 | Line count |
| Test Coverage | 85% | >90% | pytest-cov |
| Test Execution | 5.9s | <10s | pytest timing |
| Mock Usage | High | 50% reduction | Mock count |

### 8.2 Qualitative Metrics

- **Code clarity**: Peer review feedback
- **Maintainability**: Time to add features
- **Debugging**: Time to fix bugs
- **Onboarding**: New developer understanding

---

## 9. Implementation Schedule

### Week 1
- **Day 1**: Phase 1 - Critical import fixes
- **Day 2-3**: Phase 2 - Method refactoring
- **Day 4-5**: Phase 2 - Complexity reduction

### Week 2
- **Day 1-2**: Phase 3 - Module splitting
- **Day 3-4**: Phase 3 - Test improvements
- **Day 5**: Testing and validation

### Week 3
- **Day 1-2**: Phase 3 - Performance tests
- **Day 3-5**: Bug fixes and documentation

### Month 2
- **Week 1**: Phase 4 - Interfaces
- **Week 2**: Phase 4 - Dependency injection
- **Week 3**: Phase 4 - Circular dependency fixes
- **Week 4**: Final testing and documentation

---

## 10. Appendices

### Appendix A: File Change Summary

| File | Changes | Priority | Effort |
|------|---------|----------|--------|
| example.py | 5 imports, split methods | P0/P1 | 1h |
| module.py | 7 imports, split __init__ | P0/P1 | 1.5h |
| runner.py | 2 imports, split into 2 files | P0/P2 | 3h |
| validation.py | 3 imports | P0 | 0.5h |
| loader.py | 4 imports, extract methods | P0/P1 | 1h |
| comparison.py | 1 import, split methods | P0/P1 | 1h |
| project.py | 2 imports | P0 | 0.5h |
| translation.py | 3 imports | P0 | 0.5h |
| z3_utils.py | 2 imports | P0 | 0.5h |
| __init__.py | 6 imports | P0 | 0.5h |

### Appendix B: Tool Configuration

#### isort Configuration
```ini
[settings]
profile = black
import_heading_stdlib = Standard library imports
import_heading_thirdparty = Third-party imports
import_heading_firstparty = Local imports
force_single_line = true
lines_after_imports = 2
```

#### pytest Configuration
```ini
[tool.pytest.ini_options]
markers = [
    "benchmark: Performance benchmark tests",
    "slow: Slow running tests",
]
testpaths = ["src/model_checker/builder/tests"]
```

#### Pre-commit Hooks
```yaml
repos:
  - repo: https://github.com/pycqa/isort
    rev: 5.12.0
    hooks:
      - id: isort
        args: ["--profile", "black"]
  
  - repo: https://github.com/psf/black
    rev: 23.0.0
    hooks:
      - id: black
  
  - repo: local
    hooks:
      - id: complexity-check
        name: Check Complexity
        entry: python scripts/check_complexity.py
        language: python
        files: \.py$
```

### Appendix C: Validation Scripts

```python
# scripts/validate_phase1.py
"""Validate Phase 1 completion."""

import subprocess
import sys
from pathlib import Path

def check_imports():
    """Check for absolute imports."""
    result = subprocess.run(
        ['grep', '-r', 'from model_checker.builder', 
         'src/model_checker/builder/', '--exclude-dir=tests'],
        capture_output=True
    )
    if result.returncode == 0:
        print("FAIL: Absolute imports found")
        print(result.stdout.decode())
        return False
    return True

def check_tests():
    """Run test suite."""
    result = subprocess.run(
        ['python', '-m', 'pytest', 
         'src/model_checker/builder/tests/', '-q'],
        capture_output=True
    )
    return result.returncode == 0

if __name__ == '__main__':
    if check_imports() and check_tests():
        print("Phase 1 validation: PASSED")
        sys.exit(0)
    else:
        print("Phase 1 validation: FAILED")
        sys.exit(1)
```

---

**Document Status**: Complete  
**Implementation Status**: Ready to begin  
**Next Action**: Begin Phase 1 implementation

[← Back to Plans](README.md) | [Related: Quality Audit →](../research/025_builder_package_quality_audit.md)