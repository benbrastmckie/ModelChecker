# Plan 084: Builder Package Enhancement

**Status:** Approved  
**Priority:** P2 (High)  
**Timeline:** 2 weeks  
**Compliance Score:** 78/100 → 90/100  

## Executive Summary

The builder package orchestrates model checking operations and has good structure with excellent test coverage (2.69 ratio) and robust error handling (21 exception classes). However, it needs type hints for 419 functions (80% missing) and has 4 methods exceeding complexity guidelines. This enhancement focuses on comprehensive type annotation and method refactoring.

## Current State Analysis

### Package Structure
```
builder/
├── __init__.py              # Package exports (67 lines)
├── module.py               # Module building (589 lines)
├── runner.py               # Execution runner (456 lines)
├── validator.py            # Input validation (312 lines)
├── config.py               # Configuration (234 lines)
├── errors.py               # 21 exception classes (289 lines) ✓
├── utils.py                # Builder utilities (178 lines)
├── progress.py             # Progress tracking (245 lines)
├── results.py              # Result management (367 lines)
├── cache.py                # Build caching (298 lines)
├── optimizer.py            # Optimization (412 lines)
├── parallel.py             # Parallel execution (356 lines)
├── profiler.py             # Performance profiling (234 lines)
└── tests/                  # Test suite (35 files, 9,604 lines) ✓
```

### Current Compliance
- **Type Hints:** 105/524 functions (20.0%) ❌
- **Error Handling:** 21 custom exceptions ✓
- **Method Complexity:** 4 methods > 75 lines ⚠️
- **Technical Debt:** 0 TODO/FIXME ✓
- **Test Coverage:** Excellent (2.69 ratio) ✓
- **Documentation:** Comprehensive README ✓

## Implementation Strategy

Given the package size and importance, we'll take a systematic approach:
1. Add type hints module by module
2. Refactor complex methods
3. Maintain excellent test coverage throughout

## Week 1: Core Modules and Types

### Day 1-2: Type System Foundation

#### Create types.py for Builder Types
```python
# builder/types.py
from typing import (
    TypeVar, Dict, List, Optional, Union, Any, 
    Callable, Protocol, runtime_checkable, TypedDict
)
from dataclasses import dataclass
from enum import Enum
import z3

# Type variables
T = TypeVar('T')
R = TypeVar('R')  # Result type

# Enums
class BuildStatus(Enum):
    """Build execution status."""
    PENDING = "pending"
    RUNNING = "running"
    SUCCESS = "success"
    FAILED = "failed"
    TIMEOUT = "timeout"

class ValidationLevel(Enum):
    """Validation strictness levels."""
    NONE = "none"
    BASIC = "basic"
    STRICT = "strict"
    PARANOID = "paranoid"

# Type aliases
ModulePath = str
ExampleName = str
TheoryName = str
BuildResult = Union['SuccessResult', 'FailureResult']

# Typed dictionaries
class BuildConfig(TypedDict):
    """Configuration for build process."""
    module_path: str
    theory: str
    timeout: int
    parallel: bool
    cache_enabled: bool
    validation_level: str

@dataclass
class BuildContext:
    """Context for build execution."""
    config: BuildConfig
    start_time: float
    variables: Dict[str, Any]
    cache_key: Optional[str] = None

# Protocols
@runtime_checkable
class Buildable(Protocol):
    """Protocol for buildable objects."""
    def build(self) -> BuildResult: ...
    def validate(self) -> bool: ...

@runtime_checkable
class Cacheable(Protocol):
    """Protocol for cacheable operations."""
    def get_cache_key(self) -> str: ...
    def is_cache_valid(self) -> bool: ...

# Callback types
ProgressCallback = Callable[[str, float], None]
ErrorHandler = Callable[[Exception], Optional[BuildResult]]
```

### Day 3-4: module.py Type Hints (89 functions)

```python
# Before (module.py)
class BuildModule:
    def __init__(self, module_flags):
        self.module_flags = module_flags
        self.module_path = module_flags.file_path
        self.module = None
    
    def load_module(self):
        spec = importlib.util.spec_from_file_location(
            self.module_name, self.module_path
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module

# After
from typing import Dict, List, Optional, Any, Union
import importlib.util
from types import ModuleType
from .types import (
    BuildConfig, BuildContext, BuildResult, 
    ExampleName, TheoryName, ModulePath
)
from .errors import BuilderError, ModuleLoadError

class BuildModule:
    """Manages module building and execution."""
    
    def __init__(self, module_flags: BuildConfig) -> None:
        """Initialize build module.
        
        Args:
            module_flags: Build configuration
        """
        self.module_flags: BuildConfig = module_flags
        self.module_path: ModulePath = module_flags['module_path']
        self.module: Optional[ModuleType] = None
        self.context: Optional[BuildContext] = None
    
    def load_module(self) -> ModuleType:
        """Load Python module from path.
        
        Returns:
            Loaded module
            
        Raises:
            ModuleLoadError: If module cannot be loaded
        """
        try:
            spec = importlib.util.spec_from_file_location(
                self.module_name, self.module_path
            )
            if spec is None or spec.loader is None:
                raise ModuleLoadError(
                    f"Cannot create spec for {self.module_path}"
                )
            
            module: ModuleType = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
        except Exception as e:
            raise ModuleLoadError(
                f"Failed to load module: {e}",
                context={'path': self.module_path}
            )
    
    def extract_examples(
        self
    ) -> Dict[ExampleName, Dict[str, Any]]:
        """Extract examples from module."""
        ...
    
    def build_example(
        self,
        example_name: ExampleName,
        timeout: Optional[int] = None
    ) -> BuildResult:
        """Build a single example."""
        ...
```

### Day 5: runner.py Type Hints (67 functions) + Complexity Refactor

```python
# Before - Complex method (112 lines)
def execute_build(self, config, examples):
    # Validation
    # ... 30 lines of validation
    
    # Setup
    # ... 25 lines of setup
    
    # Execution
    # ... 35 lines of execution
    
    # Cleanup
    # ... 22 lines of cleanup

# After - Refactored
from typing import List, Dict, Optional, Tuple
from .types import BuildConfig, BuildResult, ExampleName

class BuildRunner:
    """Executes build operations."""
    
    def execute_build(
        self,
        config: BuildConfig,
        examples: List[ExampleName]
    ) -> List[BuildResult]:
        """Execute build for examples.
        
        Args:
            config: Build configuration
            examples: Examples to build
            
        Returns:
            List of build results
        """
        # Refactored into smaller methods
        self._validate_build_inputs(config, examples)
        context = self._setup_build_context(config)
        
        try:
            results = self._execute_examples(examples, context)
            return results
        finally:
            self._cleanup_build_context(context)
    
    def _validate_build_inputs(
        self,
        config: BuildConfig,
        examples: List[ExampleName]
    ) -> None:
        """Validate build inputs (30 lines → separate method)."""
        ...
    
    def _setup_build_context(
        self,
        config: BuildConfig
    ) -> BuildContext:
        """Setup build context (25 lines → separate method)."""
        ...
    
    def _execute_examples(
        self,
        examples: List[ExampleName],
        context: BuildContext
    ) -> List[BuildResult]:
        """Execute examples (35 lines → separate method)."""
        ...
    
    def _cleanup_build_context(
        self,
        context: BuildContext
    ) -> None:
        """Cleanup after build (22 lines → separate method)."""
        ...
```

## Week 2: Remaining Modules

### Day 6-7: validator.py and config.py (78 functions)

```python
# validator.py type hints
from typing import Any, Dict, List, Optional, Tuple, Union
from .types import BuildConfig, ValidationLevel
from .errors import ValidationError

class BuildValidator:
    """Validates build inputs and configurations."""
    
    def __init__(
        self,
        level: ValidationLevel = ValidationLevel.BASIC
    ) -> None:
        """Initialize validator with level."""
        self.level: ValidationLevel = level
    
    def validate_config(
        self,
        config: BuildConfig
    ) -> Tuple[bool, Optional[str]]:
        """Validate build configuration.
        
        Returns:
            Tuple of (is_valid, error_message)
        """
        ...
    
    def validate_module(
        self,
        module_path: str
    ) -> bool:
        """Validate module file exists and is valid."""
        ...

# config.py type hints  
class ConfigManager:
    """Manages build configurations."""
    
    def load_config(
        self,
        path: Optional[str] = None
    ) -> BuildConfig:
        """Load configuration from file or defaults."""
        ...
    
    def merge_configs(
        self,
        base: BuildConfig,
        override: Dict[str, Any]
    ) -> BuildConfig:
        """Merge configurations with overrides."""
        ...
```

### Day 8: utils.py and progress.py (52 functions)

```python
# utils.py with types
from typing import Optional, List, Dict, Any
from pathlib import Path

def find_module_files(
    directory: Union[str, Path],
    pattern: str = "*.py"
) -> List[Path]:
    """Find module files in directory."""
    ...

def format_build_output(
    result: BuildResult,
    verbose: bool = False
) -> str:
    """Format build result for display."""
    ...

# progress.py with types
class ProgressTracker:
    """Tracks build progress."""
    
    def __init__(
        self,
        total: int,
        callback: Optional[ProgressCallback] = None
    ) -> None:
        """Initialize progress tracker."""
        self.total: int = total
        self.completed: int = 0
        self.callback: Optional[ProgressCallback] = callback
    
    def update(
        self,
        message: str,
        increment: int = 1
    ) -> None:
        """Update progress."""
        ...
```

### Day 9: results.py and cache.py (84 functions)

```python
# results.py with types
@dataclass
class SuccessResult:
    """Successful build result."""
    example: ExampleName
    model: Any
    time_elapsed: float
    metadata: Dict[str, Any] = field(default_factory=dict)

@dataclass
class FailureResult:
    """Failed build result."""
    example: ExampleName
    error: Exception
    time_elapsed: float
    traceback: Optional[str] = None

class ResultManager:
    """Manages build results."""
    
    def store_result(
        self,
        result: BuildResult
    ) -> None:
        """Store build result."""
        ...
    
    def get_summary(self) -> Dict[str, Any]:
        """Get results summary."""
        ...

# cache.py with types
class BuildCache:
    """Caches build results."""
    
    def get(
        self,
        key: str
    ) -> Optional[BuildResult]:
        """Get cached result."""
        ...
    
    def set(
        self,
        key: str,
        result: BuildResult,
        ttl: Optional[int] = None
    ) -> None:
        """Cache result with optional TTL."""
        ...
```

### Day 10-11: optimizer.py, parallel.py, profiler.py (91 functions)

```python
# optimizer.py with types and complexity refactor
class BuildOptimizer:
    """Optimizes build execution."""
    
    # Refactor complex method (98 lines → 3 methods)
    def optimize_execution_plan(
        self,
        examples: List[ExampleName],
        dependencies: Dict[ExampleName, List[ExampleName]]
    ) -> List[List[ExampleName]]:
        """Optimize execution order.
        
        Returns:
            Batches of examples to execute
        """
        graph = self._build_dependency_graph(dependencies)
        layers = self._topological_layers(graph)
        return self._optimize_layers(layers)
    
    def _build_dependency_graph(
        self,
        dependencies: Dict[ExampleName, List[ExampleName]]
    ) -> Dict[ExampleName, Set[ExampleName]]:
        """Build dependency graph (35 lines)."""
        ...
    
    def _topological_layers(
        self,
        graph: Dict[ExampleName, Set[ExampleName]]
    ) -> List[List[ExampleName]]:
        """Create topological layers (38 lines)."""
        ...
    
    def _optimize_layers(
        self,
        layers: List[List[ExampleName]]
    ) -> List[List[ExampleName]]:
        """Optimize within layers (25 lines)."""
        ...

# parallel.py with types
class ParallelExecutor:
    """Executes builds in parallel."""
    
    def execute_parallel(
        self,
        tasks: List[Callable[[], BuildResult]],
        max_workers: Optional[int] = None
    ) -> List[BuildResult]:
        """Execute tasks in parallel."""
        ...

# profiler.py with types  
class BuildProfiler:
    """Profiles build performance."""
    
    def profile(
        self,
        func: Callable[[], T]
    ) -> Tuple[T, Dict[str, float]]:
        """Profile function execution."""
        ...
```

### Day 12-13: Testing and Validation

#### Verify Type Coverage
```bash
# Check type coverage
mypy src/model_checker/builder --strict

# Verify all functions typed
python scripts/check_type_coverage.py builder

# Expected output: 524/524 functions typed (100%)
```

#### Test Refactored Methods
```python
# tests/test_complexity_refactor.py
def test_execute_build_refactored():
    """Test refactored execute_build maintains behavior."""
    runner = BuildRunner()
    config = create_test_config()
    examples = ['ex1', 'ex2']
    
    results = runner.execute_build(config, examples)
    
    # Verify same behavior as before
    assert len(results) == 2
    assert all(isinstance(r, BuildResult) for r in results)

def test_optimize_execution_plan_refactored():
    """Test refactored optimizer maintains behavior."""
    optimizer = BuildOptimizer()
    examples = ['a', 'b', 'c']
    deps = {'b': ['a'], 'c': ['a', 'b']}
    
    plan = optimizer.optimize_execution_plan(examples, deps)
    
    # Verify correct ordering
    assert plan[0] == ['a']
    assert plan[1] == ['b']
    assert plan[2] == ['c']
```

### Day 14: Final Review

- Run full test suite
- Generate compliance report
- Update documentation

## Method Complexity Refactoring

### Methods to Refactor

1. **module.py::BuildModule.process_theory()** - 87 lines
   - Split into: validate_theory, setup_theory, execute_theory

2. **runner.py::BuildRunner.execute_build()** - 112 lines
   - Split into: validate_inputs, setup_context, execute, cleanup

3. **optimizer.py::BuildOptimizer.optimize_execution_plan()** - 98 lines
   - Split into: build_graph, topological_layers, optimize_layers

4. **results.py::ResultManager.generate_report()** - 79 lines
   - Split into: collect_stats, format_sections, write_report

## Success Metrics

### Required Outcomes
- Type hints: 105/524 → 524/524 functions (100%)
- Complex methods: 4 → 0 (all under 75 lines)
- Test coverage: Maintain 2.69 ratio
- Compliance score: 78/100 → 90/100

### Quality Improvements
- Full IDE support for builder operations
- Better maintainability with smaller methods
- Improved debugging with typed structures
- Clearer interfaces with protocols

## Definition of Done

- [ ] All 524 functions have complete type hints
- [ ] types.py created with comprehensive type definitions
- [ ] 4 complex methods refactored into smaller units
- [ ] mypy passes with --strict flag
- [ ] All existing tests pass (35 test files)
- [ ] New tests for refactored methods
- [ ] Test coverage ratio ≥ 2.69 maintained
- [ ] Documentation updated for new types
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Research 041: Framework Quality and Compliance Audit](../research/041_framework_quality_compliance_audit.md)
- [Method Complexity Guidelines](../../../maintenance/METHOD_COMPLEXITY.md)