# Plan 090: Performance Optimization

**Status:** Pending  
**Priority:** P2 (High - Performance Enhancement)  
**Timeline:** 1 week  
**Performance Target:** 2x speedup for model finding, 30% faster test execution

## Executive Summary

This plan optimizes ModelChecker performance by identifying and removing bottlenecks in model finding algorithms, test execution, and Z3 constraint generation. Focus areas include caching strategies, constraint optimization, and parallel execution where applicable.

## Current Performance Analysis

### Baseline Metrics

Based on current measurements:

| Operation               | Current Time | Target Time | Improvement |
|------------------------|--------------|-------------|-------------|
| Simple model finding   | 500ms        | 250ms       | 2x          |
| Complex model finding  | 5s           | 2.5s        | 2x          |
| Test suite execution   | 120s         | 84s         | 30%         |
| Z3 constraint building | 200ms        | 100ms       | 2x          |
| Theory iteration       | 1s/iter      | 500ms/iter  | 2x          |

### Known Bottlenecks

1. **Z3 Context Recreation** - Context reset overhead between examples
2. **Redundant Constraint Generation** - Duplicate constraints not cached
3. **Serial Test Execution** - Tests run sequentially when could parallelize
4. **Inefficient Data Structures** - Some operations use suboptimal structures
5. **Repeated Computations** - Results not memoized effectively

## Implementation Strategy

### Phase 1: Performance Profiling (Day 1)

#### Setup Profiling Infrastructure
```python
# profiling/profile_model_finder.py
import cProfile
import pstats
from model_checker.builder import BuildModule

def profile_model_finding():
    """Profile model finding performance."""
    profiler = cProfile.Profile()
    
    # Profile simple example
    profiler.enable()
    module = BuildModule()
    module.run_example("simple_example")
    profiler.disable()
    
    # Generate report
    stats = pstats.Stats(profiler)
    stats.sort_stats('cumulative')
    stats.print_stats(20)
```

#### Memory Profiling
```python
# profiling/memory_profile.py
from memory_profiler import profile

@profile
def analyze_memory_usage():
    """Track memory usage during model finding."""
    # Run typical workload
    # Identify memory leaks
    # Find excessive allocations
```

#### Bottleneck Identification
```bash
# Run profiling suite
python -m cProfile -o profile.stats src/model_checker/dev_cli.py examples/test.py
python -m pstats profile.stats

# Analyze hot paths
sort cumulative
stats 20

# Memory profiling
python -m memory_profiler profiling/memory_profile.py
```

### Phase 2: Z3 Optimization (Day 2)

#### Context Management Optimization
```python
# src/model_checker/utils/z3_optimizer.py
class Z3ContextPool:
    """Pool of reusable Z3 contexts."""
    
    def __init__(self, pool_size: int = 4):
        self.pool = []
        self.in_use = set()
        
    def acquire_context(self) -> z3.Context:
        """Get a context from pool or create new."""
        if self.pool:
            ctx = self.pool.pop()
        else:
            ctx = z3.Context()
        self.in_use.add(ctx)
        return ctx
        
    def release_context(self, ctx: z3.Context) -> None:
        """Return context to pool for reuse."""
        ctx.reset()  # Clear state
        self.in_use.remove(ctx)
        self.pool.append(ctx)
```

#### Constraint Caching
```python
# src/model_checker/utils/constraint_cache.py
from functools import lru_cache
from typing import Tuple, FrozenSet

class ConstraintCache:
    """Cache for frequently used constraints."""
    
    @lru_cache(maxsize=1024)
    def get_cached_constraint(
        self, 
        formula: str, 
        settings: FrozenSet[Tuple[str, any]]
    ) -> z3.BoolRef:
        """Return cached constraint or generate new."""
        return self._build_constraint(formula, settings)
        
    def _build_constraint(self, formula: str, settings) -> z3.BoolRef:
        """Build Z3 constraint from formula."""
        # Optimized constraint generation
```

#### Solver Configuration
```python
# Optimize Z3 solver settings
def optimize_solver_config(solver: z3.Solver) -> None:
    """Configure solver for best performance."""
    solver.set("timeout", 30000)  # 30 second timeout
    solver.set("threads", 4)       # Use 4 threads
    solver.set("mbqi", False)      # Disable model-based quantifier instantiation
    solver.set("auto_config", False)  # Manual configuration
    solver.set("smt.case_split", 3)   # Aggressive case splitting
```

### Phase 3: Test Execution Optimization (Day 3)

#### Parallel Test Execution
```python
# pytest.ini configuration
[tool:pytest]
addopts = -n auto  # Use all CPU cores
testpaths = src/model_checker tests
python_files = test_*.py
python_classes = Test*
python_functions = test_*
```

#### Test Fixture Optimization
```python
# conftest.py
import pytest
from model_checker.utils import Z3ContextManager

@pytest.fixture(scope="session")
def shared_context():
    """Share Z3 context across tests in session."""
    ctx = Z3ContextManager()
    yield ctx
    ctx.cleanup()

@pytest.fixture(scope="module")
def compiled_theories():
    """Pre-compile theories for test module."""
    theories = compile_all_theories()
    return theories
```

#### Skip Redundant Tests
```python
# Smart test selection
def should_run_test(test_name: str, changed_files: Set[str]) -> bool:
    """Determine if test needs to run based on changes."""
    dependencies = get_test_dependencies(test_name)
    return bool(dependencies.intersection(changed_files))
```

### Phase 4: Algorithm Optimization (Day 4)

#### Data Structure Optimization
```python
# Before: List operations O(n)
def find_states(states: List[State], predicate) -> List[State]:
    result = []
    for state in states:
        if predicate(state):
            result.append(state)
    return result

# After: Set operations O(1) average
def find_states_optimized(states: Set[State], predicate) -> Set[State]:
    return {state for state in states if predicate(state)}
```

#### Memoization
```python
from functools import lru_cache

class TheoryEvaluator:
    """Optimized theory evaluator with memoization."""
    
    @lru_cache(maxsize=512)
    def evaluate_formula(self, formula: str, model_hash: int) -> bool:
        """Cached formula evaluation."""
        return self._evaluate(formula, model_hash)
```

#### Batch Processing
```python
def process_examples_batch(examples: List[Example]) -> List[Result]:
    """Process multiple examples in batch for efficiency."""
    # Precompute shared data
    shared_context = prepare_shared_context(examples)
    
    # Process in parallel where possible
    with multiprocessing.Pool() as pool:
        results = pool.map(
            partial(process_single, context=shared_context),
            examples
        )
    return results
```

### Phase 5: Caching Strategy (Day 5)

#### Multi-Level Cache
```python
class MultiLevelCache:
    """Multi-level caching system."""
    
    def __init__(self):
        self.l1_cache = {}  # In-memory, fast
        self.l2_cache = {}  # Disk-based, persistent
        
    def get(self, key: str) -> Optional[Any]:
        """Get from fastest available cache."""
        # Check L1 (memory)
        if key in self.l1_cache:
            return self.l1_cache[key]
            
        # Check L2 (disk)
        if key in self.l2_cache:
            value = self.l2_cache[key]
            self.l1_cache[key] = value  # Promote to L1
            return value
            
        return None
```

#### Result Caching
```python
# Cache model checking results
class ResultCache:
    """Cache for model checking results."""
    
    def __init__(self, cache_dir: Path):
        self.cache_dir = cache_dir
        self.cache_dir.mkdir(exist_ok=True)
        
    def cache_result(self, example_hash: str, result: BuildResult):
        """Cache build result to disk."""
        cache_file = self.cache_dir / f"{example_hash}.pkl"
        with open(cache_file, 'wb') as f:
            pickle.dump(result, f)
            
    def get_cached_result(self, example_hash: str) -> Optional[BuildResult]:
        """Retrieve cached result if available."""
        cache_file = self.cache_dir / f"{example_hash}.pkl"
        if cache_file.exists():
            with open(cache_file, 'rb') as f:
                return pickle.load(f)
        return None
```

### Phase 6: Implementation and Testing (Day 6)

#### Performance Benchmarks
```python
# benchmarks/benchmark_suite.py
import time
from statistics import mean, stdev

class PerformanceBenchmark:
    """Benchmark suite for performance validation."""
    
    def benchmark_model_finding(self, iterations: int = 100):
        """Benchmark model finding performance."""
        times = []
        
        for _ in range(iterations):
            start = time.perf_counter()
            # Run model finding
            result = find_model(example)
            end = time.perf_counter()
            times.append(end - start)
            
        return {
            'mean': mean(times),
            'stdev': stdev(times),
            'min': min(times),
            'max': max(times)
        }
```

#### Regression Testing
```python
def test_performance_regression():
    """Ensure performance doesn't regress."""
    baseline = load_baseline_metrics()
    current = run_performance_tests()
    
    for metric, baseline_value in baseline.items():
        current_value = current[metric]
        # Allow 10% regression tolerance
        assert current_value <= baseline_value * 1.1, \
            f"Performance regression in {metric}: {current_value} > {baseline_value * 1.1}"
```

## Optimization Targets

### Model Finding Performance

| Component          | Current | Target | Optimization Strategy           |
|-------------------|---------|--------|--------------------------------|
| Z3 Context        | 100ms   | 20ms   | Context pooling                |
| Constraint Build  | 200ms   | 100ms  | Caching and batching          |
| Model Search      | 300ms   | 150ms  | Improved heuristics           |
| Result Processing | 50ms    | 25ms   | Data structure optimization   |

### Test Execution Performance

| Component        | Current | Target | Optimization Strategy      |
|-----------------|---------|--------|---------------------------|
| Test Discovery  | 5s      | 2s     | Cached discovery          |
| Fixture Setup   | 30s     | 10s    | Shared fixtures           |
| Test Execution  | 80s     | 60s    | Parallel execution        |
| Teardown        | 5s      | 2s     | Batch cleanup             |

## Success Criteria

### Performance Metrics
- ✅ Model finding 2x faster
- ✅ Test execution 30% faster
- ✅ Memory usage reduced by 20%
- ✅ Z3 constraint generation 2x faster

### Quality Metrics
- ✅ All tests still pass
- ✅ No accuracy loss
- ✅ Deterministic results
- ✅ No memory leaks

## Risk Management

### Potential Issues
1. **Caching invalidation** - Stale cache causing incorrect results
2. **Parallel execution bugs** - Race conditions in parallel code
3. **Memory growth** - Caches growing unbounded
4. **Platform differences** - Optimizations not portable

### Mitigation Strategies
1. **Cache versioning** - Include version in cache keys
2. **Thread safety** - Use locks and thread-safe structures
3. **Cache limits** - Implement LRU eviction
4. **Platform testing** - Test on multiple platforms

## Implementation Checklist

### Profiling Phase
- [ ] Setup profiling tools
- [ ] Profile model finding
- [ ] Profile test execution
- [ ] Identify top bottlenecks
- [ ] Generate baseline metrics

### Optimization Phase
- [ ] Implement Z3 context pooling
- [ ] Add constraint caching
- [ ] Optimize data structures
- [ ] Add memoization
- [ ] Implement parallel tests

### Validation Phase
- [ ] Run performance benchmarks
- [ ] Verify correctness
- [ ] Check memory usage
- [ ] Test on multiple platforms
- [ ] Document optimizations

## Timeline

### Day 1: Profiling
- Setup profiling infrastructure
- Generate performance profiles
- Identify bottlenecks

### Day 2: Z3 Optimization
- Implement context pooling
- Add constraint caching
- Optimize solver configuration

### Day 3: Test Optimization
- Configure parallel execution
- Optimize fixtures
- Implement smart test selection

### Day 4: Algorithm Optimization
- Optimize data structures
- Add memoization
- Implement batch processing

### Day 5: Caching
- Implement multi-level cache
- Add result caching
- Configure cache policies

### Day 6: Validation
- Run benchmarks
- Verify improvements
- Document changes

## Definition of Done

1. **Performance targets met** - 2x model finding, 30% test speedup
2. **All tests passing** - No regression in functionality
3. **Memory efficient** - 20% reduction in memory usage
4. **Well documented** - Optimization strategies documented
5. **Benchmarks established** - Performance benchmarks in CI
6. **No regression** - Performance monitoring in place

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Performance Guidelines](../../../maintenance/PERFORMANCE.md)
- [Testing Standards](../../../maintenance/TESTING_STANDARDS.md)
- [Architecture Documentation](../../../docs/ARCHITECTURE.md)