# Performance Optimization Guidelines

[← Back to Implementation](README.md) | [Development Workflow →](DEVELOPMENT_WORKFLOW.md) | [Refactoring →](REFACTORING.md)

## Table of Contents

1. [Overview](#overview)
2. [Performance Targets](#performance-targets)
3. [Z3 Solver Optimization](#z3-solver-optimization)
4. [Memory Management](#memory-management)
5. [Component-Specific Benchmarks](#component-specific-benchmarks)
6. [Progress System Performance](#progress-system-performance)
7. [Caching Strategies](#caching-strategies)
8. [Resource Limits](#resource-limits)
9. [Profiling Methodology](#profiling-methodology)
10. [Performance Regression Detection](#performance-regression-detection)
11. [Timing Consistency Requirements](#timing-consistency-requirements)
12. [Optimization Patterns](#optimization-patterns)
13. [Success Metrics](#success-metrics)
14. [Troubleshooting Performance Issues](#troubleshooting-performance-issues)

## Overview

This document provides comprehensive performance optimization guidelines for the ModelChecker framework, focusing on measurable targets, systematic optimization approaches, and maintaining consistent performance across different use cases.

**Core Performance Philosophy**: Optimize for the common case while maintaining predictable performance bounds for all scenarios. Every optimization must be measurable and have clear success criteria.

## Performance Targets

### Primary Performance Goals

| Component | Operation | Target Time | Memory Limit | Success Rate |
|-----------|-----------|-------------|--------------|--------------|
| **Simple Models** | N≤4, basic constraints | < 0.5s | < 10MB | > 99% |
| **Medium Models** | N≤8, moderate complexity | < 2.0s | < 50MB | > 95% |
| **Complex Models** | N≤16, full constraints | < 10.0s | < 200MB | > 90% |
| **Progress Updates** | Animation refresh | < 100ms | < 1MB | 100% |
| **Theory Loading** | Cold start | < 1.0s | < 20MB | 100% |
| **Syntax Parsing** | Formula parsing | < 0.1s | < 5MB | > 99% |

### Scaling Targets

Performance should scale predictably with problem size:

```python
# Expected scaling patterns
def expected_time(N):
    """Expected time complexity for N atomic propositions."""
    if N <= 4:
        return 0.1 * (2 ** N)  # Linear in model count
    elif N <= 8:
        return 0.5 * (2 ** (N * 0.8))  # Sub-exponential
    else:
        return min(10.0, 1.0 * (2 ** (N * 0.6)))  # Capped exponential

def expected_memory(N):
    """Expected memory usage for N atomic propositions."""
    base_mb = 5  # Base framework overhead
    model_mb = 0.5 * (2 ** min(N, 10))  # Model storage
    return base_mb + model_mb
```

## Z3 Solver Optimization

### Core Z3 Performance Patterns

The current Z3 optimization patterns from maintenance/PERFORMANCE.md remain the foundation:

#### Variable Minimization

```python
# GOOD - Reuse variables where possible
def create_constraints(n_atoms):
    """Create only necessary variables."""
    atoms = [z3.Bool(f'p_{i}') for i in range(n_atoms)]
    return atoms
    
# PERFORMANCE TARGET: Variable creation < 1ms per 100 variables
def benchmark_variable_creation():
    start = time.perf_counter()
    atoms = [z3.Bool(f'p_{i}') for i in range(100)]
    elapsed = time.perf_counter() - start
    assert elapsed < 0.001, f"Variable creation took {elapsed:.4f}s"
```

#### Bit Vector Size Optimization

```python
def calculate_optimal_bit_size(n_states):
    """Calculate minimum required bit vector size."""
    if n_states <= 0:
        return 1
    return max(1, math.ceil(math.log2(n_states)))

# PERFORMANCE TARGET: Bit size calculation < 1μs
def benchmark_bit_size_calculation():
    start = time.perf_counter()
    for i in range(1000):
        size = calculate_optimal_bit_size(i)
    elapsed = time.perf_counter() - start
    assert elapsed < 0.001, f"1000 calculations took {elapsed:.4f}s"
```

#### Constraint Ordering

```python
# GOOD - Add most restrictive constraints first
def add_constraints_optimally(solver, constraints):
    """Add constraints in order of selectivity."""
    # Sort by estimated selectivity (most restrictive first)
    sorted_constraints = sorted(constraints, key=estimate_selectivity, reverse=True)
    
    for constraint in sorted_constraints:
        solver.add(constraint)
        # Early termination check
        if solver.check() == z3.unsat:
            return z3.unsat
    
    return solver.check()

# PERFORMANCE TARGET: Constraint ordering < 10ms for 100 constraints
```

#### Solver Timeout Management

```python
def solve_with_adaptive_timeout(constraints, base_timeout=1000):
    """Solve with timeout that adapts to problem complexity."""
    # Estimate complexity
    complexity = estimate_constraint_complexity(constraints)
    timeout_ms = min(base_timeout * complexity, 30000)  # Cap at 30s
    
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    
    for constraint in constraints:
        solver.add(constraint)
    
    return solver.check(), timeout_ms

# PERFORMANCE TARGET: Timeout handling overhead < 1ms
```

## Memory Management

### Memory Performance Targets

| Operation | Peak Memory | Cleanup Time | Memory Growth |
|-----------|-------------|--------------|---------------|
| Simple model (N≤4) | < 10MB | < 10ms | < 1MB/iteration |
| Medium model (N≤8) | < 50MB | < 50ms | < 5MB/iteration |
| Complex model (N≤16) | < 200MB | < 100ms | < 10MB/iteration |
| Progress animation | < 1MB | < 1ms | 0MB (stable) |

### Memory Management Patterns

#### Systematic Cleanup

```python
class PerformantModelChecker:
    """Model checker with aggressive memory management."""
    
    def __init__(self):
        self.solver = z3.Solver()
        self._temp_constraints = []
        self._memory_threshold = 100 * 1024 * 1024  # 100MB
    
    def check_model(self, constraints):
        """Check model with memory monitoring."""
        try:
            # Monitor memory before operation
            initial_memory = self._get_memory_usage()
            
            result = self._solve(constraints)
            
            # Check memory growth
            final_memory = self._get_memory_usage()
            growth = final_memory - initial_memory
            
            if growth > self._memory_threshold:
                logger.warning(f"High memory growth: {growth/1024/1024:.1f}MB")
            
            return result
        finally:
            # Always clean up
            self._cleanup()
    
    def _cleanup(self):
        """Aggressive cleanup with timing."""
        cleanup_start = time.perf_counter()
        
        self.solver.reset()
        self._temp_constraints.clear()
        
        # Force garbage collection for large models
        if self._get_memory_usage() > self._memory_threshold:
            gc.collect()
        
        cleanup_time = time.perf_counter() - cleanup_start
        if cleanup_time > 0.1:  # 100ms threshold
            logger.warning(f"Slow cleanup: {cleanup_time:.3f}s")

# PERFORMANCE TARGET: Cleanup < 100ms, memory growth < 10MB per operation
```

#### Generator-Based Processing

```python
def generate_models_efficiently(constraints, max_models):
    """Memory-efficient model generation."""
    solver = z3.Solver()
    solver.add(constraints)
    
    count = 0
    memory_baseline = get_memory_usage()
    
    while count < max_models:
        check_start = time.perf_counter()
        
        if solver.check() == z3.sat:
            model = solver.model()
            
            # Memory check
            current_memory = get_memory_usage()
            if current_memory - memory_baseline > 50 * 1024 * 1024:  # 50MB
                logger.warning("High memory usage in generator")
                gc.collect()
                memory_baseline = get_memory_usage()
            
            yield model
            
            # Block this model
            block = z3.Not(z3.And([v() == model[v] for v in model]))
            solver.add(block)
            count += 1
            
            # Performance check
            check_time = time.perf_counter() - check_start
            if check_time > 2.0:  # 2s threshold
                logger.warning(f"Slow model generation: {check_time:.3f}s")
        else:
            break

# PERFORMANCE TARGET: < 50MB memory growth per 100 models
```

## Component-Specific Benchmarks

### Builder Module Performance

```python
class BuilderPerformanceBenchmarks:
    """Performance benchmarks for Builder module."""
    
    @benchmark(target_time=0.5, target_memory=10)
    def test_simple_build_performance(self):
        """Builder should handle simple examples quickly."""
        premises = ["A"]
        conclusions = ["B"]
        settings = {'N': 3}
        
        start = time.perf_counter()
        result = self.build_and_check(premises, conclusions, settings)
        elapsed = time.perf_counter() - start
        
        assert elapsed < 0.5, f"Simple build took {elapsed:.3f}s"
        return elapsed
    
    @benchmark(target_time=2.0, target_memory=50)
    def test_medium_build_performance(self):
        """Builder should handle medium complexity reasonably."""
        premises = ["(A \\wedge B)", "(C \\vee D)"]
        conclusions = ["(E \\rightarrow F)"]
        settings = {'N': 6}
        
        start = time.perf_counter()
        result = self.build_and_check(premises, conclusions, settings)
        elapsed = time.perf_counter() - start
        
        assert elapsed < 2.0, f"Medium build took {elapsed:.3f}s"
        return elapsed
```

### Iteration Module Performance

```python
class IterationPerformanceBenchmarks:
    """Performance benchmarks for iteration functionality."""
    
    @benchmark(target_time=5.0, target_memory=100)
    def test_multi_model_iteration(self):
        """Iteration should find multiple models efficiently."""
        settings = {
            'N': 4,
            'iterate': 5,
            'max_time': 5
        }
        
        start = time.perf_counter()
        results = self.iterate_models(settings)
        elapsed = time.perf_counter() - start
        
        assert elapsed < 5.0, f"5-model iteration took {elapsed:.3f}s"
        assert len(results) >= 3, "Should find at least 3 models"
        return elapsed, len(results)
```

### Syntax Module Performance

```python
class SyntaxPerformanceBenchmarks:
    """Performance benchmarks for syntax parsing."""
    
    @benchmark(target_time=0.1, target_memory=5)
    def test_formula_parsing_performance(self):
        """Formula parsing should be fast."""
        formulas = [
            "A \\wedge B",
            "(A \\vee B) \\rightarrow C",
            "\\Box (A \\rightarrow \\Diamond B)",
            "((A \\wedge B) \\vee C) \\rightarrow (D \\wedge (E \\vee F))"
        ]
        
        start = time.perf_counter()
        for formula in formulas:
            parsed = self.syntax.parse(formula)
        elapsed = time.perf_counter() - start
        
        assert elapsed < 0.1, f"Parsing 4 formulas took {elapsed:.3f}s"
        return elapsed
```

## Progress System Performance

### Progress Animation Targets

Based on the unified progress system, specific performance requirements:

```python
class ProgressPerformanceBenchmarks:
    """Benchmarks for progress system performance."""
    
    @benchmark(target_time=0.1, target_memory=1)
    def test_progress_update_performance(self):
        """Progress updates should be fast and lightweight."""
        progress = TimeBasedProgress(message="Test", timeout=5.0)
        
        start = time.perf_counter()
        
        # Simulate 50 updates (5 seconds at 100ms intervals)
        for i in range(50):
            progress._update_display()
            time.sleep(0.001)  # Small delay to simulate work
        
        elapsed = time.perf_counter() - start
        
        # Should complete much faster than real-time
        assert elapsed < 0.1, f"50 progress updates took {elapsed:.3f}s"
        return elapsed
    
    @benchmark(target_memory=1)
    def test_progress_memory_stability(self):
        """Progress system should not leak memory."""
        baseline = get_memory_usage()
        
        # Create and destroy multiple progress bars
        for i in range(100):
            progress = TimeBasedProgress(f"Test {i}", timeout=1.0)
            progress.start()
            progress.complete("Done")
            del progress
        
        gc.collect()
        final = get_memory_usage()
        growth = (final - baseline) / (1024 * 1024)  # MB
        
        assert growth < 1.0, f"Progress system leaked {growth:.1f}MB"
        return growth
```

### Thread Performance

```python
@benchmark(target_time=0.01)
def test_thread_creation_performance():
    """Thread creation should be fast."""
    start = time.perf_counter()
    
    # Create and start background thread
    stop_event = threading.Event()
    thread = threading.Thread(target=lambda: None)
    thread.daemon = True
    thread.start()
    thread.join(timeout=0.001)
    
    elapsed = time.perf_counter() - start
    assert elapsed < 0.01, f"Thread creation took {elapsed:.4f}s"
    return elapsed
```

## Caching Strategies

### Multi-Level Caching

```python
class PerformanceCache:
    """Multi-level cache for performance optimization."""
    
    def __init__(self):
        # Level 1: In-memory LRU cache for frequently accessed data
        self.l1_cache = LRUCache(maxsize=128)
        
        # Level 2: Larger cache for parsed formulas
        self.formula_cache = LRUCache(maxsize=1000)
        
        # Level 3: Theory-specific caches
        self.theory_caches = {}
        
        # Performance metrics
        self.cache_hits = 0
        self.cache_misses = 0
    
    @lru_cache(maxsize=128)
    def get_truth_conditions(self, formula: str) -> z3.ExprRef:
        """Cache truth conditions with performance monitoring."""
        start = time.perf_counter()
        
        try:
            result = self._compute_truth_conditions(formula)
            self.cache_hits += 1
            return result
        except Exception:
            self.cache_misses += 1
            raise
        finally:
            elapsed = time.perf_counter() - start
            if elapsed > 0.1:  # 100ms threshold
                logger.warning(f"Slow truth condition computation: {elapsed:.3f}s")

# PERFORMANCE TARGET: Cache hit ratio > 80%, cache lookup < 1ms
```

### Adaptive Cache Sizing

```python
class AdaptiveCache:
    """Cache that adapts size based on memory pressure."""
    
    def __init__(self, initial_size=100):
        self.cache = {}
        self.max_size = initial_size
        self.memory_threshold = 50 * 1024 * 1024  # 50MB
        
    def get(self, key):
        """Get with memory pressure monitoring."""
        # Check memory pressure
        if get_memory_usage() > self.memory_threshold:
            self._shrink_cache()
        
        return self.cache.get(key)
    
    def _shrink_cache(self):
        """Shrink cache under memory pressure."""
        old_size = len(self.cache)
        
        # Remove 25% of entries (LRU)
        remove_count = len(self.cache) // 4
        items = list(self.cache.items())
        for i in range(remove_count):
            del self.cache[items[i][0]]
        
        logger.info(f"Shrunk cache from {old_size} to {len(self.cache)} entries")

# PERFORMANCE TARGET: Cache shrinking < 10ms, memory reduction > 20%
```

## Resource Limits

### Dynamic Resource Management

```python
class ResourceManager:
    """Manages computational resources with performance monitoring."""
    
    def __init__(self):
        self.cpu_threshold = 80.0  # CPU usage percentage
        self.memory_limit = 512 * 1024 * 1024  # 512MB
        self.time_limits = {
            'simple': 1.0,
            'medium': 5.0,
            'complex': 30.0
        }
    
    def allocate_resources(self, operation_type, estimated_complexity):
        """Allocate resources based on operation characteristics."""
        # Determine time limit
        time_limit = self.time_limits.get(operation_type, 10.0)
        
        # Adjust for system load
        cpu_usage = get_cpu_usage()
        if cpu_usage > self.cpu_threshold:
            time_limit *= 1.5  # More generous timeout under load
        
        # Memory check
        available_memory = get_available_memory()
        if available_memory < self.memory_limit:
            raise ResourceError("Insufficient memory for operation")
        
        return {
            'time_limit': time_limit,
            'memory_limit': min(available_memory * 0.8, self.memory_limit),
            'priority': self._calculate_priority(operation_type)
        }
    
    def _calculate_priority(self, operation_type):
        """Calculate operation priority for resource allocation."""
        priorities = {
            'simple': 'high',
            'medium': 'normal', 
            'complex': 'low'
        }
        return priorities.get(operation_type, 'normal')

# PERFORMANCE TARGET: Resource allocation < 1ms, accurate prediction > 90%
```

### Timeout Management

```python
class TimeoutManager:
    """Manages timeouts with performance feedback."""
    
    def __init__(self):
        self.timeout_history = []
        self.success_rate_threshold = 0.9
    
    def get_adaptive_timeout(self, operation_type, base_timeout):
        """Calculate timeout based on historical performance."""
        recent_timeouts = self._get_recent_timeouts(operation_type)
        
        if not recent_timeouts:
            return base_timeout
        
        # Calculate success rate
        successful = [t for t in recent_timeouts if t['completed']]
        success_rate = len(successful) / len(recent_timeouts)
        
        if success_rate < self.success_rate_threshold:
            # Increase timeout if success rate is low
            return base_timeout * 1.5
        elif success_rate > 0.95:
            # Decrease timeout if success rate is very high
            return base_timeout * 0.8
        
        return base_timeout
    
    def record_timeout_result(self, operation_type, elapsed_time, completed):
        """Record timeout performance for future optimization."""
        self.timeout_history.append({
            'type': operation_type,
            'elapsed': elapsed_time,
            'completed': completed,
            'timestamp': time.time()
        })
        
        # Keep only recent history (last 100 operations)
        if len(self.timeout_history) > 100:
            self.timeout_history = self.timeout_history[-100:]

# PERFORMANCE TARGET: Timeout accuracy > 90%, adaptation overhead < 1ms
```

## Profiling Methodology

### Systematic Performance Profiling

```python
import cProfile
import pstats
import tracemalloc
from contextlib import contextmanager

@contextmanager
def performance_profile(sort_by='cumulative', top_functions=20):
    """Context manager for comprehensive performance profiling."""
    # Start CPU profiling
    profiler = cProfile.Profile()
    profiler.enable()
    
    # Start memory profiling
    tracemalloc.start()
    
    try:
        yield
    finally:
        # Stop profiling
        profiler.disable()
        current_memory, peak_memory = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        
        # Generate reports
        stats = pstats.Stats(profiler)
        stats.sort_stats(sort_by)
        
        print(f"\n=== PERFORMANCE PROFILE ===")
        print(f"Peak memory usage: {peak_memory / 1024 / 1024:.1f} MB")
        print(f"Current memory usage: {current_memory / 1024 / 1024:.1f} MB")
        print(f"\nTop {top_functions} functions by {sort_by}:")
        stats.print_stats(top_functions)

# Usage example
def profile_model_checking():
    """Profile a complete model checking operation."""
    with performance_profile() as p:
        # Run the operation to profile
        result = check_model(premises, conclusions, settings)
    
    return result
```

### Component-Specific Profiling

```python
class ComponentProfiler:
    """Profiler specialized for ModelChecker components."""
    
    def __init__(self):
        self.component_times = {}
        self.component_memory = {}
        
    def profile_component(self, component_name):
        """Decorator for profiling specific components."""
        def decorator(func):
            def wrapper(*args, **kwargs):
                start_time = time.perf_counter()
                start_memory = get_memory_usage()
                
                try:
                    result = func(*args, **kwargs)
                    
                    elapsed = time.perf_counter() - start_time
                    memory_used = get_memory_usage() - start_memory
                    
                    # Record performance data
                    if component_name not in self.component_times:
                        self.component_times[component_name] = []
                        self.component_memory[component_name] = []
                    
                    self.component_times[component_name].append(elapsed)
                    self.component_memory[component_name].append(memory_used)
                    
                    # Log if performance is poor
                    if elapsed > 1.0:  # 1 second threshold
                        logger.warning(f"{component_name} slow: {elapsed:.3f}s")
                    
                    if memory_used > 50 * 1024 * 1024:  # 50MB threshold
                        logger.warning(f"{component_name} high memory: {memory_used/1024/1024:.1f}MB")
                    
                    return result
                    
                except Exception as e:
                    elapsed = time.perf_counter() - start_time
                    logger.error(f"{component_name} failed after {elapsed:.3f}s: {e}")
                    raise
                    
            return wrapper
        return decorator
    
    def get_performance_summary(self):
        """Get summary of component performance."""
        summary = {}
        for component in self.component_times:
            times = self.component_times[component]
            memory = self.component_memory[component]
            
            summary[component] = {
                'avg_time': sum(times) / len(times),
                'max_time': max(times),
                'avg_memory': sum(memory) / len(memory),
                'max_memory': max(memory),
                'call_count': len(times)
            }
        
        return summary

# Usage
profiler = ComponentProfiler()

@profiler.profile_component('syntax_parsing')
def parse_formula(formula):
    return syntax.parse(formula)
```

## Performance Regression Detection

### Automated Performance Testing

```python
class PerformanceRegressionDetector:
    """Detects performance regressions in CI/CD."""
    
    def __init__(self, baseline_file='performance_baseline.json'):
        self.baseline_file = baseline_file
        self.regression_threshold = 1.2  # 20% slowdown threshold
        self.memory_threshold = 1.3  # 30% memory increase threshold
    
    def run_performance_tests(self):
        """Run standard performance test suite."""
        results = {}
        
        # Test suite
        tests = [
            ('simple_model', self._test_simple_model),
            ('medium_model', self._test_medium_model),
            ('syntax_parsing', self._test_syntax_parsing),
            ('progress_animation', self._test_progress_animation),
            ('memory_cleanup', self._test_memory_cleanup)
        ]
        
        for test_name, test_func in tests:
            try:
                start = time.perf_counter()
                start_memory = get_memory_usage()
                
                test_func()
                
                elapsed = time.perf_counter() - start
                memory_used = get_memory_usage() - start_memory
                
                results[test_name] = {
                    'time': elapsed,
                    'memory': memory_used,
                    'success': True
                }
                
            except Exception as e:
                results[test_name] = {
                    'error': str(e),
                    'success': False
                }
        
        return results
    
    def check_for_regressions(self, current_results):
        """Check current results against baseline."""
        if not os.path.exists(self.baseline_file):
            # No baseline exists, save current as baseline
            self._save_baseline(current_results)
            return {'status': 'baseline_created', 'regressions': []}
        
        baseline = self._load_baseline()
        regressions = []
        
        for test_name, current in current_results.items():
            if not current.get('success', False):
                continue
                
            if test_name not in baseline:
                continue
                
            baseline_test = baseline[test_name]
            
            # Check time regression
            time_ratio = current['time'] / baseline_test['time']
            if time_ratio > self.regression_threshold:
                regressions.append({
                    'test': test_name,
                    'type': 'time',
                    'ratio': time_ratio,
                    'current': current['time'],
                    'baseline': baseline_test['time']
                })
            
            # Check memory regression
            memory_ratio = current['memory'] / baseline_test['memory']
            if memory_ratio > self.memory_threshold:
                regressions.append({
                    'test': test_name,
                    'type': 'memory',
                    'ratio': memory_ratio,
                    'current': current['memory'],
                    'baseline': baseline_test['memory']
                })
        
        return {'status': 'checked', 'regressions': regressions}
    
    def _save_baseline(self, results):
        """Save performance baseline."""
        with open(self.baseline_file, 'w') as f:
            json.dump(results, f, indent=2)
    
    def _load_baseline(self):
        """Load performance baseline."""
        with open(self.baseline_file, 'r') as f:
            return json.load(f)

# PERFORMANCE TARGET: Regression detection < 5s, accuracy > 95%
```

### Continuous Performance Monitoring

```python
class ContinuousPerformanceMonitor:
    """Monitors performance in production/development."""
    
    def __init__(self, metrics_file='performance_metrics.log'):
        self.metrics_file = metrics_file
        self.alert_thresholds = {
            'avg_response_time': 2.0,  # 2 seconds
            'memory_usage': 200 * 1024 * 1024,  # 200MB
            'error_rate': 0.05  # 5%
        }
    
    def log_operation(self, operation_type, elapsed_time, memory_used, success):
        """Log performance metrics for an operation."""
        metrics = {
            'timestamp': time.time(),
            'operation': operation_type,
            'elapsed_time': elapsed_time,
            'memory_used': memory_used,
            'success': success
        }
        
        # Write to metrics file
        with open(self.metrics_file, 'a') as f:
            f.write(json.dumps(metrics) + '\n')
        
        # Check for alerts
        self._check_alerts(metrics)
    
    def _check_alerts(self, metrics):
        """Check if metrics trigger alerts."""
        if metrics['elapsed_time'] > self.alert_thresholds['avg_response_time']:
            logger.warning(f"Slow operation: {metrics['operation']} took {metrics['elapsed_time']:.3f}s")
        
        if metrics['memory_used'] > self.alert_thresholds['memory_usage']:
            memory_mb = metrics['memory_used'] / (1024 * 1024)
            logger.warning(f"High memory usage: {metrics['operation']} used {memory_mb:.1f}MB")
    
    def get_performance_summary(self, hours=24):
        """Get performance summary for recent operations."""
        cutoff_time = time.time() - (hours * 3600)
        metrics = []
        
        with open(self.metrics_file, 'r') as f:
            for line in f:
                try:
                    metric = json.loads(line.strip())
                    if metric['timestamp'] > cutoff_time:
                        metrics.append(metric)
                except:
                    continue
        
        if not metrics:
            return {}
        
        # Calculate summary statistics
        times = [m['elapsed_time'] for m in metrics if m['success']]
        memory = [m['memory_used'] for m in metrics if m['success']]
        success_count = sum(1 for m in metrics if m['success'])
        
        return {
            'total_operations': len(metrics),
            'success_rate': success_count / len(metrics),
            'avg_time': sum(times) / len(times) if times else 0,
            'max_time': max(times) if times else 0,
            'avg_memory': sum(memory) / len(memory) if memory else 0,
            'max_memory': max(memory) if memory else 0
        }
```

## Timing Consistency Requirements

### Deterministic Performance

```python
class TimingConsistencyManager:
    """Ensures consistent timing across different environments."""
    
    def __init__(self):
        self.timing_variance_threshold = 0.3  # 30% variance allowed
        self.baseline_measurements = {}
    
    def measure_operation_consistency(self, operation_func, operation_name, runs=5):
        """Measure timing consistency for an operation."""
        times = []
        
        for i in range(runs):
            start = time.perf_counter()
            operation_func()
            elapsed = time.perf_counter() - start
            times.append(elapsed)
        
        # Calculate statistics
        avg_time = sum(times) / len(times)
        min_time = min(times)
        max_time = max(times)
        variance = max_time - min_time
        variance_ratio = variance / avg_time if avg_time > 0 else 0
        
        # Check consistency
        is_consistent = variance_ratio <= self.timing_variance_threshold
        
        result = {
            'operation': operation_name,
            'runs': runs,
            'avg_time': avg_time,
            'min_time': min_time,
            'max_time': max_time,
            'variance': variance,
            'variance_ratio': variance_ratio,
            'is_consistent': is_consistent
        }
        
        if not is_consistent:
            logger.warning(f"Inconsistent timing for {operation_name}: {variance_ratio:.1%} variance")
        
        return result
    
    def validate_timing_requirements(self):
        """Validate all timing requirements are met."""
        operations = [
            ('simple_model_check', lambda: self._simple_model_check()),
            ('syntax_parse', lambda: self._syntax_parse()),
            ('progress_update', lambda: self._progress_update())
        ]
        
        results = {}
        for name, func in operations:
            results[name] = self.measure_operation_consistency(func, name)
        
        return results

# PERFORMANCE TARGET: Timing variance < 30%, reproducibility > 95%
```

### Environment-Specific Adjustments

```python
class EnvironmentPerformanceAdapter:
    """Adapts performance expectations to different environments."""
    
    def __init__(self):
        self.environment_factors = {
            'development': 1.0,
            'ci': 2.0,  # CI environments are often slower
            'docker': 1.5,  # Docker adds some overhead
            'low_memory': 3.0  # Constrained memory environments
        }
    
    def detect_environment(self):
        """Detect current execution environment."""
        # Check for CI environment
        if any(var in os.environ for var in ['CI', 'GITHUB_ACTIONS', 'TRAVIS']):
            return 'ci'
        
        # Check for Docker
        if os.path.exists('/.dockerenv'):
            return 'docker'
        
        # Check memory constraints
        available_memory = get_available_memory()
        if available_memory < 1 * 1024 * 1024 * 1024:  # < 1GB
            return 'low_memory'
        
        return 'development'
    
    def adjust_timeouts(self, base_timeouts):
        """Adjust timeouts for current environment."""
        environment = self.detect_environment()
        factor = self.environment_factors.get(environment, 1.0)
        
        adjusted = {}
        for operation, timeout in base_timeouts.items():
            adjusted[operation] = timeout * factor
        
        logger.info(f"Adjusted timeouts for {environment} environment (factor: {factor})")
        return adjusted
```

## Optimization Patterns

### Performance-First Development

```python
class PerformanceFirstPattern:
    """Template for performance-first development."""
    
    def __init__(self):
        self.performance_targets = {}
        self.measurement_overhead = 0.001  # 1ms measurement overhead budget
    
    def implement_with_performance_monitoring(self, operation_name, target_time, target_memory):
        """Template for implementing operations with performance monitoring."""
        def decorator(func):
            def wrapper(*args, **kwargs):
                # Minimal overhead measurement start
                start_time = time.perf_counter()
                start_memory = get_memory_usage() if target_memory else None
                
                try:
                    result = func(*args, **kwargs)
                    
                    # Measure performance
                    elapsed = time.perf_counter() - start_time
                    memory_used = (get_memory_usage() - start_memory) if start_memory else 0
                    
                    # Check targets
                    if elapsed > target_time:
                        logger.warning(f"{operation_name} exceeded time target: {elapsed:.3f}s > {target_time}s")
                    
                    if target_memory and memory_used > target_memory:
                        memory_mb = memory_used / (1024 * 1024)
                        target_mb = target_memory / (1024 * 1024)
                        logger.warning(f"{operation_name} exceeded memory target: {memory_mb:.1f}MB > {target_mb:.1f}MB")
                    
                    return result
                    
                except Exception as e:
                    elapsed = time.perf_counter() - start_time
                    logger.error(f"{operation_name} failed after {elapsed:.3f}s: {e}")
                    raise
                    
            return wrapper
        return decorator

# Usage example
@PerformanceFirstPattern().implement_with_performance_monitoring(
    'model_checking', target_time=2.0, target_memory=50*1024*1024
)
def check_model_with_monitoring(premises, conclusions, settings):
    return check_model(premises, conclusions, settings)
```

### Hot Path Optimization

```python
class HotPathOptimizer:
    """Optimizer for frequently executed code paths."""
    
    def __init__(self):
        self.call_counts = {}
        self.hot_path_threshold = 100  # 100 calls = hot path
        
    def mark_execution(self, path_name):
        """Mark execution of a code path."""
        self.call_counts[path_name] = self.call_counts.get(path_name, 0) + 1
        
        # Suggest optimization for hot paths
        if self.call_counts[path_name] == self.hot_path_threshold:
            logger.info(f"Hot path detected: {path_name} (100+ executions)")
    
    def optimize_hot_path(self, func, path_name):
        """Apply hot path optimizations."""
        def optimized_wrapper(*args, **kwargs):
            self.mark_execution(path_name)
            
            # Apply hot path optimizations
            if self.call_counts.get(path_name, 0) > self.hot_path_threshold:
                # Use optimized version
                return self._optimized_execution(func, args, kwargs)
            else:
                # Use standard version
                return func(*args, **kwargs)
        
        return optimized_wrapper
    
    def _optimized_execution(self, func, args, kwargs):
        """Execute with hot path optimizations."""
        # Example optimizations:
        # - Skip redundant checks
        # - Use cached results
        # - Pre-allocate memory
        return func(*args, **kwargs)

# PERFORMANCE TARGET: Hot path identification overhead < 1μs
```

## Success Metrics

### Quantitative Performance Metrics

| Metric Category | Target | Measurement Method | Frequency |
|----------------|--------|-------------------|-----------|
| **Response Time** | 95% under target | Automated timing | Every operation |
| **Memory Usage** | Peak under limits | Memory profiling | Every operation |
| **Throughput** | Operations/second | Batch testing | Weekly |
| **Success Rate** | > 95% completion | Error tracking | Continuous |
| **Regression Rate** | < 5% per month | Baseline comparison | Per release |

### Performance Dashboard

```python
class PerformanceDashboard:
    """Real-time performance monitoring dashboard."""
    
    def __init__(self):
        self.metrics = {}
        self.alerts = []
    
    def update_metrics(self, category, metric_name, value):
        """Update performance metric."""
        if category not in self.metrics:
            self.metrics[category] = {}
        
        if metric_name not in self.metrics[category]:
            self.metrics[category][metric_name] = []
        
        self.metrics[category][metric_name].append({
            'value': value,
            'timestamp': time.time()
        })
        
        # Keep only recent data (last 1000 points)
        self.metrics[category][metric_name] = self.metrics[category][metric_name][-1000:]
    
    def get_performance_summary(self):
        """Get current performance summary."""
        summary = {}
        
        for category, metrics in self.metrics.items():
            summary[category] = {}
            
            for metric_name, values in metrics.items():
                if values:
                    recent_values = [v['value'] for v in values[-10:]]  # Last 10 values
                    summary[category][metric_name] = {
                        'current': values[-1]['value'],
                        'average': sum(recent_values) / len(recent_values),
                        'trend': self._calculate_trend(values)
                    }
        
        return summary
    
    def _calculate_trend(self, values):
        """Calculate performance trend."""
        if len(values) < 2:
            return 'stable'
        
        recent = values[-5:]  # Last 5 values
        older = values[-10:-5] if len(values) >= 10 else values[:-5]
        
        if not older:
            return 'stable'
        
        recent_avg = sum(v['value'] for v in recent) / len(recent)
        older_avg = sum(v['value'] for v in older) / len(older)
        
        change = (recent_avg - older_avg) / older_avg
        
        if change > 0.1:
            return 'degrading'
        elif change < -0.1:
            return 'improving'
        else:
            return 'stable'
```

## Troubleshooting Performance Issues

### Common Performance Problems

#### Z3 Solver Performance

```python
def diagnose_z3_performance(solver, constraints):
    """Diagnose Z3 solver performance issues."""
    issues = []
    
    # Check constraint count
    if len(constraints) > 1000:
        issues.append({
            'type': 'too_many_constraints',
            'count': len(constraints),
            'recommendation': 'Break into smaller problems or use constraint hierarchies'
        })
    
    # Check variable count
    variables = set()
    for constraint in constraints:
        variables.update(get_variables(constraint))
    
    if len(variables) > 500:
        issues.append({
            'type': 'too_many_variables',
            'count': len(variables),
            'recommendation': 'Reduce variable count or use bit vector encoding'
        })
    
    # Check for complex constraints
    complex_constraints = [c for c in constraints if estimate_complexity(c) > 10]
    if complex_constraints:
        issues.append({
            'type': 'complex_constraints',
            'count': len(complex_constraints),
            'recommendation': 'Simplify constraints or use approximations'
        })
    
    return issues
```

#### Memory Performance Issues

```python
def diagnose_memory_issues():
    """Diagnose memory performance issues."""
    issues = []
    
    # Check for memory leaks
    gc.collect()
    objects_before = len(gc.get_objects())
    
    # Simulate some operations
    test_operations()
    
    gc.collect()
    objects_after = len(gc.get_objects())
    
    if objects_after > objects_before * 1.1:  # 10% growth
        issues.append({
            'type': 'potential_memory_leak',
            'growth': objects_after - objects_before,
            'recommendation': 'Check for circular references and cleanup'
        })
    
    # Check memory fragmentation
    memory_usage = get_memory_usage()
    if memory_usage > 100 * 1024 * 1024:  # 100MB
        issues.append({
            'type': 'high_memory_usage',
            'usage_mb': memory_usage / (1024 * 1024),
            'recommendation': 'Use generators and aggressive cleanup'
        })
    
    return issues
```

#### Threading Performance Issues

```python
def diagnose_threading_issues():
    """Diagnose threading performance issues."""
    issues = []
    
    # Check thread count
    thread_count = threading.active_count()
    if thread_count > 10:
        issues.append({
            'type': 'too_many_threads',
            'count': thread_count,
            'recommendation': 'Use thread pools or reduce concurrency'
        })
    
    # Check for blocking operations
    main_thread = threading.current_thread()
    if hasattr(main_thread, '_target') and main_thread._target:
        issues.append({
            'type': 'blocking_main_thread',
            'recommendation': 'Move blocking operations to background threads'
        })
    
    return issues
```

### Performance Debugging Tools

```python
class PerformanceDebugger:
    """Comprehensive performance debugging toolkit."""
    
    def __init__(self):
        self.debug_enabled = False
        self.trace_data = []
    
    def enable_debug_mode(self):
        """Enable detailed performance debugging."""
        self.debug_enabled = True
        logger.setLevel(logging.DEBUG)
        
    def trace_operation(self, operation_name):
        """Decorator to trace operation performance."""
        def decorator(func):
            def wrapper(*args, **kwargs):
                if not self.debug_enabled:
                    return func(*args, **kwargs)
                
                start = time.perf_counter()
                start_memory = get_memory_usage()
                
                try:
                    result = func(*args, **kwargs)
                    
                    elapsed = time.perf_counter() - start
                    memory_used = get_memory_usage() - start_memory
                    
                    trace_entry = {
                        'operation': operation_name,
                        'elapsed': elapsed,
                        'memory_used': memory_used,
                        'success': True,
                        'timestamp': time.time()
                    }
                    
                    self.trace_data.append(trace_entry)
                    
                    logger.debug(f"TRACE: {operation_name} took {elapsed:.3f}s, used {memory_used/1024/1024:.1f}MB")
                    
                    return result
                    
                except Exception as e:
                    elapsed = time.perf_counter() - start
                    
                    trace_entry = {
                        'operation': operation_name,
                        'elapsed': elapsed,
                        'error': str(e),
                        'success': False,
                        'timestamp': time.time()
                    }
                    
                    self.trace_data.append(trace_entry)
                    
                    logger.debug(f"TRACE ERROR: {operation_name} failed after {elapsed:.3f}s: {e}")
                    raise
                    
            return wrapper
        return decorator
    
    def generate_performance_report(self):
        """Generate comprehensive performance report."""
        if not self.trace_data:
            return "No trace data available"
        
        report = ["=== PERFORMANCE DEBUG REPORT ===\n"]
        
        # Overall statistics
        total_operations = len(self.trace_data)
        successful_operations = [t for t in self.trace_data if t['success']]
        failed_operations = [t for t in self.trace_data if not t['success']]
        
        report.append(f"Total operations: {total_operations}")
        report.append(f"Successful: {len(successful_operations)}")
        report.append(f"Failed: {len(failed_operations)}")
        
        if successful_operations:
            times = [t['elapsed'] for t in successful_operations]
            memories = [t['memory_used'] for t in successful_operations]
            
            report.append(f"\nTiming statistics:")
            report.append(f"  Average time: {sum(times)/len(times):.3f}s")
            report.append(f"  Min time: {min(times):.3f}s")
            report.append(f"  Max time: {max(times):.3f}s")
            
            report.append(f"\nMemory statistics:")
            avg_memory = sum(memories) / len(memories) / (1024 * 1024)
            max_memory = max(memories) / (1024 * 1024)
            report.append(f"  Average memory: {avg_memory:.1f}MB")
            report.append(f"  Max memory: {max_memory:.1f}MB")
        
        # Slowest operations
        if successful_operations:
            slowest = sorted(successful_operations, key=lambda x: x['elapsed'], reverse=True)[:5]
            report.append(f"\nSlowest operations:")
            for op in slowest:
                report.append(f"  {op['operation']}: {op['elapsed']:.3f}s")
        
        return "\n".join(report)
```

### Performance Optimization Checklist

Before deploying performance optimizations:

- [ ] **Measure First**: Profile current performance to identify bottlenecks
- [ ] **Set Targets**: Define specific, measurable performance goals
- [ ] **Optimize Systematically**: Focus on the biggest bottlenecks first
- [ ] **Measure Again**: Verify optimization effectiveness
- [ ] **Test Thoroughly**: Ensure optimizations don't break functionality
- [ ] **Monitor Continuously**: Set up monitoring for regression detection
- [ ] **Document Changes**: Record optimization techniques and results

## Conclusion

These performance optimization guidelines provide a systematic approach to maintaining and improving ModelChecker performance. The key principles are:

1. **Measure Everything**: All optimizations must be based on data
2. **Set Clear Targets**: Every operation has specific performance goals
3. **Optimize Systematically**: Focus on the biggest impact optimizations
4. **Monitor Continuously**: Detect regressions early and automatically
5. **Scale Predictably**: Performance should scale according to expected patterns

Apply these guidelines consistently to maintain high performance across all ModelChecker components while ensuring reliable, predictable behavior for users.

---

[← Back to Implementation](README.md) | [Development Workflow →](DEVELOPMENT_WORKFLOW.md) | [Refactoring →](REFACTORING.md)