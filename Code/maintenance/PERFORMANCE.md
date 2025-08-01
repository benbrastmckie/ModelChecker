# Performance Guidelines

[← Error Handling](ERROR_HANDLING.md) | [Back to Maintenance](README.md) | [Version Control →](VERSION_CONTROL.md)

## Overview

This document provides performance optimization guidelines for the ModelChecker codebase, focusing on Z3 solver optimization and memory management.

## Z3 Solver Optimization

### Minimize Variable Count

```python
# GOOD - Reuse variables where possible
def create_constraints(n_atoms):
    # Create only necessary variables
    atoms = [z3.Bool(f'p_{i}') for i in range(n_atoms)]
    
# BAD - Creating unnecessary variables
def create_constraints(max_possible):
    # Creates variables that may never be used
    atoms = [z3.Bool(f'p_{i}') for i in range(max_possible)]
```

### Use Appropriate Bit Vector Sizes

```python
# Calculate minimum required bits
import math

def calculate_bit_size(n_states):
    """Calculate minimum bit vector size for n states."""
    if n_states <= 0:
        return 1
    return max(1, math.ceil(math.log2(n_states)))

# Use calculated size
bit_size = calculate_bit_size(n_states)
state_var = z3.BitVec('state', bit_size)
```

### Add Constraints Efficiently

```python
# GOOD - Add constraints in order of importance
solver = z3.Solver()

# Add most restrictive constraints first
solver.add(critical_constraint)
solver.add(important_constraint)
solver.add(optional_constraint)

# Check satisfiability early if possible
if solver.check() == z3.unsat:
    return None  # Fail fast
```

### Use Solver Timeouts

```python
def solve_with_timeout(constraints, timeout_ms=10000):
    """Solve with configurable timeout."""
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    
    for constraint in constraints:
        solver.add(constraint)
    
    result = solver.check()
    if result == z3.unknown:
        # Handle timeout
        reason = solver.reason_unknown()
        if "timeout" in reason:
            raise TimeoutError(f"Solver timeout after {timeout_ms}ms")
    
    return result
```

## Memory Management

### Clean Up Temporary Objects

```python
class ModelChecker:
    def __init__(self):
        self.solver = z3.Solver()
        self._temp_constraints = []
    
    def check_model(self, constraints):
        try:
            # Use solver
            result = self._solve(constraints)
            return result
        finally:
            # Always clean up
            self.solver.reset()
            self._temp_constraints.clear()
```

### Use Generators for Large Iterations

```python
# GOOD - Memory efficient
def generate_models(constraints, max_models):
    """Generate models one at a time."""
    solver = z3.Solver()
    solver.add(constraints)
    
    count = 0
    while count < max_models and solver.check() == z3.sat:
        model = solver.model()
        yield model
        
        # Block this model
        block = z3.Not(z3.And([v() == model[v] for v in model]))
        solver.add(block)
        count += 1

# BAD - Loads all models into memory
def get_all_models(constraints, max_models):
    models = []
    # ... collect all models
    return models
```

### Implement Proper Cleanup

```python
class TheorySemantics:
    def __init__(self):
        self.cache = {}
        self.solver = None
    
    def __del__(self):
        """Clean up resources."""
        if self.solver:
            self.solver.reset()
        self.cache.clear()
```

## Caching Strategies

### Memoization for Expensive Operations

```python
from functools import lru_cache

@lru_cache(maxsize=128)
def compute_truth_conditions(formula: str) -> z3.ExprRef:
    """Cache parsed formulas to avoid re-parsing."""
    # Expensive parsing operation
    return parse_and_convert(formula)
```

### Manual Caching with Size Limits

```python
class FormulaCache:
    def __init__(self, max_size=1000):
        self.cache = {}
        self.max_size = max_size
    
    def get(self, formula):
        return self.cache.get(formula)
    
    def set(self, formula, result):
        if len(self.cache) >= self.max_size:
            # Remove oldest entry (simple FIFO)
            oldest = next(iter(self.cache))
            del self.cache[oldest]
        self.cache[formula] = result
```

## Profiling and Benchmarking

### Time Critical Sections

```python
import time
from contextlib import contextmanager

@contextmanager
def timer(name):
    """Time a code block."""
    start = time.perf_counter()
    try:
        yield
    finally:
        end = time.perf_counter()
        print(f"{name} took {end - start:.3f}s")

# Usage
with timer("Model checking"):
    result = check_model(premises, conclusions)
```

### Profile Memory Usage

```python
import tracemalloc

def profile_memory(func):
    """Decorator to profile memory usage."""
    def wrapper(*args, **kwargs):
        tracemalloc.start()
        result = func(*args, **kwargs)
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        print(f"{func.__name__} - Current: {current/1024/1024:.1f}MB, Peak: {peak/1024/1024:.1f}MB")
        return result
    return wrapper
```

## Optimization Checklist

### Before Optimizing

1. **Profile first** - Identify actual bottlenecks
2. **Set performance goals** - Define acceptable thresholds
3. **Maintain correctness** - Don't sacrifice accuracy for speed

### Common Optimizations

1. **Reduce Z3 variable count** - Use minimum necessary variables
2. **Order constraints** - Most restrictive first
3. **Cache results** - Avoid recomputing expensive operations
4. **Use generators** - Process large datasets incrementally
5. **Set timeouts** - Prevent infinite loops
6. **Clean up resources** - Prevent memory leaks

### Performance Monitoring

```python
import logging
import functools

def log_performance(func):
    """Log performance metrics for functions."""
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        start_time = time.perf_counter()
        try:
            result = func(*args, **kwargs)
            elapsed = time.perf_counter() - start_time
            if elapsed > 1.0:  # Log slow operations
                logging.warning(f"{func.__name__} took {elapsed:.2f}s")
            return result
        except Exception as e:
            elapsed = time.perf_counter() - start_time
            logging.error(f"{func.__name__} failed after {elapsed:.2f}s: {e}")
            raise
    return wrapper
```

---

[← Error Handling](ERROR_HANDLING.md) | [Back to Maintenance](README.md) | [Version Control →](VERSION_CONTROL.md)