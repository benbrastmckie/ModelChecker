# Maximize Mode Optimization Guide

## Current Performance Issues

When running with `maximize=True`, the system experiences slowness due to:

1. **Exponential growth in state space** as N increases (2^N states)
2. **Complex counterfactual formulas** requiring extensive computation
3. **Imposition relation calculations** for all world/state combinations
4. **Multiprocessing overhead** from serialization/deserialization

## Immediate Optimizations

### 1. Disable Maximize for Normal Runs
```python
# In examples.py, change line 898:
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Changed from True
}
```

### 2. Use Command Line Flag Instead
Run with `-m` flag only when needed:
```bash
./dev_cli.py /path/to/examples.py -m
```

### 3. Reduce Starting N Values
For faster maximize runs, reduce initial N in complex examples:
```python
IM_CM_0_settings = {
    'N' : 3,  # Reduced from 4
    # ... other settings
}
```

### 4. Increase Time Limits
Allow more time per iteration to find models at higher N:
```python
'max_time' : 5,  # Increased from 1
```

## Code-Level Optimizations

### 1. Early Termination
Add a maximum N limit to prevent excessive searching:
```python
# In compare_semantics method
MAX_N_LIMIT = 6  # Stop at N=6 regardless
if active_cases[theory_name] >= MAX_N_LIMIT:
    results.append((theory_name, active_cases[theory_name]))
    continue
```

### 2. Adaptive Time Limits
Increase time limits as N grows:
```python
# In try_single_N_static
adaptive_time = settings['max_time'] * (1.5 ** (settings['N'] - initial_N))
success = run_time < adaptive_time
```

### 3. Caching Imposition Relations
Cache imposition calculations between iterations:
```python
# In ImpositionSemantics
self._imposition_cache = {}

def cached_imposition(self, x, world, outcome):
    key = (x, world, outcome)
    if key not in self._imposition_cache:
        self._imposition_cache[key] = self.imposition(x, world, outcome)
    return self._imposition_cache[key]
```

### 4. Parallel Example Processing
Process multiple examples in parallel rather than sequentially:
```python
# In run_comparison
with concurrent.futures.ProcessPoolExecutor() as executor:
    futures = []
    for example_name, example_case in self.example_range.items():
        future = executor.submit(self.process_single_example, 
                               example_name, example_case)
        futures.append(future)
    
    for future in concurrent.futures.as_completed(futures):
        result = future.result()
        # Process result
```

## Recommended Workflow

1. **Development**: Use `maximize=False` for normal development
2. **Testing**: Run specific examples with small N values
3. **Benchmarking**: Use maximize mode with carefully selected examples
4. **Production**: Consider implementing the code-level optimizations above

## Example Usage Patterns

### Quick Test (Fast)
```python
# Single example, fixed N
example_range = {
    "IM_CM_22": IM_CM_22_example,  # Simple example
}
general_settings["maximize"] = False
```

### Maximize Test (Slow but Informative)
```bash
# Run with command line flag
./dev_cli.py examples.py -m
```

### Custom Maximize Settings
```python
# In examples.py
if "--quick-maximize" in sys.argv:
    # Limit examples for maximize testing
    example_range = {
        "IM_CM_22": IM_CM_22_example,  # Only simple examples
    }
```

## Performance Expectations

With optimizations:
- **N=3**: < 1 second
- **N=4**: 1-5 seconds  
- **N=5**: 5-30 seconds
- **N=6**: 30+ seconds (depends on formula complexity)

Without optimizations, times can be 10x longer for complex formulas.