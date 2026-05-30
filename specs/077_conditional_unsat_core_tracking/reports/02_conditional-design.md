# Research Report: Conditional Unsat Core Tracking Design (Round 2)

**Task**: 77 - Conditional unsat core tracking for CVC5 solver
**Date**: 2026-04-03
**Session**: sess_1775242482_487b6b
**Round**: 2 (follows up on Round 1 findings and integrates Task 79 results)

## Executive Summary

Round 1 found that `produce-unsat-cores` alone adds only 10-30% overhead (~0.1ms). However, Task 79 discovered that **the combination of `produce-unsat-cores=true` WITH tracked assertions creates 4-5x overhead**. Disabling this combination (plus adding `decision=stoponly` and `bv-eager-eval=true`) reduces CVC5's performance gap from 8.9x slower to just 1.65x slower than Z3.

This round designs the conditional mechanism for toggling unsat core tracking and integrates with Task 79's optimizations.

## Code Path Analysis

### When Unsat Cores Are Needed

| Scenario | Cores Needed? | Settings Check |
|----------|---------------|----------------|
| Regular SAT example | No | - |
| Regular UNSAT example (normal run) | No* | `print_constraints=False` AND `print_z3=False` |
| UNSAT with constraint printing | Yes | `print_constraints=True` |
| UNSAT with raw Z3 output | Yes | `print_z3=True` |
| Model iteration | No | Always |
| Jupyter notebook UNSAT display | Yes | Built-in behavior |

*Note: Currently cores ARE extracted on every UNSAT but only displayed when settings enable it.

### Assertion Tracking Flow (`cvc5_adapter.py`)

```python
def __init__(self) -> None:
    self._solver = CVC5Solver()
    self._solver.set('produce-unsat-cores', 'true')  # <-- SET UNCONDITIONALLY

    # Label -> constraint mapping for tracked assertions
    self._tracked: Dict[str, Any] = {}
    self._reverse: Dict[int, str] = {}           # Python ID -> label
    self._term_id_to_label: Dict[int, str] = {}  # CVC5 term ID -> label
    self._str_to_label: Dict[str, str] = {}      # String repr -> label (lazy)
```

The overhead comes from three sources:

1. **CVC5's internal proof tracking**: When `produce-unsat-cores=true`, CVC5 maintains proof annotations for each assertion
2. **Python-side bookkeeping**: 4 dictionaries maintained for label mapping (minimal overhead)
3. **Lazy string conversion**: `_str_to_label` only populated when `unsat_core()` is called

Task 79's finding: The combination of tracked assertions (~500 constraints) with proof production creates significant overhead on UNSAT problems where the core must be computed.

### Structure.py Solver Flow

```
ModelDefaults.__init__()
    |
    +-> solve()
         |
         +-> _setup_solver()  # Adds all constraints via assert_tracked()
         |
         +-> solver.check()
         |
         +-> if UNSAT: solver.unsat_core()  # ALWAYS CALLED
```

The key issue: `solver.unsat_core()` is called on every UNSAT result, but the data is only used when `print_constraints=True` or `print_z3=True`.

### Where Cores Are Actually Consumed

```
structure.py:_get_relevant_constraints()   # print_grouped_constraints() path
    if self.unsat_core is not None:
        return [self.constraint_dict[str(c)] for c in self.unsat_core]

structure.py:print_model()
    if self.settings["print_z3"]:
        if not self.z3_model_status:
            print(self.unsat_core, file=output)

logos/semantic.py:print_structure()  # Line 1699
    if print_constraints and self.unsat_core is not None:
        self.print_grouped_constraints(output)
```

## Recommended Conditional Mechanism

### Option B: Settings-Based Auto-Detection (Recommended)

Check `print_constraints` and `print_z3` settings at solver creation time to determine if cores are needed.

```python
# In cvc5_adapter.py
class CVC5SolverAdapter:
    def __init__(self, need_unsat_cores: bool = True) -> None:
        from cvc5.pythonic import Solver as CVC5Solver
        self._solver = CVC5Solver()

        self._need_unsat_cores = need_unsat_cores

        if need_unsat_cores:
            self._solver.set('produce-unsat-cores', 'true')
        else:
            # Apply Task 79 optimizations when cores not needed
            self._solver.set('decision', 'stoponly')
            self._solver.set('bv-eager-eval', 'true')

        # Tracking dictionaries always maintained (minimal overhead)
        self._tracked: Dict[str, Any] = {}
        self._reverse: Dict[int, str] = {}
        self._term_id_to_label: Dict[int, str] = {}
        self._str_to_label: Dict[str, str] = {}
```

```python
# In registry.py
def create_solver(settings: Optional[Dict[str, Any]] = None) -> TrackedSolverProtocol:
    backend = get_active_backend(settings)
    validate_backend(backend)

    if backend == "cvc5":
        from .cvc5_adapter import CVC5SolverAdapter
        # Auto-detect if cores are needed from settings
        need_cores = False
        if settings:
            need_cores = settings.get('print_constraints', False) or \
                        settings.get('print_z3', False)
        return CVC5SolverAdapter(need_unsat_cores=need_cores)
    elif backend == "z3":
        from .z3_adapter import Z3SolverAdapter
        return Z3SolverAdapter()  # Z3 tracking overhead is negligible
```

**Rationale**:
- **Safe**: If user enables `print_constraints` or `print_z3`, cores are automatically enabled
- **Fast by default**: Normal runs without print flags get optimized configuration
- **Simple**: No new settings to explain, leverages existing print flags
- **Backward compatible**: Current behavior preserved when print flags enabled

### Fallback Mechanism

When `need_unsat_cores=False`, the `unsat_core()` method returns an empty list:

```python
def unsat_core(self) -> List[str]:
    if not self._need_unsat_cores:
        return []  # Core tracking disabled - return empty

    # ... existing core extraction logic
```

This is safe because:
1. Code that iterates over `unsat_core` will simply have no items
2. `print_grouped_constraints()` checks `unsat_core is not None` but an empty list is truthy - need adjustment

**Adjustment needed in structure.py**:

```python
def _get_relevant_constraints(self, output: TextIO) -> List[Any]:
    if self.z3_model is not None:
        print("SATISFIABLE CONSTRAINTS:", file=output)
        return self.model_constraints.all_constraints
    elif self.unsat_core is not None and len(self.unsat_core) > 0:
        print("UNSATISFIABLE CORE CONSTRAINTS:", file=output)
        return [self.constraint_dict[str(c)] for c in self.unsat_core]
    else:
        print("UNSATISFIABLE (core not available)", file=output)
        return self.model_constraints.all_constraints  # Show all constraints
```

## Integration with Task 79 Optimizations

### Configuration Matrix

| Mode | `produce-unsat-cores` | `decision` | `bv-eager-eval` | Use Case |
|------|----------------------|------------|-----------------|----------|
| Diagnostic | `true` | (default) | (default) | Debugging, constraint analysis |
| Performance | `false` | `stoponly` | `true` | Normal model checking |

### Bundled Configuration

Rather than three separate toggles, bundle them into a single "mode":

```python
class CVC5SolverAdapter:
    def __init__(self, need_unsat_cores: bool = True) -> None:
        # ...
        if need_unsat_cores:
            self._configure_diagnostic_mode()
        else:
            self._configure_performance_mode()

    def _configure_diagnostic_mode(self) -> None:
        """Configure for full diagnostics with unsat core support."""
        self._solver.set('produce-unsat-cores', 'true')

    def _configure_performance_mode(self) -> None:
        """Configure for maximum performance without core tracking."""
        self._solver.set('decision', 'stoponly')
        self._solver.set('bv-eager-eval', 'true')
        # Note: produce-unsat-cores is false by default
```

### Expected Performance

Based on Task 79 benchmarks:

| Configuration | Total Time (9 examples) | vs Z3 |
|--------------|------------------------|-------|
| Current (cores enabled) | 10.072s | 8.90x slower |
| Performance mode | 1.861s | 1.65x slower |
| Z3 | 1.131s | 1.00x |

**Projected improvement**: 5.4x faster on CVC5 UNSAT examples.

## Implementation Plan Outline

### Phase 1: CVC5 Adapter Enhancement

1. Add `need_unsat_cores` parameter to `CVC5SolverAdapter.__init__()`
2. Add `_configure_diagnostic_mode()` and `_configure_performance_mode()` methods
3. Update `unsat_core()` to return empty list when disabled
4. Update `reset()` to preserve mode configuration

### Phase 2: Registry Integration

1. Update `create_solver()` to accept and pass settings
2. Add auto-detection logic for `print_constraints`/`print_z3`
3. Add tests for both modes

### Phase 3: Structure.py Safety Updates

1. Update `_get_relevant_constraints()` to handle empty cores gracefully
2. Update any code that assumes `unsat_core` is populated on UNSAT
3. Add informative message when core unavailable

### Phase 4: Testing

1. Unit tests for CVC5 adapter mode switching
2. Integration tests verifying correct mode selection
3. Performance benchmarks comparing modes
4. Regression tests for print_constraints functionality

## Risk Analysis

### Potential Issues

| Risk | Mitigation |
|------|------------|
| Silent core loss | Empty list returned + informative print message |
| Setting detection failure | Default to diagnostic mode (safe fallback) |
| Mode switching mid-session | Not supported; solver created fresh per example |
| Z3 adapter asymmetry | Z3 overhead negligible, always enable cores |

### Backward Compatibility

- Users with `print_constraints=True` see no change
- Users without print flags get faster CVC5 (breaking change in perf, not behavior)
- Explicit `diagnostic_mode` setting could be added for override

## Alternatives Considered

### Option A: Explicit `diagnostic_mode` Setting

Add new setting `diagnostic_mode: bool` that users set explicitly.

**Pros**: Clear user intent
**Cons**: Another setting to learn, defaults unclear

**Decision**: Use auto-detection; add explicit setting later if needed.

### Option C: Lazy Core Initialization

Only enable cores when `unsat_core()` is first called.

**Pros**: No API changes
**Cons**: CVC5 may not support enabling cores mid-solve; timing issues

**Decision**: Rejected - CVC5 requires option set before assertions.

### Option D: Separate Solver Factories

Create `CVC5DiagnosticSolver` and `CVC5PerformanceSolver` classes.

**Pros**: Clear separation
**Cons**: Code duplication, complex registry

**Decision**: Rejected - single class with mode parameter is cleaner.

## Sources

- Task 79 Research Report: `specs/079_cvc5_solver_options_tuning/reports/01_cvc5-options-research.md`
- Task 77 Round 1 Report: `specs/077_conditional_unsat_core_tracking/reports/01_unsat-core-overhead.md`
- CVC5 Options: https://cvc5.github.io/docs/cvc5-1.0.2/options.html
- CVC5 GitHub Issue #5141: Performance with unsat cores
