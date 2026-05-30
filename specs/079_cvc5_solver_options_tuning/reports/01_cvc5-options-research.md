# CVC5 Solver Options Research Report

## Executive Summary

Research into CVC5 solver configuration options for improving performance on the logos theory's modal logic constraint profile has identified significant optimization opportunities. The key finding is that **disabling `produce-unsat-cores` provides a 4-5x speedup**, reducing CVC5's performance gap with Z3 from ~9x slower to ~1.6x slower. Additional options like `decision=stoponly` and `bv-eager-eval=true` provide incremental improvements.

## Background

### Problem Statement
Task 76 benchmarks showed CVC5 dramatically slower on UNSAT proofs (avg 9.37x) while competitive on SAT results. Prior research (Task 77) ruled out `produce-unsat-cores` overhead as the sole cause, finding only 10-30% overhead from that option alone. This research systematically tests additional CVC5 options to identify the root cause and potential mitigations.

### Test Workload Characteristics
The logos theory uses:
- **Bitvector reasoning**: Finite-domain state representation using BitVec sorts
- **Uninterpreted functions**: For accessibility relations and semantic mappings
- **Tracked assertions**: Each constraint has a label for unsat core extraction
- **Modal logic structure**: Kripke semantics with world accessibility

## Round 1: CVC5 Option Inventory

### Available Options via Python API

CVC5 options are accessible through `solver.set(option, value)`. Key option categories:

#### Bitvector Solving
| Option | Values | Default | Notes |
|--------|--------|---------|-------|
| `bitblast` | lazy, eager | lazy | Eager incompatible with UF/arrays |
| `bv-sat-solver` | cadical, cryptominisat, kissat, minisat | cadical | SAT backend choice |
| `bv-solver` | bitblast, bitblast-internal | bitblast | Solver implementation |
| `bv-eager-eval` | true/false | false | Eager evaluation mode |
| `bv-gauss-elim` | true/false | false | Gaussian elimination |
| `bv-to-bool` | true/false | false | Lift 1-bit BV to booleans |

#### Decision Heuristics
| Option | Values | Default | Notes |
|--------|--------|---------|-------|
| `decision` | internal, justification, stoponly | internal | SAT decision mode |

#### Proof/Core Production
| Option | Values | Default | Notes |
|--------|--------|---------|-------|
| `produce-unsat-cores` | true/false | false | Enable unsat core extraction |
| `unsat-cores-mode` | off, sat-proof, assumptions | off | Core production method |
| `produce-proofs` | true/false | false | Full proof production |

#### Int-Blasting (BV-to-Integer)
| Option | Values | Default | Notes |
|--------|--------|---------|-------|
| `solve-bv-as-int` | off, sum, iand, bitwise, bv | off | Convert BV to integer arithmetic |

#### Simplification
| Option | Values | Default | Notes |
|--------|--------|---------|-------|
| `simplification` | batch, none | batch | Preprocessing mode |
| `ite-simp` | true/false | false | ITE simplification (incompatible with cores) |
| `unconstrained-simp` | true/false | false | Unconstrained simp (incompatible with incremental) |

### Incompatible Options

Several options are incompatible with this workload:

1. **`bitblast=eager`**: "Eager bit-blasting currently does not support model generation for the combination of bit-vectors with arrays or uninterpreted functions."

2. **`ite-simp=true`**: "ITE simp not supported with unsat cores"

3. **`unconstrained-simp=true`**: "unconstrained simplification not supported with incremental solving"

## Round 2: Profiling Results

### Initial Benchmark (3 worst-case UNSAT examples)

| Configuration | CL_TH_1 | CF_TH_2 | MOD_TH_5 | Total | vs Baseline |
|--------------|---------|---------|----------|-------|-------------|
| baseline (with cores) | 2.09s | 2.67s | 2.10s | 7.01s | 1.00x |
| no-unsat-cores | 0.33s | 0.82s | 0.21s | 1.26s | **0.18x** |

**Key Finding**: Simply disabling `produce-unsat-cores` provides a **5.6x speedup** on UNSAT problems.

This contradicts the Task 77 finding of "10-30% overhead" - the difference is that the previous test measured only the overhead of enabling the option, not the overhead of the tracked assertion pattern required to support it.

### Extended Benchmark (6 UNSAT + 3 SAT examples)

#### Top Configurations

| Configuration | Total | vs Baseline | Notes |
|--------------|-------|-------------|-------|
| no-cores+stoponly+bv-eager-eval | 1.861s | 0.18x | Best overall |
| no-cores+decision-stoponly | 1.869s | 0.19x | Simpler, nearly as good |
| no-cores+bv-eager-eval | 2.121s | 0.21x | Good UNSAT + SAT balance |
| no-cores+sat-cryptominisat | 2.337s | 0.23x | Best SAT backend |
| no-unsat-cores | 2.546s | 0.25x | Simple baseline |
| baseline-with-cores | 10.072s | 1.00x | Current default |

#### Z3 Comparison

| Solver | Total Time | vs Z3 |
|--------|-----------|-------|
| Z3 | 1.131s | 1.00x |
| CVC5 (optimized) | 1.861s | 1.65x slower |
| CVC5 (current) | 10.072s | 8.90x slower |

**The optimized CVC5 configuration reduces the performance gap from 8.9x to 1.65x.**

### Per-Example Breakdown

| Example | Z3 | CVC5 (current) | CVC5 (optimized) | Improvement |
|---------|-----|----------------|------------------|-------------|
| CL_TH_1 (UNSAT) | 0.107s | 2.093s | 0.233s | 9.0x faster |
| CF_TH_2 (UNSAT) | 0.086s | 2.665s | 0.377s | 7.1x faster |
| MOD_TH_5 (UNSAT) | 0.074s | 2.104s | 0.184s | 11.4x faster |
| REL_TH_1 (UNSAT) | 0.042s | 1.009s | 0.056s | 18.0x faster |
| MOD_TH_3 (UNSAT) | 0.039s | 1.075s | 0.089s | 12.1x faster |
| EXT_TH_7 (UNSAT) | 0.028s | 0.401s | 0.054s | 7.4x faster |
| CF_CM_1 (SAT) | 0.492s | 0.510s | 0.716s | 0.7x (slight regression) |
| MOD_CM_3 (SAT) | 0.176s | 0.089s | 0.077s | 1.2x faster |
| REL_CM_3 (SAT) | 0.085s | 0.127s | 0.075s | 1.7x faster |

## Round 3: Option Analysis

### Why `produce-unsat-cores` Has Such Impact

The overhead comes from multiple sources:
1. **Tracked assertion bookkeeping**: Each constraint requires label management
2. **SAT solver assumptions pattern**: CVC5 may use solve-under-assumptions
3. **Core extraction algorithm**: Post-processing to identify minimal core
4. **Proof production overhead**: Internal proof tracking for core justification

The combination of ~500 tracked assertions with the core production machinery creates significant overhead that compounds on UNSAT problems where the core must be computed.

### `decision=stoponly` Effect

The `stoponly` decision mode uses justification heuristics only to stop early, not for decisions. This reduces overhead while retaining some benefits of justification-based reasoning. On UNSAT problems, early stopping based on conflict detection provides significant speedup.

### `bv-eager-eval=true` Effect

Enables eager evaluation of bitvector expressions during constraint propagation. This reduces the depth of the search tree by evaluating concrete values earlier. Particularly effective on CF_TH_2 (0.377s vs 0.505s with stoponly alone).

### Options That Didn't Help

1. **`solve-bv-as-int`**: The int-blasting modes (sum, iand, bitwise) showed no significant improvement and slight regressions in some cases. The workload's bitwise operations don't benefit from integer arithmetic translation.

2. **`bv-gauss-elim=true`**: Gaussian elimination added overhead (7.47s vs 7.01s baseline).

3. **`bv-to-bool=true`**: Lifting 1-bit bitvectors to booleans hurt performance (8.52s vs 7.01s).

## Round 4: Integration Recommendations

### Option 1: Configurable Unsat Core Mode (Recommended)

Add a `diagnostic_mode` setting that controls whether unsat cores are produced:

```python
# In CVC5SolverAdapter.__init__
if settings.get("diagnostic_mode", True):
    self._solver.set("produce-unsat-cores", "true")
else:
    self._solver.set("decision", "stoponly")
    self._solver.set("bv-eager-eval", "true")
```

**Pros**:
- Users can opt for speed when they don't need diagnostics
- Preserves current behavior by default
- No code changes to unsat_core() method needed

**Cons**:
- Requires API surface for mode selection
- Users must understand trade-off

### Option 2: Always Optimize (Fast Mode)

Remove `produce-unsat-cores` and use optimized settings by default:

```python
# In CVC5SolverAdapter.__init__
self._solver.set("decision", "stoponly")
self._solver.set("bv-eager-eval", "true")
# No produce-unsat-cores
```

Modify `unsat_core()` to return empty list when cores unavailable:

```python
def unsat_core(self) -> List[str]:
    """Get labels of constraints in the unsatisfiable core."""
    # CVC5 running without core production - return empty
    return []
```

**Pros**:
- Simplest implementation
- Best performance by default

**Cons**:
- Loses diagnostic capability entirely
- May break user workflows that rely on unsat cores

### Option 3: Hybrid Approach

Use optimized settings by default, but provide a `with_diagnostics()` context manager or flag:

```python
# Fast mode (default)
solver = create_solver()

# Diagnostic mode (when needed)
solver = create_solver(settings={"diagnostic_mode": True})
```

**Pros**:
- Best of both worlds
- Clear API for users who need diagnostics

**Cons**:
- More complex implementation
- Potential confusion about default behavior

## Recommended Configuration

For immediate implementation, the following CVC5 options provide the best balance:

```python
# Optimized CVC5 configuration
self._solver.set("decision", "stoponly")
self._solver.set("bv-eager-eval", "true")
# Optionally, based on diagnostic_mode setting:
# self._solver.set("produce-unsat-cores", "true")
```

**Expected Performance**: ~1.6x slower than Z3 (down from ~9x slower)

## Appendix: Test Scripts

Test scripts created during research:
- `code/scripts/test_cvc5_options.py` - Initial broad option testing
- `code/scripts/test_cvc5_options_focused.py` - Focused testing on promising options

## Sources

- [CVC5 Options Documentation](https://cvc5.github.io/docs/cvc5-1.0.2/options.html)
- [CVC5 Python API](https://cvc5.github.io/docs/cvc5-1.1.2/api/python/base/solver.html)
- [CVC5 Statistics](https://cvc5.github.io/docs/cvc5-1.1.1/statistics.html)
- [Bit-Precise Reasoning via Int-Blasting](https://cvc5.github.io/papers/2022/ZoharIMNNPRBT-VMCAI22.pdf)
- [cvc5: A Versatile and Industrial-Strength SMT Solver](https://www-cs.stanford.edu/~preiner/publications/2022/BarbosaBBKLMMMN-TACAS22.pdf)
