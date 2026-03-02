# Stage 5: Dual-Solver Validation

## Metadata
- **Stage**: 5/6 (Phase 3 - Bimodal Abstraction Integration)
- **Estimated Duration**: 1 day (8 hours)
- **Complexity**: Medium-High
- **Dependencies**: Stage 4 complete (examples & iteration migrated)
- **Files**:
  - All bimodal tests (unit + integration) - VALIDATE
  - `code/tests/integration/test_solver_equivalence.py` - VALIDATE
  - `tests/integration/test_performance_validation.py` - VALIDATE
  - `benchmark_abstraction_overhead.py` - CREATE & RUN
- **Coverage Target**: Maintain all coverage targets (>85% overall, >90% witness)
- **Risk**: Medium - Performance regression detection, equivalence validation

## Objective

Validate that both Z3 and CVC5 backends work correctly through the abstraction layer. Ensure backward compatibility with Z3, maintain CVC5 performance, and verify semantic equivalence between solvers.

**Success Criteria**:
- Z3 backend: All tests pass (100% backward compatibility)
- CVC5 backend: Performance maintained (~6ms on BM_CM_*)
- Equivalence: Z3 and CVC5 produce same sat/unsat results
- Abstraction overhead: <5% measured and documented
- No memory leaks or resource issues

## Implementation Tasks

### Task 1: Z3 Regression Testing (Backward Compatibility)
**Duration**: 2 hours

- [ ] Configure settings: `SMT_SOLVER=z3`
- [ ] Run full bimodal unit test suite with Z3
- [ ] Run full bimodal integration test suite with Z3
- [ ] Compare results against pre-abstraction baseline
- [ ] Document any differences or regressions
- [ ] Verify all examples work (timeouts are expected per Phase 0 baseline)

**Testing Commands**:
```bash
# Run all bimodal unit tests with Z3
PYTHONPATH=code/src SMT_SOLVER=z3 pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v

# Run all bimodal integration tests with Z3
PYTHONPATH=code/src SMT_SOLVER=z3 pytest code/src/model_checker/theory_lib/bimodal/tests/integration/ -v

# Run all examples with Z3
cd Code
PYTHONPATH=src SMT_SOLVER=z3 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Expected: All tests PASS, behavior identical to pre-abstraction Z3
```

### Task 2: CVC5 Performance Validation
**Duration**: 2 hours

- [ ] Configure settings: `SMT_SOLVER=cvc5`
- [ ] Run performance validation suite
- [ ] Measure solve times for 6 critical examples
- [ ] Compare against Phase 1 direct CVC5 measurements
- [ ] Verify BM_CM_* examples ~6ms (vs 5000ms+ with Z3)
- [ ] Document performance metrics

**Critical Examples**:
1. BM_CM_1: ~6ms (Z3: >5000ms)
2. BM_CM_2: ~6ms (Z3: >5000ms)
3. TN_CM_2: ~0.2ms (Z3: timeout)
4. TN_CM_3: ~0.2ms (Z3: timeout)
5. MD_CM_1: fast
6. MD_CM_2: fast

**Testing Commands**:
```bash
# Run performance tests
PYTHONPATH=code/src SMT_SOLVER=cvc5 pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_performance_validation.py -v

# Expected: All critical examples solve in <10ms
```

### Task 3: Equivalence Testing (Z3 vs CVC5)
**Duration**: 2 hours

- [ ] Run equivalence test suite: `test_solver_equivalence.py`
- [ ] Execute all 22 examples with both Z3 and CVC5
- [ ] Compare sat/unsat results
- [ ] Verify semantic equivalence of models
- [ ] Document expected differences (if any)
- [ ] Handle cases where Z3 times out but CVC5 succeeds

**Testing Commands**:
```bash
# Run equivalence tests
PYTHONPATH=code/src pytest code/tests/integration/test_solver_equivalence.py -v

# Expected: sat/unsat agreement on all solvable examples
# Note: Z3 timeouts don't count as disagreements
```

**Equivalence Test Pattern**:
```python
def test_example_equivalence(self):
    """Verify Z3 and CVC5 agree on sat/unsat."""
    factory = SolverFactory()

    # Run with Z3
    z3_result = run_with_solver(factory.create("z3"), "BM_CM_1")

    # Run with CVC5
    cvc5_result = run_with_solver(factory.create("cvc5"), "BM_CM_1")

    # If both solved, results must agree
    if z3_result != "unknown" and cvc5_result != "unknown":
        self.assertEqual(z3_result, cvc5_result)
```

### Task 4: Abstraction Overhead Benchmarking
**Duration**: 2 hours

- [ ] Create benchmark script: `benchmark_abstraction_overhead.py`
- [ ] Compare Phase 3 (abstraction) vs Phase 1 (direct CVC5) performance
- [ ] Measure overhead on 6 critical examples
- [ ] Calculate overhead percentage
- [ ] Target: <5% overhead
- [ ] Document results in performance table

**Benchmark Script Structure**:
```python
import time
from model_checker.solver import SolverFactory

def benchmark_example(example_name, iterations=10):
    """Benchmark example with abstraction."""
    factory = SolverFactory()
    adapter = factory.create("cvc5")

    times = []
    for _ in range(iterations):
        start = time.time()
        result = run_example(adapter, example_name)
        duration = (time.time() - start) * 1000  # ms
        times.append(duration)

    avg_time = sum(times) / len(times)
    return avg_time

# Compare against Phase 1 baseline
phase1_baseline = {"BM_CM_1": 6.0, "BM_CM_2": 6.0, ...}
phase3_results = {name: benchmark_example(name) for name in phase1_baseline}

# Calculate overhead
for name in phase1_baseline:
    overhead = (phase3_results[name] - phase1_baseline[name]) / phase1_baseline[name] * 100
    print(f"{name}: {overhead:.2f}% overhead")
```

**Testing Commands**:
```bash
cd Code
nix-shell ../shell.nix --run "PYTHONPATH=src python3 benchmark_abstraction_overhead.py"

# Expected: <5% overhead on all critical examples
```

### Task 5: Memory and Resource Validation
**Duration**: 1 hour

- [ ] Check for memory leaks (long-running examples)
- [ ] Verify resource cleanup (solver instances)
- [ ] Test multiple solver creation/destruction cycles
- [ ] Profile memory usage with both solvers
- [ ] Ensure no resource accumulation

**Memory Test Pattern**:
```python
import tracemalloc

def test_no_memory_leaks():
    """Test repeated solver creation doesn't leak memory."""
    tracemalloc.start()

    factory = SolverFactory()
    baseline = tracemalloc.get_traced_memory()

    # Create and destroy 100 solvers
    for _ in range(100):
        adapter = factory.create("cvc5")
        solver = adapter.create_solver()
        # ... use solver
        del solver
        del adapter

    current = tracemalloc.get_traced_memory()
    growth = (current[0] - baseline[0]) / baseline[0]

    # Memory growth should be minimal (<10%)
    assert growth < 0.10
```

### Task 6: Document Validation Results
**Duration**: 1 hour

- [ ] Create performance comparison table (Phase 1 vs Phase 3)
- [ ] Document equivalence test results (all 22 examples)
- [ ] Record overhead measurements
- [ ] Note any solver-specific behaviors
- [ ] Capture findings for Stage 6 reporting

**Performance Table Template**:
```markdown
| Example | Z3 Baseline | CVC5 Phase 1 | CVC5 Phase 3 | Overhead | Status |
|---------|-------------|--------------|--------------|----------|--------|
| BM_CM_1 | 5000ms+     | 6.0ms        | 6.2ms        | 3.3%     | ✅     |
| BM_CM_2 | 5000ms+     | 6.0ms        | 6.1ms        | 1.7%     | ✅     |
| ...     | ...         | ...          | ...          | ...      | ...    |
```

**Equivalence Table Template**:
```markdown
| Example | Z3 Result | CVC5 Result | Agreement | Status |
|---------|-----------|-------------|-----------|--------|
| BM_CM_1 | sat       | sat         | ✅        | ✅     |
| BM_CM_2 | sat       | sat         | ✅        | ✅     |
| TN_CM_2 | timeout   | sat         | N/A       | ✅     |
| ...     | ...       | ...         | ...       | ...    |
```

## Testing Strategy

**Comprehensive Test Matrix**:
```bash
# 1. Z3 full regression
PYTHONPATH=code/src SMT_SOLVER=z3 pytest code/src/model_checker/theory_lib/bimodal/tests/ -v

# 2. CVC5 full validation
PYTHONPATH=code/src SMT_SOLVER=cvc5 pytest code/src/model_checker/theory_lib/bimodal/tests/ -v

# 3. Equivalence testing
PYTHONPATH=code/src pytest code/tests/integration/test_solver_equivalence.py -v

# 4. Performance validation
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_performance_validation.py -v

# 5. Coverage check (both solvers)
PYTHONPATH=code/src SMT_SOLVER=z3 pytest code/src/model_checker/theory_lib/bimodal/tests/ --cov=model_checker.theory_lib.bimodal --cov-report=term-missing
PYTHONPATH=code/src SMT_SOLVER=cvc5 pytest code/src/model_checker/theory_lib/bimodal/tests/ --cov=model_checker.theory_lib.bimodal --cov-report=term-missing
```

**Performance Benchmarking**:
```bash
# Run benchmarks
cd Code
PYTHONPATH=src python3 benchmark_abstraction_overhead.py > performance_results.txt

# Analyze results
cat performance_results.txt | grep "overhead"
# Expected: All <5%
```

**Memory Profiling**:
```bash
# Profile memory usage
PYTHONPATH=code/src python3 -m memory_profiler test_memory_usage.py
```

## Success Criteria Checklist

- [ ] Z3 regression tests: All pass (100% backward compatibility)
- [ ] CVC5 performance tests: All critical examples ~6ms
- [ ] Equivalence tests: Z3 and CVC5 agree on all solvable examples
- [ ] Abstraction overhead: <5% measured on all examples
- [ ] No memory leaks detected
- [ ] No resource cleanup issues
- [ ] Performance metrics documented
- [ ] Equivalence results documented
- [ ] Both solvers fully validated

## Common Issues & Solutions

### Issue 1: Z3 Regression Failures
**Problem**: Tests that passed before now fail with Z3
**Cause**: Abstraction bug or incorrect adapter implementation
**Solution**: Compare Z3 adapter behavior against direct Z3, fix discrepancies

### Issue 2: CVC5 Performance Degradation
**Problem**: CVC5 slower than Phase 1 (>5% overhead)
**Cause**: Abstraction overhead in hot paths
**Solution**: Profile critical paths, optimize adapter methods, consider caching

### Issue 3: Equivalence Test Failures
**Problem**: Z3 and CVC5 produce different sat/unsat results
**Cause**: Solver semantic differences or adapter bugs
**Solution**: Investigate specific examples, validate adapter implementations, document expected differences

### Issue 4: Memory Leaks
**Problem**: Memory usage grows with repeated solver creation
**Cause**: Improper resource cleanup in adapter
**Solution**: Ensure solver destruction releases all resources, add explicit cleanup

### Issue 5: Inconsistent Performance
**Problem**: Performance varies widely between runs
**Cause**: System load or solver initialization overhead
**Solution**: Run multiple iterations, average results, control for system load

## Risk Mitigation

**Risk**: Performance regression not detected
**Impact**: Abstraction overhead exceeds 5%
**Mitigation**: Comprehensive benchmarking, multiple iterations, profiling

**Risk**: Equivalence differences not understood
**Impact**: Unknown solver behavior differences
**Mitigation**: Document all differences, validate semantics, consult solver documentation

**Risk**: Z3 regressions introduced
**Impact**: Backward compatibility broken
**Mitigation**: Extensive Z3 regression suite, compare against baseline

## Dependencies for Next Stage

Stage 6 (Documentation & Reporting) requires:
- ✅ Z3 fully validated (all tests pass)
- ✅ CVC5 fully validated (performance maintained)
- ✅ Equivalence validated (results agree)
- ✅ Overhead measured (<5%)
- ✅ No resource issues
- ✅ Performance and equivalence data collected

## Notes

**Performance Target**: <5% abstraction overhead is acceptable given benefits (dual-solver support, cleaner API, future extensibility).

**Equivalence Expectations**: Z3 may timeout where CVC5 succeeds (expected per Phase 1 findings). This doesn't count as disagreement.

**Coverage Maintenance**: All coverage targets from previous stages must be maintained (>85% overall, >90% witness).

**Validation Thoroughness**: This stage is critical for proving the abstraction layer works correctly. Take time to be thorough.

---

**Stage 5 Status**: ☐ Pending
**Previous Stage**: [Stage 4: Examples & Iteration Migration](stage04_examples_iteration_migration.md)
**Next Stage**: [Stage 6: Documentation & Reporting](stage06_documentation_reporting.md)
