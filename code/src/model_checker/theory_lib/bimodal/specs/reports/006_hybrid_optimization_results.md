# Hybrid Witness-ForAll Optimization - Performance Results

## Metadata
- **Date**: 2025-10-02
- **Related Plan**: specs/plans/005_hybrid_witness_forall_optimization.md
- **Related Reports**:
  - specs/reports/005_universal_witness_integration.md
  - specs/reports/003_future_past_asymmetry_investigation.md

## Methodology

### Test Environment
- **Hardware**: Standard development machine
- **Z3 Version**: Python bindings (latest)
- **Test Cases**: BM_CM_1 (Future → Box), BM_CM_2 (Past → Box)
- **Measurement**: Z3 solver run time (seconds)

### Implementation Phases
1. **Baseline**: Original ForAll with z3.And in antecedent
2. **Phase 1**: Nested implications
3. **Phase 2**: Explicit pattern annotation
4. **Phase 3**: Witness instantiation hints (tested but disabled)
5. **Phase 4**: Z3 configuration tuning

## Performance Results

### Test Case: BM_CM_1 (`\Future A |- \Box A`)

| Phase | Implementation | Time (s) | vs Baseline | vs Previous | Notes |
|-------|---------------|----------|-------------|-------------|-------|
| Baseline | Original z3.And structure | timeout (~30s) | - | - | Would timeout |
| Phase 1 | Nested implications | 4.49 | - | - | First completion! |
| Phase 2 | + Explicit patterns | 5.00 | - | +11% | Slight regression |
| Phase 3 | + Witness hints | 14.1 | - | +182% | **Disabled** |
| Phase 4 | + Z3 config (tuned) | **0.002** | **15000x** | **99.96%** | **Final** |

### Test Case: BM_CM_2 (`\Past A |- \Box A`)

| Phase | Implementation | Time (s) | vs Baseline | vs Previous | Notes |
|-------|---------------|----------|-------------|-------------|-------|
| Baseline | Original z3.And structure | 3.24 | - | - | Already working |
| Phase 1 | Nested implications | 3.24 | Same | Same | No change |
| Phase 2 | + Explicit patterns | 0.03 | 99% | 99% | Major improvement! |
| Phase 3 | + Witness hints | 3.54 | -9% | +11700% | **Disabled** |
| Phase 4 | + Z3 config (tuned) | **0.03** | **99%** | **Same** | **Final** |

### Overall Impact

**BM_CM_1 (Problematic Case)**:
- Baseline: timeout (>30s)
- Final: 0.002s
- **Improvement: ~15000x faster**

**BM_CM_2 (Baseline Case)**:
- Baseline: 3.24s
- Final: 0.03s
- **Improvement: ~108x faster**

## Key Findings

### 1. Nested Implications (Phase 1)
**Impact**: Critical foundation
- Enabled BM_CM_1 to complete for first time
- No performance change for BM_CM_2
- Clearer structure for Z3 pattern inference

**Mechanism**: By separating `is_world()` and `is_valid_time_for_world()` checks into nested implications instead of `z3.And()`, Z3 can infer simpler patterns and instantiate more efficiently.

### 2. Explicit Patterns (Phase 2)
**Impact**: Huge improvement for some cases
- BM_CM_1: 11% slower (5.00s vs 4.49s)
- BM_CM_2: 99% faster! (0.03s vs 3.24s)
- Mixed results suggest pattern quality varies by formula structure

**Mechanism**: `patterns=[is_world(other_world)]` forces Z3 to instantiate ForAll only when `is_world(...)` ground terms appear. This is extremely efficient when ground terms are limited (BM_CM_2) but can be slower when many ground terms exist (BM_CM_1).

### 3. Witness Instantiation Hints (Phase 3)
**Impact**: Performance regression - DISABLED
- BM_CM_1: 182% slower (14.1s vs 5.00s)
- BM_CM_2: 11700% slower (3.54s vs 0.03s)
- Creates too many ForAll instantiations via ground terms

**Mechanism**: Hints generate constraints like `is_world(accessible_world(eval_world, eval_time))`, creating ground terms that trigger the explicit patterns from Phase 2. However, this creates an instantiation explosion rather than helpful guidance.

**Lesson**: Witness-ForAll integration needs more sophisticated approach than simple ground term generation. The hints work conceptually but need refinement to avoid triggering excessive instantiations.

### 4. Z3 Configuration (Phase 4)
**Impact**: Dramatic improvement - THE KEY OPTIMIZATION
- BM_CM_1: 99.96% faster (0.002s vs 5.00s)
- BM_CM_2: Maintained fast performance (0.03s)
- Conservative instantiation prevents runaway behavior

**Final Configuration**:
```python
_z3_config = {
    'smt.mbqi': False,              # Explicit patterns sufficient
    'smt.qi.eager_threshold': 100.0, # Conservative instantiation
    'smt.qi.max_instances': 1000,    # Safety limit
}
```

**Mechanism**:
- **MBQI disabled**: Model-based quantifier instantiation adds overhead when explicit patterns already work. E-matching alone is sufficient.
- **High eager_threshold**: Makes Z3 more conservative about instantiating quantifiers, preventing speculative instantiation loops.
- **Max instances limit**: Provides safety net against pathological cases while allowing enough instantiations for valid reasoning.

## Analysis

### What Worked

1. **Nested Implications (Phase 1)**: Essential structural improvement
2. **Explicit Patterns (Phase 2)**: Guides E-matching effectively
3. **Conservative Z3 Config (Phase 4)**: THE critical optimization
   - Disabling MBQI was counterintuitive but crucial
   - Conservative thresholds prevent instantiation explosion
   - Total speedup: 15000x for BM_CM_1, 108x for BM_CM_2

### What Didn't Work

1. **Witness Instantiation Hints (Phase 3)**: Created performance regression
   - Concept is sound: use witness ground terms to guide ForAll instantiation
   - Implementation issue: hints trigger too many pattern matches
   - Future work: Need selective hint generation or refined patterns

### Why Phase 4 Succeeds

The key insight is that **explicit patterns + conservative instantiation** is more effective than **explicit patterns + MBQI + hints**.

**Without Phase 4 config**:
- Z3 tries to instantiate ForAll eagerly
- Pattern triggers on every `is_world(...)` term
- Creates cascade of instantiations

**With Phase 4 config**:
- Z3 instantiates conservatively
- Only instantiates when truly necessary
- Pattern matching happens but doesn't cascade
- MBQI overhead avoided entirely

## Recommended Configuration

### For Box Operator (Universal Quantification)

```python
def true_at(self, argument, eval_point):
    """Box is true when argument is true in ALL accessible worlds.

    Optimized with explicit pattern and nested implications.
    """
    semantics = self.semantics
    eval_time = eval_point["time"]

    other_world = z3.Int('box_true_world')

    return z3.ForAll(
        [other_world],
        z3.Implies(
            semantics.is_world(other_world),
            z3.Implies(
                semantics.is_valid_time_for_world(other_world, eval_time),
                semantics.true_at(argument, {"world": other_world, "time": eval_time})
            )
        ),
        patterns=[semantics.is_world(other_world)]  # Explicit pattern
    )
```

### For Z3 Solver

```python
_z3_config = {
    'smt.mbqi': False,              # Disable MBQI when patterns work
    'smt.qi.eager_threshold': 100.0, # Conservative instantiation
    'smt.qi.max_instances': 1000,    # Reasonable limit
}
```

Apply via:
```python
solver = z3.Solver()
for key, value in semantics._z3_config.items():
    solver.set(key, value)
```

## Limitations

### Remaining Issues

1. **Formula-Specific Sensitivity**: Different formulas may benefit from different configurations
2. **Witness Hint Integration**: Phase 3 hints need refinement to be useful
3. **Parameter Tuning**: Current config works well but may not be optimal for all cases

### When This Approach May Not Work

- **Deeply nested modals**: May need higher `max_instances`
- **Complex accessibility relations**: May benefit from different patterns
- **Large M values**: May need adjusted thresholds

## Future Work

### Potential Improvements

1. **Adaptive Configuration**: Adjust Z3 parameters based on formula complexity
2. **Selective Witness Hints**: Generate hints only for specific witness predicates
3. **Pattern Refinement**: Multi-patterns or pattern guards to control instantiation
4. **Profiling Integration**: Use Z3's quantifier profiling to tune dynamically

### Applying to Other Operators

The same optimization strategy can be applied to:
- **Diamond operator**: If ForAll ever needed (currently witness-based)
- **Past/Future operators**: If modal quantification added
- **Frame constraints**: Any universal quantification over worlds

### Research Directions

1. **Witness-ForAll Bridge**: Investigate why hints cause regression
   - Perhaps hints should only assert witness validity, not trigger patterns
   - Maybe separate hint predicates from pattern triggers
2. **Pattern Libraries**: Build catalog of effective patterns for modal operators
3. **Automatic Tuning**: Machine learning to predict optimal Z3 config per formula

## Conclusion

### Success Metrics

✓ BM_CM_1 completes without timeout: **0.002s** (was >30s)
✓ BM_CM_2 maintains performance: **0.03s** (was 3.24s)
✓ 100-15000x speedup on Box formulas
✓ All existing examples pass
✓ No regressions in test suite

### Implementation Status

- **Phase 1** (Nested implications): ✓ Complete
- **Phase 2** (Explicit patterns): ✓ Complete
- **Phase 3** (Witness hints): ✓ Implemented, Disabled (needs refinement)
- **Phase 4** (Z3 config): ✓ Complete and Highly Effective

### Key Takeaways

1. **Structure matters**: Nested implications enable better pattern inference
2. **Explicit patterns work**: Direct Z3 to instantiate efficiently
3. **Conservative is better**: High thresholds prevent instantiation explosions
4. **MBQI not always helpful**: Explicit patterns sufficient, MBQI adds overhead
5. **Measure everything**: Phase 3 seemed promising but regressed performance

### Recommendations for Future Modal Operators

When implementing modal operators with ForAll quantification:

1. Use nested implications for cleaner structure
2. Add explicit patterns on simplest predicate (e.g., `is_world`)
3. Configure Z3 conservatively:
   - Disable MBQI if patterns work
   - Use high eager_threshold (100+)
   - Set reasonable max_instances (1000-2000)
4. Test witness hints carefully - they can help or hurt
5. Profile before and after each optimization

---

**Plan Reference**: specs/plans/005_hybrid_witness_forall_optimization.md
**Related Reports**:
- specs/reports/005_universal_witness_integration.md (strategy research)
- specs/reports/003_future_past_asymmetry_investigation.md (problem analysis)
