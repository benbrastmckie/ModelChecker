# Implementation Plan: Task #74

- **Task**: 74 - Investigate CVC5 model evaluation and iteration performance bottleneck
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/074_investigate_cvc5_iteration_performance/reports/02_cvc5-deep-dive.md
- **Artifacts**: plans/02_cvc5-performance-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

The research identified two root causes for CVC5's 32x slowdown vs Z3: (1) Python truthiness checks (`if not model:`) triggering expensive `__len__()` enumeration on CVC5 models (~48s overhead), and (2) string conversion in `assert_tracked()` invoking CVC5's slow pretty printer (~8s overhead). This plan fixes both issues with targeted code changes.

### Research Integration

- Root cause 1 accounts for 85% of overhead (5 calls at ~9.5s each)
- Root cause 2 accounts for 14% of overhead (523 calls at ~15ms each)
- `model.eval()` is NOT the bottleneck (CVC5 is actually faster than Z3 in isolation)
- Expected improvement: from 32x slower to ~20x slower (matching raw solver ratio)

## Goals & Non-Goals

**Goals**:
- Eliminate Python-level performance overhead in CVC5 model operations
- Reduce CVC5 BuildExample time from ~18s to ~0.5-1s (matching solver ratio)
- Maintain full backward compatibility with Z3 backend
- Preserve unsat core tracking functionality

**Non-Goals**:
- Improving CVC5's native solver performance (out of scope)
- Hybrid Z3/CVC5 switching strategy (deferred to future task)
- CVC5 solver option tuning (not possible at runtime per research)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Lazy string conversion breaks unsat core matching | H | M | Test unsat core extraction with CVC5 |
| `is None` check misses falsy model values | M | L | Review CVC5 model semantics; test edge cases |
| Regression in Z3 performance | M | L | Run full test suite with both backends |

## Implementation Phases

### Phase 1: Fix Truthiness Checks in structure.py [COMPLETED]

**Goal**: Eliminate expensive `__len__()` calls by using explicit `is None` checks

**Tasks**:
- [ ] Change line 328: `if not self.z3_model:` -> `if self.z3_model is None:`
- [ ] Change line 389: `if self.z3_model:` -> `if self.z3_model is not None:`
- [ ] Change line 592: `if not self.z3_model:` -> `if self.z3_model is None:`
- [ ] Change line 875: `if not self.z3_model:` -> `if self.z3_model is None:`

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - 4 truthiness check replacements

**Verification**:
- Run existing tests: `cd code && pytest tests/ -k model`
- Verify no regressions with Z3 backend

---

### Phase 2: Defer String Conversion in cvc5_adapter.py [COMPLETED]

**Goal**: Eliminate ~8s overhead from string conversion during constraint setup

**Tasks**:
- [ ] Remove immediate `str(constraint)` call from `assert_tracked()` (line 80)
- [ ] Implement lazy string conversion in `unsat_core()` method
- [ ] Update `_str_to_label` to be populated on-demand when unsat core is requested
- [ ] Add comment documenting the performance rationale

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Defer string conversion

**Implementation detail**:
```python
def assert_tracked(self, constraint, label):
    ...
    self._tracked[label] = constraint
    self._reverse[id(constraint)] = label
    # String conversion deferred until unsat_core() is called
    # (CVC5's str() is expensive: ~15ms per term)
    self._solver.add(constraint)

def unsat_core(self):
    # Lazy populate string-to-label mapping only when needed
    if not self._str_to_label:
        self._str_to_label = {str(c): l for l, c in self._tracked.items()}
    ...
```

**Verification**:
- Test unsat core extraction: create UNSAT model, verify core labels are correct
- Verify SAT models still work (string conversion should never be needed)

---

### Phase 3: Performance Verification [COMPLETED]

**Goal**: Verify the fixes achieve expected performance improvement

**Tasks**:
- [ ] Run counterfactual example with CVC5 backend
- [ ] Measure BuildExample construction time
- [ ] Compare against baseline (~18s) and target (~1s)
- [ ] Run full test suite with both Z3 and CVC5 backends

**Timing**: 30 minutes

**Files to modify**:
- None (verification only)

**Verification commands**:
```bash
# Test CVC5 performance after fixes
cd code && PYTHONPATH=src python -c "
from model_checker.solver.lifecycle import set_backend_with_invalidation
from model_checker.builder.example import BuildExample
import model_checker.theory_lib.logos.subtheories.counterfactual.examples as cf_examples
import time

semantic_theory = list(cf_examples.semantic_theories.values())[0]
example_case = cf_examples.example_range.get('CF_CM_1')

class MockBuildModule:
    def __init__(self, semantic_theories):
        self.semantic_theories = semantic_theories
        self.general_settings = {}
        self.module_flags = type('Flags', (), {'file_path': 'test'})()
        self.raw_general_settings = {}

mock_module = MockBuildModule({'default': semantic_theory})

set_backend_with_invalidation('cvc5')
cvc5_case = [example_case[0], example_case[1], {**example_case[2], 'solver': 'cvc5'}]
t0 = time.perf_counter()
cvc5_example = BuildExample(mock_module, semantic_theory, cvc5_case)
elapsed = time.perf_counter() - t0
print(f'CVC5 BuildExample time: {elapsed:.3f}s')
print(f'Target: <1s, Baseline: ~18s')
print(f'Status: {\"PASS\" if elapsed < 2 else \"NEEDS INVESTIGATION\"}')"
```

**Success criteria**:
- CVC5 BuildExample time < 2 seconds (10x improvement from ~18s baseline)
- All existing tests pass with both backends
- Unsat core extraction still works correctly

---

### Phase 4: Documentation and Cleanup [COMPLETED]

**Goal**: Document the performance fix and update any relevant comments

**Tasks**:
- [ ] Add inline comments explaining the `is None` pattern choice
- [ ] Update any docstrings that reference model truthiness checks
- [ ] Create implementation summary

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Add explanatory comments
- `code/src/model_checker/solver/cvc5_adapter.py` - Document lazy conversion rationale

**Verification**:
- Code review for clarity

## Testing & Validation

- [ ] Unit tests pass: `cd code && pytest tests/`
- [ ] CVC5 backend tests pass: `pytest tests/ -k cvc5`
- [ ] Z3 backend tests pass: `pytest tests/ -k z3`
- [ ] Counterfactual examples work with CVC5 solver option
- [ ] Unsat core extraction works with CVC5 backend
- [ ] Performance improvement verified (BuildExample < 2s)

## Artifacts & Outputs

- Modified `code/src/model_checker/models/structure.py` (4 line changes)
- Modified `code/src/model_checker/solver/cvc5_adapter.py` (lazy string conversion)
- Implementation summary at `specs/074_investigate_cvc5_iteration_performance/summaries/02_cvc5-performance-summary.md`

## Rollback/Contingency

If the fixes cause regressions:
1. Revert the 4 truthiness check changes in structure.py
2. Restore immediate string conversion in cvc5_adapter.py
3. File follow-up task for deeper CVC5 integration investigation

The changes are localized and easily reversible via git revert.
