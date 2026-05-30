# Research Report: Model-Checker Architecture for CVC5 Optimizations

- **Task**: 75 - Optimize CVC5 solver integration following best practices
- **Date**: 2026-03-31
- **Mode**: Team Research (2 teammates)
- **Session**: sess_1774997480_uR4fvT

## Summary

Team research analyzed the model-checker's dual-solver architecture to design elegant, maintainable CVC5 optimizations. Both teammates independently converged on the same recommendation: enhance `CVC5SolverAdapter` internals with a three-layer term identification fallback, requiring no changes to the protocol interface or any other files. The `is None` pattern is already fully applied across all relevant locations.

## Key Findings

### 1. Architecture Overview (Teammate A)

The model-checker uses a clean Protocol-based adapter pattern:

```
              ┌──────────────────────────┐
              │  registry / create_solver │
              └────────────┬─────────────┘
                           |
            +--------------+-------------+
            |                            |
            v                            v
    ┌───────────────┐          ┌──────────────────┐
    │Z3SolverAdapter│          │CVC5SolverAdapter  │
    │               │          │                   │
    │ Uses Z3 native│          │ Manual tracking:  │
    │ assert_and_   │          │ _tracked (label)  │
    │ track()       │          │ _reverse (py id)  │
    │               │          │ _str_to_label     │
    └───────┬───────┘          └────────┬──────────┘
            |                           |
            +----------+----------------+
                       |
                       v
            ┌──────────────────────┐
            │ TrackedSolverProtocol │  (structural typing)
            │ - add()              │
            │ - check()            │
            │ - model()            │
            │ - assert_tracked()   │
            │ - unsat_core()       │
            │ - push() / pop()     │
            └──────────────────────┘
```

Key architectural properties:
- **Structural subtyping via Protocols** - no shared base class, maximum flexibility
- **`z3_shim.py`** - transitional compatibility layer, transparent to optimizations
- **Iteration path** - CVC5 bypasses adapter, accesses raw solver directly (intentional)

### 2. `is None` Pattern Status (Teammate A)

**Fully applied - no action required.** All critical locations confirmed:

| File | Line | Method | Pattern |
|------|------|--------|---------|
| structure.py | 110 | `__init__` | `if self.z3_model is None:` |
| structure.py | 329 | `interpret()` | `if self.z3_model is None:` |
| structure.py | 391 | `_get_relevant_constraints()` | `if self.z3_model is not None:` |
| structure.py | 595 | `print_input_sentences()` | `if self.z3_model is None:` |
| structure.py | 879 | `extract_verify_falsify_state()` | `if self.z3_model is None:` |
| iterator.py | 52 | | `z3_model is None` |
| example.py | 260 | | `z3_model is None` |
| logos/semantic.py | 1465, 1693 | | `z3_model is not None` / `is None` |
| bimodal/semantic.py | 1820+ | | `z3_model is None` |
| testing.py | 140 | | `z3_model is not None` |

No remaining `if not self.z3_model:` or `if self.z3_model:` patterns exist.

### 3. Design Pattern Analysis (Teammate B)

Four patterns evaluated for term tracking:

| Pattern | Fit | Complexity | Extensibility | Matches Codebase |
|---------|-----|------------|---------------|------------------|
| **Adapter (current)** | **High** | **Low** | **Medium** | **Yes** |
| Strategy | Medium | Medium | High | Partial |
| Bridge | Medium | High | High | No |
| Template Method | Low | Medium | Low | No |

**Recommendation**: Continue with the Adapter pattern. The term tracking enhancement is an implementation detail within `CVC5SolverAdapter`, not a shared abstraction.

### 4. Prior Art Validation (Teammate B)

| System | Language | Term Tracking Approach |
|--------|----------|----------------------|
| **pySMT** | Python | Per-adapter tracking; own formula layer |
| **JavaSMT** | Java | Solver-native equality via `isSame()` |
| **Dolmen/Alt-Ergo** | OCaml | Algebraic types give structural equality |

All major multi-solver systems use per-adapter tracking strategies. The project's approach is consistent with industry practice.

## Synthesis

### Conflicts Resolved

None - both teammates independently reached the same conclusion: enhance `CVC5SolverAdapter` internals with term ID tracking, no protocol changes needed.

### Gaps Identified

None significant. Both teammates covered complementary angles (architecture internals vs. design patterns/prior art) that together provide complete coverage.

### Recommended Implementation

**Three-layer term identification fallback in `CVC5SolverAdapter`:**

```
Layer 1: Python object identity - id(term)
         O(1), works when solver returns same wrapper object (~50% hit rate)

Layer 2: CVC5 term ID - term.get_id()        [NEW]
         O(1), stable across wrapper recreation

Layer 3: String representation - str(term)
         O(n), deferred/lazy, computed only when Layers 1-2 both fail
```

**Changes required (4 locations, ~15 lines in `cvc5_adapter.py` only):**

1. **Constructor**: Add `_term_id_to_label: Dict[int, str] = {}`
2. **`assert_tracked()`**: Register `constraint.get_id()` -> label
3. **`unsat_core()`**: Insert Layer 2 lookup between py_id and str fallback
4. **`reset()`**: Clear `_term_id_to_label`

**Guarded with `hasattr(constraint, 'get_id')`** for safety if CVC5 API changes.

### Naming Improvements (from Teammate B)

Consider renaming internal dicts for clarity:
- `_reverse` -> `_by_py_id` (communicates intent)
- `_str_to_label` -> `_by_str` (simpler)
- Add `_str_populated: bool` flag to prevent repopulating when strings are never needed

### Documentation

Add class-level docstring explaining the three-layer tracking strategy and its performance rationale. This serves as guidance for future adapter authors.

### Extensibility

Future backends will fit the same pattern:
- **Bitwuzla**: `term.id()` - matches CVC5 `get_id()` exactly
- **Yices**: Terms are integer indices internally
- No shared `TermTracker` abstraction needed

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Architecture & adapter analysis | completed | High |
| B | Design patterns & prior art | completed | High |

## Performance Impact

| Optimization | Overhead Eliminated | Status |
|-------------|---------------------|--------|
| `is None` checks | ~48s (85%) | Already applied |
| Term ID tracking | ~7.9s (14%) | Ready to implement |
| Model cores | Variable | Optional (CVC5-specific method) |

After implementation, CVC5 should perform at ~20x slower than Z3 (raw solver ratio) rather than the observed 32x.

## References

- Task 74 reports: `specs/074_*/reports/*.md`
- Task 75 report 01: `specs/075_*/reports/01_cvc5-best-practices.md`
- CVC5 Term API: cvc5.github.io/docs/cvc5-1.0.0/api/cpp/term.html
- pySMT: github.com/pysmt/pysmt
- JavaSMT: github.com/sosy-lab/java-smt
