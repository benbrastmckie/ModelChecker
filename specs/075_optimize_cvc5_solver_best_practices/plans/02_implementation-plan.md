# Implementation Plan: CVC5 Solver Optimization

- **Task**: 75 - Optimize CVC5 solver integration following best practices
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 74 (completed - provided performance findings)
- **Research Inputs**: reports/01_cvc5-best-practices.md, reports/02_team-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md
- **Type**: z3

## Overview

Add three-layer term identification fallback to `CVC5SolverAdapter.unsat_core()` to eliminate string conversion overhead during unsat core extraction. The implementation is minimal (~15 lines in 4 locations) and internal to `cvc5_adapter.py` - no protocol changes required.

### Research Integration

Team research (reports/02_team-research.md) confirmed:
1. `is None` pattern already applied in structure.py - no action needed
2. Term ID tracking via `get_id()` eliminates ~7.9s overhead (14% of excess time)
3. Adapter pattern is consistent with industry practice (pySMT, JavaSMT)

## Goals & Non-Goals

**Goals**:
- Add term ID-based lookup (Layer 2) to `unsat_core()` for O(1) term matching
- Register `constraint.get_id()` in `assert_tracked()`
- Clear tracking dict in `reset()`
- Add defensive `hasattr()` guard for API safety

**Non-Goals**:
- Protocol changes (not needed)
- Modifying Z3 adapter (uses native `assert_and_track`)
- Model core optimization (optional, out of scope)
- Renaming internal dicts (cosmetic, out of scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| CVC5 API changes `get_id()` | Low | Low | Guard with `hasattr()` check |
| Performance regression | Medium | Low | Run benchmark before/after |
| Dict memory growth | Low | Low | Already reset in `reset()` method |

## Implementation Phases

### Phase 1: Add Term ID Tracking Infrastructure [COMPLETED]

**Goal**: Add new tracking dictionary and register term IDs during `assert_tracked()`

**Tasks**:
- [ ] Add `_term_id_to_label: Dict[int, str] = {}` to `__init__`
- [ ] Register `constraint.get_id() -> label` in `assert_tracked()` with `hasattr()` guard
- [ ] Clear `_term_id_to_label` in `reset()` method

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Lines 27, 62-82, 209-220

**Verification**:
- Code review: new dict initialized, registered, cleared
- No import changes needed (int is builtin)

---

### Phase 2: Implement Three-Layer Lookup in unsat_core() [COMPLETED]

**Goal**: Insert Layer 2 (term ID) lookup between existing Layer 1 (py id) and Layer 3 (string)

**Tasks**:
- [ ] After py_id lookup fails, try `term.get_id()` lookup with `hasattr()` guard
- [ ] Only fall through to string matching if both Layer 1 and Layer 2 miss

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Lines 147-167

**Verification**:
- Code review: three-layer fallback logic correct
- Maintains existing behavior when `get_id()` unavailable

---

### Phase 3: Test and Validate [COMPLETED]

**Goal**: Verify optimization works and provides expected performance improvement

**Tasks**:
- [ ] Run existing CVC5 tests to verify no regression
- [ ] Run example.py with CVC5 backend, confirm unsat_core still works
- [ ] Optional: benchmark unsat_core extraction time before/after

**Timing**: 30 minutes

**Verification**:
- All existing tests pass
- Example with CVC5 backend produces correct results
- No errors or warnings from new code path

## Testing & Validation

- [ ] Run `pytest code/src/model_checker/solver/` to verify adapter tests pass
- [ ] Run example with `--solver cvc5` flag to verify end-to-end
- [ ] Verify no import errors (no new dependencies)

## Artifacts & Outputs

- `code/src/model_checker/solver/cvc5_adapter.py` - Modified with term ID tracking
- `specs/075_optimize_cvc5_solver_best_practices/summaries/02_execution-summary.md` - Implementation summary

## Rollback/Contingency

If the optimization causes issues:
1. Remove `_term_id_to_label` dict and all references
2. Remove Layer 2 lookup from `unsat_core()`
3. Existing Layer 1 + Layer 3 fallback continues to work

The change is additive and backwards-compatible - removing it restores original behavior.
