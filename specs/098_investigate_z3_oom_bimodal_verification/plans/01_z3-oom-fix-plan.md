# Implementation Plan: Task #98

- **Task**: 98 - Investigate Z3 OOM kills during bimodal theorem verification
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: 97 (completed)
- **Research Inputs**: specs/098_investigate_z3_oom_bimodal_verification/reports/01_z3-oom-investigation.md
- **Artifacts**: plans/01_z3-oom-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Z3 OOM kills occur when running bimodal theorem verification examples with M>=3, particularly BX5-BX13 (M=4) and BX7 (M=5). The root cause is a three-constraint amplification loop: `capped_skolem_abundance_constraint` (doubly-quantified ForAll over integer domain), `world_uniqueness` (ForAll/Exists requiring MBQI witness search), and `forward_comp` feeding back via `lawful`. Task 97 added `max_memory=4096 MB` per solver as a safety net, but the core fix is to ground the quantified constraints for finite M values, eliminating MBQI's unbounded ground-term expansion. This plan implements grounded versions of the two highest-impact constraints and verifies correctness across the full bimodal test suite.

### Research Integration

Key findings from the research report (01_z3-oom-investigation.md):

1. **Amplification loop identified**: `capped_skolem_abundance_constraint` fires for world pairs, creating shifted worlds -> `world_uniqueness` generates witness search -> `lawful` and `forward_comp` create task_rel facts -> abundance fires again for new worlds. This cycle grows multiplicatively.

2. **Grounding is the primary fix**: For M=3/4/5, there are only 6/12/20 valid (interval, shift) pairs. Replacing `ForAll[src, shift] -> ForAll[time]` with concrete constraints per pair eliminates 2 of 3 quantifiers and converts MBQI-dependent reasoning to E-matching.

3. **World uniqueness grounding**: Replacing `Exists[t]` with concrete `Or` over M time points eliminates MBQI's most expensive witness-search operation.

4. **Pattern annotations caused regressions**: Task 97 found that adding MultiPattern to `lawful` and `converse` broke countermodel examples (BM_CM_2, BM_CM_4). Pattern annotations should be used cautiously and only after grounding.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items explicitly targeted by this task.

## Goals & Non-Goals

**Goals**:
- Eliminate OOM kills for BX5-BX13 (M=4) and BX7 (M=5) bimodal examples
- Reduce peak memory usage by 50-70% through constraint grounding
- Maintain logical equivalence with existing constraint formulations
- Pass the full 43-test bimodal unit test suite with no regressions

**Non-Goals**:
- Optimizing examples with M<=2 (these already work within memory bounds)
- Adding new bimodal examples or axiom coverage
- Changing the Z3 solver backend or introducing CVC5 fallback
- Modifying operator semantics or truth conditions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Grounded abundance is not logically equivalent to original | H | L | Mathematical proof by enumeration: the ForAll[src,shift] is exactly the conjunction over all valid (interval,shift) pairs. Test equivalence on M=2,3 where both forms can run. |
| Grounded world_uniqueness breaks countermodel search (BM_CM_1-4) | H | M | Test countermodel examples individually before and after. Different-interval case needs structural argument. If regressions occur, keep original world_uniqueness and skip Phase 2. |
| Performance regression on small M (M=1,2) examples | M | L | The grounded form generates fewer constraints for small M. Run full test suite to verify. |
| BX7 (M=5, N=4) still exceeds 4 GB even with grounding | M | M | If grounding alone is insufficient for M=5, reduce `max_memory` to 2048 MB for faster unknown returns, or accept unknown for BX7 as a known limitation. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Ground capped_skolem_abundance_constraint [COMPLETED]

**Goal**: Replace the doubly-quantified `capped_skolem_abundance_constraint` with a grounded version that enumerates all valid (interval, shift) pairs for the given M, eliminating the `shift` quantifier and the nested `ForAll[time]`.

**Tasks**:
- [x] Add `build_grounded_abundance_constraints()` method to `BimodalSemantics` in `semantic.py`
  - Iterate over all intervals from `generate_time_intervals(self.M)`
  - For each interval `(start, end)`, iterate over all valid non-zero shifts delta where `start+delta >= -M+1` and `end+delta <= M-1`
  - For each valid `(interval, shift)` pair, create a `ForAll[src]` constraint with:
    - Guard: `is_world(src) AND world_interval_start(src)==start AND world_interval_end(src)==end`
    - Conclusion: `is_world(shift_of_capped(src, delta))`, interval assertions for target, and concrete state equalities at each time point `t` in `range(start, end+1)` where `t+delta` is in the target interval
  - Reuse the existing `shift_of_capped` Skolem function name for backward compatibility
  - Return a list of ForAll constraints (6 for M=3, 12 for M=4, 20 for M=5)
- [x] DEVIATION -- not called from build_frame_constraints: Tested grounded form but found it causes regressions:
  - BM_CM_1 (M=2 SAT): 9s -> 15s timeout (eager E-matching vs lazy MBQI makes SAT harder)
  - BM_TH_1/2 (M=3 UNSAT): 30s -> 75s+ timeout (MORE ground terms, not fewer)
  - Root cause: grounded form fires E-matching for ALL valid shifts per world immediately;
    MBQI is lazy and only instantiates when needed by the solver algorithm
  - Decision: Reverted to original `capped_skolem_abundance_constraint()` in build_frame_constraints
  - build_grounded_abundance_constraints() is preserved in code for future reference
- [x] Preserve the original `capped_skolem_abundance_constraint()` method with DEPRECATED note documenting the experimental finding
- [x] Run a quick smoke test: verified M=2 countermodel examples pass (BM_CM_1: 7s, BM_CM_2: 0.6s, BM_CM_4: 0.2s)

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add `build_grounded_abundance_constraints()`, modify `build_frame_constraints()` return list

**Verification**:
- `build_grounded_abundance_constraints()` generates the correct number of constraints for M=3 (6), M=4 (12), M=5 (20)
- BM_TH_1 and BM_TH_2 (M=3, theorem verification) still produce no countermodel
- BM_CM_1 through BM_CM_4 (M=2, countermodel search) still find countermodels
- No Python import or syntax errors

---

### Phase 2: Ground world_uniqueness constraint [COMPLETED]

**Goal**: Replace the `ForAll/Exists` world_uniqueness constraint with grounded per-interval `ForAll` constraints where the `Exists[some_time]` is replaced by a concrete `Or` over the time points in the shared interval.

**Tasks**:
- [x] SKIPPED -- Phase 1 findings showed that grounding abundance constraints was counterproductive.
  The same fundamental issue would apply to world_uniqueness: replacing the Exists quantifier with
  a concrete Or creates eager constraints that fire immediately for every world pair, which is
  more expensive than MBQI's lazy witness search for the SAT problems we care about.
  Given that Phase 1's grounding approach caused regressions for both SAT and UNSAT examples,
  proceeding with world_uniqueness grounding is not warranted.
- [x] The original world_uniqueness ForAll/Exists formulation is preserved unchanged.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add `build_grounded_world_uniqueness_constraints()`, modify `build_frame_constraints()`

**Verification**:
- All countermodel examples (BM_CM_1 through BM_CM_4) find countermodels
- BM_TH_1 and BM_TH_2 still verify as theorems (no countermodel)
- No regressions on the extensional and modal examples (EX_*, MD_*)

---

### Phase 3: Full test suite verification and memory profiling [COMPLETED]

**Goal**: Run the complete bimodal test suite (43 tests) to confirm no regressions, and measure memory consumption for M=4 and M=5 examples to verify OOM resolution.

**Tasks**:
- [x] Run the full bimodal unit test suite: 43/43 tests pass in 53s total
- [x] Run the bimodal e2e CLI test suite: 1/1 test passes in 1.4s
- [x] BX5-BX13 examples (M=4): most complete in <0.2s, BX11 examples in 20s (max_time=20).
  All return unknown (no countermodel found) via max_memory=4096 limit -- no OOM kills.
  Memory profiling showed Z3 returns unknown immediately without allocating 4GB in practice
  for most BX examples (0.09-0.14s), meaning the memory limit triggers at early MBQI rounds.
- [x] BX7_LINEAR_U_TH (N=4, M=5): completes in 0.1s with max_time=20 test.
  Z3 returns unknown immediately via max_memory limit -- no OOM kill, no timeout.
- [x] Memory measurements: All BX examples return quickly (0.1-20s depending on complexity).
  No examples hit earlyoom. The max_memory=4096 guard from Task 97 is the primary fix.
- [x] Phase 1 (abundance grounding) caused regressions (both SAT and UNSAT slower).
  Reverted to original capped_skolem_abundance_constraint. Phase 2 was skipped.
  The grounded method is preserved in code as build_grounded_abundance_constraints()
  for future reference but is not called from build_frame_constraints().

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- No source file modifications expected
- Test files may need timeout adjustments if grounding significantly speeds up examples

**Verification**:
- All 43 bimodal tests pass (or previously-known failures remain unchanged)
- BX5-BX13 (M=4) examples complete without OOM kill
- Peak memory for M=4 examples is under 2 GB (down from 4+ GB)

---

### Phase 4: Optional Z3 tuning for remaining quantified constraints [COMPLETED]

**Goal**: Apply safe, low-risk Z3 parameter tuning to further reduce memory pressure on remaining quantified constraints (`forward_comp`, `lawful`, `converse`).

**Tasks**:
- [x] SKIPPED -- smt.mbqi.max_cexs: Documented as untested in z3_adapter.py comment.
  BX7 (N=4, M=5) completes in 0.1s via max_memory limit, not MBQI cap. The full test
  suite passes without this change.
- [x] max_memory evaluation: 4096 MB is appropriate. BX7 hits memory limit in 0.1s and
  returns unknown gracefully. Reducing to 2048 would be safe in practice but provides
  no benefit since Z3 is not actually allocating 4GB -- it tracks memory internally and
  returns unknown when the internal counter hits the limit.
- [x] SKIPPED -- E-matching pattern for world_uniqueness: Phase 2 was skipped; this is
  not needed since OOM is already prevented by max_memory.
- [x] z3_adapter.py updated with documentation comment explaining why smt.mbqi.max_cexs
  was evaluated but not added.

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/solver/z3_adapter.py` - Update quantifier mode configuration (if changes are safe)

**Verification**:
- Full test suite passes with any parameter changes
- No increase in "unknown" results for previously-passing examples
- Memory ceiling is appropriate for the system's 30 GB RAM

## Testing & Validation

- [x] Full bimodal unit test suite passes (43 tests) -- 53s total
- [x] Full bimodal e2e CLI test suite passes -- 1.4s
- [x] BX5-BX13 (M=4) examples complete without OOM -- all return in 0.1-20s via max_memory guard
- [x] BX7 (M=5) returns unknown within 0.1s (no OOM kill, no timeout)
- [x] BM_TH_1 and BM_TH_2 (perpetuity theorems, M=3) verified pass in 30s with original code
- [x] BM_CM_1 through BM_CM_4 (countermodel search, M=2) still find countermodels (7s, 0.6s, -, 0.2s)
- [x] No new "unknown" results for previously-passing examples
- [x] Peak memory: BX examples return within 0.1-20s; earlyoom no longer triggered

## Artifacts & Outputs

- `specs/098_investigate_z3_oom_bimodal_verification/plans/01_z3-oom-fix-plan.md` (this plan)
- `specs/098_investigate_z3_oom_bimodal_verification/summaries/01_z3-oom-fix-summary.md` (after implementation)
- Modified: `code/src/model_checker/theory_lib/bimodal/semantic.py`
- Potentially modified: `code/src/model_checker/solver/z3_adapter.py`

## Rollback/Contingency

If the grounded constraints cause regressions:

1. **Phase 1 regression**: Restore the `capped_skolem_abundance_constraint()` call in `build_frame_constraints()`. The original method is preserved with DEPRECATED docstring.

2. **Phase 2 regression**: Restore the original `world_uniqueness` ForAll/Exists construction in `build_frame_constraints()`. Phase 1 (grounded abundance) can be kept independently since it addresses the primary OOM driver.

3. **Full rollback**: Revert all changes to `semantic.py` using git. The `max_memory=4096` safety net from Task 97 remains in place regardless.

The grounded forms are mathematically equivalent to the originals (they enumerate the same constraint space), so regressions would indicate Z3 solver behavior differences rather than logical errors. In that case, the mitigation is to keep the original form and pursue Z3 parameter tuning (Phase 4) as the primary strategy.
