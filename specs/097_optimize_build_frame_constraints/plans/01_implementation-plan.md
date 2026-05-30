# Implementation Plan: Task #97

- **Task**: 97 - Optimize build_frame_constraints for Z3 solver performance
- **Status**: [NOT STARTED]
- **Effort**: 7 hours
- **Dependencies**: None (task 96 full test suite verification is complete)
- **Research Inputs**: specs/097_optimize_build_frame_constraints/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The `build_frame_constraints()` function in `semantic.py` (lines 467-687) constructs 13 constraint groups for the bimodal logic model checker. Team research identified 12 concrete optimization opportunities across three risk tiers. This plan implements optimizations in strict risk order -- safe tautology removal and array inequality replacement first, then pattern annotations and solver tuning, with full regression testing after each phase. Definition of done: all non-timeout examples produce identical valid/invalid classifications, and no new timeout regressions appear.

### Research Integration

The team research report (4 teammates) provided:
- **Teammate A**: 8 direct Z3 optimization techniques with line-level targeting
- **Teammate B**: Critical finding -- `world_uniqueness` can use array inequality for ~200x speedup; solver configuration benchmarks showing `qi.max_instances` and `mbqi.max_iterations` improvements
- **Critic**: Identified absence of isolation tests, undocumented ordering sensitivity, and the soundness risk of adding patterns to ForAll/Exists (resolved by array inequality approach)
- **Teammate D**: Strategic coordination with task 98, Lean alignment safety confirmation, and need for benchmarking infrastructure

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No active roadmap items. ROADMAP.md contains only template placeholders.

## Goals & Non-Goals

**Goals**:
- Remove provably tautological constraints that waste solver overhead
- Replace expensive ForAll/Exists `world_uniqueness` with array inequality (~200x faster in isolation)
- Add Z3 quantifier pattern hints (MultiPattern) to heavy quantifier blocks
- Add solver parameter guards (`qi.max_instances`, `max_memory`) to bound OOM risk
- Validate every change preserves identical valid/invalid classification across all examples
- Establish a lightweight baseline-capture mechanism for future optimization work

**Non-Goals**:
- Architectural changes (CEGAR, incremental solving, symmetry reduction)
- Addressing the exponential `max_world_id` growth (fundamental scalability limit, future work)
- Switching solver backends (CVC5 confirmed incompatible)
- Uncommenting `task_restriction` or `task_minimization`
- Changing `time_interval_constraint` to grounded form (infeasible at N=3,M=4)
- Full benchmarking infrastructure (only lightweight baseline capture is in scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing `classical_truth` shifts E-matching index timing for `truth_condition` | H | L | Validate against EX_FALSO_TH and no-sentence-letter examples specifically |
| Array inequality for `world_uniqueness` changes semantic guard on temporal overlap | H | L | Semantically sound per research; validate all countermodel examples |
| Constraint reordering breaks undocumented "order matters" invariant | H | M | Reorder only `world_interval` position; run full suite 3x to catch non-determinism |
| MultiPattern on `lawful` causes missed instantiations (incompleteness) | M | L | Test theorem examples that depend on lawful transitions (BM_CM_1/2/4, perpetuity principles) |
| `qi.max_instances` cap causes `unknown` on valid examples | H | M | Start with high cap (10000), test all examples; increase if any regress |
| Non-deterministic Z3 behavior masks regressions | M | M | Run test suite 3 times per phase; flag any intermittent failures |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1    | 1      | --         |
| 2    | 2      | 1          |
| 3    | 3      | 2          |
| 4    | 4      | 3          |
| 5    | 5      | 4          |

Phases are strictly sequential because each change must be validated against the baseline before proceeding. No parallel execution is safe for correctness-sensitive solver changes.

---

### Phase 1: Baseline Capture and Test Infrastructure [COMPLETED]

**Goal**: Capture exact pass/fail/result for all bimodal examples as the reference baseline, and create a lightweight script to compare future runs against this baseline.

**Tasks**:
- [ ] Run the full bimodal test suite and record which examples pass, fail, or timeout: `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -v --tb=short 2>&1 | tee baseline_output.txt`
- [ ] Run KNOWN_TIMEOUT_EXAMPLES individually with extended timeout (60s) to capture their baseline behavior (pass/fail/unknown)
- [ ] Create a simple baseline comparison script (`code/scripts/compare_bimodal_baseline.sh`) that runs the test suite and diffs the pass/fail list against the saved baseline
- [ ] Document the exact count: N passing, N failing, N timeout, N skipped
- [ ] Save baseline results to `specs/097_optimize_build_frame_constraints/baseline_results.txt`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/scripts/compare_bimodal_baseline.sh` - New script for baseline comparison
- `specs/097_optimize_build_frame_constraints/baseline_results.txt` - Saved baseline data

**Verification**:
- Baseline file exists with all example results recorded
- Comparison script can be run and reports 0 regressions against itself

---

### Phase 2: Tier 1 Safe Changes -- Tautology Removal and Array Inequality [COMPLETED]

**Goal**: Implement the two highest-confidence, lowest-risk optimizations: remove the `classical_truth` tautology and replace `world_uniqueness` ForAll/Exists with array inequality.

**Tasks**:
- [ ] Remove `classical_truth` constraint definition (lines 507-517) and its entry in the return list (line 671)
- [ ] Remove associated variable declarations (`world_state`, `sentence_letter`) if not used elsewhere in the method
- [ ] Replace `world_uniqueness` ForAll/Exists block (lines 593-616) with array inequality: `world_function(w1) != world_function(w2)` for all distinct valid world pairs
- [ ] Add a `MultiPattern` trigger on the new `world_uniqueness` constraint to guide Z3 on when to instantiate
- [ ] Update comments and docstring for `build_frame_constraints` to reflect the removed/changed constraints (remove item 3 "Truth value constraints", update item 9 "World uniqueness")
- [ ] Run full bimodal test suite and compare against Phase 1 baseline
- [ ] Run test suite 2 additional times to check for non-deterministic regressions (BM_CM_1, BM_CM_2, BM_CM_4)
- [ ] Specifically test EX_FALSO_TH example to verify `truth_condition` E-matching is unaffected

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Remove `classical_truth`, rewrite `world_uniqueness`

**Verification**:
- All previously passing examples still pass (0 regressions in baseline comparison)
- No new intermittent failures across 3 test runs
- `classical_truth` no longer appears in the constraint return list
- `world_uniqueness` uses `world_function(w1) != world_function(w2)` instead of ForAll/Exists

---

### Phase 3: Pattern Annotations and Constraint Reordering [COMPLETED]

**Goal**: Add MultiPattern annotations to `lawful` and `converse` constraints, and move `world_interval` before `lawful` in the return list to establish interval bounds early for MBQI seeding.

**Tasks**:
- [ ] Add `MultiPattern` to the `lawful` constraint with trigger on `(world_function(lawful_world), world_interval_start(lawful_world))` -- fires when both a world's history and interval start are known
- [ ] Add `MultiPattern` to the `converse` constraint (in `build_converse_constraint()`) with appropriate trigger pattern
- [ ] Reorder the return list to move `world_interval` before `lawful` and frame axioms -- proposed order: `valid_main_world`, `valid_main_time`, `enumeration_constraint`, `convex_world_ordering`, `world_interval`, `lawful`, `nullity_identity`, `converse`, `forward_comp`, `skolem_abundance`, `world_uniqueness`
- [ ] Update the `# NOTE: order matters!` comment with documentation explaining the rationale for the new ordering
- [ ] Run full test suite 3 times and compare against Phase 1 baseline (critical: reordering is the highest-risk change in this phase)
- [ ] If any regressions: revert reordering but keep pattern annotations; retest

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Pattern annotations on `lawful`, `converse`; reorder return list
- Possibly `code/src/model_checker/theory_lib/bimodal/semantic.py` (within `build_converse_constraint()`) for converse pattern

**Verification**:
- All previously passing examples still pass across 3 test runs
- `lawful` and `converse` constraints have MultiPattern annotations
- Return list order updated and comment documents the rationale
- If reordering caused regressions: reordering reverted, patterns retained

---

### Phase 4: Solver Configuration Guards [COMPLETED]

**Goal**: Add `qi.max_instances` cap and `max_memory` guard to the Z3 solver adapter to bound OOM risk and reduce spurious quantifier instantiation, directly supporting task 98 coordination.

**Tasks**:
- [ ] Add `self._solver.set('smt.qi.max_instances', 10000)` to `_configure_solver()` in `z3_adapter.py` (after existing `mbqi.max_iterations` line)
- [ ] Add `z3.set_param('memory_max_size', 4096)` (or equivalent per-solver `max_memory` setting) as a global memory guard -- validate the correct Z3 API call
- [ ] Run full test suite and compare against Phase 1 baseline
- [ ] If any example that previously returned `sat`/`unsat` now returns `unknown`: increase `max_instances` cap and retest
- [ ] Document the chosen parameter values and rationale in code comments

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/solver/z3_adapter.py` - Add `qi.max_instances` and memory guard to `_configure_solver()`

**Verification**:
- All previously passing examples still pass
- No examples that were `sat`/`unsat` are now returning `unknown`
- Z3 adapter has documented solver parameter settings
- Memory guard is active (can be verified by checking Z3 params in a debug session)

---

### Phase 5: Full Regression Testing and Cleanup [COMPLETED]

**Goal**: Run comprehensive validation across all examples including KNOWN_TIMEOUT_EXAMPLES, clean up any dead code or stale comments, and document the final state.

**Tasks**:
- [ ] Run the full bimodal test suite 3 times and compare against Phase 1 baseline -- all must match
- [ ] Run KNOWN_TIMEOUT_EXAMPLES individually with extended timeout to verify no behavioral changes
- [ ] Run the comparison script from Phase 1 and confirm 0 regressions
- [ ] Remove any dead code left from Phase 2 changes (unused variable declarations, orphaned comments)
- [ ] Update the `build_frame_constraints` docstring to accurately reflect the current constraint list and numbering
- [ ] Add a brief code comment at the top of `build_frame_constraints` noting which optimizations were applied and referencing this plan and the research report
- [ ] If the `time_interval` variable assignment on line 589 is unused (currently commented out in the return list), verify it is still needed and add a comment explaining its status

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Docstring updates, dead code cleanup
- `code/scripts/compare_bimodal_baseline.sh` - Final run for verification

**Verification**:
- 0 regressions across 3 full test suite runs compared to Phase 1 baseline
- KNOWN_TIMEOUT_EXAMPLES behave identically to baseline
- No dead code or stale comments remain
- Docstring accurately reflects current constraint structure

## Testing & Validation

- [ ] Phase 1 baseline captured and saved
- [ ] Each phase validated against baseline with 0 regressions
- [ ] Non-deterministic examples (BM_CM_1, BM_CM_2, BM_CM_4) tested 3x per phase
- [ ] EX_FALSO_TH specifically validated after `classical_truth` removal
- [ ] KNOWN_TIMEOUT_EXAMPLES validated at Phase 5
- [ ] No example that was sat/unsat changed to unknown (or vice versa)
- [ ] Final full suite run: 3 passes, all matching baseline

## Artifacts & Outputs

- `specs/097_optimize_build_frame_constraints/plans/01_implementation-plan.md` (this file)
- `specs/097_optimize_build_frame_constraints/baseline_results.txt` (Phase 1 output)
- `code/scripts/compare_bimodal_baseline.sh` (baseline comparison tool)
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (optimized constraints)
- `code/src/model_checker/solver/z3_adapter.py` (solver parameter tuning)

## Rollback/Contingency

Each phase modifies at most 2 files. If a phase introduces regressions:
1. `git stash` or `git checkout` the modified files to revert that phase
2. Re-run test suite to confirm revert restores baseline behavior
3. Skip the problematic optimization and proceed to next phase
4. Document which optimization was skipped and why in the execution summary

If multiple phases compound into regressions detected only at Phase 5:
1. Use `git log` to identify which commit introduced the regression
2. Bisect by reverting phases in reverse order until baseline is restored
3. Re-apply only the phases that pass individually

The baseline comparison script from Phase 1 enables rapid regression detection at every stage.
