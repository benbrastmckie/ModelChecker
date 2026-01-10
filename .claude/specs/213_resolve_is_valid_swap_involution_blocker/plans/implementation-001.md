# Implementation Plan: Task 213

**Project Number**: 213  
**Type**: research  
**Priority**: high  
**Complexity**: medium  
**Estimated Hours**: 6.0  
**Phases**: 5

---

## Overview

Resolve the is_valid_swap_involution blocker by implementing the solution identified in comprehensive research: The original theorem is semantically FALSE for arbitrary formulas and must be reformulated to restrict to derivable formulas only.

**Critical Research Finding**: The is_valid_swap_involution theorem (`is_valid T φ.swap → is_valid T φ`) is UNPROVABLE as stated because it's semantically false. The swap operation exchanges all_past ↔ all_future, which quantify over different time ranges (past s<t vs future s>t). A counterexample exists in asymmetric temporal models where a formula is valid after swap but not before.

**Solution**: Reformulate as `derivable_valid_swap_involution` with explicit derivability precondition: `DerivationTree [] φ.swap → is_valid T φ`. This is provable using the temporal_duality rule which guarantees swap preservation for derivable formulas.

**Impact**: Resolves 4 blocked tasks (184, 193, 209, 213) representing 10.7 hours of total invested effort across 15 failed proof strategies.

---

## Research Inputs

### Research Report
- Path: .opencode/specs/213_resolve_is_valid_swap_involution_blocker/reports/research-001.md
- Key Finding: Theorem is semantically false for arbitrary formulas; counterexample constructed
- Recommended Solution: Reformulate for derivable formulas only (Solution 2 from research)

### Research Summary  
- Path: .opencode/specs/213_resolve_is_valid_swap_involution_blocker/summaries/research-summary.md
- Executive Summary: 586-line comprehensive analysis proving theorem unprovability
- Implementation Guidance: Use temporal_duality rule for proof

### Related Tasks
- Task 184: Initial attempt (4 hours estimated, blocked)
- Task 193: Multiple proof attempts (3.7 hours actual, blocked)
- Task 209: Lean 4 techniques research (3 hours actual, partial)
- Task 213: Comprehensive research (3.5 hours actual, researched)
- Total Investment: 10.7 hours across 4 tasks

---

## Phase 1: Remove Unprovable Theorem

**Estimated Time**: 0.5 hours

**Objective**: Remove the semantically false is_valid_swap_involution theorem from Truth.lean

**Steps**:
1. Locate theorem at Logos/Core/Semantics/Truth.lean line 691
2. Review current sorry placeholder and helper lemma truth_at_swap_swap
3. Add detailed comment explaining why theorem is unprovable:
   ```lean
   -- NOTE: The theorem `is_valid_swap_involution` as originally stated is UNPROVABLE.
   -- It claims: is_valid T φ.swap → is_valid T φ
   -- This is semantically FALSE for arbitrary formulas containing temporal operators.
   -- Counterexample: φ = all_past(atom "p") in model where p is true in future but false in past.
   -- See task 213 research report for detailed semantic analysis.
   -- The theorem IS true for derivable formulas (see derivable_valid_swap_involution below).
   ```
4. Delete the theorem definition (line 691)
5. Delete or preserve helper lemma truth_at_swap_swap (decision: preserve as it's fully proven and may be useful)
6. Document deletion in commit message

**Files Modified**:
- Logos/Core/Semantics/Truth.lean

**Acceptance Criteria**:
- [ ] Unprovable theorem removed from Truth.lean
- [ ] Detailed comment added explaining unprovability
- [ ] Helper lemma truth_at_swap_swap decision made (preserve or remove)
- [ ] File compiles without errors (one theorem deleted)

---

## Phase 2: Add Provable Theorem

**Estimated Time**: 2.0 hours

**Objective**: Implement derivable_valid_swap_involution restricted to derivable formulas

**Steps**:
1. Add new theorem definition with derivability precondition:
   ```lean
   theorem derivable_valid_swap_involution {φ : Formula} 
       (h_deriv : DerivationTree [] φ.swap) : is_valid T φ := by
     -- Proof using temporal_duality rule
     sorry  -- To be proven in this phase
   ```

2. Implement proof using temporal_duality rule from proof system:
   - The temporal_duality rule states: If φ is derivable, then φ.swap is derivable
   - Use soundness theorem: DerivationTree Γ φ → is_valid Γ φ
   - Apply to h_deriv : DerivationTree [] φ.swap
   - Get is_valid [] φ.swap
   - Use involution φ.swap.swap = φ to transport to is_valid [] φ
   - This approach WORKS because we're using soundness, not semantic validity directly

3. Add detailed documentation comment explaining:
   - Why derivability precondition is necessary
   - How this differs from the unprovable version
   - Reference to task 213 research report

4. Verify proof compiles and type-checks

**Files Modified**:
- Logos/Core/Semantics/Truth.lean (add new theorem after deleted one)

**Acceptance Criteria**:
- [ ] derivable_valid_swap_involution theorem added
- [ ] Derivability precondition explicit in signature
- [ ] Proof implemented using temporal_duality + soundness
- [ ] No sorry placeholders
- [ ] Detailed documentation comment added
- [ ] Theorem compiles and type-checks

**Risk Mitigation**:
- If temporal_duality rule is not directly usable, explore alternative: use soundness theorem + swap_derivable helper
- If proof is complex, break into helper lemmas
- Estimated time includes buffer for proof refinement

---

## Phase 3: Update temporal_duality Usage Site

**Estimated Time**: 1.5 hours

**Objective**: Update the single usage site at Truth.lean line 1172 to use new theorem

**Steps**:
1. Locate usage of is_valid_swap_involution at Truth.lean line 1172 (temporal_duality case)
2. Review context to understand what's being proven
3. Check if derivability precondition is satisfied:
   - temporal_duality case should have DerivationTree available
   - If not, may need to thread derivability through calling context
4. Update function call from is_valid_swap_involution to derivable_valid_swap_involution
5. Provide derivability proof as additional argument
6. Verify proof compiles and passes in context

**Files Modified**:
- Logos/Core/Semantics/Truth.lean (update line 1172 usage)

**Acceptance Criteria**:
- [ ] Usage site at line 1172 identified
- [ ] Derivability precondition satisfied at usage site
- [ ] Function call updated to derivable_valid_swap_involution
- [ ] Derivability argument provided
- [ ] Updated proof compiles and type-checks
- [ ] No regressions in surrounding proofs

**Contingency**:
- If derivability is not available at usage site, may need to refactor calling code
- If refactoring is extensive, document as separate follow-up task

---

## Phase 4: Build Verification

**Estimated Time**: 1.0 hour

**Objective**: Verify all changes compile and tests pass

**Steps**:
1. Run full build: `lake build`
2. Check for compilation errors in Truth.lean
3. Check for compilation errors in dependent modules
4. Run test suite: `lake exe test`
5. Verify no test regressions
6. Run targeted tests for Truth.lean module
7. Check SORRY_REGISTRY.md - remove entry for is_valid_swap_involution line 691
8. Update IMPLEMENTATION_STATUS.md if needed

**Files Modified**:
- Documentation/ProjectInfo/SORRY_REGISTRY.md (remove entry)
- Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md (update if needed)

**Acceptance Criteria**:
- [ ] `lake build` completes successfully
- [ ] No compilation errors in Truth.lean
- [ ] No compilation errors in dependent modules
- [ ] `lake exe test` passes all tests
- [ ] No test regressions
- [ ] SORRY_REGISTRY.md updated (entry removed)
- [ ] IMPLEMENTATION_STATUS.md updated if needed

**Validation**:
- Confirm sorry count decreases by 1 (from 10 to 9)
- Confirm no new build errors introduced
- Confirm existing tests still pass

---

## Phase 5: Documentation Updates

**Estimated Time**: 1.0 hour

**Objective**: Document resolution and lessons learned

**Steps**:
1. Update task 213 status to [COMPLETED] in TODO.md
2. Add completion timestamp to task 213
3. Link implementation artifacts in task 213
4. Close related tasks (184, 193, 209) with resolution notes:
   - Reference task 213 as resolution
   - Update status to [COMPLETED] or [ABANDONED] as appropriate
   - Add closure notes explaining resolution path

5. Create resolution summary in Documentation/Research/:
   - File: Documentation/Research/is_valid_swap_involution_resolution.md
   - Content: Executive summary of problem, research findings, solution
   - Lessons learned: Syntactic vs semantic properties, derivability scoping

6. Update state.json:
   - Mark task 213 as completed
   - Mark tasks 184, 193, 209 as resolved
   - Update repository health metrics

**Files Modified**:
- .opencode/specs/TODO.md (task 213, 184, 193, 209 status updates)
- .opencode/specs/state.json (completion tracking)
- Documentation/Research/is_valid_swap_involution_resolution.md (new)

**Acceptance Criteria**:
- [ ] Task 213 marked [COMPLETED] in TODO.md
- [ ] Completion timestamp added
- [ ] Implementation artifacts linked
- [ ] Tasks 184, 193, 209 closed with resolution notes
- [ ] Resolution summary created in Documentation/Research/
- [ ] state.json updated with completion data
- [ ] All acceptance criteria from task 213 marked complete

**Documentation Content**:
- Executive summary of 10.7-hour journey
- Key lesson: Always verify semantic validity before attempting proof
- Syntactic properties (derivations) vs semantic properties (validity)
- Temporal operator swap is not symmetric in arbitrary models
- Scoping theorems correctly prevents wasted effort

---

## Success Criteria

### Primary Success Metrics
- [ ] Unprovable theorem removed from Truth.lean
- [ ] Provable derivable_valid_swap_involution theorem added and proven
- [ ] temporal_duality usage site updated successfully
- [ ] Full codebase builds without errors
- [ ] All tests pass
- [ ] Tasks 184, 193, 209, 213 closed
- [ ] SORRY_REGISTRY count decreased by 1 (10 → 9)

### Quality Metrics
- [ ] No new sorry placeholders introduced
- [ ] No test regressions
- [ ] Documentation comprehensive and clear
- [ ] Lessons learned documented for future reference
- [ ] Code follows Lean 4 style guidelines

### Impact Metrics
- [ ] 10.7 hours of blocked work resolved
- [ ] 4 tasks closed (184, 193, 209, 213)
- [ ] Longest-standing blocked proof resolved
- [ ] Clear guidance for future temporal operator proofs
- [ ] Prevention of future attempts to prove false theorems

---

## Risk Assessment

### Low Risk
- Phase 1 (Removal): Simple deletion with explanation
- Phase 4 (Build): Standard verification process
- Phase 5 (Documentation): No code changes

### Medium Risk
- Phase 2 (Add Theorem): Proof may be more complex than anticipated
  - Mitigation: 2-hour estimate includes buffer for complexity
  - Fallback: Break into helper lemmas if needed
- Phase 3 (Update Usage): Derivability may not be available at usage site
  - Mitigation: 1.5-hour estimate includes refactoring buffer
  - Fallback: Document as follow-up task if extensive refactoring needed

### Overall Risk: Low-Medium
- Solution is well-researched and validated
- Proof strategy is clear from research report
- Main uncertainty is proof complexity, not correctness

---

## Dependencies

### Prerequisites
- Task 213 research completed (DONE)
- Research report available with detailed analysis (DONE)
- Counterexample and semantic analysis documented (DONE)

### External Dependencies
- None - solution is self-contained within Truth.lean

### Blocking
- This implementation blocks no other tasks
- Unblocks tasks 184, 193, 209 (will be closed upon completion)

---

## Notes

### Research Integration
This plan fully integrates findings from task 213 comprehensive research report:
- Problem diagnosis: Theorem semantically false for arbitrary formulas
- Root cause: Temporal operator swap asymmetry
- Solution: Restriction to derivable formulas
- Proof strategy: Use temporal_duality + soundness

### Lessons Learned Preview
Key takeaway for future work: Always verify semantic validity before attempting formal proof. The 10.7 hours invested across tasks 184, 193, 209 were spent trying to prove a false statement. This could have been avoided by semantic analysis upfront.

### Future Work
If derivable_valid_swap_involution proves insufficient for some use cases:
- Option: Add model-theoretic symmetry axiom for specific models
- Option: Reformulate temporal operators to be symmetric by definition
- See task 213 research report Solutions 3-4 for details

---

## Timeline

**Total Estimated Effort**: 6.0 hours

**Suggested Schedule**:
- Phase 1: 0.5 hours (remove unprovable theorem)
- Phase 2: 2.0 hours (add provable theorem)
- Phase 3: 1.5 hours (update usage site)
- Phase 4: 1.0 hour (build verification)
- Phase 5: 1.0 hour (documentation)

**Critical Path**: Phase 2 (proof complexity) is most time-critical

**Buffer**: 2-hour estimate for Phase 2 includes 30min buffer for unexpected complexity
