# Implementation Plan: Apply Proven Involution Proof Pattern to Task 193

- **Task**: 209 - Research Lean 4 techniques for completing task 193 involution proof
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: 
  - Main Report: .opencode/specs/209_research_lean4_involution_techniques/reports/research-001.md
  - Summary: .opencode/specs/209_research_lean4_involution_techniques/summaries/research-summary.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: lean
- **Lean Intent**: true

---

## Overview

Apply the proven `simp only` involution pattern discovered in research to complete the `is_valid_swap_involution` theorem in Truth.lean. Research identified an existing solution pattern from Perpetuity/Helpers.lean (line 74) that uses `simp only [Formula.swap_past_future, Formula.swap_past_future_involution] at h` to transport truth values across involutions with pattern-matched definitions. This is a simple 4-line proof with 95%+ success probability based on proven codebase patterns.

**Definition of Done**: The `is_valid_swap_involution` theorem compiles without `sorry`, all tests pass, and task 193 is marked COMPLETED.

---

## Goals & Non-Goals

**Goals**:
- Apply proven `simp only` pattern from Perpetuity/Helpers.lean to is_valid_swap_involution
- Replace `sorry` at line 713 with complete 4-line proof
- Update theorem docstring to explain the simp only technique
- Verify compilation and test success
- Complete task 193 (currently 85% done with helper lemma proven)

**Non-Goals**:
- Modify the existing `truth_at_swap_swap` helper lemma (already complete and proven)
- Add new helper lemmas (research shows they are unnecessary)
- Change the theorem signature or API
- Modify Formula.lean or involution definitions
- Implement alternative proof strategies (fallbacks available if needed)

---

## Risks & Mitigations

**Risk 1**: `swap_past_future_involution` might not be marked `@[simp]`
- **Likelihood**: Low (involution theorems typically have simp attribute)
- **Impact**: Medium (would prevent simp only from working)
- **Mitigation**: Check Formula.lean for `@[simp]` attribute, add if missing
- **Detection**: Compilation error during build
- **Fallback**: Use Alternative 1 (helper with symmetry) from research report

**Risk 2**: `simp only` might unfold too much or too little
- **Likelihood**: Very Low (pattern proven in production code)
- **Impact**: Low (would require tactic adjustment)
- **Mitigation**: Use explicit lemma list as shown in research pattern
- **Detection**: Type mismatch during compilation
- **Fallback**: Use Alternative 1 or consult research report Alternative 2

**Risk 3**: Downstream usage at line 1171 might break
- **Likelihood**: Very Low (theorem signature unchanged)
- **Impact**: Low (isolated to one usage site)
- **Mitigation**: Verify line 1171 compiles after changes
- **Detection**: Build error in Truth.lean
- **Fallback**: Revert changes and investigate usage requirements

---

## Implementation Phases

### Phase 1: Apply simp only Pattern to Complete Proof [NOT STARTED]

**Goal**: Replace sorry with proven 4-line proof using simp only pattern from research

**Tasks**:
- [ ] Open Logos/Core/Semantics/Truth.lean
- [ ] Navigate to line 680-713 (is_valid_swap_involution theorem)
- [ ] Replace current proof attempt (lines 682-713) with research solution
- [ ] Update theorem docstring to explain simp only technique
- [ ] Verify Formula.swap_past_future_involution has @[simp] attribute
- [ ] Build Truth.lean module to verify compilation
- [ ] Run full build to check for regressions
- [ ] Run test suite to verify all tests pass
- [ ] Verify downstream usage at line 1171 compiles correctly
- [ ] Update task 193 status to COMPLETED in TODO.md

**Timing**: 30 minutes

**Implementation Details**:

**Step 1**: Replace proof (lines 680-713)

Current code (lines 680-713):
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  -- [30+ lines of failed proof attempts]
  sorry
```

New code (4 lines):
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
    is_valid T φ := by
  intro F M τ t ht
  have h_swap : truth_at M τ t ht φ.swap_past_future := h F M τ t ht
  simp only [Formula.swap_past_future, Formula.swap_past_future_involution] at h_swap
  exact h_swap
```

**Step 2**: Update docstring (before line 680)

Add explanation of simp only technique:
```lean
/--
Validity is invariant under the temporal swap involution.
If `φ.swap` is valid, then so is `φ` (since swap is involutive).

Proof strategy:
1. Instantiate hypothesis h to get truth_at M τ t ht φ.swap
2. Use simp only with involution to simplify φ.swap to φ in hypothesis
3. Close goal with simplified hypothesis

The key technique is using `simp only [Formula.swap_past_future, 
Formula.swap_past_future_involution] at h_swap` to handle the involution
in the hypothesis. This pattern is used successfully in Perpetuity/Helpers.lean
and works correctly with pattern-matched definitions like truth_at.
-/
```

**Step 3**: Verify simp attribute

Check Formula.lean for:
```lean
@[simp]
theorem swap_past_future_involution (φ : Formula) : 
    φ.swap_past_future.swap_past_future = φ
```

If `@[simp]` is missing, add it before the theorem.

**Step 4**: Build and test

```bash
# Module build
lake build Logos.Core.Semantics.Truth

# Full build
lake build

# Test suite
lake exe test
```

**Expected Results**:
- No `sorry` warning for is_valid_swap_involution
- No compilation errors in Truth.lean
- No new build errors in codebase
- All existing tests pass
- Line 1171 usage compiles correctly

**Acceptance Criteria**:
- [ ] Proof replaced with 4-line simp only pattern
- [ ] No `sorry` at line 713 (or equivalent after edit)
- [ ] Docstring updated with simp only explanation
- [ ] Formula.swap_past_future_involution has @[simp] attribute
- [ ] Truth.lean compiles with lake build Logos.Core.Semantics.Truth
- [ ] Full build succeeds with lake build
- [ ] All tests pass with lake exe test
- [ ] Line 1171 downstream usage compiles correctly
- [ ] No new build errors introduced
- [ ] Proof is mathematically sound and type-checks

---

## Testing & Validation

**Unit Tests**:
- [ ] Compile Truth.lean module: `lake build Logos.Core.Semantics.Truth`
- [ ] Verify no `sorry` warning for is_valid_swap_involution
- [ ] Check for compilation errors in Truth.lean

**Integration Tests**:
- [ ] Full codebase build: `lake build`
- [ ] Verify no new errors in dependent modules
- [ ] Check downstream usage at line 1171 compiles

**Regression Tests**:
- [ ] Run test suite: `lake exe test`
- [ ] Verify all existing tests pass
- [ ] Confirm no test failures or timeouts

**Verification Tests**:
- [ ] Check helper lemma truth_at_swap_swap still accessible
- [ ] Verify involution property Formula.swap_past_future_involution available
- [ ] Confirm theorem signature unchanged (API compatibility)

**Success Criteria**:
- Zero `sorry` in is_valid_swap_involution theorem
- Zero compilation errors in Truth.lean
- Zero new build errors in codebase
- 100% existing test pass rate
- Proof verified by Lean type checker

---

## Artifacts & Outputs

**Primary Artifacts**:
- plans/implementation-001.md (this file)
- Modified file: Logos/Core/Semantics/Truth.lean (lines 680-713)

**Expected Changes**:
- Remove ~30 lines of failed proof attempts
- Add 4 lines of working proof
- Update docstring (~10 lines)
- Net reduction: ~16 lines

**Documentation Updates**:
- Theorem docstring in Truth.lean
- Task 193 status in TODO.md (PARTIAL → COMPLETED)
- SORRY_REGISTRY.md (remove entry if tracked)

**No New Files**: All changes are modifications to existing files

---

## Rollback/Contingency

**If simp only pattern fails**:

1. **Fallback 1**: Use Alternative 1 from research (helper with symmetry)
   - Implementation time: +10 minutes
   - Success probability: 90%
   - Code:
     ```lean
     theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap_past_future) :
         is_valid T φ := by
       intro F M τ t ht
       have h1 := (truth_at_swap_swap M τ t ht φ.swap_past_future).symm.mpr (h F M τ t ht)
       exact (truth_at_swap_swap M τ t ht φ).mp h1
     ```

2. **Fallback 2**: Add congruence lemma (Alternative 2 from research)
   - Implementation time: +20 minutes
   - Success probability: 95%
   - Requires adding new lemma truth_at_congr

3. **Fallback 3**: Consult Lean Zulip
   - Implementation time: +2 hours (async)
   - Success probability: 99%
   - Post question with minimal reproducible example

**Revert Procedure**:
1. Use git to revert Truth.lean changes
2. Restore original sorry at line 713
3. Document issue in task 193 notes
4. Update TODO.md status back to PARTIAL
5. Create new research task if needed

**Revert Command**:
```bash
git checkout HEAD -- Logos/Core/Semantics/Truth.lean
```

**Contingency Time Budget**: +45 minutes (total 1.25 hours with primary approach)

---

## Research Integration

**Research Findings Applied**:

1. **Solution Pattern**: `simp only [Formula.swap_past_future, Formula.swap_past_future_involution] at h`
   - Source: Perpetuity/Helpers.lean line 74
   - Proven: Already in production code
   - Applicability: Direct match to our problem

2. **Root Cause Understanding**: Pattern-matched definitions require simp, not rw
   - `truth_at` is structurally recursive
   - Propositional equality insufficient for transport
   - `simp only` handles pattern matching correctly

3. **Tool Validation**: Loogle CLI tested and functional
   - Binary: /home/benjamin/.cache/loogle/.lake/build/bin/loogle
   - Status: Available for future research
   - Not needed for this implementation (solution found in codebase)

**Research Success Metrics**:
- [x] Viable proof strategy identified
- [x] Strategy addresses pattern-matching + equality transport challenge
- [x] Concrete Lean 4 code example provided
- [x] Implementation time estimated (30 minutes)
- [x] Alternative approaches explored (3 fallbacks documented)
- [x] Success probability assessed (95%+)

**Research Quality**: High - Found proven solution in codebase with clear implementation path

---

## Time Breakdown

| Task | Estimated | Cumulative |
|------|-----------|------------|
| Replace proof code | 10 min | 10 min |
| Update docstring | 5 min | 15 min |
| Verify simp attribute | 2 min | 17 min |
| Build Truth.lean | 3 min | 20 min |
| Full build | 5 min | 25 min |
| Run tests | 3 min | 28 min |
| Verify downstream usage | 2 min | 30 min |
| **Total** | **30 min** | **30 min** |

**Buffer**: 30 minutes allocated (100% buffer for 30-minute estimate)

**Total with Buffer**: 60 minutes (1 hour)

**Confidence**: Very High (95%+) based on proven pattern

---

## Success Metrics

**Primary Metrics**:
- Proof compiles without `sorry`: Yes/No
- All tests pass: Yes/No
- No new build errors: Yes/No
- Implementation time ≤ 30 minutes: Yes/No

**Quality Metrics**:
- Proof uses proven pattern from codebase: Yes/No
- Docstring explains technique clearly: Yes/No
- No regressions in dependent code: Yes/No
- Task 193 marked COMPLETED: Yes/No

**Research Validation Metrics**:
- Research findings directly applicable: Yes/No
- Estimated time accurate: Yes/No
- Success probability accurate: Yes/No
- Fallback plans adequate: Yes/No

---

## Implementation Notes

**Why This Approach**:
1. **Proven Pattern**: Exact same technique already in production (Perpetuity/Helpers.lean)
2. **Minimal Changes**: Only 4 lines of proof code
3. **No New Dependencies**: Uses existing helpers and involution theorems
4. **Type-Safe**: Lean's simplifier handles all type checking
5. **No Axioms**: Pure tactic-based proof

**Why Not Alternative Approaches**:
1. **Helper with Symmetry**: More complex (applies helper twice), unnecessary given simp only works
2. **Congruence Lemma**: Adds new lemma, increases maintenance burden
3. **Calc-Style**: Overly verbose for simple proof

**Key Insight from Research**:
The `simp only` tactic can handle pattern-matched definitions like `truth_at` where `rw` and `Eq.mp` fail. This is because `simp` recursively simplifies subterms and applies multiple lemmas in sequence, while `rw` requires exact syntactic matches.

**Pattern Applicability**:
This pattern applies to any involution proof with pattern-matched definitions:
- Involution property: `f (f x) = x`
- Pattern-matched definition: `def g : T → Prop` with cases
- Goal: Transport across involution using `simp only [f, f_involution] at h`

**Future Reuse**:
Consider documenting this pattern in LEAN_STYLE_GUIDE.md for future involution proofs.

---

## Completion Checklist

**Pre-Implementation**:
- [x] Research completed and solution identified
- [x] Plan created following plan.md standard
- [x] Risks assessed and mitigations defined
- [x] Fallback strategies documented

**Implementation**:
- [ ] Truth.lean opened and theorem located
- [ ] Proof code replaced with simp only pattern
- [ ] Docstring updated with explanation
- [ ] Simp attribute verified on involution theorem
- [ ] Changes saved

**Verification**:
- [ ] Truth.lean module builds successfully
- [ ] Full codebase builds successfully
- [ ] All tests pass
- [ ] Downstream usage verified
- [ ] No regressions detected

**Documentation**:
- [ ] Theorem docstring updated
- [ ] Task 193 status updated to COMPLETED
- [ ] SORRY_REGISTRY.md updated if applicable
- [ ] Implementation summary created (if needed)

**Completion**:
- [ ] All acceptance criteria met
- [ ] Task 209 marked COMPLETED
- [ ] Task 193 marked COMPLETED
- [ ] Changes committed (if requested)

---

## Summary

This plan implements the research findings from task 209 to complete task 193's `is_valid_swap_involution` theorem. The solution uses a proven `simp only` pattern from the existing codebase (Perpetuity/Helpers.lean) that handles involutions with pattern-matched definitions correctly.

**Key Advantages**:
- Simple 4-line proof
- Proven pattern already in production
- 95%+ success probability
- 30-minute implementation time
- No new dependencies or helpers needed

**Deliverables**:
- Complete proof for is_valid_swap_involution (no sorry)
- Updated documentation explaining simp only technique
- Full build verification with all tests passing
- Task 193 completion (from 85% to 100%)

The implementation is straightforward because research identified an exact match to our problem in the existing codebase. The `simp only` tactic handles the pattern-matching interaction that blocked previous proof attempts, providing a clean and simple solution.
