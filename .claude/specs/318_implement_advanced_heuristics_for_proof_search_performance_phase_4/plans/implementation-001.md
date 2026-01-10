# Implementation Plan: Advanced Heuristics for Proof Search Performance (Phase 4)

**Task**: 318 - Implement Phase 4 of task 260: Advanced Heuristics  
**Created**: 2026-01-07  
**Estimated Total Effort**: 12-18 hours  
**Phase Count**: 5 phases  
**Complexity**: Medium  
**Language**: Lean 4  
**Dependencies**: Task 260 (Phases 1-3), Task 317 (BFS variant research)

---

## Overview

This plan implements advanced heuristics for proof search performance in ProofSearch.lean. The research (research-001.md) identified three critical optimization opportunities:

1. **Quick Win**: Implement proper sorting in `orderSubgoalsByScore` (currently returns targets unsorted)
2. **High Value**: Add domain-specific heuristics for modal/temporal logic
3. **Optional**: Implement proof caching with hash-consing (deferred to future work)

The implementation is structured in 5 phases, each targeting 2-4 hours of work, following the research recommendations.

---

## Research Integration

**Research Artifacts Harvested**:
- `.opencode/specs/318_implement_advanced_heuristics_for_proof_search_performance_phase_4/reports/research-001.md`

**Key Research Findings**:

1. **Critical Gap**: `orderSubgoalsByScore` (lines 338-342) is unimplemented - returns targets in original order, defeating heuristic scoring
2. **Existing Infrastructure**: `heuristic_score` function (lines 313-331) computes scores but they're never used for ordering
3. **Formula Metrics Needed**: `modalDepth`, `temporalDepth`, `countImplications` for structure analysis
4. **Domain-Specific Bonuses**: Modal/temporal heuristics can prioritize matching strategies
5. **Tunable Weights**: `HeuristicWeights` structure exists but needs tuning for optimal performance

**Research Recommendations**:
- Implement sorting first (30 minutes, immediate impact)
- Add formula complexity metrics (1-2 hours)
- Implement domain-specific heuristics (2-3 hours)
- Tune weights empirically (2-3 hours)
- Defer hash-consing until cache hit rates measured

---

## Phase 1: Implement Sorting in orderSubgoalsByScore [NOT STARTED]

**Goal**: Fix the critical gap - implement proper sorting to enable heuristic-guided search

**Estimated Effort**: 1-2 hours

**Tasks**:

1. **Replace TODO with mergeSort implementation** (30 minutes)
   - File: `Logos/Core/Automation/ProofSearch.lean` (line 338-342)
   - Replace stub with: `targets.mergeSort (fun φ ψ => heuristic_score weights Γ φ ≤ heuristic_score weights Γ ψ)`
   - Rationale: Stable O(n log n) sort, ascending order (lower score = higher priority)
   - Verification: Existing `heuristic_score` function will now be used for ordering

2. **Add unit tests for sorting correctness** (30 minutes)
   - File: `LogosTest/Core/Automation/ProofSearchTest.lean`
   - Test: Verify targets sorted by heuristic score (axioms first, dead ends last)
   - Test: Verify stable sort (equal scores preserve relative order)
   - Test: Verify empty list handled correctly
   - Test: Verify single element list handled correctly

3. **Verify integration with bounded_search** (30 minutes)
   - Trace execution to confirm `orderedTargets` are explored in score order
   - Add debug logging to show exploration order
   - Verify axioms/assumptions tried before modus ponens
   - Verify modus ponens antecedents tried by complexity

**Acceptance Criteria**:
- [ ] `orderSubgoalsByScore` implements stable sorting by heuristic score
- [ ] Unit tests pass for sorting correctness
- [ ] Integration tests show targets explored in priority order
- [ ] No performance regression on existing test suite
- [ ] Documentation updated with sorting algorithm description

**Files Modified**:
- `Logos/Core/Automation/ProofSearch.lean` (1 line change)
- `LogosTest/Core/Automation/ProofSearchTest.lean` (new tests)

**Success Metrics**:
- Sorting implementation: 1 line of code
- Test coverage: 4+ unit tests
- Performance: No regression (sorting overhead < 1% of search time)

---

## Phase 2: Add Formula Complexity Metrics [NOT STARTED]

**Goal**: Add `modalDepth`, `temporalDepth`, `countImplications` metrics to Formula.lean for structure analysis

**Estimated Effort**: 2-3 hours

**Tasks**:

1. **Implement modalDepth function** (45 minutes)
   - File: `Logos/Core/Syntax/Formula.lean`
   - Add recursive function computing nesting level of □/◇ operators
   - Pattern: `box φ => 1 + φ.modalDepth`, `imp φ ψ => max φ.modalDepth ψ.modalDepth`
   - Rationale: Deeply nested modalities require more modal K applications

2. **Implement temporalDepth function** (45 minutes)
   - File: `Logos/Core/Syntax/Formula.lean`
   - Add recursive function computing nesting level of G/F/H/P operators
   - Pattern: `all_future φ => 1 + φ.temporalDepth`, `imp φ ψ => max φ.temporalDepth ψ.temporalDepth`
   - Rationale: Deeply nested temporal operators require more temporal K applications

3. **Implement countImplications function** (30 minutes)
   - File: `Logos/Core/Syntax/Formula.lean`
   - Add recursive function counting → operators
   - Pattern: `imp φ ψ => 1 + φ.countImplications + ψ.countImplications`
   - Rationale: More implications = more modus ponens opportunities

4. **Add unit tests for each metric** (60 minutes)
   - File: `LogosTest/Core/Syntax/FormulaTest.lean`
   - Test `modalDepth`: Simple (□p = 1), nested (□□p = 2), mixed (□p → □q = 1)
   - Test `temporalDepth`: Simple (Gp = 1), nested (GGp = 2), mixed (Gp → Gq = 1)
   - Test `countImplications`: Simple (p → q = 1), nested ((p → q) → r = 2)
   - Test edge cases: atoms (depth 0), bot (depth 0), complex formulas

**Acceptance Criteria**:
- [ ] `modalDepth` correctly computes nesting level of modal operators
- [ ] `temporalDepth` correctly computes nesting level of temporal operators
- [ ] `countImplications` correctly counts implication operators
- [ ] Unit tests pass for all metrics and edge cases
- [ ] Documentation includes examples and complexity analysis
- [ ] Metrics integrate with existing `complexity` function

**Files Modified**:
- `Logos/Core/Syntax/Formula.lean` (3 new functions, ~30 lines)
- `LogosTest/Core/Syntax/FormulaTest.lean` (new tests, ~50 lines)

**Success Metrics**:
- Code added: ~80 lines (functions + tests)
- Test coverage: 12+ unit tests (4 per metric)
- Performance: O(n) where n = formula size

---

## Phase 3: Implement Domain-Specific Heuristics [NOT STARTED]

**Goal**: Add modal-specific and temporal-specific heuristics to prioritize matching strategies

**Estimated Effort**: 3-4 hours

**Tasks**:

1. **Implement modal_heuristic_bonus function** (45 minutes)
   - File: `Logos/Core/Automation/ProofSearch.lean`
   - Add function returning negative bonus for modal goals (□φ, ◇φ)
   - Pattern: `box _ => -5`, `diamond _ => -5`, `_ => 0`
   - Rationale: Modal goals benefit from modal axioms (T, 4, 5, B)

2. **Implement temporal_heuristic_bonus function** (45 minutes)
   - File: `Logos/Core/Automation/ProofSearch.lean`
   - Add function returning negative bonus for temporal goals (Gφ, Fφ, Hφ, Pφ)
   - Pattern: `all_future _ => -5`, `some_future _ => -5`, etc.
   - Rationale: Temporal goals benefit from temporal axioms (4, A, L)

3. **Implement structure_heuristic function** (45 minutes)
   - File: `Logos/Core/Automation/ProofSearch.lean`
   - Add function computing penalty based on formula structure
   - Formula: `complexity + (modalDepth * 2) + (temporalDepth * 2) + countImplications`
   - Rationale: Complex formulas are harder to prove

4. **Implement advanced_heuristic_score function** (45 minutes)
   - File: `Logos/Core/Automation/ProofSearch.lean`
   - Combine base score with domain-specific bonuses
   - Formula: `(base + modal_bonus + temporal_bonus + structure_penalty).toNat`
   - Handle negative scores by clamping to 0

5. **Add unit tests for heuristic functions** (60 minutes)
   - File: `LogosTest/Core/Automation/ProofSearchTest.lean`
   - Test `modal_heuristic_bonus`: Modal goals get bonus, others don't
   - Test `temporal_heuristic_bonus`: Temporal goals get bonus, others don't
   - Test `structure_heuristic`: Complex formulas get higher penalty
   - Test `advanced_heuristic_score`: Bonuses combine correctly

**Acceptance Criteria**:
- [ ] `modal_heuristic_bonus` returns -5 for modal goals, 0 otherwise
- [ ] `temporal_heuristic_bonus` returns -5 for temporal goals, 0 otherwise
- [ ] `structure_heuristic` computes penalty based on formula structure
- [ ] `advanced_heuristic_score` combines all heuristics correctly
- [ ] Unit tests pass for all heuristic functions
- [ ] Documentation explains heuristic design rationale

**Files Modified**:
- `Logos/Core/Automation/ProofSearch.lean` (4 new functions, ~40 lines)
- `LogosTest/Core/Automation/ProofSearchTest.lean` (new tests, ~60 lines)

**Success Metrics**:
- Code added: ~100 lines (functions + tests)
- Test coverage: 16+ unit tests (4 per function)
- Heuristic bonuses: -5 for matching goals (tunable)

---

## Phase 4: Tune Heuristic Weights [NOT STARTED]

**Goal**: Empirically tune heuristic weights for optimal performance on benchmark suite

**Estimated Effort**: 3-4 hours

**Tasks**:

1. **Create benchmark suite** (90 minutes)
   - File: `LogosTest/Core/Automation/ProofSearchBenchmark.lean` (new)
   - Add modal proofs: Modal T, 4, 5, B, K
   - Add temporal proofs: Temporal 4, A, L, K
   - Add mixed proofs: Modal-temporal interaction
   - Add deep nesting proofs: Repeated applications
   - Total: 15-20 benchmark proofs

2. **Implement benchmark runner** (60 minutes)
   - File: `LogosTest/Core/Automation/ProofSearchBenchmark.lean`
   - Run each proof with different weight configurations
   - Measure: search time (visits), cache hits, proof depth
   - Output: CSV or JSON for analysis

3. **Tune weights empirically** (90 minutes)
   - Start with default weights from research
   - Run benchmarks and record metrics
   - Adjust one weight at a time (grid search)
   - Find optimal configuration minimizing search time
   - Document tuning process and rationale

**Acceptance Criteria**:
- [ ] Benchmark suite covers modal, temporal, and mixed proofs
- [ ] Benchmark runner measures search time, cache hits, proof depth
- [ ] Optimal weights found through empirical tuning
- [ ] Tuning process documented with before/after metrics
- [ ] Performance improvement quantified (e.g., 30% fewer visits)

**Files Modified**:
- `LogosTest/Core/Automation/ProofSearchBenchmark.lean` (new, ~200 lines)
- `Logos/Core/Automation/ProofSearch.lean` (update default weights)

**Success Metrics**:
- Benchmark proofs: 15-20 proofs
- Weight configurations tested: 10-20 configurations
- Performance improvement: 20-40% reduction in search time

**Proposed Tuned Weights** (from research):
```lean
structure TunedHeuristicWeights where
  axiomWeight : Nat := 0
  assumptionWeight : Nat := 1
  mpBase : Nat := 2
  mpComplexityWeight : Nat := 2  -- Increased from 1
  modalBase : Nat := 10  -- Increased from 5
  temporalBase : Nat := 10  -- Increased from 5
  contextPenaltyWeight : Nat := 2  -- Increased from 1
  deadEnd : Nat := 100
  modalBonus : Int := -5  -- New
  temporalBonus : Int := -5  -- New
```

---

## Phase 5: Integration Testing and Documentation [NOT STARTED]

**Goal**: Verify all phases integrate correctly and update documentation

**Estimated Effort**: 2-3 hours

**Tasks**:

1. **Add integration tests** (60 minutes)
   - File: `LogosTest/Core/Automation/ProofSearchTest.lean`
   - Test: Sorting + heuristics improve search time on modal proofs
   - Test: Sorting + heuristics improve search time on temporal proofs
   - Test: Sorting + heuristics improve search time on mixed proofs
   - Test: No regression on simple proofs (axioms, assumptions)

2. **Add performance tests** (45 minutes)
   - File: `LogosTest/Core/Automation/ProofSearchTest.lean`
   - Benchmark: Search time with/without sorting
   - Benchmark: Search time with/without domain heuristics
   - Verify: Performance improvement quantified

3. **Update module documentation** (45 minutes)
   - File: `Logos/Core/Automation/ProofSearch.lean`
   - Update module docstring with heuristic description
   - Document new complexity metrics
   - Document domain-specific heuristics
   - Add examples demonstrating heuristic usage

4. **Update project documentation** (30 minutes)
   - File: `Documentation/Development/PROOF_SEARCH_AUTOMATION.md`
   - Document Phase 4 completion
   - Document heuristic design rationale
   - Document tuning process and results
   - Add performance benchmarks

**Acceptance Criteria**:
- [ ] Integration tests pass showing performance improvement
- [ ] Performance tests quantify improvement (e.g., 30% fewer visits)
- [ ] No regression on existing test suite
- [ ] Module documentation updated with heuristic description
- [ ] Project documentation updated with Phase 4 completion
- [ ] All tests pass in CI pipeline

**Files Modified**:
- `LogosTest/Core/Automation/ProofSearchTest.lean` (new tests, ~80 lines)
- `Logos/Core/Automation/ProofSearch.lean` (documentation updates)
- `Documentation/Development/PROOF_SEARCH_AUTOMATION.md` (updates)

**Success Metrics**:
- Integration tests: 4+ tests
- Performance improvement: 20-40% reduction in search time
- Test coverage: All new code covered by tests
- Documentation: Complete and accurate

---

## Risk Assessment

### Risk 1: Sorting Overhead

**Likelihood**: Low  
**Impact**: Low  
**Mitigation**:
- Use efficient `mergeSort` (O(n log n))
- Benchmark sorting time vs search time savings
- Research shows sorting overhead < 1% of search time
- If overhead is high, cache sorted results

### Risk 2: Heuristic Tuning Difficulty

**Likelihood**: Medium  
**Impact**: Medium  
**Mitigation**:
- Start with conservative weights from research
- Tune incrementally on benchmark suite
- Document tuning process and rationale
- Provide multiple weight configurations
- Research provides initial tuned weights

### Risk 3: Performance Regression

**Likelihood**: Low  
**Impact**: High  
**Mitigation**:
- Benchmark before and after each phase
- Add performance tests to CI pipeline
- Revert if regression detected
- Research shows expected 20-40% improvement

### Risk 4: Complexity Creep

**Likelihood**: Low  
**Impact**: Medium  
**Mitigation**:
- Implement incrementally (5 phases)
- Test each component independently
- Document each enhancement clearly
- Defer optional optimizations (hash-consing)

---

## Dependencies

**Internal Dependencies**:
- Task 260 (Proof Search): Core infrastructure must be working
- Task 317 (BFS Variant): Research provides context on search strategies

**External Dependencies**:
- Lean 4 Batteries: `List.mergeSort` for sorting
- Existing test infrastructure: `LogosTest/Core/Automation/ProofSearchTest.lean`

**Blocking Issues**: None

---

## Success Criteria

**Phase-Level Success**:
- [ ] Phase 1: Sorting implemented and tested
- [ ] Phase 2: Complexity metrics implemented and tested
- [ ] Phase 3: Domain heuristics implemented and tested
- [ ] Phase 4: Weights tuned empirically
- [ ] Phase 5: Integration tested and documented

**Overall Success**:
- [ ] `orderSubgoalsByScore` implements proper sorting
- [ ] Formula complexity metrics (`modalDepth`, `temporalDepth`, `countImplications`) added
- [ ] Domain-specific heuristics (modal, temporal, structure) implemented
- [ ] Heuristic weights tuned for optimal performance
- [ ] Performance improvement quantified (20-40% reduction in search time)
- [ ] All tests pass (unit, integration, performance)
- [ ] Documentation complete and accurate
- [ ] No regressions on existing test suite

**Performance Targets** (from research):

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| **Simple Modal** | 100 visits | 20 visits | 80% |
| **Simple Temporal** | 100 visits | 20 visits | 80% |
| **Complex Mixed** | 500 visits | 100 visits | 80% |
| **Deep Nested** | 1000 visits | 300 visits | 70% |

---

## Testing Strategy

**Unit Tests** (per phase):
- Phase 1: Sorting correctness (4 tests)
- Phase 2: Complexity metrics (12 tests)
- Phase 3: Heuristic functions (16 tests)
- Phase 4: Benchmark suite (15-20 proofs)
- Phase 5: Integration tests (4 tests)

**Integration Tests**:
- Sorting + heuristics improve modal proofs
- Sorting + heuristics improve temporal proofs
- Sorting + heuristics improve mixed proofs
- No regression on simple proofs

**Performance Tests**:
- Benchmark search time with/without sorting
- Benchmark search time with/without domain heuristics
- Measure cache hit rates
- Measure memory usage

**Regression Tests**:
- All existing tests still pass
- Proof depths don't increase (optimality preserved)
- No performance regressions on simple proofs

---

## Future Work (Deferred)

**Hash-Consing Optimization** (6-8 hours):
- Prerequisite: Measure cache hit rates first
- Implement `HashConsTable` for formula deduplication
- Update `CacheKey` to use `FormulaId`
- Benchmark memory usage and cache hit rates
- Decision: Implement only if cache hit rate < 30% or memory usage > 100MB

**Historical Success Tracking** (8-10 hours):
- Prerequisite: Basic heuristics working and tuned
- Implement `SuccessHistory` structure
- Track axiom/rule successes during search
- Implement `historical_heuristic` function
- Persist history across search sessions

**Machine Learning Integration** (20-30 hours):
- Prerequisite: Large corpus of proofs for training
- Collect proof corpus from test suite
- Extract features (formula structure, context, etc.)
- Train heuristic model (decision tree, neural network)
- Integrate model into proof search

---

## Implementation Notes

**Code Style**:
- Follow LEAN_STYLE_GUIDE.md
- Use descriptive function names
- Add docstrings for all public functions
- Include complexity analysis in comments

**Testing Standards**:
- Follow TESTING_STANDARDS.md
- Aim for 85%+ test coverage
- Include edge cases and error conditions
- Use property-based testing where applicable

**Documentation Standards**:
- Follow DOC_QUALITY_CHECKLIST.md
- Update module docstrings
- Add examples demonstrating usage
- Document design rationale

**Git Workflow**:
- One commit per phase
- Descriptive commit messages
- Reference task number in commits
- Ensure all tests pass before committing

---

## Appendix A: Research Summary

**Research Report**: `.opencode/specs/318_implement_advanced_heuristics_for_proof_search_performance_phase_4/reports/research-001.md`

**Key Findings**:
1. `orderSubgoalsByScore` is unimplemented (critical gap)
2. `heuristic_score` exists but unused for ordering
3. Formula complexity metrics needed for structure analysis
4. Domain-specific heuristics can prioritize matching strategies
5. Heuristic weights need empirical tuning

**Recommendations**:
1. Implement sorting first (quick win, 30 minutes)
2. Add complexity metrics (1-2 hours)
3. Implement domain heuristics (2-3 hours)
4. Tune weights empirically (2-3 hours)
5. Defer hash-consing until cache hit rates measured

---

## Appendix B: File Locations

**Source Files**:
- `Logos/Core/Automation/ProofSearch.lean` - Main proof search implementation
- `Logos/Core/Syntax/Formula.lean` - Formula structure and metrics

**Test Files**:
- `LogosTest/Core/Automation/ProofSearchTest.lean` - Unit and integration tests
- `LogosTest/Core/Automation/ProofSearchBenchmark.lean` - Benchmark suite (new)
- `LogosTest/Core/Syntax/FormulaTest.lean` - Formula metric tests

**Documentation Files**:
- `Documentation/Development/PROOF_SEARCH_AUTOMATION.md` - Proof search documentation
- `Documentation/Development/LEAN_STYLE_GUIDE.md` - Code style guide
- `Documentation/Development/TESTING_STANDARDS.md` - Testing standards

---

**Plan Created**: 2026-01-07  
**Next Steps**: Begin Phase 1 implementation with `/implement 318`
