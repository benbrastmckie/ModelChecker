# Implementation Plan: Automated Proof Search for TM Logic

## Metadata

- **Task Number**: 260
- **Task Name**: proof_search
- **Language**: lean
- **Proof Strategy**: Extend existing bounded DFS with proof term construction, tactic integration, and BFS variant
- **Complexity**: medium-high
- **Total Estimated Effort**: 53 hours
- **Plan Version**: 1
- **Created**: 2026-01-05
- **Research Integrated**: Yes
- **Research Report**: .opencode/specs/260_proof_search/reports/research-001.md

## Overview

### Problem Statement

Task 260's original description is **outdated**. The research reveals that core proof search infrastructure is **already implemented** (461 lines in `Logos/Core/Automation/ProofSearch.lean`). The actual work needed is to:

1. **Add proof term construction** - Currently returns `Bool` (success/failure), need `Option DerivationTree`
2. **Create tactic integration** - Enable interactive use via `by modal_search`
3. **Implement BFS variant** - Complement existing DFS for completeness
4. **Enhance heuristics** - Add S4/S5 axiom preferences and domain-specific patterns
5. **Expand test coverage** - Add modal K, temporal K, complex formulas, and negative cases

### Current Status (Research Findings)

**✅ Already Implemented** (461 lines production code):
- Bounded depth-first search with heuristics
- Proof caching and memoization (HashMap-based)
- Visit limits and cycle detection
- Configurable heuristic weights
- Search statistics tracking (hits, misses, visited, pruned)
- Helper functions for modal/temporal reasoning
- 14 TM axiom schema matching
- Backward chaining via modus ponens
- Modal K and Temporal K context transformations

**❌ Missing Features**:
- Proof term construction (returns `Bool` only)
- Tactic wrappers for interactive use
- Breadth-first search variant
- Advanced domain-specific heuristics (S4/S5 patterns)
- Comprehensive test coverage (modal K, temporal K, complex formulas)

### Scope

**In Scope**:
- Modify `SearchResult` to return `Option DerivationTree`
- Update `bounded_search` to construct proof terms
- Create `modal_search` and `temporal_search` tactics
- Implement queue-based BFS variant
- Add S4/S5 axiom preference heuristics
- Expand test suite with modal/temporal cases

**Out of Scope**:
- Parallel search strategies (future enhancement)
- Machine learning-based heuristics (future enhancement)
- Integration with external provers (future enhancement)

### Lean-Specific Constraints

- **Termination Proofs**: Must maintain termination proofs for recursive search
- **Proof Term Validity**: Constructed `DerivationTree` must be well-typed
- **Tactic Monad**: Tactics must work in `TacticM` monad
- **Aesop Integration**: Register tactics as Aesop rules
- **Noncomputable**: Proof search may need `noncomputable` keyword

### Definition of Done

- [ ] `SearchResult` returns `Option DerivationTree` instead of `Bool`
- [ ] `bounded_search` constructs valid proof terms
- [ ] `modal_search` tactic works interactively
- [ ] BFS variant implemented and tested
- [ ] S4/S5 heuristics improve search effectiveness
- [ ] Test coverage includes modal K, temporal K, complex formulas
- [ ] All tests pass (`lake build`, `lake test`)
- [ ] Documentation updated with examples
- [ ] No regressions in existing functionality

## Proof Strategy

### High-Level Approach

**Phase 1: Proof Term Construction** (Foundation)
- Modify type signatures to return `Option DerivationTree`
- Update `bounded_search` to build proof terms incrementally
- Verify termination proofs still hold
- Test with simple examples (axioms, assumptions, modus ponens)

**Phase 2: Tactic Integration** (User Interface)
- Create `modal_search` tactic wrapper
- Add syntax for depth/heuristic configuration
- Integrate with Aesop rule system
- Document tactic usage patterns

**Phase 3: BFS Variant** (Completeness)
- Implement queue-based frontier management
- Add level-by-level expansion
- Compare performance vs DFS
- Document when to use BFS vs DFS

**Phase 4: Advanced Heuristics** (Optimization)
- Add S4/S5 axiom preference patterns
- Implement proof success pattern learning
- Add adaptive depth adjustment
- Test heuristic effectiveness

**Phase 5: Expanded Testing** (Quality Assurance)
- Add modal K rule test cases
- Add temporal K rule test cases
- Add complex formula stress tests
- Add performance benchmarks
- Add negative case coverage

### Key Tactics to Use

- **Proof Construction**: `exact`, `refine`, `constructor`, `apply`
- **Termination**: `termination_by`, `decreasing_by`
- **Tactic Monad**: `TacticM`, `evalTactic`, `withMainContext`
- **Aesop**: `@[aesop safe]`, `@[aesop norm]`

### Mathlib Theorems to Leverage

- `Std.Data.HashMap` - Already used for caching
- `Std.Data.HashSet` - Already used for visited tracking
- `List.qsort` - Already used for heuristic ordering
- `Option.bind`, `Option.map` - For proof term composition

### Potential Pitfalls and Mitigation

**Pitfall 1: Termination Proof Complexity**
- **Risk**: Proof term construction may complicate termination proofs
- **Mitigation**: Keep depth-based termination, add well-founded recursion if needed

**Pitfall 2: Tactic Monad Complexity**
- **Risk**: Tactic integration requires understanding `TacticM` internals
- **Mitigation**: Start with simple wrapper, reference Mathlib tactics (`solve_by_elim`)

**Pitfall 3: BFS Memory Usage**
- **Risk**: BFS uses O(b^d) memory vs DFS O(d)
- **Mitigation**: Add queue size limits, document memory trade-offs

**Pitfall 4: Heuristic Tuning**
- **Risk**: S4/S5 heuristics may not generalize well
- **Mitigation**: Make weights configurable, benchmark on diverse examples

## Implementation Phases

### Phase 1: Proof Term Construction (15-20 hours)

**Objective**: Modify `bounded_search` to construct `DerivationTree` proof terms instead of returning `Bool`.

**Tasks**:

1. **Update Type Signatures** (2 hours)
   - Change `SearchResult` from `Bool` to `Option DerivationTree`
   - Update `bounded_search` return type
   - Update `search_with_heuristics` and `search_with_cache` signatures
   - Update `ProofCache` to store `Option DerivationTree`

2. **Implement Proof Construction for Axioms** (3 hours)
   - Modify axiom matching to construct `DerivationTree.axiom`
   - Add axiom schema identification (which of 14 axioms matched)
   - Test with simple axiom examples

3. **Implement Proof Construction for Assumptions** (2 hours)
   - Modify assumption checking to construct `DerivationTree.assume`
   - Handle context membership correctly
   - Test with assumption examples

4. **Implement Proof Construction for Modus Ponens** (4 hours)
   - Recursively construct antecedent proof
   - Combine with implication to build `DerivationTree.mp`
   - Handle multiple antecedent candidates
   - Test with modus ponens chains

5. **Implement Proof Construction for Modal K** (3 hours)
   - Transform context with `box_context`
   - Recursively construct inner proof
   - Build `DerivationTree.modal_k`
   - Test with modal formulas

6. **Implement Proof Construction for Temporal K** (3 hours)
   - Transform context with `future_context`
   - Recursively construct inner proof
   - Build `DerivationTree.temporal_k`
   - Test with temporal formulas

7. **Verify Termination Proofs** (2 hours)
   - Ensure `termination_by` still works
   - Add `decreasing_by` proofs if needed
   - Test with deep recursion

**Acceptance Criteria**:
- [ ] `SearchResult` is `Option DerivationTree`
- [ ] `bounded_search` constructs valid proof terms
- [ ] Axiom proofs work (14 TM axiom schemata)
- [ ] Assumption proofs work
- [ ] Modus ponens proofs work
- [ ] Modal K proofs work
- [ ] Temporal K proofs work
- [ ] Termination proofs verified
- [ ] All existing tests pass with new types

**Estimated Hours**: 19 hours

---

### Phase 2: Tactic Integration (8-12 hours)

**Objective**: Create interactive tactics (`modal_search`, `temporal_search`) for use in proofs.

**Tasks**:

1. **Create Basic Tactic Wrapper** (3 hours)
   - Implement `modal_search` tactic in `TacticM` monad
   - Extract goal from tactic state
   - Call `bounded_search` with default parameters
   - Apply constructed proof term to goal

2. **Add Syntax for Configuration** (2 hours)
   - Add `(depth := n)` syntax
   - Add `(visitLimit := n)` syntax
   - Add `(weights := {...})` syntax
   - Parse configuration from tactic arguments

3. **Integrate with Aesop** (3 hours)
   - Register `modal_search` as Aesop rule
   - Configure priority and safety levels
   - Test `by aesop` integration
   - Document Aesop usage

4. **Create Specialized Tactics** (2 hours)
   - Implement `temporal_search` for temporal formulas
   - Implement `propositional_search` for propositional formulas
   - Document when to use each tactic

5. **Document Tactic Usage** (2 hours)
   - Add examples to module documentation
   - Create tutorial section
   - Document configuration options
   - Add troubleshooting guide

**Acceptance Criteria**:
- [ ] `modal_search` tactic works in proofs
- [ ] Configuration syntax works (depth, visitLimit, weights)
- [ ] Aesop integration functional
- [ ] `temporal_search` and `propositional_search` work
- [ ] Documentation includes examples
- [ ] Tactics tested with real theorems

**Estimated Hours**: 12 hours

---

### Phase 3: Breadth-First Search Variant (10-15 hours)

**Objective**: Implement queue-based BFS variant to complement existing DFS.

**Tasks**:

1. **Design BFS Data Structures** (2 hours)
   - Define `SearchQueue` type (frontier management)
   - Define `BFSState` (queue, cache, visited, stats)
   - Design level-by-level expansion strategy

2. **Implement Queue Operations** (3 hours)
   - Implement `enqueue` (add goals to frontier)
   - Implement `dequeue` (get next goal)
   - Implement `isEmpty` check
   - Test queue operations

3. **Implement BFS Core Algorithm** (4 hours)
   - Implement `bfs_search` function
   - Add level-by-level expansion
   - Add queue size limits
   - Handle termination conditions

4. **Implement Proof Term Construction for BFS** (3 hours)
   - Construct `DerivationTree` during BFS
   - Handle proof term composition
   - Test with simple examples

5. **Compare BFS vs DFS Performance** (2 hours)
   - Benchmark on diverse examples
   - Measure memory usage
   - Document trade-offs
   - Recommend when to use each

6. **Document BFS Usage** (1 hour)
   - Add BFS examples
   - Document performance characteristics
   - Add usage guidelines

**Acceptance Criteria**:
- [ ] `bfs_search` function implemented
- [ ] Queue-based frontier management works
- [ ] Level-by-level expansion correct
- [ ] Proof term construction works for BFS
- [ ] Performance comparison documented
- [ ] BFS tests pass
- [ ] Documentation includes BFS examples

**Estimated Hours**: 15 hours

---

### Phase 4: Advanced Domain-Specific Heuristics (12-18 hours)

**Objective**: Enhance heuristics with S4/S5 axiom preferences and domain-specific patterns.

**Tasks**:

1. **Implement S4 Axiom Preferences** (3 hours)
   - Identify S4 axiom patterns (□φ → □□φ, □φ → φ)
   - Add heuristic weights for S4 axioms
   - Test with S4 theorems

2. **Implement S5 Axiom Preferences** (3 hours)
   - Identify S5 axiom patterns (◇□φ → □φ, φ → □◇φ)
   - Add heuristic weights for S5 axioms
   - Test with S5 theorems

3. **Implement Proof Success Pattern Learning** (4 hours)
   - Track successful proof patterns
   - Adjust heuristic weights based on success
   - Test adaptive heuristics

4. **Implement Adaptive Depth Adjustment** (3 hours)
   - Start with shallow depth
   - Increase depth if search fails
   - Add iterative deepening strategy

5. **Benchmark Heuristic Effectiveness** (3 hours)
   - Test on diverse theorem set
   - Measure search time reduction
   - Document heuristic impact

6. **Document Heuristic Tuning** (2 hours)
   - Add heuristic tuning guide
   - Document weight configuration
   - Add examples of effective weights

**Acceptance Criteria**:
- [ ] S4 axiom preferences implemented
- [ ] S5 axiom preferences implemented
- [ ] Proof success pattern learning works
- [ ] Adaptive depth adjustment works
- [ ] Heuristics benchmarked and documented
- [ ] Tuning guide created
- [ ] Tests pass with new heuristics

**Estimated Hours**: 18 hours

---

### Phase 5: Expanded Test Coverage (8-12 hours)

**Objective**: Add comprehensive test coverage for modal K, temporal K, complex formulas, and negative cases.

**Tasks**:

1. **Add Modal K Rule Tests** (2 hours)
   - Test `□(φ → ψ) → (□φ → □ψ)` derivation
   - Test context transformation
   - Test nested modal operators

2. **Add Temporal K Rule Tests** (2 hours)
   - Test `G(φ → ψ) → (Gφ → Gψ)` derivation
   - Test context transformation
   - Test nested temporal operators

3. **Add Complex Formula Tests** (3 hours)
   - Test deeply nested formulas
   - Test large contexts
   - Test mixed modal/temporal formulas

4. **Add Negative Case Tests** (2 hours)
   - Test unprovable goals
   - Test depth limit enforcement
   - Test visit limit enforcement

5. **Add Performance Benchmarks** (2 hours)
   - Benchmark search time vs depth
   - Benchmark cache effectiveness
   - Benchmark heuristic impact

6. **Document Test Coverage** (1 hour)
   - Update test documentation
   - Add coverage report
   - Document test organization

**Acceptance Criteria**:
- [ ] Modal K rule tests pass
- [ ] Temporal K rule tests pass
- [ ] Complex formula tests pass
- [ ] Negative case tests pass
- [ ] Performance benchmarks created
- [ ] Test coverage documented
- [ ] All tests pass (`lake test`)

**Estimated Hours**: 12 hours

---

## Mathlib Integration

### Required Imports

Already imported:
- `Std.Data.HashMap` - Proof caching
- `Std.Data.HashSet` - Visited tracking

New imports needed:
- `Lean.Elab.Tactic` - Tactic monad
- `Aesop` - Aesop integration

### Relevant Namespaces

- `Logos.Core.Syntax` - Formula definitions
- `Logos.Core.ProofSystem` - DerivationTree
- `Logos.Core.Theorems.ModalS4` - S4 axiom theorems
- `Logos.Core.Theorems.ModalS5` - S5 axiom theorems

### API Usage Patterns

**Proof Term Construction**:
```lean
-- Axiom proof
DerivationTree.axiom (Axiom.prop_k φ ψ χ)

-- Assumption proof
DerivationTree.assume h

-- Modus ponens proof
DerivationTree.mp (proof_of_imp : DerivationTree Γ (φ.imp ψ)) 
                  (proof_of_ant : DerivationTree Γ φ)

-- Modal K proof
DerivationTree.modal_k (proof : DerivationTree (box_context Γ) φ)
```

**Tactic Monad**:
```lean
def modal_search (depth : Nat := 10) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Extract formula from goal type
  -- Call bounded_search
  -- Apply proof term to goal
```

### Version Compatibility Notes

- Lean 4 version: Compatible with current toolchain
- Mathlib version: No specific version requirements
- Aesop version: Latest stable

## Testing and Validation

### Type Checking

```bash
# Build all modules
lake build Logos.Core.Automation.ProofSearch

# Check for errors
lake build --verbose
```

### Unit Tests

**Test File**: `LogosTest/Core/Automation/ProofSearchTest.lean`

**Existing Tests** (68 lines):
- Axiom matching (15 positive, 2 negative)
- Heuristic scoring (5 baseline, 2 weighted)
- Subgoal ordering (1 case)
- Bounded search (3 cases)
- Caching (1 case)
- Visit limits (1 case)

**New Tests to Add**:
- Proof term construction (axioms, assumptions, modus ponens)
- Modal K rule application
- Temporal K rule application
- Complex formulas
- Negative cases (unprovable goals)
- BFS variant
- Tactic integration

### Property Testing

**Properties to Test**:
- Soundness: If search returns proof, it's valid
- Completeness: If derivable within depth, search finds it
- Termination: Search always terminates within depth bound
- Caching: Cache hits return same result as cache misses

### Example Usage Verification

```lean
-- Test proof term construction
example : ⊢ (Formula.atom "p").box.imp (Formula.atom "p") := by
  modal_search (depth := 5)

-- Test with context
example (p q : Formula) (h : ⊢ p) (h2 : ⊢ p.imp q) : ⊢ q := by
  modal_search (depth := 3)

-- Test modal K
example (p : Formula) : ⊢ p.box.imp p.box.box := by
  modal_search (depth := 10)
```

### Documentation Review

- [ ] Module documentation updated
- [ ] Function docstrings complete
- [ ] Examples added to documentation
- [ ] Tactic usage documented
- [ ] Heuristic tuning guide created

## Artifacts

### Lean Source Files

- `Logos/Core/Automation/ProofSearch.lean` - Main implementation (modify existing 461 lines)
- `Logos/Core/Automation/ProofSearchBFS.lean` - BFS variant (new, ~200 lines)
- `Logos/Core/Automation/ProofSearchTactics.lean` - Tactic integration (new, ~150 lines)
- `Logos/Core/Automation/ProofSearchHeuristics.lean` - Advanced heuristics (new, ~200 lines)

### Test Files

- `LogosTest/Core/Automation/ProofSearchTest.lean` - Existing tests (expand from 68 to ~300 lines)
- `LogosTest/Core/Automation/ProofSearchBFSTest.lean` - BFS tests (new, ~100 lines)
- `LogosTest/Core/Automation/ProofSearchTacticsTest.lean` - Tactic tests (new, ~100 lines)

### Documentation

- `Documentation/UserGuide/PROOF_SEARCH.md` - User guide (new)
- `Documentation/Development/PROOF_SEARCH_INTERNALS.md` - Developer guide (new)

## Rollback

### Git Commit Strategy

**Incremental Commits per Phase**:
- Phase 1: "feat(proof-search): add proof term construction"
- Phase 2: "feat(proof-search): add tactic integration"
- Phase 3: "feat(proof-search): add BFS variant"
- Phase 4: "feat(proof-search): add advanced heuristics"
- Phase 5: "test(proof-search): expand test coverage"

### Revert Procedure if Proof Blocked

**If Phase 1 Fails** (Proof Term Construction):
1. Revert to `Bool` return type
2. Keep existing infrastructure
3. Document blocker in SORRY_REGISTRY.md
4. Create follow-up task for proof term construction

**If Phase 2 Fails** (Tactic Integration):
1. Keep proof term construction
2. Remove tactic wrappers
3. Document limitation in user guide
4. Proof search still usable programmatically

**If Phase 3 Fails** (BFS Variant):
1. Keep DFS implementation
2. Remove BFS files
3. Document DFS-only limitation
4. BFS is optional enhancement

**If Phase 4 Fails** (Advanced Heuristics):
1. Keep basic heuristics
2. Remove S4/S5 preferences
3. Document heuristic limitations
4. Basic heuristics still functional

### Alternative Approaches if Primary Strategy Fails

**Alternative 1: Proof Sketch Instead of Full Proof**
- Return proof sketch (strategy used) instead of full `DerivationTree`
- Simpler to implement, still useful for debugging
- Can be upgraded to full proof later

**Alternative 2: Tactic-Only Interface**
- Skip programmatic API, focus on tactic integration
- Simpler for users, less flexible
- Proof term construction happens in tactic monad

**Alternative 3: External Prover Integration**
- Delegate to external prover (e.g., Z3, CVC5)
- Translate TM logic to SMT-LIB
- Reconstruct proof from external result

## Summary

This plan enhances the **already-implemented** proof search infrastructure (461 lines) with:

1. **Proof Term Construction** (19 hours) - Return `Option DerivationTree` instead of `Bool`
2. **Tactic Integration** (12 hours) - Enable `by modal_search` in proofs
3. **BFS Variant** (15 hours) - Complement DFS with queue-based search
4. **Advanced Heuristics** (18 hours) - Add S4/S5 preferences and adaptive depth
5. **Expanded Testing** (12 hours) - Add modal K, temporal K, complex formulas

**Total Effort**: 76 hours (revised from 40-60 hours to account for proof term construction complexity)

**Key Insight**: Task 260's description is outdated. The core infrastructure is production-ready. The actual work is enhancing it with proof term construction, tactic integration, and advanced features.

**Risk Mitigation**: Each phase is independently valuable. If later phases fail, earlier phases still provide significant value (e.g., proof term construction alone is a major improvement).

**Success Criteria**: Proof search becomes usable in interactive proofs via tactics, constructs valid proof terms, and supports both DFS and BFS strategies with configurable heuristics.
