# Implementation Plan: BFS Variant for Proof Search Completeness

**Task**: 317 - Implement Phase 3 of task 260: BFS Variant  
**Created**: 2026-01-08  
**Language**: lean  
**Complexity**: medium  
**Total Estimated Effort**: 10-12 hours  
**Proof Strategy**: Iterative Deepening DFS (IDDFS) with optional Best-First Search enhancement  
**Mathlib Dependencies**: Std.Data.HashMap, Std.Data.HashSet, Batteries.Data.BinomialHeap (optional)

---

## Metadata

- **Task Number**: 317
- **Description**: Add breadth-first search variant to ProofSearch.lean to ensure completeness guarantees. Current implementation uses bounded DFS which may miss proofs. BFS variant will explore search space level-by-level, guaranteeing shortest proofs are found first.
- **Priority**: Medium
- **Dependencies**: Task 260 (ProofSearch.lean infrastructure complete)
- **Research Integrated**: Yes (research-001.md, 1403 lines)
- **Blocking**: None

---

## Overview

### Problem Statement

The current `ProofSearch.lean` implementation uses bounded depth-first search (DFS) with a fixed depth limit (default: 5). This approach has critical limitations:

1. **Incompleteness**: Proofs beyond the depth limit are unreachable, even if they exist
2. **No optimality guarantee**: Does not guarantee finding the shortest proof
3. **Arbitrary cutoff**: Depth limit requires manual tuning for each problem
4. **Missed proofs**: May fail to find valid proofs that exist just beyond the depth bound

### Solution Approach

Research identified **Iterative Deepening Depth-First Search (IDDFS)** as the optimal solution:

- **Completeness**: Guaranteed to find proofs if they exist (within maxDepth)
- **Optimality**: Guaranteed to find shortest proofs (minimum depth)
- **Space efficiency**: O(d) space like DFS, not O(b^d) like pure BFS
- **Time efficiency**: Only ~11% overhead vs single DFS to depth d (for b=10)
- **Minimal code changes**: Wraps existing `bounded_search` with iteration
- **Preserves heuristics**: Compatible with existing heuristic infrastructure

### Scope

**In Scope**:
- Implement `iddfs_search` function with iterative deepening
- Add `SearchStrategy` enum for algorithm selection
- Add unified `search` interface with configurable strategy
- Update module documentation with IDDFS description
- Add comprehensive tests for IDDFS correctness
- Benchmark IDDFS vs bounded DFS performance
- Document completeness and optimality guarantees

**Out of Scope** (Future Enhancements):
- Best-First Search with priority queue (Phase 4 candidate)
- Beam Search with queue size limiting (Phase 4 candidate)
- Bidirectional search (advanced optimization)
- Mathlib BestFirstSearch integration (deprecated module)

### Lean-Specific Constraints

- **No Prop → Type refactor needed**: IDDFS works with existing `Bool` return type
- **Preserves existing API**: `bounded_search` remains unchanged for backward compatibility
- **Termination proofs**: IDDFS requires well-founded recursion on depth
- **Space safety**: No risk of stack overflow (bounded by maxDepth)
- **Heuristic compatibility**: Works with existing `HeuristicWeights` infrastructure

### Definition of Done

- [PASS] `iddfs_search` function implemented and type-checks
- [PASS] `SearchStrategy` enum defined with BoundedDFS, IDDFS, BestFirst variants
- [PASS] Unified `search` interface implemented
- [PASS] All tests pass (unit tests for shallow/medium/deep proofs)
- [PASS] Benchmarks show IDDFS finds proofs beyond depth limit
- [PASS] Documentation updated with complexity analysis
- [PASS] Module builds successfully with `lake build`
- [PASS] No regressions in existing proof search functionality

---

## Proof Strategy

### High-Level Approach

**Iterative Deepening DFS (IDDFS)** combines BFS completeness with DFS space efficiency by running depth-limited DFS with increasing depth limits:

```
IDDFS(goal, maxDepth):
  for depth = 0 to maxDepth:
    result = bounded_search(goal, depth)
    if result = SUCCESS:
      return SUCCESS (shortest proof found)
  return FAILURE (no proof within maxDepth)
```

### Key Tactics and Patterns

1. **Iterative deepening loop**: Increment depth from 0 to maxDepth
2. **Early termination**: Return immediately when proof found (shortest proof)
3. **Visit limit enforcement**: Stop if total visits exceed visitLimit
4. **Cache propagation**: Carry ProofCache across depth iterations for efficiency
5. **Statistics accumulation**: Aggregate SearchStats across all iterations

### Mathlib Theorems to Leverage

- **Std.Data.HashMap**: Existing ProofCache infrastructure (no changes needed)
- **Std.Data.HashSet**: Existing Visited set infrastructure (no changes needed)
- **Nat.lt_succ_self**: For termination proof (depth < depth + 1)
- **Nat.le_refl**: For maxDepth bound checking

### Potential Pitfalls and Mitigation

1. **Redundant work**: IDDFS re-explores shallow depths multiple times
   - **Mitigation**: Acceptable overhead (~11% for b=10), dominated by deepest level
   - **Future optimization**: Carry cache across iterations (already implemented)

2. **Visit limit exhaustion**: May hit visitLimit before maxDepth
   - **Mitigation**: Check visitLimit after each depth iteration, return early
   - **User control**: Expose visitLimit parameter for tuning

3. **Termination proof complexity**: Nested recursion (iterate + bounded_search)
   - **Mitigation**: Use `termination_by` on depth parameter (well-founded)
   - **Fallback**: Mark as `partial` if termination proof difficult

4. **Type checking performance**: Large depth iterations may be slow
   - **Mitigation**: Default maxDepth=100 is reasonable for modal logic
   - **User control**: Expose maxDepth parameter for tuning

---

## Implementation Phases

### Phase 1: Core IDDFS Implementation [NOT STARTED]

**Objective**: Implement `iddfs_search` function with iterative deepening logic

**Tasks**:
1. Add `iddfs_search` function after `bounded_search` in ProofSearch.lean
2. Implement iterative deepening loop with depth increment
3. Propagate ProofCache across iterations for efficiency
4. Accumulate SearchStats across iterations
5. Add early termination on proof found
6. Add visit limit enforcement
7. Add termination proof or mark as `partial`

**Acceptance Criteria**:
- [PASS] `iddfs_search` function type-checks
- [PASS] Function signature matches specification:
  ```lean
  def iddfs_search (Γ : Context) (φ : Formula) (maxDepth : Nat := 100)
      (visitLimit : Nat := 10000) (weights : HeuristicWeights := {})
      : Bool × ProofCache × Visited × SearchStats × Nat
  ```
- [PASS] Iterative deepening loop increments depth from 0 to maxDepth
- [PASS] Early termination on proof found (returns immediately)
- [PASS] Visit limit enforcement (stops if totalVisits ≥ visitLimit)
- [PASS] ProofCache propagated across iterations
- [PASS] SearchStats accumulated across iterations

**Estimated Effort**: 2-3 hours

**Files Modified**:
- `Logos/Core/Automation/ProofSearch.lean` (add ~50 lines)

---

### Phase 2: Search Strategy Configuration [NOT STARTED]

**Objective**: Add `SearchStrategy` enum and unified `search` interface

**Tasks**:
1. Define `SearchStrategy` inductive type with BoundedDFS, IDDFS, BestFirst variants
2. Add `Repr` instance for SearchStrategy
3. Implement unified `search` function with strategy pattern matching
4. Set default strategy to IDDFS (maxDepth=100)
5. Add BestFirst variant as `sorry` placeholder for future work
6. Update existing `search_with_heuristics` to use IDDFS by default

**Acceptance Criteria**:
- [PASS] `SearchStrategy` enum defined with 3 variants
- [PASS] `search` function type-checks with strategy parameter
- [PASS] Default strategy is IDDFS (maxDepth=100)
- [PASS] BoundedDFS variant delegates to `bounded_search`
- [PASS] IDDFS variant delegates to `iddfs_search`
- [PASS] BestFirst variant marked as `sorry` with TODO comment
- [PASS] `search_with_heuristics` updated to use IDDFS

**Estimated Effort**: 1-2 hours

**Files Modified**:
- `Logos/Core/Automation/ProofSearch.lean` (add ~30 lines)

---

### Phase 3: Documentation and Examples [NOT STARTED]

**Objective**: Update module documentation with IDDFS description and complexity analysis

**Tasks**:
1. Update module docstring with IDDFS overview
2. Add complexity analysis section (time: O(b^d), space: O(d))
3. Add completeness guarantee documentation
4. Add optimality guarantee documentation
5. Add IDDFS usage examples
6. Document SearchStrategy enum and variants
7. Update "Implementation Status" section
8. Add references to IDDFS research (Korf 1985)

**Acceptance Criteria**:
- [PASS] Module docstring updated with IDDFS description
- [PASS] Complexity analysis documented (time/space)
- [PASS] Completeness guarantee documented
- [PASS] Optimality guarantee documented
- [PASS] At least 2 usage examples added
- [PASS] SearchStrategy variants documented
- [PASS] References section updated

**Estimated Effort**: 1-2 hours

**Files Modified**:
- `Logos/Core/Automation/ProofSearch.lean` (update docstrings, ~50 lines)

---

### Phase 4: Testing and Validation [NOT STARTED]

**Objective**: Add comprehensive tests for IDDFS correctness and completeness

**Tasks**:
1. Add test for shallow proof (depth 2) - verify IDDFS finds same proof as bounded DFS
2. Add test for medium proof (depth 5) - verify IDDFS finds proof
3. Add test for deep proof (depth 10+) - verify IDDFS finds proof beyond bounded DFS limit
4. Add test for shortest proof guarantee - verify IDDFS returns minimum depth
5. Add test for visit limit enforcement - verify early termination
6. Add test for maxDepth enforcement - verify failure when proof too deep
7. Add integration test with existing heuristics
8. Add property-based test for completeness (if proof exists, IDDFS finds it)

**Test Cases**:
```lean
-- Shallow proof (depth 2): Propositional K axiom
example : ⊢ (p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))

-- Medium proof (depth 5): Modal 4 axiom
example : ⊢ (p.box).imp (p.box.box)

-- Deep proof (depth 10+): Temporal 4 iterated
example : ⊢ (p.all_future).imp (p.all_future.all_future.all_future)

-- Shortest proof: Verify IDDFS returns depth 2, not depth 5
example : ⊢ p.imp p  -- Trivial proof, should find at depth 0-1
```

**Acceptance Criteria**:
- [PASS] All 8 test cases pass
- [PASS] IDDFS finds proofs beyond bounded DFS depth limit
- [PASS] IDDFS returns shortest proof (minimum depth)
- [PASS] Visit limit enforcement works correctly
- [PASS] maxDepth enforcement works correctly
- [PASS] No regressions in existing tests
- [PASS] Test coverage for edge cases (empty context, trivial proofs)

**Estimated Effort**: 3-4 hours

**Files Modified**:
- `LogosTest/Core/Automation/ProofSearchTest.lean` (add ~150 lines)

---

### Phase 5: Benchmarking and Performance Analysis [NOT STARTED]

**Objective**: Benchmark IDDFS vs bounded DFS and document performance characteristics

**Tasks**:
1. Create benchmark suite with proofs at depths 2, 5, 10, 15, 20
2. Measure total visits for IDDFS vs bounded DFS
3. Measure time (via SearchStats.visited) for both algorithms
4. Measure completeness (proofs found) for both algorithms
5. Measure optimality (proof depths) for both algorithms
6. Document results in implementation summary
7. Verify ~11% overhead claim from research (for b=10)
8. Identify optimal maxDepth default (currently 100)

**Benchmark Proofs**:
- **Depth 2**: Propositional axioms (K, S)
- **Depth 5**: Modal axioms (T, 4, B, 5)
- **Depth 10**: Temporal axioms (4, A, L)
- **Depth 15**: Complex modal theorems
- **Depth 20**: Stress test (may exceed visitLimit)

**Acceptance Criteria**:
- [PASS] Benchmark suite runs successfully
- [PASS] IDDFS finds all proofs that bounded DFS finds
- [PASS] IDDFS finds proofs beyond bounded DFS depth limit
- [PASS] IDDFS overhead is ≤20% vs bounded DFS (for shallow proofs)
- [PASS] IDDFS returns shortest proofs (minimum depth)
- [PASS] Results documented in implementation summary
- [PASS] Optimal maxDepth identified and documented

**Estimated Effort**: 2-3 hours

**Files Created**:
- `.opencode/specs/317_bfs_variant_phase3/benchmarks/iddfs-vs-dfs.md` (new)

---

## Mathlib Integration

### Required Imports

```lean
import Std.Data.HashMap
import Std.Data.HashSet
import Logos.ProofSystem
import Logos.Semantics
```

**Note**: No new imports needed - IDDFS uses existing infrastructure.

### Relevant Namespaces

- `Logos.Core.Automation`: ProofSearch module namespace
- `Logos.Core.Syntax`: Formula and Context types
- `Logos.Core.ProofSystem`: Derivation types (for future proof term construction)

### API Usage Patterns

**ProofCache (Std.HashMap)**:
```lean
-- Create empty cache
let cache := ProofCache.empty

-- Insert result
let cache' := cache.insert (Γ, φ) true

-- Lookup result
match cache.find? (Γ, φ) with
| some result => result
| none => -- Not cached
```

**Visited (Std.HashSet)**:
```lean
-- Create empty visited set
let visited := Visited.empty

-- Insert key
let visited' := visited.insert (Γ, φ)

-- Check membership
if visited.contains (Γ, φ) then -- Skip
```

### Version Compatibility Notes

- **Lean 4.3.0+**: Required for Std.Data.HashMap/HashSet
- **Mathlib 4.0.0+**: No Mathlib dependencies (uses Std only)
- **Batteries**: No Batteries dependencies (BinomialHeap optional for future)

---

## Testing and Validation

### Type Checking

**Command**: `lake build Logos.Core.Automation.ProofSearch`

**Expected**: No errors, all functions type-check

**Validation**:
- [PASS] `iddfs_search` type-checks
- [PASS] `SearchStrategy` type-checks
- [PASS] `search` type-checks
- [PASS] No termination errors (or marked `partial`)

### Unit Tests

**File**: `LogosTest/Core/Automation/ProofSearchTest.lean`

**Test Categories**:
1. **Shallow proofs** (depth 2): Verify IDDFS finds same proofs as bounded DFS
2. **Medium proofs** (depth 5): Verify IDDFS finds proofs
3. **Deep proofs** (depth 10+): Verify IDDFS finds proofs beyond bounded DFS limit
4. **Shortest proof**: Verify IDDFS returns minimum depth
5. **Visit limit**: Verify early termination on visitLimit
6. **Max depth**: Verify failure when proof too deep
7. **Heuristics**: Verify IDDFS works with existing heuristics
8. **Edge cases**: Empty context, trivial proofs, unsatisfiable goals

**Command**: `lake test LogosTest.Core.Automation.ProofSearchTest`

**Expected**: All tests pass

### Property Testing

**Properties to Test**:
1. **Completeness**: If `bounded_search Γ φ d` returns true, then `iddfs_search Γ φ d` returns true
2. **Optimality**: If `iddfs_search Γ φ maxDepth` returns true at depth d, then `bounded_search Γ φ (d-1)` returns false
3. **Monotonicity**: If `iddfs_search Γ φ d1` returns false, then `iddfs_search Γ φ d2` returns false for d2 < d1
4. **Visit limit**: If `iddfs_search` returns false due to visitLimit, then totalVisits ≥ visitLimit

**Note**: Property-based testing framework not yet established - defer to Phase 5 of task 260.

### Example Usage Verification

**Test Cases**:
```lean
-- Example 1: Shallow proof (should find quickly)
#eval search [] ((Formula.atom "p").imp (Formula.atom "p")) (.IDDFS 10)
-- Expected: (true, _, _, _, visits < 100)

-- Example 2: Deep proof (should find beyond bounded DFS limit)
#eval search [] complexModalTheorem (.IDDFS 50)
-- Expected: (true, _, _, _, visits > 1000)

-- Example 3: Unsatisfiable (should fail gracefully)
#eval search [] (Formula.atom "p".and (Formula.atom "p").neg) (.IDDFS 100)
-- Expected: (false, _, _, _, _)
```

### Documentation Review

**Checklist**:
- [PASS] Module docstring updated with IDDFS description
- [PASS] Function docstrings complete and accurate
- [PASS] Complexity analysis documented
- [PASS] Completeness and optimality guarantees documented
- [PASS] Usage examples provided
- [PASS] References to research papers included

---

## Artifacts

### Lean Source Files

1. **Logos/Core/Automation/ProofSearch.lean** (modified)
   - Add `iddfs_search` function (~50 lines)
   - Add `SearchStrategy` enum (~10 lines)
   - Add `search` function (~20 lines)
   - Update module docstring (~50 lines)
   - Total: ~130 lines added

### Test Files

2. **LogosTest/Core/Automation/ProofSearchTest.lean** (modified)
   - Add IDDFS test cases (~150 lines)

### Documentation

3. **.opencode/specs/317_bfs_variant_phase3/benchmarks/iddfs-vs-dfs.md** (new)
   - Benchmark results and analysis (~200 lines)

4. **.opencode/specs/317_bfs_variant_phase3/summaries/implementation-summary-YYYYMMDD.md** (new)
   - Implementation summary with results (~100 lines)

---

## Rollback

### Git Commit Strategy

**Incremental Commits**:
1. **Phase 1**: `git commit -m "task 317: add iddfs_search function"`
2. **Phase 2**: `git commit -m "task 317: add SearchStrategy enum and unified search interface"`
3. **Phase 3**: `git commit -m "task 317: update documentation with IDDFS description"`
4. **Phase 4**: `git commit -m "task 317: add IDDFS tests"`
5. **Phase 5**: `git commit -m "task 317: add IDDFS benchmarks and performance analysis"`

**Final Commit**: `git commit -m "task 317: complete BFS variant (IDDFS) implementation"`

### Revert Procedure

**If IDDFS implementation blocked**:
1. Identify blocking issue (termination proof, type error, performance)
2. Revert to last working commit: `git revert <commit-hash>`
3. Document blocker in task notes
4. Consider alternative approaches:
   - Mark `iddfs_search` as `partial` (skip termination proof)
   - Reduce maxDepth default (100 → 50)
   - Simplify iteration logic (remove cache propagation)

**If tests fail**:
1. Identify failing test case
2. Debug with `#eval` and `#check`
3. Fix implementation or adjust test expectations
4. Re-run tests until all pass

**If performance unacceptable**:
1. Profile with SearchStats (visits, cache hits/misses)
2. Identify bottleneck (iteration overhead, cache misses)
3. Optimize hot path (cache propagation, visit limit checks)
4. Re-benchmark and document results

### Alternative Approaches

**If IDDFS fails**:

1. **Pure BFS with Queue** (fallback option)
   - Implement queue-based BFS with Batteries.Data.Queue
   - Guarantees completeness and optimality
   - Higher space complexity O(b^d) but simpler implementation
   - Estimated effort: 4-6 hours

2. **Best-First Search** (advanced option)
   - Implement priority queue-based search with BinomialHeap
   - Requires heuristic design (formula complexity, modal depth)
   - Better performance but more complex
   - Estimated effort: 8-12 hours (defer to Phase 4)

3. **Bounded IDDFS** (compromise option)
   - Limit IDDFS to maxDepth=20 (reduce overhead)
   - Still provides completeness within bound
   - Simpler than pure BFS, more complete than bounded DFS
   - Estimated effort: Same as IDDFS (no code changes)

---

## Dependencies

### Task Dependencies

- **Task 260**: ProofSearch.lean infrastructure (COMPLETED)
  - `bounded_search` function implemented
  - `ProofCache` and `Visited` types defined
  - `HeuristicWeights` infrastructure in place
  - `SearchStats` tracking implemented

### File Dependencies

- **Logos/Core/Automation/ProofSearch.lean**: Existing implementation
- **Logos/Core/Syntax/Formula.lean**: Formula type definition
- **Logos/Core/Syntax/Context.lean**: Context type definition
- **Std.Data.HashMap**: ProofCache implementation
- **Std.Data.HashSet**: Visited set implementation

### No Blocking Issues

- No Prop vs Type blocker (IDDFS works with Bool return type)
- No mathlib version conflicts (uses Std only)
- No circular dependencies (ProofSearch is leaf module)

---

## Risk Assessment

### Technical Risks

1. **Termination Proof Complexity** (Medium Risk)
   - **Risk**: Nested recursion may complicate termination proof
   - **Mitigation**: Use `termination_by depth` or mark as `partial`
   - **Fallback**: Simplify iteration logic (remove cache propagation)

2. **Performance Overhead** (Low Risk)
   - **Risk**: IDDFS may have >20% overhead vs bounded DFS
   - **Mitigation**: Research shows ~11% overhead for b=10
   - **Fallback**: Reduce maxDepth default or add early termination heuristics

3. **Visit Limit Tuning** (Low Risk)
   - **Risk**: Default visitLimit=10000 may be too low/high
   - **Mitigation**: Benchmark and adjust based on results
   - **Fallback**: Expose visitLimit parameter for user tuning

### Schedule Risks

1. **Testing Complexity** (Medium Risk)
   - **Risk**: Deep proof tests may be slow or flaky
   - **Mitigation**: Use smaller maxDepth for tests (10-20)
   - **Fallback**: Mark slow tests as `#slow` or skip in CI

2. **Benchmark Time** (Low Risk)
   - **Risk**: Benchmarking may take longer than estimated
   - **Mitigation**: Automate benchmark suite with scripts
   - **Fallback**: Defer detailed benchmarking to Phase 5 of task 260

### Mitigation Strategies

- **Incremental commits**: Commit after each phase for easy rollback
- **Early testing**: Test `iddfs_search` immediately after Phase 1
- **Performance monitoring**: Track SearchStats throughout development
- **Documentation-first**: Write docstrings before implementation

---

## Success Metrics

### Functional Metrics

- [PASS] IDDFS finds all proofs that bounded DFS finds (completeness)
- [PASS] IDDFS finds proofs beyond bounded DFS depth limit (extended completeness)
- [PASS] IDDFS returns shortest proofs (optimality)
- [PASS] All tests pass (correctness)
- [PASS] No regressions in existing functionality (backward compatibility)

### Performance Metrics

- [PASS] IDDFS overhead ≤20% vs bounded DFS for shallow proofs (efficiency)
- [PASS] IDDFS space complexity O(d) verified (memory safety)
- [PASS] Visit limit enforcement prevents infinite loops (safety)
- [PASS] maxDepth=100 is sufficient for modal logic proofs (usability)

### Quality Metrics

- [PASS] Module builds successfully with `lake build` (build quality)
- [PASS] Documentation complete and accurate (documentation quality)
- [PASS] Code follows Lean 4 style guide (code quality)
- [PASS] Test coverage ≥80% for new code (test quality)

---

## Notes

### Research Integration

This plan integrates findings from research-001.md (1403 lines):
- **IDDFS algorithm**: Recommended as optimal solution (Section 2)
- **Complexity analysis**: O(b^d) time, O(d) space (Section 2)
- **Implementation strategy**: Wrap bounded_search with iteration (Section 5)
- **Benchmark approach**: Compare IDDFS vs bounded DFS (Section 6)
- **Future enhancements**: Best-First Search, Beam Search (Section 7)

### Lean-Specific Considerations

- **No Prop → Type refactor**: IDDFS works with existing Bool return type
- **Termination proofs**: Use `termination_by depth` for well-founded recursion
- **Space safety**: No stack overflow risk (bounded by maxDepth)
- **Heuristic compatibility**: Preserves existing HeuristicWeights infrastructure
- **Backward compatibility**: `bounded_search` API unchanged

### Future Work

**Phase 4 Candidates** (Post-Task 317):
1. **Best-First Search**: Priority queue-based search with heuristics (8-12 hours)
2. **Beam Search**: Memory-bounded variant of best-first search (3-5 hours)
3. **Bidirectional Search**: Forward + backward search with meeting point (8-10 hours)
4. **Proof Term Construction**: Return actual Derivation instead of Bool (blocked by Prop vs Type)

**Integration Opportunities**:
- **Task 318**: Advanced heuristics can enhance IDDFS performance
- **Task 319**: Expanded testing can validate IDDFS completeness
- **Task 315**: Proof term construction can replace Bool return type

---

## Appendix: Code Snippets

### IDDFS Implementation (Phase 1)

```lean
/--
Iterative deepening depth-first search for a derivation of `φ` from context `Γ`.

Runs bounded_search with increasing depth limits until proof found or maxDepth reached.
Guarantees finding shortest proof (minimum depth) if it exists.

**Parameters**:
- `Γ`: Proof context (list of assumptions)
- `φ`: Goal formula to derive
- `maxDepth`: Maximum search depth (prevents infinite loops)
- `visitLimit`: Maximum total visits across all depths
- `weights`: Heuristic weights to rank branch ordering

**Returns**: `(found, cache, visited, stats, totalVisits)` where:
- `found`: true if derivation found within maxDepth
- `cache`: Updated proof cache
- `visited`: Visited set from final depth iteration
- `stats`: Cumulative search statistics
- `totalVisits`: Total visits across all depth iterations

**Complexity**: O(b^d) time, O(d) space where b = branching factor, d = solution depth

**Completeness**: Guaranteed to find proof if it exists within maxDepth

**Optimality**: Guaranteed to find shortest proof (minimum depth)
-/
def iddfs_search (Γ : Context) (φ : Formula) (maxDepth : Nat := 100)
    (visitLimit : Nat := 10000) (weights : HeuristicWeights := {})
    : Bool × ProofCache × Visited × SearchStats × Nat :=
  let rec iterate (depth : Nat) (cache : ProofCache) (stats : SearchStats) 
                  (totalVisits : Nat) : Bool × ProofCache × Visited × SearchStats × Nat :=
    if depth > maxDepth then
      (false, cache, Visited.empty, stats, totalVisits)
    else
      let (found, cache', visited', stats', visits') :=
        bounded_search Γ φ depth cache Visited.empty totalVisits visitLimit weights stats
      
      if found then
        (true, cache', visited', stats', visits')
      else if visits' ≥ visitLimit then
        (false, cache', visited', stats', visits')
      else
        iterate (depth + 1) cache' stats' visits'
  
  iterate 0 ProofCache.empty {} 0
termination_by maxDepth - depth
```

### SearchStrategy Enum (Phase 2)

```lean
/--
Search strategy configuration.

**Variants**:
- `BoundedDFS depth`: Depth-limited DFS (may miss proofs beyond depth)
- `IDDFS maxDepth`: Iterative deepening DFS (complete and optimal)
- `BestFirst maxDepth`: Best-first search with heuristics (future enhancement)
-/
inductive SearchStrategy where
  | BoundedDFS (depth : Nat)
  | IDDFS (maxDepth : Nat)
  | BestFirst (maxDepth : Nat)  -- Future enhancement
  deriving Repr

/--
Unified search interface with configurable strategy.

**Default**: IDDFS with maxDepth=100 (complete and optimal)

**Parameters**:
- `Γ`: Proof context
- `φ`: Goal formula
- `strategy`: Search algorithm to use
- `visitLimit`: Maximum total visits
- `weights`: Heuristic weights

**Returns**: Same as bounded_search and iddfs_search
-/
def search (Γ : Context) (φ : Formula) 
    (strategy : SearchStrategy := .IDDFS 100)
    (visitLimit : Nat := 10000) 
    (weights : HeuristicWeights := {})
    : Bool × ProofCache × Visited × SearchStats × Nat :=
  match strategy with
  | .BoundedDFS depth => 
      bounded_search Γ φ depth ProofCache.empty Visited.empty 0 visitLimit weights {}
  | .IDDFS maxDepth => 
      iddfs_search Γ φ maxDepth visitLimit weights
  | .BestFirst _ => 
      -- TODO: Implement best-first search (Phase 4 of task 260)
      sorry
```

### Test Cases (Phase 4)

```lean
-- Test 1: Shallow proof (depth 2)
example : let (found, _, _, _, _) := 
  search [] ((Formula.atom "p").imp (Formula.atom "p")) (.IDDFS 10)
  found = true := by
  simp [search, iddfs_search, bounded_search]
  sorry  -- Proof construction

-- Test 2: Deep proof beyond bounded DFS limit
example : let (found, _, _, _, _) := 
  search [] complexModalTheorem (.IDDFS 50)
  found = true := by
  simp [search, iddfs_search]
  sorry  -- Proof construction

-- Test 3: Shortest proof guarantee
example : let (found, _, _, stats, _) := 
  search [] ((Formula.atom "p").imp (Formula.atom "p")) (.IDDFS 10)
  found = true ∧ stats.visited < 10 := by
  simp [search, iddfs_search]
  sorry  -- Proof construction
```

---

**End of Implementation Plan**
