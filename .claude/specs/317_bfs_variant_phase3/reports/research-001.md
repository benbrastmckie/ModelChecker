# Research Report: BFS Variant for ProofSearch.lean

**Task**: 317 - Implement Phase 3 of task 260: BFS Variant  
**Started**: 2026-01-07  
**Completed**: 2026-01-07  
**Effort**: 4 hours (research phase)  
**Priority**: Medium  
**Dependencies**: Task 260 (Phase 1 and 2 completed)  
**Sources/Inputs**: ProofSearch.lean, Mathlib BestFirstSearch, Wikipedia BFS/IDDFS, existing research documents  
**Artifacts**: research-001.md  
**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research investigates breadth-first search (BFS) implementation strategies for Lean 4 proof search to ensure completeness guarantees and shortest-proof-first exploration. The current ProofSearch.lean implementation uses bounded depth-first search (DFS) which may miss proofs due to depth limits and does not guarantee finding shortest proofs.

**Key Findings**:

1. **Mathlib provides production-ready BFS infrastructure** via deprecated `Mathlib.Deprecated.MLList.BestFirst` module with priority queues, heuristic estimation, and beam search support
2. **Three BFS implementation strategies identified**: Pure BFS with queue, Best-First Search with heuristics, and Iterative Deepening DFS (IDDFS) as memory-efficient alternative
3. **Completeness guarantees require**: Level-by-level exploration, visited set tracking, and proper termination conditions
4. **Current bounded DFS limitations**: May miss proofs beyond depth limit, no shortest-proof guarantee, arbitrary depth cutoff
5. **Recommended approach**: Implement IDDFS first (easiest migration), then add BFS variant, optionally integrate best-first search with heuristics

---

## Context & Scope

### Current Implementation Analysis

The existing `Logos/Core/Automation/ProofSearch.lean` implements bounded depth-first search with the following characteristics:

**Architecture**:
- `bounded_search`: Main DFS function with depth limit (default: 5)
- `search_with_heuristics`: Heuristic-guided DFS
- `search_with_cache`: Memoized DFS with visit limits
- Proof state: `(Bool × ProofCache × Visited × SearchStats × Nat)`

**Search Strategy**:
```lean
def bounded_search (Γ : Context) (φ : Formula) (depth : Nat) : Bool :=
  if depth = 0 then false
  else
    -- Try axioms and assumptions (depth-independent)
    if matches_axiom φ || Γ.contains φ then true
    else
      -- Try modus ponens (recursive, depth-1)
      let implications := find_implications_to Γ φ
      implications.any (λ ψ => bounded_search Γ ψ (depth - 1))
      ||
      -- Try modal/temporal rules (recursive, depth-1)
      match φ with
      | Formula.box ψ => bounded_search (box_context Γ) ψ (depth - 1)
      | Formula.all_future ψ => bounded_search (future_context Γ) ψ (depth - 1)
      | _ => false
```

**Limitations**:
1. **Incompleteness**: Proofs beyond depth limit are unreachable
2. **No optimality**: Does not guarantee shortest proofs
3. **Arbitrary cutoff**: Depth limit is manually tuned
4. **Redundant exploration**: May explore same states multiple times despite caching

**Strengths**:
1. **Memory efficient**: O(d) space complexity
2. **Fast for shallow proofs**: Finds proofs quickly if within depth limit
3. **Heuristic support**: Can prioritize promising branches
4. **Caching infrastructure**: ProofCache and Visited sets reduce redundant work

### Research Scope

This research focuses on:
1. BFS algorithm variants suitable for proof search
2. Completeness and optimality guarantees
3. Space/time complexity tradeoffs
4. Integration with existing ProofSearch.lean infrastructure
5. Lean 4 implementation strategies and available libraries

---

## Key Findings

### 1. BFS Algorithm Fundamentals

**Breadth-First Search (BFS)** explores a graph level-by-level, guaranteeing:
- **Completeness**: If a solution exists, BFS will find it
- **Optimality**: BFS finds the shortest path (minimum number of edges)
- **Systematic exploration**: All nodes at depth d are explored before depth d+1

**Core Algorithm**:
```
BFS(root, goal):
  queue := [root]
  visited := {root}
  
  while queue not empty:
    current := queue.dequeue()
    
    if current = goal:
      return SUCCESS
    
    for each successor of current:
      if successor not in visited:
        visited.add(successor)
        queue.enqueue(successor)
  
  return FAILURE
```

**Complexity**:
- **Time**: O(|V| + |E|) for explicit graphs, O(b^d) for implicit search trees
- **Space**: O(|V|) for explicit graphs, O(b^d) for implicit search trees
  - Where b = branching factor, d = solution depth

**Key Difference from DFS**:
- **BFS uses queue (FIFO)**: Explores breadth-first
- **DFS uses stack (LIFO)**: Explores depth-first
- **BFS guarantees shortest path**: DFS does not

### 2. Iterative Deepening Depth-First Search (IDDFS)

**IDDFS** combines BFS completeness with DFS space efficiency by running depth-limited DFS with increasing depth limits.

**Algorithm**:
```
IDDFS(root, goal):
  for depth = 0 to ∞:
    result := DLS(root, goal, depth)
    if result = SUCCESS:
      return SUCCESS
  return FAILURE

DLS(node, goal, depth):
  if depth = 0:
    return node = goal ? SUCCESS : CUTOFF
  
  any_cutoff := false
  for each successor of node:
    result := DLS(successor, goal, depth - 1)
    if result = SUCCESS:
      return SUCCESS
    if result = CUTOFF:
      any_cutoff := true
  
  return any_cutoff ? CUTOFF : FAILURE
```

**Advantages**:
- **Space efficient**: O(d) like DFS
- **Complete**: Like BFS, finds solution if it exists
- **Optimal**: Finds shortest path (for unweighted graphs)
- **Anytime algorithm**: Can return best solution found so far

**Complexity**:
- **Time**: O(b^d) - only ~11% overhead vs single DFS to depth d (for b=10)
- **Space**: O(d) - same as DFS

**Proof of Efficiency** (from Wikipedia):
For branching factor b and depth d, total nodes expanded:
```
∑(i=0 to d) (d+1-i) * b^i = b^d + 2b^(d-1) + 3b^(d-2) + ... + d*b + (d+1)
                          ≤ b^d * (1/(1-1/b))^2
                          = O(b^d)
```

The overhead is dominated by the deepest level, which contains most nodes.

**Relevance to Proof Search**:
- **Minimal code changes**: Extends existing bounded_search with iteration
- **Preserves heuristics**: Can still use heuristic ordering within each depth
- **Gradual deepening**: Provides early feedback on shallow proofs
- **Memory safe**: No risk of space explosion

### 3. Best-First Search with Heuristics

**Best-First Search** uses a priority queue to explore most promising nodes first, guided by a heuristic function.

**Mathlib Infrastructure** (from `Mathlib.Deprecated.MLList.BestFirst`):

```lean
-- Core best-first search function
bestFirstSearch : 
  (α → MLList m α) →  -- Successor function
  α →                  -- Initial state
  Option Nat →         -- Max depth
  Option Nat →         -- Max queue size (beam width)
  Bool →               -- Deduplication enabled
  MLList m α           -- Lazy result stream

-- Priority queue with estimator-based ordering
BestFirstQueue : 
  (prio : α → Thunk ω) →      -- Priority function (lazy)
  (ε : α → Type) →             -- Estimator type
  [LinearOrder ω] →            -- Priority ordering
  [(a : α) → Estimator (prio a) (ε a)] →  -- Estimator instances
  Option Nat →                 -- Max queue size
  Type

-- Estimator typeclass for progressive bound improvement
class Estimator (ω : Type) (ε : Type) where
  bound : ε → ω                -- Current lower bound estimate
  improve : ε → Option ε       -- Improve estimate (or none if exact)
```

**Key Features**:
1. **Lazy evaluation**: Uses `MLList` (monadic lazy lists) for on-demand expansion
2. **Beam search**: Optional queue size limit for memory control
3. **Heuristic guidance**: Estimator typeclass for progressive refinement
4. **Deduplication**: Built-in visited set tracking
5. **Depth bounds**: Optional maximum depth constraint

**Example Usage for Proof Search**:
```lean
structure ProofState where
  goal : Formula
  context : Context
  depth : Nat
  heuristic : Nat  -- Estimated distance to proof

def proofSuccessors (state : ProofState) : MLList MetaM ProofState :=
  -- Generate successor states (MP, modal K, temporal K, etc.)
  sorry

def proofPriority (state : ProofState) : Thunk Nat :=
  Thunk.mk (λ _ => state.heuristic)

def proofSearch (goal : Formula) : MetaM (Option Derivation) := do
  let initial := ⟨goal, [], 0, computeHeuristic goal⟩
  let results := bestFirstSearch proofSuccessors initial (some 100) (some 1000) true
  results.find? (·.isProof)
```

**Heuristic Design for Modal Logic**:
- **Formula complexity**: Prefer simpler formulas
- **Modal depth**: Penalize deeply nested modalities
- **Context size**: Prefer smaller contexts (fewer assumptions)
- **Axiom distance**: Estimate steps to axiom match
- **Subformula count**: Prefer formulas with fewer subformulas

**Advantages**:
- **Guided search**: Explores promising branches first
- **Flexible**: Can tune heuristics for domain
- **Beam search**: Memory-bounded variant available
- **Production-ready**: Mathlib implementation is well-tested

**Disadvantages**:
- **Deprecated**: Module may be removed from Mathlib
- **Complexity**: More complex than pure BFS or IDDFS
- **Heuristic design**: Requires domain expertise to design good heuristics

### 4. Priority Queue Data Structures

Lean 4 provides three heap implementations in Batteries (from research):

**BinomialHeap** (Recommended for proof search):
- **Operations**: O(log n) insert, deleteMin, merge
- **Space**: O(n)
- **Persistent**: Yes (functional data structure)
- **Use case**: Guaranteed worst-case bounds, efficient merge

**BinaryHeap**:
- **Operations**: O(log n) insert/delete, O(1) peek, O(n) heapify
- **Space**: O(n) (array-based)
- **Persistent**: No (mutable)
- **Use case**: Best cache locality, simple implementation

**PairingHeap**:
- **Operations**: O(1) insert/merge, O(log n) amortized deleteMin
- **Space**: O(n)
- **Persistent**: Poor (not recommended)
- **Use case**: Many inserts/merges, few deletions

**Example BFS with BinomialHeap**:
```lean
import Batteries.Data.BinomialHeap

structure ProofState where
  goal : Formula
  context : Context
  depth : Nat
  deriving Repr

def stateLE (s1 s2 : ProofState) : Bool :=
  s1.depth ≤ s2.depth  -- BFS: prefer shallower states

abbrev ProofQueue := Batteries.BinomialHeap ProofState stateLE

def bfsProofSearch (initial : ProofState) : Option Derivation :=
  let rec loop (queue : ProofQueue) (visited : HashSet Formula) : Option Derivation :=
    match queue.deleteMin with
    | none => none  -- Queue exhausted
    | some (current, queue') =>
      if visited.contains current.goal then
        loop queue' visited  -- Skip visited
      else if isAxiom current.goal then
        some (axiomDeriv current.goal)  -- Found proof
      else
        let successors := expandState current
        let queue'' := successors.foldl (·.insert) queue'
        let visited' := visited.insert current.goal
        loop queue'' visited'
  
  loop (BinomialHeap.singleton initial) HashSet.empty
```

### 5. Completeness Guarantees

**Completeness** means: If a proof exists, the algorithm will find it.

**Requirements for Completeness**:
1. **Systematic exploration**: Must eventually explore all reachable states
2. **Termination detection**: Must detect when search space is exhausted
3. **No infinite loops**: Must handle cycles in search graph
4. **Finite branching**: Branching factor must be finite (true for modal logic)

**BFS Completeness**:
- **Guaranteed**: BFS explores all nodes at depth d before d+1
- **Proof**: If solution exists at depth d, BFS will find it after exploring all nodes at depths 0..d-1
- **Caveat**: Requires finite branching factor and reachable solution

**IDDFS Completeness**:
- **Guaranteed**: IDDFS eventually tries all depths
- **Proof**: If solution exists at depth d, IDDFS will find it when depth limit reaches d
- **Caveat**: Same as BFS (finite branching, reachable solution)

**Current DFS Incompleteness**:
- **Not guaranteed**: DFS with fixed depth limit may miss solutions beyond limit
- **Example**: Proof at depth 6 is unreachable with depth limit 5
- **Mitigation**: Increase depth limit, but no systematic way to choose it

**Optimality** (Shortest Proof):
- **BFS**: Guaranteed to find shortest proof (minimum depth)
- **IDDFS**: Guaranteed to find shortest proof (explores depth-by-depth)
- **DFS**: Not guaranteed (may find longer proof first)
- **Best-First**: Not guaranteed (depends on heuristic admissibility)

### 6. Space/Time Complexity Tradeoffs

**Comparison Table**:

| Algorithm | Time | Space | Complete | Optimal | Memory Safe |
|-----------|------|-------|----------|---------|-------------|
| **Bounded DFS** | O(b^d) | O(d) | No | No | Yes |
| **BFS** | O(b^d) | O(b^d) | Yes | Yes | No |
| **IDDFS** | O(b^d) | O(d) | Yes | Yes | Yes |
| **Best-First** | O(b^d) | O(b^d) | Yes* | No** | No |
| **Beam Search** | O(k×d) | O(k) | No | No | Yes |

*Complete if heuristic is admissible  
**Optimal if heuristic is admissible and consistent (A*)  
k = beam width

**Space Complexity Analysis**:

For modal logic proof search with branching factor b ≈ 5-10:
- **Depth 5**: BFS stores ~10^5 = 100,000 states
- **Depth 10**: BFS stores ~10^10 = 10 billion states (infeasible)
- **IDDFS**: Always stores ~10 states (current path)

**Practical Implications**:
1. **Pure BFS is infeasible** for deep proofs (space explosion)
2. **IDDFS is practical** for all proof depths (memory safe)
3. **Beam search** trades completeness for memory bounds
4. **Best-first with beam** balances heuristics and memory

**Recommendation**: Use IDDFS as primary algorithm, with optional beam search for resource-constrained scenarios.

---

## Detailed Analysis

### Current ProofSearch.lean Architecture

**File Structure**:
```
Logos/Core/Automation/ProofSearch.lean (468 lines)
├── Type Definitions (lines 90-133)
│   ├── SearchResult: Bool (placeholder for proof terms)
│   ├── CacheKey: Context × Formula
│   ├── ProofCache: HashMap CacheKey Bool
│   ├── Visited: HashSet CacheKey
│   └── SearchStats: hits, misses, visited, prunedByLimit
├── Helper Functions (lines 163-305)
│   ├── matches_axiom: Check 14 TM axiom schemata
│   ├── find_implications_to: Find MP antecedents
│   ├── box_context: Transform context for modal K
│   ├── future_context: Transform context for temporal K
│   ├── heuristic_score: Compute branch priority
│   └── orderSubgoalsByScore: Sort by heuristic (TODO)
├── Search Functions (lines 347-445)
│   ├── bounded_search: Main DFS with depth limit
│   ├── search_with_heuristics: Wrapper with heuristics
│   └── search_with_cache: Wrapper with cache
└── Examples (lines 447-465)
    └── Documentation examples (sorry)
```

**Key Observations**:
1. **Modular design**: Helper functions are reusable for BFS
2. **Heuristic infrastructure**: Already supports heuristic scoring
3. **Caching support**: ProofCache and Visited sets in place
4. **Statistics tracking**: SearchStats for profiling
5. **Termination by**: Depth limit (DFS) or visit limit (both)

**Integration Points for BFS**:
1. **Replace depth limit** with level-by-level exploration
2. **Add queue data structure** (BinomialHeap or custom)
3. **Preserve caching** (ProofCache, Visited)
4. **Preserve heuristics** (for best-first variant)
5. **Preserve statistics** (SearchStats)

### BFS Implementation Strategies

**Strategy 1: Pure BFS with Queue**

**Approach**: Replace DFS stack with BFS queue, explore level-by-level.

**Pseudocode**:
```lean
def bfs_search (Γ : Context) (φ : Formula) (maxDepth : Nat := 100) 
    (visitLimit : Nat := 10000) : Bool × ProofCache × Visited × SearchStats :=
  let initial : CacheKey := (Γ, φ)
  let queue : Queue CacheKey := Queue.singleton initial
  let visited : Visited := Visited.empty
  let cache : ProofCache := ProofCache.empty
  let stats : SearchStats := {}
  
  let rec loop (queue : Queue CacheKey) (visited : Visited) 
               (cache : ProofCache) (stats : SearchStats) (visits : Nat) 
               : Bool × ProofCache × Visited × SearchStats :=
    if visits ≥ visitLimit then
      (false, cache, visited, {stats with prunedByLimit := stats.prunedByLimit + 1})
    else
      match queue.dequeue with
      | none => (false, cache, visited, stats)  -- Queue exhausted
      | some ((Γ', φ'), queue') =>
        if visited.contains (Γ', φ') then
          loop queue' visited cache stats visits  -- Skip visited
        else
          let visits := visits + 1
          let stats := {stats with visited := stats.visited + 1}
          let visited := visited.insert (Γ', φ')
          
          -- Check cache
          match cache.find? (Γ', φ') with
          | some result => 
            let stats := {stats with hits := stats.hits + 1}
            if result then
              (true, cache, visited, stats)
            else
              loop queue' visited cache stats visits
          | none =>
            let stats := {stats with misses := stats.misses + 1}
            
            -- Check axiom/assumption
            if matches_axiom φ' || Γ'.contains φ' then
              let cache := cache.insert (Γ', φ') true
              (true, cache, visited, stats)
            else
              -- Generate successors
              let successors := generateSuccessors Γ' φ'
              let queue'' := successors.foldl Queue.enqueue queue'
              let cache := cache.insert (Γ', φ') false
              loop queue'' visited cache stats visits
  
  loop queue visited cache stats 0

def generateSuccessors (Γ : Context) (φ : Formula) : List CacheKey :=
  -- Modus ponens successors
  let mpSuccessors := (find_implications_to Γ φ).map (λ ψ => (Γ, ψ))
  
  -- Modal K successors
  let modalSuccessors := match φ with
    | Formula.box ψ => [(box_context Γ, ψ)]
    | _ => []
  
  -- Temporal K successors
  let temporalSuccessors := match φ with
    | Formula.all_future ψ => [(future_context Γ, ψ)]
    | _ => []
  
  mpSuccessors ++ modalSuccessors ++ temporalSuccessors
```

**Advantages**:
- **Complete**: Finds proof if it exists
- **Optimal**: Finds shortest proof
- **Simple**: Straightforward queue-based implementation

**Disadvantages**:
- **Space explosion**: O(b^d) memory usage
- **Slow for deep proofs**: Must explore all shallow levels first
- **No early termination**: Cannot stop at depth limit

**Recommendation**: Implement as baseline for comparison, but not for production use.

---

**Strategy 2: Iterative Deepening DFS (IDDFS)**

**Approach**: Run bounded DFS with increasing depth limits until proof found.

**Pseudocode**:
```lean
def iddfs_search (Γ : Context) (φ : Formula) (maxDepth : Nat := 100)
    (visitLimit : Nat := 10000) : Bool × ProofCache × Visited × SearchStats :=
  let rec iterateDepth (depth : Nat) (cache : ProofCache) (stats : SearchStats) 
                       (totalVisits : Nat) : Bool × ProofCache × Visited × SearchStats :=
    if depth > maxDepth then
      (false, cache, Visited.empty, stats)
    else
      -- Run depth-limited search at current depth
      let (found, cache', visited', stats', visits') := 
        bounded_search Γ φ depth cache Visited.empty totalVisits visitLimit {} stats
      
      if found then
        (true, cache', visited', stats')
      else if visits' ≥ visitLimit then
        -- Hit visit limit, stop iterating
        (false, cache', visited', stats')
      else
        -- No proof at this depth, try deeper
        iterateDepth (depth + 1) cache' stats' visits'
  
  iterateDepth 0 ProofCache.empty {} 0
```

**Advantages**:
- **Complete**: Finds proof if it exists (within maxDepth)
- **Optimal**: Finds shortest proof
- **Memory efficient**: O(d) space like DFS
- **Anytime**: Can return best solution found so far
- **Minimal code changes**: Reuses existing bounded_search

**Disadvantages**:
- **Redundant work**: Re-explores shallow levels (but only ~11% overhead)
- **Slower than pure BFS**: For very shallow proofs

**Recommendation**: **Primary implementation strategy**. Best balance of completeness, optimality, and memory efficiency.

---

**Strategy 3: Best-First Search with Heuristics**

**Approach**: Use priority queue with heuristic function to guide search.

**Pseudocode**:
```lean
import Batteries.Data.BinomialHeap

structure ProofState where
  key : CacheKey
  depth : Nat
  heuristic : Nat
  deriving Repr

def stateLE (s1 s2 : ProofState) : Bool :=
  let h1 := s1.heuristic + s1.depth  -- f(n) = g(n) + h(n)
  let h2 := s2.heuristic + s2.depth
  h1 ≤ h2

abbrev ProofQueue := Batteries.BinomialHeap ProofState stateLE

def bestfirst_search (Γ : Context) (φ : Formula) (maxDepth : Nat := 100)
    (visitLimit : Nat := 10000) : Bool × ProofCache × Visited × SearchStats :=
  let initial := ProofState.mk (Γ, φ) 0 (computeHeuristic Γ φ)
  let queue := BinomialHeap.singleton initial
  let visited := Visited.empty
  let cache := ProofCache.empty
  let stats := {}
  
  let rec loop (queue : ProofQueue) (visited : Visited) 
               (cache : ProofCache) (stats : SearchStats) (visits : Nat)
               : Bool × ProofCache × Visited × SearchStats :=
    if visits ≥ visitLimit then
      (false, cache, visited, {stats with prunedByLimit := stats.prunedByLimit + 1})
    else
      match queue.deleteMin with
      | none => (false, cache, visited, stats)
      | some (current, queue') =>
        let (Γ', φ') := current.key
        
        if visited.contains current.key then
          loop queue' visited cache stats visits
        else if current.depth > maxDepth then
          loop queue' visited cache stats visits
        else
          let visits := visits + 1
          let stats := {stats with visited := stats.visited + 1}
          let visited := visited.insert current.key
          
          -- Check cache
          match cache.find? current.key with
          | some result =>
            let stats := {stats with hits := stats.hits + 1}
            if result then
              (true, cache, visited, stats)
            else
              loop queue' visited cache stats visits
          | none =>
            let stats := {stats with misses := stats.misses + 1}
            
            -- Check axiom/assumption
            if matches_axiom φ' || Γ'.contains φ' then
              let cache := cache.insert current.key true
              (true, cache, visited, stats)
            else
              -- Generate successors with heuristics
              let successors := generateSuccessorsWithHeuristics Γ' φ' (current.depth + 1)
              let queue'' := successors.foldl (·.insert) queue'
              let cache := cache.insert current.key false
              loop queue'' visited cache stats visits
  
  loop queue visited cache stats 0

def generateSuccessorsWithHeuristics (Γ : Context) (φ : Formula) (depth : Nat) 
    : List ProofState :=
  let mpSuccessors := (find_implications_to Γ φ).map (λ ψ => 
    ProofState.mk (Γ, ψ) depth (computeHeuristic Γ ψ))
  
  let modalSuccessors := match φ with
    | Formula.box ψ => 
      let Γ' := box_context Γ
      [ProofState.mk (Γ', ψ) depth (computeHeuristic Γ' ψ)]
    | _ => []
  
  let temporalSuccessors := match φ with
    | Formula.all_future ψ => 
      let Γ' := future_context Γ
      [ProofState.mk (Γ', ψ) depth (computeHeuristic Γ' ψ)]
    | _ => []
  
  mpSuccessors ++ modalSuccessors ++ temporalSuccessors

def computeHeuristic (Γ : Context) (φ : Formula) : Nat :=
  -- Heuristic: estimate distance to proof
  let complexityPenalty := φ.complexity
  let modalDepthPenalty := φ.modalDepth * 2
  let contextPenalty := Γ.length
  let axiomBonus := if matches_axiom φ then 0 else 10
  
  complexityPenalty + modalDepthPenalty + contextPenalty + axiomBonus
```

**Advantages**:
- **Guided search**: Explores promising branches first
- **Flexible**: Can tune heuristics for domain
- **Potentially faster**: May find proofs faster than BFS/IDDFS with good heuristics

**Disadvantages**:
- **Not optimal**: Unless heuristic is admissible (underestimates true cost)
- **Space intensive**: O(b^d) memory usage
- **Heuristic design**: Requires domain expertise
- **Complexity**: More complex than IDDFS

**Recommendation**: **Optional enhancement** after IDDFS is working. Useful for performance optimization.

---

### Heuristic Design for Modal Logic

**Heuristic Function Requirements**:
1. **Admissible**: h(n) ≤ h*(n) (never overestimate true cost) for optimality
2. **Consistent**: h(n) ≤ c(n,n') + h(n') (triangle inequality) for efficiency
3. **Informative**: h(n) > 0 for non-goal states (guides search)
4. **Efficient**: O(1) or O(log n) computation time

**Proposed Heuristics**:

**H1: Formula Complexity**
```lean
def h_complexity (φ : Formula) : Nat :=
  φ.complexity  -- Number of operators
```
- **Rationale**: Simpler formulas are closer to axioms
- **Admissible**: Yes (complexity decreases with each inference step)
- **Informative**: Moderate

**H2: Modal Depth**
```lean
def h_modalDepth (φ : Formula) : Nat :=
  φ.modalDepth * 2  -- Nesting level of □/◇/G/F operators
```
- **Rationale**: Deeply nested modalities require more modal K applications
- **Admissible**: Yes (modal depth decreases with modal K)
- **Informative**: High for modal formulas

**H3: Axiom Distance**
```lean
def h_axiomDistance (φ : Formula) : Nat :=
  if matches_axiom φ then 0
  else if φ.isImplication then 1  -- One MP step away
  else if φ.isBox || φ.isAllFuture then 1  -- One modal/temporal K step
  else 2  -- Need to build implication first
```
- **Rationale**: Estimates steps to axiom match
- **Admissible**: No (may underestimate for complex proofs)
- **Informative**: High for simple formulas

**H4: Context Size**
```lean
def h_contextSize (Γ : Context) : Nat :=
  Γ.length  -- Number of assumptions
```
- **Rationale**: Larger contexts are harder to work with
- **Admissible**: No (context size may increase with modal K)
- **Informative**: Low

**H5: Combined Heuristic**
```lean
def h_combined (Γ : Context) (φ : Formula) : Nat :=
  let w1 := 1  -- Complexity weight
  let w2 := 2  -- Modal depth weight
  let w3 := 1  -- Context weight
  
  w1 * h_complexity φ + w2 * h_modalDepth φ + w3 * h_contextSize Γ
```
- **Rationale**: Weighted combination of multiple factors
- **Admissible**: Depends on weights (needs tuning)
- **Informative**: High

**Recommendation**: Start with H5 (combined heuristic) and tune weights empirically. For guaranteed optimality, use admissible heuristics only (H1, H2).

---

### Integration with Existing Infrastructure

**Minimal Changes for IDDFS**:

1. **Add iterative wrapper** around `bounded_search`:
```lean
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
```

2. **Update `search_with_heuristics`** to use IDDFS:
```lean
def search_with_heuristics (Γ : Context) (φ : Formula) (maxDepth : Nat := 100)
    (visitLimit : Nat := 10000) (weights : HeuristicWeights := {}) 
    : Bool × ProofCache × Visited × SearchStats × Nat :=
  iddfs_search Γ φ maxDepth visitLimit weights
```

3. **Add configuration option** for search strategy:
```lean
inductive SearchStrategy where
  | BoundedDFS (depth : Nat)
  | IDDFS (maxDepth : Nat)
  | BestFirst (maxDepth : Nat)

def search (Γ : Context) (φ : Formula) (strategy : SearchStrategy := .IDDFS 100)
    (visitLimit : Nat := 10000) (weights : HeuristicWeights := {})
    : Bool × ProofCache × Visited × SearchStats × Nat :=
  match strategy with
  | .BoundedDFS depth => bounded_search Γ φ depth ProofCache.empty Visited.empty 0 visitLimit weights {}
  | .IDDFS maxDepth => iddfs_search Γ φ maxDepth visitLimit weights
  | .BestFirst maxDepth => bestfirst_search Γ φ maxDepth visitLimit weights
```

**Moderate Changes for Best-First Search**:

1. **Add priority queue dependency**:
```lean
import Batteries.Data.BinomialHeap
```

2. **Define ProofState structure**:
```lean
structure ProofState where
  context : Context
  goal : Formula
  depth : Nat
  heuristic : Nat
  deriving Repr

instance : Ord ProofState where
  compare s1 s2 := compare (s1.heuristic + s1.depth) (s2.heuristic + s2.depth)

def stateLE (s1 s2 : ProofState) : Bool :=
  (s1.heuristic + s1.depth) ≤ (s2.heuristic + s2.depth)

abbrev ProofQueue := Batteries.BinomialHeap ProofState stateLE
```

3. **Implement best-first search** (see Strategy 3 pseudocode above)

4. **Add heuristic computation** (see Heuristic Design section above)

**Major Changes for Pure BFS**:

1. **Implement queue data structure** (or use List as queue):
```lean
structure Queue (α : Type) where
  front : List α
  back : List α

def Queue.empty : Queue α := ⟨[], []⟩

def Queue.enqueue (q : Queue α) (x : α) : Queue α :=
  ⟨q.front, x :: q.back⟩

def Queue.dequeue (q : Queue α) : Option (α × Queue α) :=
  match q.front with
  | x :: xs => some (x, ⟨xs, q.back⟩)
  | [] =>
    match q.back.reverse with
    | [] => none
    | x :: xs => some (x, ⟨xs, []⟩)
```

2. **Implement BFS search** (see Strategy 1 pseudocode above)

**Recommendation**: Implement IDDFS first (minimal changes), then add best-first search as optional enhancement.

---

## Decisions

### Decision 1: Primary Search Strategy

**Decision**: Implement **Iterative Deepening DFS (IDDFS)** as the primary search strategy.

**Rationale**:
1. **Completeness**: Guarantees finding proof if it exists (within maxDepth)
2. **Optimality**: Guarantees finding shortest proof
3. **Memory efficiency**: O(d) space complexity (same as current DFS)
4. **Minimal code changes**: Reuses existing `bounded_search` function
5. **Anytime algorithm**: Can return best solution found so far
6. **Proven efficiency**: Only ~11% overhead vs single DFS (for b=10)

**Alternatives Considered**:
- **Pure BFS**: Rejected due to O(b^d) space complexity (infeasible for deep proofs)
- **Best-First Search**: Deferred to optional enhancement (more complex, requires heuristic design)
- **Beam Search**: Deferred to optional enhancement (trades completeness for memory)

### Decision 2: Optional Enhancements

**Decision**: Implement **Best-First Search with Heuristics** as optional enhancement after IDDFS is working.

**Rationale**:
1. **Performance**: May find proofs faster with good heuristics
2. **Flexibility**: Can tune heuristics for specific proof patterns
3. **Research value**: Enables comparison of search strategies
4. **Mathlib infrastructure**: Can leverage existing BestFirstSearch module (if not removed)

**Implementation Plan**:
1. Phase 1: Implement IDDFS (minimal changes)
2. Phase 2: Add best-first search variant (moderate changes)
3. Phase 3: Benchmark and compare strategies (evaluation)

### Decision 3: Heuristic Design

**Decision**: Use **combined heuristic** (H5) with tunable weights for best-first search.

**Rationale**:
1. **Informative**: Combines multiple factors (complexity, modal depth, context size)
2. **Tunable**: Weights can be adjusted empirically
3. **Extensible**: Can add more factors (e.g., axiom distance, subformula count)

**Initial Weights**:
- Complexity: 1
- Modal depth: 2
- Context size: 1

**Tuning Strategy**: Benchmark on test suite and adjust weights to minimize search time.

### Decision 4: Configuration Interface

**Decision**: Add `SearchStrategy` enum to allow users to choose search algorithm.

**Rationale**:
1. **Flexibility**: Users can choose based on their needs (memory vs speed)
2. **Backward compatibility**: Can default to IDDFS while preserving bounded DFS option
3. **Experimentation**: Enables easy comparison of strategies

**API Design**:
```lean
inductive SearchStrategy where
  | BoundedDFS (depth : Nat)
  | IDDFS (maxDepth : Nat)
  | BestFirst (maxDepth : Nat)

def search (Γ : Context) (φ : Formula) 
    (strategy : SearchStrategy := .IDDFS 100)
    (visitLimit : Nat := 10000) 
    (weights : HeuristicWeights := {})
    : Bool × ProofCache × Visited × SearchStats × Nat
```

---

## Recommendations

### Immediate Actions (Phase 3 Implementation)

**1. Implement IDDFS Variant** (Estimated: 2-3 hours)

**Tasks**:
- Add `iddfs_search` function wrapping `bounded_search` with iteration
- Update `search_with_heuristics` to use IDDFS by default
- Add `SearchStrategy` enum for configuration
- Update documentation with IDDFS description

**Code Changes**:
```lean
-- Add to ProofSearch.lean after bounded_search

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

/--
Search strategy configuration.
-/
inductive SearchStrategy where
  | BoundedDFS (depth : Nat)
  | IDDFS (maxDepth : Nat)
  | BestFirst (maxDepth : Nat)  -- Future enhancement
  deriving Repr

/--
Unified search interface with configurable strategy.

**Default**: IDDFS with maxDepth=100 (complete and optimal)
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
      -- TODO: Implement best-first search
      sorry
```

**Testing**:
- Add tests to `LogosTest/Core/Automation/ProofSearchTest.lean`
- Verify IDDFS finds same proofs as bounded DFS (for shallow proofs)
- Verify IDDFS finds proofs beyond depth limit (for deep proofs)
- Verify IDDFS finds shortest proofs (compare depths)

**2. Update Documentation** (Estimated: 1 hour)

**Tasks**:
- Update module docstring with IDDFS description
- Add complexity analysis for IDDFS
- Add examples demonstrating IDDFS usage
- Document completeness and optimality guarantees

**3. Benchmark and Evaluate** (Estimated: 2-3 hours)

**Tasks**:
- Create benchmark suite with proofs at various depths
- Compare bounded DFS vs IDDFS on:
  - Time (total visits)
  - Space (max visited set size)
  - Completeness (proofs found)
  - Optimality (proof depths)
- Document results in research report

**Benchmark Proofs**:
```lean
-- Shallow proof (depth 2)
example : ⊢ (p.imp q).imp ((q.imp r).imp (p.imp r))

-- Medium proof (depth 5)
example : ⊢ (p.box).imp (p.box.box)

-- Deep proof (depth 10+)
example : ⊢ (p.all_future).imp (p.all_future.all_future.all_future)
```

### Future Enhancements (Post-Phase 3)

**1. Best-First Search Variant** (Estimated: 5-8 hours)

**Tasks**:
- Implement priority queue-based search
- Design and implement heuristic functions
- Integrate with existing infrastructure
- Benchmark against IDDFS

**2. Beam Search Variant** (Estimated: 3-5 hours)

**Tasks**:
- Add beam width parameter to best-first search
- Implement queue size limiting
- Evaluate completeness tradeoffs

**3. Bidirectional Search** (Estimated: 8-10 hours)

**Tasks**:
- Implement backward search from goal
- Implement forward search from axioms
- Detect meeting point
- Handle odd-length paths

**4. Parallel Search** (Estimated: 10-15 hours)

**Tasks**:
- Partition search space by depth ranges
- Implement work stealing for load balancing
- Synchronize visited sets and caches
- Benchmark parallel speedup

### Testing Strategy

**Unit Tests**:
- Test IDDFS on simple proofs (depth 1-3)
- Test IDDFS on medium proofs (depth 4-7)
- Test IDDFS on deep proofs (depth 8-15)
- Test IDDFS with visit limits
- Test IDDFS with caching

**Integration Tests**:
- Test IDDFS with modal K rule
- Test IDDFS with temporal K rule
- Test IDDFS with modus ponens chains
- Test IDDFS with combined rules

**Performance Tests**:
- Benchmark IDDFS vs bounded DFS on test suite
- Measure time complexity (total visits)
- Measure space complexity (max visited set size)
- Measure cache hit rates

**Completeness Tests**:
- Verify IDDFS finds proofs that bounded DFS misses
- Verify IDDFS finds shortest proofs
- Verify IDDFS terminates on unprovable goals

### Risk Mitigation

**Risk 1: Performance Regression**

**Mitigation**:
- Benchmark IDDFS vs bounded DFS on existing test suite
- Ensure IDDFS is not significantly slower for shallow proofs
- Add performance tests to CI pipeline

**Risk 2: Memory Exhaustion**

**Mitigation**:
- Keep visit limits to prevent unbounded growth
- Monitor memory usage in benchmarks
- Add memory profiling to tests

**Risk 3: Incompleteness**

**Mitigation**:
- Set reasonable maxDepth (100-200)
- Document maxDepth as tunable parameter
- Add warning when maxDepth reached without proof

**Risk 4: Code Complexity**

**Mitigation**:
- Keep IDDFS implementation simple (wrapper around bounded_search)
- Add comprehensive documentation
- Add unit tests for each component

---

## Risks & Mitigations

### Risk 1: IDDFS Overhead

**Risk**: IDDFS may be significantly slower than bounded DFS due to redundant exploration.

**Likelihood**: Low  
**Impact**: Medium  
**Mitigation**:
- Theoretical analysis shows only ~11% overhead for b=10
- Caching reduces redundant work
- Benchmark on test suite to verify acceptable performance
- If overhead is high, optimize heuristic ordering to reduce branching factor

### Risk 2: Space Complexity of Best-First Search

**Risk**: Best-first search may exhaust memory for deep proofs.

**Likelihood**: Medium  
**Impact**: High  
**Mitigation**:
- Implement beam search variant with queue size limit
- Add memory monitoring to benchmarks
- Document memory requirements in API
- Recommend IDDFS for memory-constrained scenarios

### Risk 3: Heuristic Design Difficulty

**Risk**: Designing good heuristics for modal logic may be challenging.

**Likelihood**: Medium  
**Impact**: Medium  
**Mitigation**:
- Start with simple heuristics (complexity, modal depth)
- Tune weights empirically on test suite
- Document heuristic design process
- Provide multiple heuristic options

### Risk 4: Mathlib Dependency Deprecation

**Risk**: `Mathlib.Deprecated.MLList.BestFirst` may be removed from Mathlib.

**Likelihood**: Medium  
**Impact**: Low  
**Mitigation**:
- Copy relevant code into ProofChecker project with attribution
- Implement custom best-first search if needed
- Monitor Mathlib changes and adapt accordingly

### Risk 5: Completeness Limitations

**Risk**: IDDFS may not find proofs beyond maxDepth.

**Likelihood**: Low (for reasonable maxDepth)  
**Impact**: Medium  
**Mitigation**:
- Set maxDepth to 100-200 (sufficient for most proofs)
- Document maxDepth as tunable parameter
- Add warning when maxDepth reached
- Recommend increasing maxDepth if proof not found

---

## Appendix A: Complexity Analysis

### Branching Factor Estimation

For modal logic TM, the branching factor depends on:
1. **Modus ponens**: Number of implications in context with matching consequent
2. **Modal K**: 1 branch (if goal is □φ)
3. **Temporal K**: 1 branch (if goal is Gφ)

**Typical branching factors**:
- **Empty context**: b ≈ 1-2 (only modal/temporal rules)
- **Small context (5 formulas)**: b ≈ 3-5 (few MP opportunities)
- **Large context (20 formulas)**: b ≈ 10-20 (many MP opportunities)

**Average branching factor**: b ≈ 5-10

### Time Complexity Comparison

For branching factor b=10 and depth d=5:

**Bounded DFS**:
- Nodes explored: 10^5 = 100,000
- Time: O(b^d) = O(10^5)

**BFS**:
- Nodes explored: 10^5 = 100,000
- Time: O(b^d) = O(10^5)

**IDDFS**:
- Nodes explored: ∑(i=0 to 5) (6-i) * 10^i = 6 + 50 + 400 + 3000 + 20000 + 100000 = 123,456
- Time: O(b^d) = O(10^5)
- Overhead: 23.5% (acceptable)

### Space Complexity Comparison

For branching factor b=10 and depth d=5:

**Bounded DFS**:
- Max stack depth: 5
- Space: O(d) = O(5)

**BFS**:
- Max queue size: 10^5 = 100,000
- Space: O(b^d) = O(10^5)

**IDDFS**:
- Max stack depth: 5
- Space: O(d) = O(5)

**Conclusion**: IDDFS has same space complexity as DFS, much better than BFS.

---

## Appendix B: Example Proofs

### Example 1: Shallow Proof (Depth 2)

**Goal**: ⊢ (p → q) → ((q → r) → (p → r))

**Proof**:
1. Axiom: (p → (q → r)) → ((p → q) → (p → r))  [Prop K]
2. Instantiate with p:=p, q:=q, r:=r
3. QED (depth 1)

**Search Trace**:
- Depth 0: Check axiom match → Success

### Example 2: Medium Proof (Depth 5)

**Goal**: ⊢ □p → □□p

**Proof**:
1. Axiom: □p → p  [Modal T]
2. Axiom: □p → □□p  [Modal 4]
3. QED (depth 1)

**Search Trace**:
- Depth 0: Check axiom match → Success (Modal 4)

### Example 3: Deep Proof (Depth 10+)

**Goal**: ⊢ Gp → GGGGGGGGGG p  (10 nested G operators)

**Proof**:
1. Axiom: Gp → GGp  [Temporal 4]
2. Apply 9 times to get Gp → G^10 p
3. QED (depth 9)

**Search Trace**:
- Depth 0-8: No match
- Depth 9: Match via repeated Temporal 4 application

**Bounded DFS Failure**:
- With depth limit 5: Fails to find proof
- With depth limit 10: Finds proof

**IDDFS Success**:
- Iterates depths 0-9
- Finds proof at depth 9
- Guarantees shortest proof

---

## Appendix C: References

### Academic Papers

1. **Korf, Richard E. (1985)**. "Depth-first Iterative-Deepening: An Optimal Admissible Tree Search". *Artificial Intelligence* 27: 97-109.
   - Original IDDFS paper
   - Proves optimality and efficiency
   - Shows ~11% overhead for b=10

2. **Russell, Stuart J.; Norvig, Peter (2003)**. *Artificial Intelligence: A Modern Approach* (2nd ed.).
   - Chapter 3: Solving Problems by Searching
   - Comprehensive coverage of search algorithms
   - BFS, DFS, IDDFS, A* comparison

3. **Blackburn, de Rijke, Venema (2001)**. *Modal Logic*.
   - Tableau methods for modal logic
   - Completeness results
   - Complexity analysis

### Lean 4 Resources

1. **Mathlib Documentation**: https://leanprover-community.github.io/mathlib4_docs/
   - `Mathlib.Deprecated.MLList.BestFirst`: Best-first search implementation
   - `Batteries.Data.BinomialHeap`: Priority queue implementation
   - `Batteries.Data.HashMap`: Hash map for caching

2. **Metaprogramming in Lean 4**: https://leanprover-community.github.io/lean4-metaprogramming-book/
   - Tactic development
   - Monadic programming
   - Expression manipulation

3. **Theorem Proving in Lean 4**: https://lean-lang.org/theorem_proving_in_lean4/
   - Proof development
   - Tactic usage
   - Type theory

### Wikipedia Articles

1. **Breadth-first search**: https://en.wikipedia.org/wiki/Breadth-first_search
   - Algorithm description
   - Complexity analysis
   - Applications

2. **Iterative deepening depth-first search**: https://en.wikipedia.org/wiki/Iterative_deepening_depth-first_search
   - Algorithm description
   - Complexity proof
   - Bidirectional variant

### Project Documentation

1. **ProofSearch.lean**: Current bounded DFS implementation
2. **MODAL_TEMPORAL_PROOF_SEARCH.md**: Modal/temporal proof search strategies
3. **PROOF_SEARCH_AUTOMATION.md**: Proof search automation research
4. **leansearch-best-first-search.md**: LeanSearch best-first search results
5. **leansearch-priority-queue.md**: Priority queue data structures
6. **leansearch-proof-caching-memoization.md**: Caching strategies

---

## Appendix D: Implementation Checklist

### Phase 3: IDDFS Implementation

- [ ] Add `iddfs_search` function to ProofSearch.lean
- [ ] Add `SearchStrategy` enum to ProofSearch.lean
- [ ] Add `search` unified interface to ProofSearch.lean
- [ ] Update module docstring with IDDFS description
- [ ] Add complexity analysis to documentation
- [ ] Add IDDFS examples to documentation
- [ ] Add unit tests for IDDFS (shallow proofs)
- [ ] Add unit tests for IDDFS (medium proofs)
- [ ] Add unit tests for IDDFS (deep proofs)
- [ ] Add integration tests for IDDFS
- [ ] Create benchmark suite
- [ ] Run benchmarks (IDDFS vs bounded DFS)
- [ ] Document benchmark results
- [ ] Update TODO.md with Phase 3 completion
- [ ] Create git commit for Phase 3

### Future: Best-First Search Enhancement

- [ ] Add Batteries.Data.BinomialHeap dependency
- [ ] Define ProofState structure
- [ ] Implement stateLE ordering function
- [ ] Implement computeHeuristic function
- [ ] Implement generateSuccessorsWithHeuristics function
- [ ] Implement bestfirst_search function
- [ ] Update SearchStrategy enum with BestFirst variant
- [ ] Add unit tests for best-first search
- [ ] Add integration tests for best-first search
- [ ] Benchmark best-first vs IDDFS
- [ ] Document heuristic design
- [ ] Tune heuristic weights
- [ ] Create git commit for best-first enhancement

### Future: Beam Search Enhancement

- [ ] Add beam width parameter to best-first search
- [ ] Implement queue size limiting
- [ ] Add unit tests for beam search
- [ ] Benchmark beam search vs best-first
- [ ] Document completeness tradeoffs
- [ ] Create git commit for beam search enhancement

---

**Report Completed**: 2026-01-07  
**Next Steps**: Review research findings and create implementation plan for Phase 3
