# Research Report: Advanced Heuristics for Proof Search Performance

**Task**: 318 - Implement Phase 4 of task 260: Advanced Heuristics  
**Started**: 2026-01-07  
**Completed**: 2026-01-07  
**Effort**: 4 hours (research phase)  
**Priority**: Medium  
**Dependencies**: Task 260 (Phases 1-3), Task 317 (BFS variant research)  
**Sources/Inputs**: ProofSearch.lean, Task 317 research report, Mathlib heuristic search, modal logic literature  
**Artifacts**: research-001.md  
**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research investigates advanced heuristics for improving proof search performance in Lean 4 modal/temporal logic. The current ProofSearch.lean implementation has basic heuristic infrastructure but lacks domain-specific optimizations and proper subgoal ordering.

**Key Findings**:

1. **orderSubgoalsByScore is unimplemented** - Currently returns targets in original order (line 338-342), defeating the purpose of heuristic scoring
2. **Heuristic scoring exists but is underutilized** - `heuristic_score` function (lines 313-331) computes scores but they're not used for ordering
3. **Three optimization opportunities identified**: (1) Implement proper sorting in orderSubgoalsByScore, (2) Add domain-specific heuristics for modal/temporal logic, (3) Implement proof caching with hash-consing
4. **Formula complexity and modal depth are key metrics** - Already computed but not leveraged for ordering
5. **Proof caching infrastructure exists** - ProofCache and Visited sets are in place, but no hash-consing optimization

**Recommended Approach**: Implement proper sorting first (quick win), then add modal/temporal heuristics, finally optimize caching with hash-consing.

---

## Context & Scope

### Current Implementation Analysis

The existing `Logos/Core/Automation/ProofSearch.lean` has heuristic infrastructure but critical gaps:

**Heuristic Infrastructure (Present)**:
- `HeuristicWeights` structure (lines 141-158): Tunable weights for scoring
- `heuristic_score` function (lines 313-331): Computes branch priority scores
- `orderSubgoalsByScore` function (lines 338-342): **TODO - not implemented**
- `SearchStats` tracking (lines 109-118): Monitors cache hits/misses

**Critical Gap**:
```lean
/--
Order candidate subgoals by heuristic score so cheaper branches are explored first.

TODO: Implement proper sorting. For now, returns targets as-is.
-/
def orderSubgoalsByScore (weights : HeuristicWeights) (Γ : Context) (targets : List Formula) :
    List Formula :=
  -- TODO: Implement sorting by heuristic score
  -- For now, just return the targets in original order
  targets
```

This means **heuristic scores are computed but never used for ordering**, resulting in arbitrary exploration order.

**Usage in bounded_search** (lines 398-399):
```lean
let implications := find_implications_to Γ φ
let orderedTargets := orderSubgoalsByScore weights Γ implications
```

The function is called but has no effect, so modus ponens antecedents are tried in the order they appear in the context, not by heuristic priority.

### Research Scope

This research focuses on:
1. Implementing proper sorting in `orderSubgoalsByScore`
2. Designing domain-specific heuristics for modal/temporal logic
3. Optimizing proof caching with hash-consing
4. Evaluating heuristic effectiveness on benchmark proofs

---

## Key Findings

### 1. Sorting Implementation for orderSubgoalsByScore

**Problem**: Function returns targets unsorted, defeating heuristic scoring.

**Solution**: Sort targets by heuristic score (ascending, since lower scores = higher priority).

**Implementation**:
```lean
def orderSubgoalsByScore (weights : HeuristicWeights) (Γ : Context) (targets : List Formula) :
    List Formula :=
  targets.mergeSort (fun φ ψ => heuristic_score weights Γ φ ≤ heuristic_score weights Γ ψ)
```

**Rationale**:
- `List.mergeSort` is stable O(n log n) sort in Lean 4 Batteries
- Comparison function: `φ ≤ ψ` means φ has lower/equal score (higher priority)
- Preserves relative order for equal scores (stable sort)

**Impact**:
- **Immediate performance improvement**: Explores cheaper branches first
- **No API changes**: Drop-in replacement for TODO
- **Minimal code**: Single line implementation
- **Tested infrastructure**: Uses existing `heuristic_score` function

**Example**:
```lean
-- Before (unsorted):
targets = [complex_formula, simple_axiom, medium_formula]
orderedTargets = [complex_formula, simple_axiom, medium_formula]  -- Same order

-- After (sorted by score):
targets = [complex_formula, simple_axiom, medium_formula]
scores = [100, 0, 50]  -- Computed by heuristic_score
orderedTargets = [simple_axiom, medium_formula, complex_formula]  -- Sorted ascending
```

### 2. Domain-Specific Heuristics for Modal/Temporal Logic

**Current Heuristics** (from `heuristic_score`, lines 313-331):

1. **Axiom matching** (weight: 0) - Highest priority
2. **Assumption matching** (weight: 1) - Second priority
3. **Modus ponens** (weight: 2 + complexity) - Depends on antecedent complexity
4. **Modal K** (weight: 5 + context penalty) - Expensive due to context transformation
5. **Temporal K** (weight: 5 + context penalty) - Expensive due to context transformation
6. **Dead end** (weight: 100) - Lowest priority

**Limitations**:
- **No modal-specific optimizations**: Doesn't prefer S4/S5 axioms for modal goals
- **No temporal-specific optimizations**: Doesn't prefer temporal axioms for temporal goals
- **No formula structure analysis**: Doesn't consider subformula patterns
- **No historical success tracking**: Doesn't learn from past proofs

**Proposed Enhancements**:

**Enhancement 1: Modal-Specific Heuristics**

Prefer modal axioms (T, 4, 5, B) when goal has modal operators:

```lean
def modal_heuristic_bonus (φ : Formula) : Int :=
  match φ with
  | Formula.box _ => -5  -- Bonus for modal goals
  | Formula.diamond _ => -5  -- Bonus for modal goals
  | _ => 0

def enhanced_heuristic_score (weights : HeuristicWeights) (Γ : Context) (φ : Formula) : Nat :=
  let base_score := heuristic_score weights Γ φ
  let modal_bonus := modal_heuristic_bonus φ
  (base_score + modal_bonus).toNat  -- Clamp to Nat (0 minimum)
```

**Rationale**:
- Modal goals (□φ, ◇φ) benefit from modal axioms (T, 4, 5, B)
- Negative bonus = higher priority (lower score)
- Encourages exploring modal-specific strategies first

**Enhancement 2: Temporal-Specific Heuristics**

Prefer temporal axioms (4, A, L) when goal has temporal operators:

```lean
def temporal_heuristic_bonus (φ : Formula) : Int :=
  match φ with
  | Formula.all_future _ => -5  -- Bonus for temporal goals
  | Formula.some_future _ => -5  -- Bonus for temporal goals
  | Formula.all_past _ => -5  -- Bonus for temporal goals
  | Formula.some_past _ => -5  -- Bonus for temporal goals
  | _ => 0
```

**Enhancement 3: Formula Structure Heuristics**

Analyze subformula patterns to predict proof difficulty:

```lean
def structure_heuristic (φ : Formula) : Nat :=
  let complexity := φ.complexity  -- Number of operators
  let modal_depth := φ.modalDepth  -- Nesting level of □/◇
  let temporal_depth := φ.temporalDepth  -- Nesting level of G/F/H/P
  let implication_count := φ.countImplications  -- Number of → operators
  
  complexity + (modal_depth * 2) + (temporal_depth * 2) + implication_count
```

**Rationale**:
- **Complexity**: More operators = harder proof
- **Modal depth**: Deeply nested modalities require more modal K applications
- **Temporal depth**: Deeply nested temporal operators require more temporal K applications
- **Implication count**: More implications = more modus ponens opportunities

**Enhancement 4: Historical Success Tracking**

Learn from past proofs to prioritize successful strategies:

```lean
structure SuccessHistory where
  axiom_successes : Std.HashMap String Nat  -- Axiom name → success count
  rule_successes : Std.HashMap String Nat  -- Rule name → success count
  deriving Inhabited

def historical_heuristic (history : SuccessHistory) (φ : Formula) : Int :=
  -- Bonus for formulas similar to past successes
  if matches_axiom φ then
    let axiom_name := identify_axiom φ
    let success_count := history.axiom_successes.findD axiom_name 0
    -(success_count.toInt)  -- More successes = higher priority
  else
    0
```

**Rationale**:
- Track which axioms/rules succeed most often
- Prioritize strategies with historical success
- Adaptive heuristic that improves over time

**Combined Heuristic**:
```lean
def advanced_heuristic_score (weights : HeuristicWeights) (Γ : Context) (φ : Formula) 
    (history : SuccessHistory := {}) : Nat :=
  let base := heuristic_score weights Γ φ
  let modal_bonus := modal_heuristic_bonus φ
  let temporal_bonus := temporal_heuristic_bonus φ
  let structure_penalty := structure_heuristic φ
  let historical_bonus := historical_heuristic history φ
  
  (base + modal_bonus + temporal_bonus + structure_penalty + historical_bonus).toNat
```

### 3. Proof Caching with Hash-Consing

**Current Caching** (lines 99-106):

```lean
abbrev CacheKey := Context × Formula
abbrev ProofCache := Std.HashMap CacheKey Bool
abbrev Visited := Std.HashSet CacheKey
```

**Limitations**:
- **No hash-consing**: Duplicate formulas stored separately
- **Large cache keys**: Context × Formula can be large
- **No structural sharing**: Subformulas not deduplicated

**Hash-Consing Optimization**:

Hash-consing is a technique to ensure each unique formula is stored only once, with all references pointing to the same object. This reduces memory usage and speeds up equality checks.

**Implementation Strategy**:

```lean
structure FormulaId where
  id : Nat
  deriving Inhabited, DecidableEq, Hashable

structure HashConsTable where
  formulas : Std.HashMap FormulaId Formula
  reverse : Std.HashMap Formula FormulaId
  next_id : Nat
  deriving Inhabited

def HashConsTable.empty : HashConsTable :=
  { formulas := {}, reverse := {}, next_id := 0 }

def HashConsTable.intern (table : HashConsTable) (φ : Formula) : FormulaId × HashConsTable :=
  match table.reverse.find? φ with
  | some id => (id, table)  -- Already interned
  | none =>
      let id := FormulaId.mk table.next_id
      let formulas' := table.formulas.insert id φ
      let reverse' := table.reverse.insert φ id
      (id, { formulas := formulas', reverse := reverse', next_id := table.next_id + 1 })

-- Optimized cache key using formula IDs
abbrev OptimizedCacheKey := List FormulaId × FormulaId  -- Context IDs × Goal ID
abbrev OptimizedProofCache := Std.HashMap OptimizedCacheKey Bool
```

**Benefits**:
- **Smaller cache keys**: FormulaId is just a Nat (8 bytes vs potentially hundreds for Formula)
- **Faster equality checks**: O(1) integer comparison vs O(n) structural comparison
- **Memory savings**: Each unique formula stored once
- **Structural sharing**: Subformulas automatically deduplicated

**Tradeoffs**:
- **Complexity**: Requires managing HashConsTable
- **Overhead**: Interning cost for new formulas
- **State management**: HashConsTable must be threaded through search

**Recommendation**: Implement hash-consing as optional optimization after basic heuristics are working. Measure memory usage and cache hit rates to justify complexity.

### 4. Heuristic Effectiveness Evaluation

**Evaluation Metrics**:

1. **Search time**: Total visits to find proof
2. **Cache hit rate**: Percentage of cache hits vs misses
3. **Proof depth**: Length of shortest proof found
4. **Memory usage**: Peak visited set size

**Benchmark Proofs**:

```lean
-- Simple modal proof (should benefit from modal heuristics)
example : ⊢ (p.box).imp (p.box.box)  -- Modal 4 axiom

-- Simple temporal proof (should benefit from temporal heuristics)
example : ⊢ (p.all_future).imp (p.all_future.all_future)  -- Temporal 4 axiom

-- Complex modal-temporal proof (should benefit from combined heuristics)
example : ⊢ (p.box.all_future).imp (p.all_future.box)  -- Modal-temporal interaction

-- Deep nested proof (should benefit from structure heuristics)
example : ⊢ (p.box.box.box.box.box).imp p  -- Repeated Modal T application
```

**Expected Results**:

| Heuristic | Simple Modal | Simple Temporal | Complex | Deep Nested |
|-----------|--------------|-----------------|---------|-------------|
| **No sorting** | 100 visits | 100 visits | 500 visits | 1000 visits |
| **Basic sorting** | 50 visits | 50 visits | 300 visits | 600 visits |
| **Modal-specific** | 20 visits | 50 visits | 150 visits | 400 visits |
| **Temporal-specific** | 50 visits | 20 visits | 150 visits | 400 visits |
| **Combined** | 20 visits | 20 visits | 100 visits | 300 visits |

**Validation Strategy**:
1. Implement each heuristic incrementally
2. Run benchmark suite after each enhancement
3. Compare metrics (visits, time, cache hits)
4. Document performance improvements
5. Tune weights empirically

---

## Detailed Analysis

### Current Heuristic Weights

From `HeuristicWeights` structure (lines 141-158):

```lean
structure HeuristicWeights where
  axiomWeight : Nat := 0           -- Highest priority
  assumptionWeight : Nat := 1      -- Second priority
  mpBase : Nat := 2                -- Modus ponens base cost
  mpComplexityWeight : Nat := 1    -- Multiplier for antecedent complexity
  modalBase : Nat := 5             -- Modal K base cost
  temporalBase : Nat := 5          -- Temporal K base cost
  contextPenaltyWeight : Nat := 1  -- Penalty per context entry
  deadEnd : Nat := 100             -- Lowest priority
```

**Analysis**:

1. **Axiom matching is prioritized** (weight 0) - Correct, axioms are cheapest
2. **Assumption matching is second** (weight 1) - Correct, assumptions are free
3. **Modus ponens is third** (weight 2+) - Reasonable, but complexity weight could be tuned
4. **Modal/temporal K are expensive** (weight 5+) - Correct, context transformation is costly
5. **Dead end is lowest** (weight 100) - Correct, no strategy available

**Tuning Opportunities**:

1. **Increase modal/temporal base weights** to 10-15 (more expensive than MP)
2. **Increase context penalty weight** to 2-3 (larger contexts are harder)
3. **Add modal/temporal bonuses** for matching goal structure (negative weights)

**Proposed Tuned Weights**:

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
  modalBonus : Int := -5  -- New: bonus for modal goals
  temporalBonus : Int := -5  -- New: bonus for temporal goals
```

### Formula Complexity Metrics

**Current Complexity** (from `Formula.lean`):

```lean
def Formula.complexity : Formula → Nat
  | atom _ => 1
  | bot => 1
  | imp φ ψ => 1 + φ.complexity + ψ.complexity
  | box φ => 1 + φ.complexity
  | diamond φ => 1 + φ.complexity
  | all_future φ => 1 + φ.complexity
  | some_future φ => 1 + φ.complexity
  | all_past φ => 1 + φ.complexity
  | some_past φ => 1 + φ.complexity
```

**Proposed Additional Metrics**:

```lean
def Formula.modalDepth : Formula → Nat
  | atom _ => 0
  | bot => 0
  | imp φ ψ => max φ.modalDepth ψ.modalDepth
  | box φ => 1 + φ.modalDepth
  | diamond φ => 1 + φ.modalDepth
  | all_future φ => φ.modalDepth
  | some_future φ => φ.modalDepth
  | all_past φ => φ.modalDepth
  | some_past φ => φ.modalDepth

def Formula.temporalDepth : Formula → Nat
  | atom _ => 0
  | bot => 0
  | imp φ ψ => max φ.temporalDepth ψ.temporalDepth
  | box φ => φ.temporalDepth
  | diamond φ => φ.temporalDepth
  | all_future φ => 1 + φ.temporalDepth
  | some_future φ => 1 + φ.temporalDepth
  | all_past φ => 1 + φ.temporalDepth
  | some_past φ => 1 + φ.temporalDepth

def Formula.countImplications : Formula → Nat
  | atom _ => 0
  | bot => 0
  | imp φ ψ => 1 + φ.countImplications + ψ.countImplications
  | box φ => φ.countImplications
  | diamond φ => φ.countImplications
  | all_future φ => φ.countImplications
  | some_future φ => φ.countImplications
  | all_past φ => φ.countImplications
  | some_past φ => φ.countImplications
```

**Usage in Heuristics**:

```lean
def structure_heuristic (φ : Formula) : Nat :=
  φ.complexity + (φ.modalDepth * 2) + (φ.temporalDepth * 2) + φ.countImplications
```

### Proof Caching Performance Analysis

**Current Cache Performance** (from SearchStats):

```lean
structure SearchStats where
  hits : Nat := 0      -- Cache hits (entries found)
  misses : Nat := 0    -- Cache misses (entries inserted)
  visited : Nat := 0   -- Nodes visited
  prunedByLimit : Nat := 0  -- Nodes pruned by visit limit
```

**Cache Hit Rate Formula**:
```
hit_rate = hits / (hits + misses)
```

**Expected Hit Rates**:
- **No caching**: 0% (all misses)
- **Basic caching**: 20-40% (some repeated subgoals)
- **Hash-consing**: 40-60% (structural sharing increases hits)

**Memory Usage**:
- **CacheKey size**: sizeof(Context) + sizeof(Formula) ≈ 100-1000 bytes
- **FormulaId size**: sizeof(Nat) = 8 bytes
- **Memory savings**: 10-100x reduction with hash-consing

**Recommendation**: Measure cache hit rates on benchmark suite before implementing hash-consing. If hit rate < 30%, hash-consing may not justify complexity.

---

## Decisions

### Decision 1: Implement Sorting First (Quick Win)

**Decision**: Implement proper sorting in `orderSubgoalsByScore` as first priority.

**Rationale**:
1. **Immediate impact**: Enables existing heuristic scores to be used
2. **Minimal code**: Single line implementation
3. **No API changes**: Drop-in replacement for TODO
4. **Foundation for enhancements**: Required for domain-specific heuristics to work

**Implementation**:
```lean
def orderSubgoalsByScore (weights : HeuristicWeights) (Γ : Context) (targets : List Formula) :
    List Formula :=
  targets.mergeSort (fun φ ψ => heuristic_score weights Γ φ ≤ heuristic_score weights Γ ψ)
```

**Estimated Effort**: 30 minutes (implementation + testing)

### Decision 2: Add Domain-Specific Heuristics (High Value)

**Decision**: Implement modal-specific and temporal-specific heuristics as second priority.

**Rationale**:
1. **High impact**: Targets modal/temporal logic domain
2. **Moderate complexity**: Requires new heuristic functions
3. **Tunable**: Can adjust bonuses empirically
4. **Extensible**: Can add more domain-specific heuristics later

**Implementation Plan**:
1. Add `modal_heuristic_bonus` function
2. Add `temporal_heuristic_bonus` function
3. Add `structure_heuristic` function
4. Combine into `advanced_heuristic_score`
5. Update `orderSubgoalsByScore` to use advanced scoring

**Estimated Effort**: 3-4 hours (implementation + testing + tuning)

### Decision 3: Defer Hash-Consing (Optional Optimization)

**Decision**: Defer hash-consing optimization until after basic heuristics are working.

**Rationale**:
1. **High complexity**: Requires managing HashConsTable state
2. **Uncertain benefit**: Need to measure cache hit rates first
3. **Not blocking**: Basic heuristics work without hash-consing
4. **Can add later**: Orthogonal to heuristic design

**Evaluation Criteria**:
- If cache hit rate < 30%: Hash-consing may not help
- If memory usage < 100MB: Hash-consing not needed
- If proof search time < 1s: Hash-consing not needed

**Estimated Effort**: 6-8 hours (implementation + testing + validation)

### Decision 4: Defer Historical Success Tracking (Future Enhancement)

**Decision**: Defer historical success tracking to future work.

**Rationale**:
1. **High complexity**: Requires persistent state management
2. **Uncertain benefit**: Need to measure heuristic effectiveness first
3. **Not blocking**: Static heuristics work without history
4. **Research opportunity**: Could be separate task/paper

**Future Work**: Consider implementing as part of machine learning integration (Task 260 Phase 6+).

---

## Recommendations

### Immediate Actions (Phase 4 Implementation)

**1. Implement Sorting in orderSubgoalsByScore** (Estimated: 30 minutes)

**Tasks**:
- Replace TODO with `mergeSort` implementation
- Add unit tests for sorting correctness
- Verify heuristic scores are used for ordering

**Code Changes**:
```lean
def orderSubgoalsByScore (weights : HeuristicWeights) (Γ : Context) (targets : List Formula) :
    List Formula :=
  targets.mergeSort (fun φ ψ => heuristic_score weights Γ φ ≤ heuristic_score weights Γ ψ)
```

**Testing**:
```lean
-- Test: Sorting by heuristic score
example : 
  let weights := {}
  let Γ := []
  let targets := [complex_formula, simple_axiom, medium_formula]
  let ordered := orderSubgoalsByScore weights Γ targets
  ordered.head? = some simple_axiom  -- Lowest score first
```

**2. Add Formula Complexity Metrics** (Estimated: 1-2 hours)

**Tasks**:
- Add `modalDepth` function to Formula.lean
- Add `temporalDepth` function to Formula.lean
- Add `countImplications` function to Formula.lean
- Add unit tests for each metric

**Code Changes** (in `Logos/Core/Syntax/Formula.lean`):
```lean
def Formula.modalDepth : Formula → Nat
  | atom _ => 0
  | bot => 0
  | imp φ ψ => max φ.modalDepth ψ.modalDepth
  | box φ => 1 + φ.modalDepth
  | diamond φ => 1 + φ.modalDepth
  | all_future φ => φ.modalDepth
  | some_future φ => φ.modalDepth
  | all_past φ => φ.modalDepth
  | some_past φ => φ.modalDepth

-- Similar for temporalDepth and countImplications
```

**3. Implement Domain-Specific Heuristics** (Estimated: 2-3 hours)

**Tasks**:
- Add `modal_heuristic_bonus` function
- Add `temporal_heuristic_bonus` function
- Add `structure_heuristic` function
- Add `advanced_heuristic_score` function
- Update `orderSubgoalsByScore` to use advanced scoring (optional flag)

**Code Changes** (in `ProofSearch.lean`):
```lean
def modal_heuristic_bonus (φ : Formula) : Int :=
  match φ with
  | Formula.box _ => -5
  | Formula.diamond _ => -5
  | _ => 0

def temporal_heuristic_bonus (φ : Formula) : Int :=
  match φ with
  | Formula.all_future _ => -5
  | Formula.some_future _ => -5
  | Formula.all_past _ => -5
  | Formula.some_past _ => -5
  | _ => 0

def structure_heuristic (φ : Formula) : Nat :=
  φ.complexity + (φ.modalDepth * 2) + (φ.temporalDepth * 2) + φ.countImplications

def advanced_heuristic_score (weights : HeuristicWeights) (Γ : Context) (φ : Formula) : Nat :=
  let base := heuristic_score weights Γ φ
  let modal_bonus := modal_heuristic_bonus φ
  let temporal_bonus := temporal_heuristic_bonus φ
  let structure_penalty := structure_heuristic φ
  (base + modal_bonus + temporal_bonus + structure_penalty).toNat
```

**4. Tune Heuristic Weights** (Estimated: 2-3 hours)

**Tasks**:
- Create benchmark suite with modal/temporal proofs
- Run benchmarks with different weight configurations
- Measure search time, visits, cache hits
- Document optimal weights

**Benchmark Proofs**:
```lean
-- Modal proofs
example : ⊢ (p.box).imp (p.box.box)  -- Modal 4
example : ⊢ (p.box).imp p  -- Modal T
example : ⊢ p.imp (p.box.diamond)  -- Modal B

-- Temporal proofs
example : ⊢ (p.all_future).imp (p.all_future.all_future)  -- Temporal 4
example : ⊢ p.imp (p.all_future.some_past)  -- Temporal A

-- Mixed proofs
example : ⊢ (p.box.all_future).imp (p.all_future.box)  -- Interaction
```

**Weight Tuning Strategy**:
1. Start with default weights
2. Run benchmarks and record metrics
3. Adjust one weight at a time
4. Re-run benchmarks and compare
5. Repeat until optimal configuration found

**5. Update Documentation** (Estimated: 1 hour)

**Tasks**:
- Update module docstring with heuristic description
- Document new complexity metrics
- Document domain-specific heuristics
- Add examples demonstrating heuristic usage

### Future Enhancements (Post-Phase 4)

**1. Hash-Consing Optimization** (Estimated: 6-8 hours)

**Prerequisite**: Measure cache hit rates and memory usage first.

**Tasks**:
- Implement `HashConsTable` structure
- Implement `intern` function for formula deduplication
- Update `CacheKey` to use `FormulaId`
- Update `bounded_search` to thread `HashConsTable`
- Benchmark memory usage and cache hit rates

**2. Historical Success Tracking** (Estimated: 8-10 hours)

**Prerequisite**: Basic heuristics working and tuned.

**Tasks**:
- Implement `SuccessHistory` structure
- Track axiom/rule successes during search
- Implement `historical_heuristic` function
- Persist history across search sessions
- Benchmark effectiveness on repeated proofs

**3. Machine Learning Integration** (Estimated: 20-30 hours)

**Prerequisite**: Large corpus of proofs for training.

**Tasks**:
- Collect proof corpus from test suite
- Extract features (formula structure, context, etc.)
- Train heuristic model (e.g., decision tree, neural network)
- Integrate model into proof search
- Benchmark against hand-tuned heuristics

### Testing Strategy

**Unit Tests**:
- Test `orderSubgoalsByScore` sorts correctly
- Test `modalDepth` computes correct nesting level
- Test `temporalDepth` computes correct nesting level
- Test `countImplications` counts correctly
- Test `modal_heuristic_bonus` returns correct bonus
- Test `temporal_heuristic_bonus` returns correct bonus
- Test `structure_heuristic` computes correct penalty
- Test `advanced_heuristic_score` combines correctly

**Integration Tests**:
- Test heuristics improve search time on modal proofs
- Test heuristics improve search time on temporal proofs
- Test heuristics improve search time on mixed proofs
- Test heuristics don't regress on simple proofs

**Performance Tests**:
- Benchmark search time with/without sorting
- Benchmark search time with/without domain heuristics
- Measure cache hit rates with/without hash-consing
- Measure memory usage with/without hash-consing

**Regression Tests**:
- Verify all existing tests still pass
- Verify proof depths don't increase (optimality)
- Verify no performance regressions on simple proofs

### Risk Mitigation

**Risk 1: Sorting Overhead**

**Mitigation**:
- Use efficient `mergeSort` (O(n log n))
- Benchmark sorting time vs search time savings
- If overhead is high, cache sorted results

**Risk 2: Heuristic Tuning Difficulty**

**Mitigation**:
- Start with conservative weights
- Tune incrementally on benchmark suite
- Document tuning process and rationale
- Provide multiple weight configurations

**Risk 3: Complexity Creep**

**Mitigation**:
- Implement incrementally (sorting → metrics → heuristics)
- Test each component independently
- Document each enhancement clearly
- Defer optional optimizations (hash-consing, history)

**Risk 4: Performance Regression**

**Mitigation**:
- Benchmark before and after each change
- Add performance tests to CI pipeline
- Revert if regression detected
- Document performance characteristics

---

## Appendix A: Implementation Checklist

### Phase 4: Advanced Heuristics Implementation

- [ ] Implement sorting in `orderSubgoalsByScore`
- [ ] Add unit tests for sorting
- [ ] Add `modalDepth` to Formula.lean
- [ ] Add `temporalDepth` to Formula.lean
- [ ] Add `countImplications` to Formula.lean
- [ ] Add unit tests for complexity metrics
- [ ] Implement `modal_heuristic_bonus`
- [ ] Implement `temporal_heuristic_bonus`
- [ ] Implement `structure_heuristic`
- [ ] Implement `advanced_heuristic_score`
- [ ] Add unit tests for heuristic functions
- [ ] Create benchmark suite
- [ ] Run benchmarks with default weights
- [ ] Tune heuristic weights empirically
- [ ] Document optimal weights
- [ ] Update module docstring
- [ ] Update documentation with examples
- [ ] Add integration tests
- [ ] Add performance tests
- [ ] Verify no regressions
- [ ] Create git commit for Phase 4

### Future: Hash-Consing Optimization

- [ ] Measure baseline cache hit rates
- [ ] Measure baseline memory usage
- [ ] Implement `HashConsTable` structure
- [ ] Implement `intern` function
- [ ] Update `CacheKey` to use `FormulaId`
- [ ] Update `bounded_search` to thread `HashConsTable`
- [ ] Add unit tests for hash-consing
- [ ] Benchmark cache hit rates with hash-consing
- [ ] Benchmark memory usage with hash-consing
- [ ] Document hash-consing benefits
- [ ] Create git commit for hash-consing

### Future: Historical Success Tracking

- [ ] Implement `SuccessHistory` structure
- [ ] Track axiom successes during search
- [ ] Track rule successes during search
- [ ] Implement `historical_heuristic` function
- [ ] Persist history across sessions
- [ ] Add unit tests for history tracking
- [ ] Benchmark effectiveness on repeated proofs
- [ ] Document history tracking
- [ ] Create git commit for history tracking

---

## Appendix B: Benchmark Suite

### Modal Logic Proofs

```lean
-- Modal T (reflexivity)
example : ⊢ (p.box).imp p

-- Modal 4 (transitivity)
example : ⊢ (p.box).imp (p.box.box)

-- Modal 5 (Euclidean)
example : ⊢ (p.diamond.box).imp (p.box)

-- Modal B (symmetry)
example : ⊢ p.imp (p.box.diamond)

-- Modal K (distribution)
example : ⊢ ((p.imp q).box).imp ((p.box).imp (q.box))
```

### Temporal Logic Proofs

```lean
-- Temporal 4 (transitivity)
example : ⊢ (p.all_future).imp (p.all_future.all_future)

-- Temporal A (symmetry)
example : ⊢ p.imp (p.all_future.some_past)

-- Temporal L (linearity)
example : ⊢ ((p.all_past).and (p.and (p.all_future))).imp (p.all_future.all_past)

-- Temporal K (distribution)
example : ⊢ ((p.imp q).all_future).imp ((p.all_future).imp (q.all_future))
```

### Modal-Temporal Interaction Proofs

```lean
-- Modal-Future interaction
example : ⊢ (p.box).imp (p.box.all_future)

-- Temporal-Future interaction
example : ⊢ (p.box).imp (p.all_future.box)

-- Complex interaction
example : ⊢ (p.box.all_future).imp (p.all_future.box)
```

### Deep Nesting Proofs

```lean
-- Deep modal nesting
example : ⊢ (p.box.box.box.box.box).imp p

-- Deep temporal nesting
example : ⊢ (p.all_future.all_future.all_future.all_future.all_future).imp p

-- Mixed deep nesting
example : ⊢ (p.box.all_future.box.all_future.box).imp p
```

---

## Appendix C: References

### Academic Papers

1. **Fitting, Melvin (1983)**. "Proof Methods for Modal and Intuitionistic Logics". *Synthese Library*.
   - Modal logic proof search strategies
   - Tableau methods for modal logic
   - Completeness results

2. **Goré, Rajeev (1999)**. "Tableau Methods for Modal and Temporal Logics". *Handbook of Tableau Methods*.
   - Comprehensive survey of tableau methods
   - Optimization techniques
   - Complexity analysis

3. **Horrocks, Ian; Patel-Schneider, Peter F. (1999)**. "Optimizing Description Logic Subsumption". *Journal of Logic and Computation*.
   - Heuristic optimization for modal logic
   - Caching strategies
   - Performance evaluation

### Lean 4 Resources

1. **Batteries Documentation**: https://github.com/leanprover-community/batteries
   - `List.mergeSort`: Stable O(n log n) sorting
   - `Std.HashMap`: Hash map for caching
   - `Std.HashSet`: Hash set for visited tracking

2. **Mathlib Documentation**: https://leanprover-community.github.io/mathlib4_docs/
   - Modal logic formalization
   - Proof search tactics
   - Heuristic search algorithms

### Project Documentation

1. **ProofSearch.lean**: Current proof search implementation
2. **Task 317 Research Report**: BFS variant research (IDDFS, best-first search)
3. **MODAL_TEMPORAL_PROOF_SEARCH.md**: Modal/temporal proof search strategies
4. **PROOF_SEARCH_AUTOMATION.md**: Proof search automation research

---

**Report Completed**: 2026-01-07  
**Next Steps**: Create implementation plan for Phase 4 based on research findings
