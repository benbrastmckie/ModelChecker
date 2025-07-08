# Implementation Plan: Simplified Fine-Preclusion Semantics

## Overview

This plan outlines a simplified implementation of Fine-preclusion semantics alongside the existing Champollion-Bernard (CB) preclusion semantics. Unlike CB preclusion which requires complex function quantification and multiple implementation strategies, Fine preclusion operates directly on sets of states without function quantification. This allows for a much cleaner implementation with a single, straightforward approach.

## Key Differences Between CB and Fine Preclusion

### Champollion-Bernard (CB) Preclusion
- **Definition**: Event `e` CB-precludes set `S` if there exists a function `h` such that:
  1. `e = {h(f_i) | f_i ∈ S}` (e is the fusion of h-images)
  2. For all `f_i ∈ S`, `h(f_i)` excludes some part of `f_i`
- **Key feature**: Requires a single function `h` that maps each element of S

### Fine Preclusion
- **Definition**: Event `e` Fine-precludes set `S` if `e` is the fusion of set `T` where:
  1. (Coverage) For all `s ∈ S`, some `t ∈ T` excludes some part of `s`
  2. (Relevance) For all `t ∈ T`, some `s ∈ S` where `t` excludes some part of `s`
- **Key feature**: No function quantification; uses set-based conditions

## Implementation Strategy

### Phase 1: Core Implementation

#### 1.1 Create FineUniNegation Operator
- **File**: `operators.py`
- **Class**: `FineUniNegation` (extends `Operator` directly, no base class needed)
- **Key Insight**: No function quantification means no need for ExclusionOperatorBase or multiple strategies
- **Implementation approach**:
  ```python
  class FineUniNegation(Operator):
      def __init__(self, operand):
          super().__init__(operand)
          self.name = r'\finexclude'
          
      def _verification_conditions(self, model):
          # Direct implementation without function quantification
          # 1. Get verifiers of operand (set S)
          # 2. For each state e, check if exists set T such that:
          #    - e = fusion(T)
          #    - Coverage: ∀s∈S ∃t∈T: excludes(t, part_of(s))
          #    - Relevance: ∀t∈T ∃s∈S: excludes(t, part_of(s))
          # Use Z3 booleans for T membership, no functions needed
  ```

#### 1.2 Single Implementation Strategy
- **No multiple strategies needed**: Fine preclusion's set-based approach eliminates the complexity that required 11 different strategies in CB preclusion
- **Direct constraint generation**: Use Z3's finite domain capabilities without complex workarounds
- **Clean separation**: Keep Fine preclusion logic separate from existing CB implementations

### Phase 2: Clean Integration

#### 2.1 Simplify Existing Code Structure
- **Remove ExclusionOperatorBase dependency**: Fine preclusion doesn't inherit from it
- **Keep existing operators intact**: Don't modify the CB preclusion implementations
- **Register operator cleanly**:
  ```python
  operators.register(
      token=r'\finexclude',
      precedence=1,
      operator_class=FineUniNegation,
      description='Fine-preclusion negation (set-based, no functions)'
  )
  ```

#### 2.2 Implementation Details
- **Use existing infrastructure**: Leverage `model.states()`, `model.excludes()`, `model.fusion()`
- **Avoid complexity**: No counters, no Skolem functions, no witness tracking
- **Clear semantics**: State `e` verifies `\finexclude A` iff `e` Fine-precludes the set of A-verifiers

### Phase 3: Testing Infrastructure

#### 3.1 Parallel Example Sets
Create new example files to run identical tests with both operators:

1. **`examples_fine.py`**: Copy of `examples.py` using `\finexclude`
2. **`examples_comparison.py`**: Side-by-side comparisons

#### 3.2 CLAIM_1 Verification Tests
Create dedicated test file `test_claim1.py`:

```python
# Test 1: CB-precluder → Fine-precluder
def test_cb_implies_fine():
    # For formulas where CB-preclusion succeeds,
    # verify Fine-preclusion also succeeds
    
# Test 2: Fine-precluder has CB-precluding part
def test_fine_has_cb_part():
    # For Fine-precluders, verify existence of
    # part that CB-precludes
```

#### 3.3 Computational Complexity Analysis
Create `benchmark.py`:
- Time model generation for both operators
- Compare constraint complexity
- Measure Z3 solving time

### Phase 4: Verification and Analysis

#### 4.1 Run Comprehensive Tests
1. Execute all existing examples with FineUniNegation
2. Compare results with ExclusionOperator
3. Document behavioral differences

#### 4.2 Verify CLAIM_1
Run specialized tests to verify:
- Every CB-precluder is a Fine-precluder
- Every Fine-precluder contains a CB-precluding part

#### 4.3 Answer QUESTION_1
Analyze computational tractability:
- Constraint count comparison
- Solving time benchmarks
- Memory usage analysis

## Implementation Order

1. **Day 1-2**: Core FineUniNegation implementation
   - Single, clean operator implementation
   - Direct verification conditions without function quantification
   - Basic unit tests

2. **Day 3-4**: Testing infrastructure
   - Create `examples_fine.py` with Fine preclusion tests
   - Implement `test_claim1.py` for CLAIM_1 verification
   - Set up comparison framework

3. **Day 5-6**: Performance analysis
   - Benchmark CB vs Fine preclusion
   - Analyze constraint complexity differences
   - Document computational tractability (QUESTION_1)

4. **Day 7**: Documentation and cleanup
   - Document findings
   - Clean up any redundant code
   - Prepare final analysis

## Expected Advantages of Simplified Approach

1. **No Function Quantification**: Eliminates the core complexity of CB preclusion
2. **Single Strategy**: No need to maintain 11 different implementation approaches
3. **Direct Semantics**: Fine preclusion maps directly to Z3 constraints
4. **Cleaner Codebase**: Significantly less code to maintain and debug

## Remaining Challenges

1. **Set Enumeration**: Still need to consider candidate sets T efficiently
2. **Constraint Size**: Coverage and relevance conditions for all state combinations
3. **Performance**: Without function witnesses, may need more solver work

## Success Criteria

1. **Functional**: FineUniNegation correctly implements Fine-preclusion
2. **Comparable**: Can run all existing examples with both operators
3. **Verified**: CLAIM_1 is confirmed through automated tests
4. **Analyzed**: Clear answer to QUESTION_1 with supporting data

## File Structure

```
strategy1_multi/
  ├── operators.py          # Add single FineUniNegation class (no base class)
  ├── examples_fine.py      # Fine-preclusion examples  
  ├── test_claim1.py        # CLAIM_1 verification
  ├── benchmark.py          # Performance comparison
  └── docs/
      ├── SEED.md           # Original specification
      ├── PLAN_1.md         # This simplified plan
      └── results/
          ├── claim1_verification.md # CLAIM_1 results
          └── tractability_analysis.md # QUESTION_1 answer
```

## Key Simplifications from Original Plan

1. **No ExclusionOperatorBase**: Fine preclusion doesn't need the complex base class
2. **Single Implementation**: One clean approach instead of multiple strategies
3. **No Function Witnesses**: Direct set-based semantics without function quantification
4. **Faster Development**: Days instead of weeks due to reduced complexity

## Next Steps

1. Review and approve this simplified plan
2. Implement single FineUniNegation operator
3. Create focused test suite
4. Analyze performance to answer QUESTION_1

