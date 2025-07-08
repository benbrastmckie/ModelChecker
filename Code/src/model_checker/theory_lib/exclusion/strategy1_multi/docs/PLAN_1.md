# Strategy 1: Fine Semantics Without Witnesses

## Overview

This plan outlines **Strategy 1**: implementing **only Fine's set-based preclusion semantics** using the traditional ModelChecker framework without witness predicates. This provides a baseline implementation that:

- Uses **only Fine semantics** (`\set_unineg`) - no CB preclusion at all
- Operates in the **older ModelChecker framework** without witness infrastructure
- Provides **direct set enumeration** without function quantification
- Enables **performance comparison** with Strategy 2's witness-based approach

Unlike Strategy 2 which implements both CB and Fine semantics using witness predicates, Strategy 1 focuses exclusively on demonstrating that Fine semantics can be implemented cleanly and efficiently without advanced Z3 features.

## Strategy 1 Focus: Fine Semantics Only

This strategy implements **only Fine preclusion semantics** for computational comparison purposes. Understanding Fine semantics:

### Fine Preclusion (Strategy 1 Implementation)
- **Operator**: `\set_unineg` 
- **Definition**: Event `e` Fine-precludes set `S` if `e` is the fusion of set `T` where:
  1. (Coverage) For all `s ∈ S`, some `t ∈ T` excludes some part of `s`
  2. (Relevance) For all `t ∈ T`, some `s ∈ S` where `t` excludes some part of `s`
- **Key advantage**: No function quantification; uses only set-based conditions
- **Implementation**: Direct set enumeration using traditional ModelChecker architecture

### Comparison with Strategy 2
- **Strategy 1**: Only Fine semantics, no witnesses, older framework
- **Strategy 2**: Both CB and Fine semantics, with witness predicates, advanced framework

This enables direct comparison of:
1. **Computational efficiency**: Traditional vs witness-based approaches
2. **Implementation complexity**: Simple set operations vs function quantification  
3. **Semantic expressiveness**: Fine-only vs CB+Fine capabilities

## Implementation Strategy

### Phase 1: Core Implementation

#### 1.1 Create FineUniNegation Operator
- **File**: `operators.py`
- **Class**: `FineUniNegation` (extends standard `Operator` class)
- **Key Insight**: No function quantification enables direct implementation in traditional framework
- **Implementation approach**:
  ```python
  class FineUniNegation(Operator):
      def __init__(self, operand):
          super().__init__(operand)
          self.name = r'\set_unineg'
          
      def _verification_conditions(self, model):
          # Direct set-based implementation
          # 1. Get verifiers of operand (set S)
          # 2. For each state e, check if exists set T such that:
          #    - e = fusion(T)
          #    - Coverage: ∀s∈S ∃t∈T: excludes(t, part_of(s))
          #    - Relevance: ∀t∈T ∃s∈S: excludes(t, part_of(s))
          # Use Z3 booleans for T membership, no witness functions needed
  ```

#### 1.2 Traditional Framework Implementation
- **Single, clean approach**: Fine preclusion's set-based semantics fit naturally in the traditional ModelChecker architecture
- **No witness infrastructure**: Uses standard Z3 constraint generation without advanced model extensions
- **Direct set enumeration**: Leverages Z3's finite domain capabilities for straightforward implementation
- **Baseline comparison**: Provides performance and complexity baseline for Strategy 2 comparison

### Phase 2: Clean Integration

#### 2.1 Traditional Framework Integration
- **Standalone implementation**: No dependencies on complex base classes or witness infrastructure
- **Standard ModelChecker patterns**: Uses traditional `Operator` inheritance and constraint generation
- **Clean operator registration**:
  ```python
  operators.register(
      token=r'\set_unineg',
      precedence=1,
      operator_class=FineUniNegation,
      description='Fine preclusion (set-based, traditional framework)'
  )
  ```

#### 2.2 Implementation Details
- **Use standard infrastructure**: Leverage existing `model.states()`, `model.excludes()`, `model.fusion()`
- **Traditional approach**: No witness functions, no advanced Z3 features, no function quantification
- **Pure Fine semantics**: State `e` verifies `\set_unineg A` iff `e` Fine-precludes the set of A-verifiers
- **Performance baseline**: Provides comparison point for witness-based Strategy 2

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

