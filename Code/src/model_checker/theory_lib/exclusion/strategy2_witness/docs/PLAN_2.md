# Implementation Plan: Witness-Based Fine Preclusion Semantics

## Overview

This plan outlines the implementation of Fine preclusion semantics within the `strategy2_witness` framework. Unlike CB preclusion which requires witness functions for existentially quantified functions, Fine preclusion only quantifies over states in the finite model, eliminating the need for witness functions. The goal is to create `FineUniNegation` operator that implements Fine preclusion alongside the existing CB preclusion, enabling verification of CLAIM_1 and evaluation of QUESTION_1.

## Semantic Foundations

### Champollion-Bernard (CB) Preclusion (Current Implementation)
- **Definition**: Event `e` CB-precludes set `S` if ∃ function `h` such that:
  1. `e = ⊔{h(f_i) | f_i ∈ S}` (e is fusion of h-images)
  2. ∀ `f_i ∈ S`, `h(f_i)` excludes some part of `f_i`
- **Witness Functions**: `h: State → State`, `y: State → State`

### Fine Preclusion (To Implement)
- **Definition**: Event `e` Fine-precludes set `S` if `e = ⊔T` where:
  1. (Coverage) ∀ `s ∈ S`, ∃ `t ∈ T`: `t` excludes some part of `s`
  2. (Relevance) ∀ `t ∈ T`, ∃ `s ∈ S`: `t` excludes some part of `s`
- **Key Insight**: No witness functions needed - all quantifiers are over finite state space

## Implementation Architecture

### Phase 1: Core Implementation Strategy

#### 1.1 No Witness Infrastructure Needed
**Key Realization**: Fine preclusion doesn't require witness functions because:
- All quantifiers are over states, not functions
- In finite models, ∃ expands to disjunction, ∀ expands to conjunction
- Set T can be represented as a simple predicate over states

#### 1.2 Direct Constraint Generation
**Approach**: Implement Fine preclusion using direct Z3 constraints:
```python
def fine_preclusion_constraints(e, S_verifiers, model):
    # For each possible subset T of states:
    #   1. Check if e = ⊔T
    #   2. Check coverage: ∀s∈S ∃t∈T (t excludes part of s)
    #   3. Check relevance: ∀t∈T ∃s∈S (t excludes part of s)
    # Use Z3's finite domain quantifiers or expand manually
```

### Phase 2: FineUniNegation Operator

#### 2.1 Core Operator Implementation
**File**: `operators.py`
```python
class FineUniNegation(Operator):
    def __init__(self, operand):
        super().__init__(operand)
        self.token = r'\finexclude'
        
    def _verification_conditions(self, model):
        # Direct implementation without witnesses
        # 1. Get verifiers of operand (set S)
        # 2. Create boolean variable for each state (T membership)
        # 3. Add Fine preclusion constraints
        # 4. State e verifies if it can be the fusion of some valid T
```

#### 2.2 Constraint Implementation Strategy
- Use Z3 boolean variables `is_in_T[state]` for set membership
- Expand quantifiers to finite conjunctions/disjunctions
- Leverage existing `excludes` and `fusion` predicates

#### 2.3 Optimization Opportunities
- Pre-compute exclusion relationships
- Use symmetry of exclusion relation
- Prune impossible T candidates early

### Phase 3: Integration with Existing Framework

#### 3.1 Minimal Model Changes
**Insight**: Since Fine preclusion doesn't need witnesses, we can:
- Use the existing model infrastructure as-is
- No need to extend WitnessAwareModel
- No need for special formula registration

#### 3.2 Operator Registration
**File**: `operators.py`
```python
# Register the new operator
operators.register(
    token=r'\finexclude',
    precedence=1,
    operator_class=FineUniNegation,
    description='Fine preclusion negation (no witnesses needed)'
)
```

### Phase 4: Testing Infrastructure

#### 4.1 Parallel Example Files
1. **`examples_fine.py`**: Fine preclusion versions of all examples
2. **`examples_comparison.py`**: Side-by-side CB vs Fine tests
3. **`test_claim1.py`**: CLAIM_1 verification tests

#### 4.2 CLAIM_1 Verification Strategy
```python
def verify_cb_implies_fine(formula):
    """Test: Every CB-precluder is a Fine-precluder"""
    # 1. Find CB-precluder using UniNegationOperator
    # 2. Check if same state Fine-precludes using WitnessUniNegation
    
def verify_fine_has_cb_part(formula):
    """Test: Every Fine-precluder contains CB-precluding part"""
    # 1. Find Fine-precluder using WitnessUniNegation
    # 2. Check all parts for CB-preclusion property
```

#### 4.3 Performance Analysis
- Compare constraint counts between CB and Fine
- Measure solving times for nested formulas
- Analyze witness predicate overhead

### Phase 5: Optimization Strategies

#### 5.1 Constraint Reduction
- Exploit symmetries in exclusion relation
- Prune redundant T-membership checks
- Optimize witness function domains

#### 5.2 Hybrid Approach
- Use CB witnesses when available for efficiency
- Fall back to Fine witnesses for completeness
- Implement conversion between witness types

## Implementation Timeline

### Week 1: Core Implementation
- [ ] Implement FineUniNegation operator with direct constraints
- [ ] Test basic Fine preclusion examples
- [ ] Verify correctness on simple formulas

### Week 2: Testing Infrastructure
- [ ] Create parallel example files
- [ ] Implement CLAIM_1 verification tests
- [ ] Run comprehensive comparison tests

### Week 3: Performance Analysis
- [ ] Benchmark CB vs Fine preclusion
- [ ] Analyze computational complexity differences
- [ ] Document findings for QUESTION_1

### Week 4: Optimization and Polish
- [ ] Implement optimizations based on findings
- [ ] Complete documentation
- [ ] Prepare final analysis report

## Expected Challenges

1. **Set Enumeration**: Potentially need to consider all subsets of states as candidates for T
2. **Constraint Size**: Coverage and relevance conditions create many constraints
3. **Performance**: Without witnesses, solver must discover valid T sets
4. **Nested Formulas**: Handling `\finexclude(\finexclude A)` efficiently

## Success Metrics

1. **Correctness**: All examples produce expected results
2. **CLAIM_1 Verified**: Automated tests confirm the theoretical claim
3. **Performance**: Clear data on computational tractability (QUESTION_1)
4. **Robustness**: Handles nested formulas without "FALSE PREMISE" issues

## File Structure

```
strategy2_witness/
  ├── operators.py              # Add WitnessUniNegation class
  ├── semantic.py               # Extend witness infrastructure
  ├── examples_fine.py          # Fine preclusion examples
  ├── examples_comparison.py    # CB vs Fine comparisons
  ├── test_claim1.py           # CLAIM_1 verification
  ├── benchmark.py             # Performance analysis
  └── docs/
      ├── SEED_2.md            # Original specification
      ├── PLAN_2.md            # This implementation plan
      └── results/
          ├── claim1_results.md # Verification results
          └── performance.md    # Tractability analysis
```

## Next Steps

1. Review and approve this revised plan
2. Implement FineUniNegation with direct constraints
3. Create test suite comparing CB and Fine preclusion
4. Analyze performance to answer QUESTION_1

