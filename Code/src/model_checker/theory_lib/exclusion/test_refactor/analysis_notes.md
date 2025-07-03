# Analysis Notes - Phase 1

## Current Baseline Behavior (MS Strategy)

Based on the existing baseline_results.json from 2025-07-02, the following examples have issues:

### Examples with False Premises (8 total):
1. **DN_ELIM** (Double Negation Elimination)
   - False premise: `\exclude \exclude A`
   - This should be a valid theorem but has a false premise

2. **TN_ENTAIL** (Triple Negation Entailment)
   - False premise: `\exclude \exclude \exclude A`
   
3. **QN_ENTAIL** (Quadruple Negation Entailment)
   - False premise: `\exclude \exclude \exclude \exclude A`

4. **CONJ_DM_LR** (Conjunctive DeMorgan's LR)
   - False premise: `\exclude (A \uniwedge B)`

5. **CONJ_DM_RL** (Conjunctive DeMorgan's RL)
   - False premise: `(\exclude A \univee \exclude B)`

6. **DISJ_DM_LR** (Disjunctive DeMorgan's LR)
   - False premise: `\exclude (A \univee B)`

7. **DISJ_DM_RL** (Disjunctive DeMorgan's RL)
   - False premise: `(\exclude A \uniwedge \exclude B)`

8. **EX_TH_18**
   - False premise: `\exclude (A \uniwedge B)`

### Examples with True Conclusions:
- None found in the baseline

### Valid Examples (No Issues):
- EMPTY, GAPS, EX_CM_1, DN_ID, DN_INTRO, TN_ID
- All distribution, absorption, and associativity examples
- Most identity examples

### No Model Found (Expected Behavior):
- GLUTS, EX_CM_15, DISJ_SYLL
- All distribution, absorption, and associativity examples

## Multi-Strategy Architecture Analysis

### Current Strategy Registry (from operators.py):
```python
STRATEGY_REGISTRY = {
    "QA": ExclusionOperatorQuantifyArrays,      # 19% success, 83% reliability
    "QI": ExclusionOperatorQuantifyIndices,     # 41% success, 71% reliability  
    "QI2": ExclusionOperatorQuantifyIndices2,   # 38% success, 69% reliability
    "BQI": ExclusionOperatorBoundedQuantifyIndices,
    "NF": ExclusionOperatorNameFunctions,
    "NA": ExclusionOperatorNameArrays,
    "SK": ExclusionOperatorSkolemized,          # 50% success, ~60% reliability
    "CD": ExclusionOperatorConstraintBased,     # 50% success
    "MS": ExclusionOperatorMultiSort,           # 50% success (DEFAULT)
    "UF": ExclusionOperatorUninterpreted,       # 50% success
    "WD": ExclusionOperatorWitnessDriven,
}

DEFAULT_STRATEGY = "MS"
```

### Strategy-Specific Storage in semantic.py:
1. **QA (Quantify Arrays)**:
   - `self.h = z3.Array(f"h", z3.BitVecSort(self.N), z3.BitVecSort(self.N))`

2. **QI/QI2 (Quantify Indices)**:
   - `self.H = z3.Function("H", z3.IntSort(), h_sort)`
   - `self.H2 = z3.Function("H", z3.IntSort(), z3.BitVecSort(self.N), z3.BitVecSort(self.N))`

3. **BQI (Bounded Quantify Indices)**:
   - `self.B_h_ix = z3.BitVec("h_ix", self.N + 5)`
   - `self.BH = z3.Function("H", z3.BitVecSort(self.N + 5), h_sort)`

4. **Function Witnesses**:
   - `self.function_witnesses = {}` - Used for evaluating exclusion formulas

### Key Issues Identified:

1. **Disconnect in Evaluation**: The `evaluate_with_witness` method in semantic.py attempts to handle strategy-specific evaluation, but this creates inconsistency between constraint generation and truth evaluation.

2. **Complex Strategy Selection**: The multi-strategy approach makes it difficult to ensure consistent semantics across constraint generation and evaluation phases.

3. **False Premise Pattern**: Most false premises involve the exclusion operator, particularly in nested exclusions (double, triple, quadruple negation).

## Recommendations for Phase 2:

1. **Simplify to SK Strategy**: The Skolemized approach is conceptually clearest and has decent performance (50% success rate).

2. **Remove evaluate_with_witness**: Replace with direct Z3 evaluation for consistency.

3. **Clean up semantic.py**: Remove all strategy-specific declarations (H, H2, h, BH, etc.)

4. **Focus on Recursive Reduction**: Ensure that `true_at` and `extended_verify` properly reduce to primitive relations.