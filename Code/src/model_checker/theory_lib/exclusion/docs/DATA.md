# Data Analysis: Test Results and Performance Metrics

[← Back to Documentation](README.md) | [Iterate →](ITERATE.md) | [Exclusion Theory →](../README.md)

## Directory Structure

```
docs/
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # Architectural patterns and design
├── DATA.md            # This file - test data analysis
├── ITERATE.md         # Model iteration and countermodel generation
├── README.md          # Documentation hub
├── SETTINGS.md        # Configuration and parameter guide
└── USER_GUIDE.md      # User-focused tutorial
```

## Overview

The **Data Analysis** document provides comprehensive analysis of all 38 examples in the exclusion theory test suite, documenting countermodel behavior and providing explicit countermodels for key examples that demonstrate the witness predicate solution to the False Premise Problem.

Within the exclusion theory validation, this data represents complete verification that Bernard and Champollion's unilateral semantics has been correctly implemented. All 22 countermodel examples successfully find countermodels (previously impossible due to the False Premise Problem), and all 16 theorem examples correctly validate as theorems.

This analysis serves researchers validating the implementation and understanding the differences between unilateral and bilateral semantics through concrete counterexamples.

## Key Result

The False Premise Problem has been solved:

```python
# Key validation: False Premise Problem solved
# EX_CM_6: Double negation elimination fails
model = BuildExample("ex_cm_6", exclusion_theory,
    premises=['\\¬unineg \\¬unineg A'],  # ¬¬A
    conclusions=['A'],                           # A
    settings={'N': 3}
)
result = model.check_validity()  # False - countermodel found!

# Results summary:
# - 22/22 countermodels found (100% success)
# - 16/16 theorems validated (100% success)
# - Average solving time: ~0.005s per example
```

## Results Summary

### Countermodel Examples (22 total)
Examples with 'CM' in their name expect countermodels (`expectation = true`):
- **All 22 countermodel examples successfully found countermodels** PASS 
- These demonstrate failures of classical logical principles in unilateral semantics
- Include frame constraint tests, negation problems, and DeMorgan's law failures

### Theorem Examples (16 total) 
Examples with 'TH' in their name expect no countermodels (`expectation = false`):
- **All 16 theorem examples correctly found no countermodels** PASS  
- These demonstrate valid logical principles that hold in unilateral semantics
- Include distribution, absorption, and associativity laws

## Complete Examples Listing

### Countermodel Examples (expectation = true)

| Example | Description | Status | Model Size |
|---------|-------------|--------|------------|
| EX_CM_1 | Empty case for checking frame constraints | PASS  Countermodel | N=2 |
| EX_CM_2 | Gaps case | PASS  Countermodel | N=3 |
| EX_CM_3 | No glut case | PASS  Countermodel | N=3 |
| EX_CM_4 | Negation to sentence (`¬A ⊭ A`) | PASS  Countermodel | N=3 |
| EX_CM_5 | Sentence to negation (`A ⊭ ¬A`) | PASS  Countermodel | N=3 |
| EX_CM_6 | Double negation elimination (`¬¬A ⊭ A`) | PASS  Countermodel | N=3 |
| EX_CM_7 | Double negation introduction (`A ⊭ ¬¬A`) | PASS  Countermodel | N=3 |
| EX_CM_8 | Triple negation entailment | PASS  Countermodel | N=3 |
| EX_CM_9 | Quadruple negation entailment | PASS  Countermodel | N=3 |
| EX_CM_10 | Conjunction DeMorgan LR (`¬A ∨ ¬B ⊭ ¬(A ∧ B)`) | PASS  Countermodel | N=3 |
| EX_CM_11 | Conjunction DeMorgan RL (`¬(A ∧ B) ⊭ ¬A ∨ ¬B`) | PASS  Countermodel | N=3 |
| EX_CM_12 | Disjunction DeMorgan LR | PASS  Countermodel | N=3 |
| EX_CM_13 | Disjunction DeMorgan RL | PASS  Countermodel | N=3 |
| EX_CM_14 | Double negation identity (`¬¬A ≡ A`) | PASS  Countermodel | N=3 |
| EX_CM_15 | Triple negation identity | PASS  Countermodel | N=3 |
| EX_CM_16 | Conjunction DeMorgan identity | PASS  Countermodel | N=3 |
| EX_CM_17 | Disjunction DeMorgan identity | PASS  Countermodel | N=3 |
| EX_CM_18 | Disjunction distribution identity | PASS  Countermodel | N=3 |
| EX_CM_19 | Complex DeMorgan (compound identity) | PASS  Countermodel | N=4 |
| EX_CM_20 | DeMorgan complex | PASS  Countermodel | N=3 |
| EX_CM_21 | Basic test (`A ⊭ B`) | PASS  Countermodel | N=3 |
| EX_CM_22 | Distribution test | PASS  Countermodel | N=3 |

### Theorem Examples (expectation = false)

| Example | Description | Status | Model Size |
|---------|-------------|--------|------------|
| EX_TH_1 | Atomic theorem (`A ⊨ A`) | PASS  No countermodel | N=2 |
| EX_TH_2 | Disjunctive syllogism (`A ∨ B, ¬A ⊨ B`) | PASS  No countermodel | N=3 |
| EX_TH_3 | Conjunction distribution LR | PASS  No countermodel | N=3 |
| EX_TH_4 | Conjunction distribution RL | PASS  No countermodel | N=3 |
| EX_TH_5 | Disjunction distribution LR | PASS  No countermodel | N=3 |
| EX_TH_6 | Disjunction distribution RL | PASS  No countermodel | N=3 |
| EX_TH_7 | Conjunction absorption LR | PASS  No countermodel | N=3 |
| EX_TH_8 | Conjunction absorption RL | PASS  No countermodel | N=3 |
| EX_TH_9 | Disjunction absorption LR | PASS  No countermodel | N=3 |
| EX_TH_10 | Disjunction absorption RL | PASS  No countermodel | N=3 |
| EX_TH_11 | Conjunction associativity LR | PASS  No countermodel | N=3 |
| EX_TH_12 | Conjunction associativity RL | PASS  No countermodel | N=3 |
| EX_TH_13 | Disjunction associativity LR | PASS  No countermodel | N=3 |
| EX_TH_14 | Disjunction associativity RL | PASS  No countermodel | N=3 |
| EX_TH_15 | Conjunction distribution identity | PASS  No countermodel | N=3 |
| EX_TH_16 | Complex unilateral formula | PASS  No countermodel | N=3 |

## Key Countermodel Examples (Detailed Analysis)

### EX_CM_4: The False Premise Problem (`¬A ⊭ A`)

**Formula**: From `¬A`, conclude `A`

**Countermodel Structure**:
```
State Space (N=3):
  □ = empty state
  a = atomic proposition A  
  b = atomic proposition B
  a.b = world containing both A and B
  c, a.c, b.c, a.b.c = impossible states (conflicting)

Evaluation World: a.b

Premise Interpretation:
  |¬A| = {a.b}  (True in a.b)
  |A| = {a.b.c, a.c}       (False in a.b)

Conclusion Interpretation:
  |A| = {a.b.c, a.c}       (False in a.b)

Exclusion Relations:
  □ excludes c
  a excludes a.c  
  b excludes b.c

Witness Functions:
  ¬(A)_h: maps A-verifiers to their exclusion sources
  ¬(A)_y: maps A-verifiers to excluded parts
```

**Significance**: This countermodel demonstrates that exclusion-based negation does not satisfy double negation elimination. The state `a.b` verifies `¬A` but does not verify `A`, showing that witness functions can create complex verification patterns that avoid classical negation behavior.

### EX_CM_6: Double Negation Elimination (`¬¬A ⊭ A`)

**Formula**: From `¬¬A`, conclude `A`

**Countermodel Structure**:
```
State Space (N=3):
  □ = empty state (evaluation world)
  All other states a, b, c, a.b, a.c, b.c, a.b.c = impossible

Evaluation World: □

Premise Interpretation:
  |¬¬A| = {□}  (True in □)
  |¬A| = ∅             (False in □)
  |A| = {a, a.b, a.b.c, a.c, b, b.c, c}  (False in □)

Conclusion Interpretation:  
  |A| = {a, a.b, a.b.c, a.c, b, b.c, c}  (False in □)

Exclusion Relations:
  □ excludes all non-empty states
  Universal exclusion pattern

Witness Functions:
  Nested witness predicates creating circular exclusion
```

**Significance**: This is perhaps the most dramatic countermodel, showing that double negation can be true in a state where the original proposition is false. The empty state `□` verifies double negation of A while falsifying A itself, completely violating classical logical intuitions.

### EX_CM_11: DeMorgan's Law Failure (`¬(A ∧ B) ⊭ (¬A ∨ ¬B)`)

**Formula**: From `¬(A \uniwedge B)`, conclude `(¬A \univee ¬B)`

**Countermodel Structure**:
```
State Space (N=3):
  State space varies, showing complex interaction patterns

Evaluation World: Varies based on witness constraints

Key Feature: Conjunction of exclusions does not distribute
```

**Significance**: Demonstrates that classical DeMorgan's laws fail in unilateral semantics, as exclusion-based negation creates different logical relationships than classical negation.

### EX_CM_21: Basic Invalidity (`A ⊭ B`)

**Formula**: From `A`, conclude `B`

**Countermodel Structure**:
```
State Space (N=3):
  □, a, b, a.b, c, a.c, b.c, a.b.c

Evaluation World: a.b.c

Premise Interpretation:
  |A| = {a, a.b, a.b.c, a.c, b, b.c, c, □}  (True in a.b.c)

Conclusion Interpretation:
  |B| = {a, a.b, a.c, b, b.c, c, □}         (False in a.b.c)
```

**Significance**: Shows basic logical independence - A can be true without B being true, validating the framework's ability to detect simple logical invalidity.

## Theoretical Significance

### The False Premise Problem Resolution

The successful countermodel detection in all EX_CM_* examples demonstrates the complete resolution of the **False Premise Problem** that plagued earlier attempts to implement exclusion semantics:

1. **Previous Issue**: Exclusion formulas in premises would evaluate as having no verifiers due to information flow barriers between constraint generation and truth evaluation.

2. **Solution**: The witness predicate approach makes witness functions first-class model citizens, ensuring witness values are accessible during truth evaluation.

3. **Validation**: All 22 countermodel examples correctly find countermodels, proving that witness functions now work correctly in complex logical contexts.

### Logical Insights

The countermodel patterns reveal key differences between unilateral and bilateral semantics:

1. **Negation Behavior**: Exclusion-based negation (`¬`) does not satisfy classical negation properties like double negation elimination.

2. **DeMorgan's Laws**: Classical DeMorgan's laws fail in unilateral semantics due to the complex interaction between witness functions and exclusion relations.

3. **Distribution Laws**: Some distribution laws that hold classically fail in the unilateral setting, while others are preserved.

4. **Absorption and Associativity**: Basic structural laws like absorption and associativity are preserved, showing that unilateral semantics maintains core logical structure while altering negation behavior.

## Implementation Validation

### Z3 Performance
- Average solving time: ~0.005 seconds per example
- No timeouts or solver failures
- Witness function interpretations correctly computed
- Model structures properly displayed with exclusion relations

### Architectural Success
- Witness predicates successfully integrated into model structure
- No information flow barriers between constraint generation and evaluation  
- Circular information dependencies resolved through registry pattern
- All 38 examples run successfully with expected results

## Documentation

### For Researchers

- **[Results Summary](#results-summary)** - Complete test suite outcomes
- **[Key Countermodels](#key-countermodel-examples-detailed-analysis)** - Detailed analysis of important failures
- **[Theoretical Significance](#theoretical-significance)** - Insights into unilateral semantics

### For Implementers

- **[Complete Listing](#complete-examples-listing)** - All 38 examples with status
- **[Performance Metrics](#implementation-validation)** - Z3 solving times and success rates
- **[Architectural Success](#architectural-success)** - Validation of witness predicates

### For Theory Comparers

- **[Logical Insights](#logical-insights)** - Differences from bilateral semantics
- **[Countermodel Structures](#key-countermodel-examples-detailed-analysis)** - Explicit model structures
- **[False Premise Resolution](#the-false-premise-problem-resolution)** - How witness predicates solved it

## Key Insights

1. **100% Success Rate**: All 38 examples produce expected results
2. **False Premise Solved**: Negation formulas now correctly compute verifiers
3. **DeMorgan's Laws Fail**: All four forms find countermodels in unilateral semantics
4. **Double Negation Fails**: Both elimination and introduction find countermodels
5. **Performance Excellence**: Average solving time ~0.005s per example

## References

### Test Implementation

- **[Examples Module](../examples.py)** - Complete test suite definition
- **[Test Module](../tests/test_examples.py)** - Automated validation
- **[Semantic Module](../semantic.py)** - Implementation being validated

### Related Documentation

- **[Architecture](ARCHITECTURE.md)** - How witness predicates enable these results
- **[User Guide](USER_GUIDE.md)** - Understanding countermodel behavior
- **[Implementation Story](../history/IMPLEMENTATION_STORY.md)** - Journey to 100% success

---

[← Back to Documentation](README.md) | [Iterate →](ITERATE.md) | [Exclusion Theory →](../README.md)
