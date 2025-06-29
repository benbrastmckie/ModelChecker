# Diagnosis Findings: Why Invalid Models Exist Despite Premise/Conclusion Constraints

## Investigation Status
- **Started**: 2025-01-29
- **Current Phase**: Beginning QA Strategy Analysis

## Core Question Under Investigation
How can Z3 find models where premises are false or conclusions are true when we explicitly constrain premise_behavior and conclusion_behavior?

---

## Findings by Strategy

### QA Strategy
**Status**: Investigation in progress
**Invalid Models**: 13 out of 34 tests

#### Initial Observations
- Starting investigation of constraint generation mechanism
- Will trace how premise_behavior and conclusion_behavior are implemented

#### Key Finding 1: Constraint Generation Mechanism
- `premise_behavior` = lambda function that calls `true_at_cached(premise, main_point)`
- `conclusion_behavior` = lambda function that calls `false_at_cached(conclusion, main_point)`
- These are set during ExclusionSemantics initialization
- `use_formula_registry = True` by default, so cached versions are used

#### Key Finding 2: Empty Verifier Problem
Analyzed examples with false premises:
1. **Disjunctive DeMorgan's RL**: `(\exclude A \uniwedge \exclude B)` has empty verifiers → evaluates to False
2. **Exclusion Contradiction**: `\exclude A` has empty verifiers → evaluates to False

But the constraints were satisfied! This suggests a disconnect between:
- Constraint generation phase (uses true_at_cached formulas)
- Truth evaluation phase (uses actual verifier membership)

#### Key Finding 3: Constraint vs Truth Evaluation Disconnect
The core issue appears to be:
1. During constraint generation, `true_at_cached` generates Z3 formulas
2. These formulas may allow empty verifier assignments
3. During truth evaluation, empty verifiers always evaluate to false
4. The constraint formula and truth evaluation use different logic!

#### Key Finding 4: Exclusion Operator Constraint Analysis
For `\exclude A` premise:
- **Generated constraint**: `Or(And(verify(0, A), 0 | w == w), And(verify(1, A), 1 | w == w), ...)`
- **What this means**: Looking for ANY state that verifies A and conflicts with main world
- **The problem**: This constraint can be satisfied even when NO verifiers exist for the exclusion!
- **Model found**: `excludes(0,1)=True, excludes(0,2)=True, excludes(0,4)=True` with main world = 0
- **Result**: Constraint evaluates to True (satisfied) but `\exclude A` has empty verifiers → False premise

#### Failure Mode Identified: Empty Verifier Bypass
**Mechanism**: The exclusion operator constraint checks if ANY state that verifies A conflicts with the main world. But it doesn't ensure that the EXCLUSION ITSELF has verifiers. The constraint is satisfied by the existence of conflicts, but the exclusion proposition ends up with no verifiers because no state verifies the exclusion of A.

### QI2 Strategy
**Status**: Analyzed
**Invalid Models**: 17 out of 34 tests

#### Key Findings
- Uses same `premise_behavior`/`conclusion_behavior` mechanism as QA
- Generates different constraint formulas due to different exclusion function implementation
- **Same fundamental issue**: Constraints can be satisfied with empty verifier models

#### Example Analysis
1. **Exclusion Contradiction** (`\exclude A` ⊢ `A`):
   - Premise constraint satisfied but `\exclude A` has empty verifiers → False
   - Conclusion constraint satisfied but `A` is True
   - Both constraints satisfied despite invalid model!

2. **Disjunctive DeMorgan's RL**:
   - Similar pattern: empty verifiers for premise lead to false premise
   - Constraint still satisfied

---

## Common Patterns
- **All strategies use the same premise/conclusion behavior mechanism**
- **All suffer from the empty verifier bypass issue**
- **The disconnect is fundamental to the architecture**

## Failure Mode Classification
- **Mode 1 (Empty Verifier Bypass)**: CONFIRMED - Constraints can be satisfied while propositions have empty verifiers
- Mode 2 (Constraint Indirection): Under investigation
- Mode 3 (Exclusion Function Loophole): Under investigation  
- Mode 4 (Main Point Selection): Under investigation

## Current Understanding

### The Core Problem
There is a fundamental architectural disconnect between:
1. **Constraint Generation Phase**: 
   - Happens BEFORE propositions are created
   - Uses complex Z3 formulas that encode semantic conditions
   - Example: `true_at(\exclude A, w)` becomes `∃x. verify(x, A) ∧ excludes(x, w)`
   
2. **Truth Evaluation Phase**: 
   - Happens AFTER model is found and propositions are created
   - Uses simple verifier membership check
   - Example: `\exclude A` is true iff `∃v ∈ verifiers(\exclude A). v ⊑ w`
   - Empty verifiers always evaluate to false

### Why Invalid Models Exist

1. **Constraint Approximation Gap**: 
   - The Z3 formulas approximate the intended semantics
   - But they don't directly constrain verifier sets
   - They can be satisfied even when the resulting propositions have empty verifiers

2. **Example: `\exclude A ⊢ A`**:
   - Premise constraint asks: "Does any A-verifier conflict with main world?"
   - This can be satisfied by having A-verifiers that exclude world 0
   - But `\exclude A` itself gets no verifiers (nothing verifies the exclusion)
   - Result: Constraint satisfied but premise is false

3. **Universal Pattern**:
   - For any formula φ constrained to be true:
     - Constraint: Complex formula encoding conditions
     - Truth: `∃v ∈ verifiers(φ). v ⊑ evaluation_world`
   - If `verifiers(φ) = ∅`, truth is False regardless of constraint satisfaction

## Comprehensive Findings

### All Strategies Affected
- **QA**: 13/34 invalid models (best performance)
- **QI2**: 17/34 invalid models  
- **SK**: 18/34 invalid models
- **CD**: 17/34 invalid models
- **MS**: ~17/34 invalid models
- **UF**: ~17/34 invalid models

All strategies share the same architecture and thus the same fundamental issue.

### Common Invalid Model Patterns

1. **Exclusion with Empty Verifiers**:
   - Formulas like `\exclude A` often get empty verifier sets
   - The constraint checks for conflicts but doesn't ensure exclusion has verifiers
   - Results in false premises

2. **Complex Formulas**:
   - `(\exclude A \uniwedge \exclude B)` - conjunction of exclusions
   - Both components may have empty verifiers
   - Conjunction also gets empty verifiers
   - Premise evaluates to false

3. **Atomic Propositions in Conclusions**:
   - When constrained to be false, atomic propositions can still get full verifier sets
   - Example: `A` gets verifiers {0,1,2,3,4,5,6,7} but constraint only prevents overlap with main world
   - Can result in true conclusions

## Root Cause Summary

The premise_behavior and conclusion_behavior constraints are architectural approximations that:
1. Generate formulas before proposition verifiers exist
2. Encode semantic conditions indirectly
3. Allow Z3 to find models where the formulas are satisfied
4. But don't guarantee the resulting propositions will have the required truth values
5. Because truth evaluation uses a different mechanism (verifier membership) than constraint generation (semantic formulas)

This is why invalid models can exist despite explicit premise/conclusion behavior constraints.