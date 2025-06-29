# Diagnosis Plan: Why Invalid Models Exist Despite Premise/Conclusion Behavior Constraints

## Objective

Investigate why ANY exclusion strategy can generate invalid countermodels (with false premises or true conclusions) despite having explicit premise_behavior and conclusion_behavior constraints in the model generation process.

## Core Question

**How can Z3 find models where premises are false or conclusions are true when we explicitly constrain:**
- `premise_behavior`: All premises must be true at the main evaluation point
- `conclusion_behavior`: All conclusions must be false at the main evaluation point

## Investigation Approach

Examine each strategy independently to understand the mechanics of constraint failure, collecting data on:
1. How premise/conclusion constraints are generated
2. Where the constraint chain breaks down
3. What Z3 model assignments violate expected behavior
4. How empty verifiers bypass truth constraints

## Investigation Framework

### For Each Strategy (QA, QI2, SK, CD, MS, UF):

#### Step 1: Trace Premise/Conclusion Constraint Generation
**Goal**: Understand exactly how premise_behavior and conclusion_behavior translate to Z3 constraints

**Method**:
```python
# For each strategy:
# 1. Capture the exact Z3 constraints for premise_behavior
# 2. Capture the exact Z3 constraints for conclusion_behavior  
# 3. Trace how truth values are constrained at main_point
# 4. Identify any gaps in the constraint chain
```

**Data to Collect**:
- Exact Z3 formulas for premise truth constraints
- Exact Z3 formulas for conclusion falsity constraints
- How main_point is constrained
- How verifier membership relates to truth values

#### Step 2: Analyze Invalid Model Mechanics
**Goal**: For each invalid model found, trace exactly why it satisfies the constraints

**Method**:
```python
# For each invalid model:
# 1. Extract the Z3 model assignments
# 2. Show how premise_behavior constraint is satisfied despite false premise
# 3. Show how conclusion_behavior constraint is satisfied despite true conclusion
# 4. Identify the specific gap that allows this
```

**Data to Collect**:
- Z3 model assignments for worlds, verifiers, exclusion function
- Step-by-step evaluation of constraint satisfaction
- Identification of constraint gap or loophole
- Classification of failure mode

#### Step 3: Empty Verifier Analysis
**Goal**: Understand how empty verifier sets interact with truth constraints

**Method**:
```python
# For models with empty verifiers:
# 1. Trace how empty set assignment happens
# 2. Show how truth constraint evaluates with empty verifiers
# 3. Identify missing constraint that would prevent this
# 4. Document the logical gap
```

**Data to Collect**:
- Verifier assignments in invalid models
- Truth evaluation with empty verifiers
- Missing constraint identification
- Logical principle violations

### Data Collection Protocol

#### For Each Strategy-Example Pair with Invalid Model:

**1. Constraint Capture**
```python
# Record:
# - Full premise_behavior constraint as generated
# - Full conclusion_behavior constraint as generated
# - Main point selection constraint
# - Verifier existence constraints
# - Truth evaluation constraints
```

**2. Model Analysis**
```python
# Record:
# - Complete Z3 model assignment
# - Verifier assignments for each proposition
# - World structure and fusion assignments
# - Exclusion function assignments
# - Truth values at main_point
```

**3. Constraint Satisfaction Trace**
```python
# For each invalid model, trace:
# - How premise_behavior constraint is satisfied
# - How conclusion_behavior constraint is satisfied
# - Where the logical expectation breaks down
# - What allows false premises or true conclusions
```

**4. Gap Identification**
```python
# Document:
# - The specific constraint gap or loophole
# - Why current constraints are insufficient
# - What additional constraint would prevent this
# - General principle violated
```

### Expected Failure Modes

#### Mode 1: Empty Verifier Bypass
- **Symptom**: Propositions with empty verifiers evaluate as true
- **Mechanism**: Truth constraint doesn't properly handle empty sets
- **Data Needed**: How truth constraints are formulated for empty verifiers

#### Mode 2: Constraint Indirection
- **Symptom**: Constraints on intermediate variables don't propagate to final truth
- **Mechanism**: Chain of constraints has weak link
- **Data Needed**: Full constraint propagation chain

#### Mode 3: Exclusion Function Loophole
- **Symptom**: Exclusion function assignments allow unexpected truth patterns
- **Mechanism**: Function constraints permit problematic assignments
- **Data Needed**: Exclusion function constraint formulation

#### Mode 4: Main Point Selection Failure
- **Symptom**: Main point not properly constrained for evaluation
- **Mechanism**: Point selection doesn't ensure proper truth evaluation
- **Data Needed**: Main point selection constraints

### Investigation Output Format

#### For Each Strategy:

**1. Constraint Generation Report**
```
Strategy: [STRATEGY_NAME]
Total Invalid Models: [COUNT]

Premise Behavior Constraints:
[Exact Z3 constraint formulation]

Conclusion Behavior Constraints:
[Exact Z3 constraint formulation]

Truth Evaluation Mechanism:
[How truth values are computed from verifiers]
```

**2. Invalid Model Analysis**
```
Example: [EXAMPLE_NAME]
Invalidity Type: [False Premise / True Conclusion]

Model Assignment:
- Worlds: [assignments]
- Verifiers: [assignments]
- Exclusion: [assignments]

Constraint Satisfaction Trace:
[Step-by-step showing why constraints are satisfied]

Identified Gap:
[Specific constraint failure]
```

**3. Failure Mode Classification**
```
Strategy: [STRATEGY_NAME]
Failure Modes Found:
- Mode 1 (Empty Verifier): [COUNT] cases
- Mode 2 (Indirection): [COUNT] cases
- Mode 3 (Exclusion Loophole): [COUNT] cases
- Mode 4 (Main Point): [COUNT] cases
- Other: [COUNT] cases

Common Patterns:
[Summary of recurring issues]
```

## Diagnostic Tools Required

### Tool 1: Premise/Conclusion Constraint Tracer (`trace_pc_constraints.py`)
```python
def trace_premise_conclusion_constraints(strategy, example):
    """Extract exact premise/conclusion behavior constraints."""
    # Capture premise_behavior constraint generation
    # Capture conclusion_behavior constraint generation
    # Show how they translate to Z3
    # Identify any transformations or indirections
```

### Tool 2: Invalid Model Analyzer (`analyze_invalid_model.py`)
```python
def analyze_invalid_model(strategy, example, model):
    """Trace why an invalid model satisfies all constraints."""
    # Extract full Z3 model
    # Evaluate premise_behavior constraint
    # Evaluate conclusion_behavior constraint
    # Show step-by-step why both are satisfied
    # Identify the specific gap
```

### Tool 3: Constraint Gap Finder (`find_constraint_gaps.py`)
```python
def find_constraint_gaps(strategy, invalid_models):
    """Identify common patterns in constraint failures."""
    # Analyze all invalid models for strategy
    # Classify failure modes
    # Find common constraint gaps
    # Generate gap report
```

## Key Investigation Questions

### Question 1: Constraint Formulation
**How exactly are premise_behavior and conclusion_behavior translated into Z3 constraints?**
- Is there indirection through intermediate variables?
- Are constraints properly connected to truth evaluation?
- Do constraints cover all evaluation paths?

### Question 2: Empty Verifier Handling
**How do truth constraints handle propositions with empty verifiers?**
- Is there an explicit constraint for empty verifier = false?
- Can empty verifiers satisfy truth constraints?
- Where is this constraint missing or weak?

### Question 3: Constraint Satisfaction
**For invalid models, how do they satisfy the constraints?**
- What Z3 assignments allow false premises to satisfy premise_behavior?
- What Z3 assignments allow true conclusions to satisfy conclusion_behavior?
- Where does the logical expectation diverge from the constraint?

### Question 4: Systematic Patterns
**Are there common patterns across all invalid models?**
- Do all strategies share similar constraint gaps?
- Are certain examples consistently problematic?
- What general principle is being violated?

## Data Collection Goals

### Primary Data
1. **Exact constraint formulations** for premise_behavior and conclusion_behavior
2. **Complete Z3 model assignments** for all invalid models
3. **Step-by-step traces** showing constraint satisfaction despite invalidity
4. **Identified constraint gaps** for each failure mode

### Analysis Products
1. **Failure mode taxonomy** with counts per strategy
2. **Common constraint gap patterns** across strategies
3. **Minimal examples** demonstrating each failure mode
4. **General principles** for preventing invalid models

## Investigation Process

### Step 1: QA Strategy Analysis
- Analyze all 13 invalid models
- Trace premise/conclusion constraints
- Identify failure modes
- Document constraint gaps

### Step 2: QI2 Strategy Analysis
- Analyze all 17 invalid models
- Compare constraint generation with QA
- Identify additional failure modes
- Document patterns

### Step 3: SK Strategy Analysis
- Analyze all 18 invalid models
- Focus on unique failures
- Compare with previous findings

### Step 4: CD Strategy Analysis
- Analyze all 17 invalid models
- Look for strategy-specific issues

### Step 5: MS Strategy Analysis
- Analyze all ~17 invalid models
- Identify any new patterns

### Step 6: UF Strategy Analysis
- Analyze all ~17 invalid models
- Complete pattern analysis

### Step 7: Synthesis
- Compile common failure modes
- Identify universal constraint gaps
- Document general principles

## Deliverables

### Per-Strategy Reports
For each strategy (QA, QI2, SK, CD, MS, UF):
1. **Constraint Analysis**: Exact premise/conclusion constraint formulations
2. **Invalid Model Traces**: Complete analysis of each invalid model
3. **Failure Mode Summary**: Classification and counts
4. **Constraint Gap Identification**: Specific missing constraints

### Synthesis Report
1. **Common Failure Modes**: Patterns across all strategies
2. **Universal Constraint Gaps**: Gaps present in all strategies
3. **Root Cause Analysis**: Why premise/conclusion constraints fail
4. **General Principles**: What's needed to prevent invalid models

## Focus and Scope

### What This Investigation IS:
- A systematic analysis of WHY invalid models can exist
- A trace of how premise/conclusion constraints fail
- A collection of constraint gaps and failure modes
- A documentation of the disconnect between logical expectation and constraint reality

### What This Investigation IS NOT:
- A comparison of which strategies are "better"
- An optimization exercise
- A performance analysis
- A solution implementation project

### Core Principle:
We expect premise_behavior and conclusion_behavior to ensure:
- All premises are true at the evaluation point
- All conclusions are false at the evaluation point

The investigation seeks to understand why this expectation fails in practice.

## Summary

This investigation plan focuses solely on understanding why invalid models can exist despite explicit premise_behavior and conclusion_behavior constraints. By examining each strategy independently and tracing exactly how invalid models satisfy the constraints, we will identify the specific gaps that allow false premises and true conclusions.

The data collected will reveal the fundamental disconnect between our logical expectations and the actual constraint formulations, providing the foundation for understanding this critical issue in model checking.