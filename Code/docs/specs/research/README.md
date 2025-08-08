# Research Reports

[← Back to Specs](../README.md)

This directory contains in-depth research reports investigating solutions to complex technical challenges in the ModelChecker framework.

## Iterator Constraint Preservation Issue

Research into fixing the issue where MODEL 2+ in iteration can have false premises or true conclusions at the evaluation world.

### Reports

1. **[Constraint Projection Approach](001_constraint_projection_approach.md)**
   - Projects MODEL 1's constraints onto MODEL 2's verify/falsify space
   - Complex but theoretically sound
   - Feasibility: LOW, Effort: HIGH

2. **[Evaluation Override Approach](002_evaluation_override_approach.md)**
   - Overrides formula evaluation to ensure correct truth values
   - Simple and practical solution
   - Feasibility: HIGH, Effort: LOW ✅

3. **[Solver Integration Approach](003_solver_integration_approach.md)**
   - Integrates iteration logic into Z3 solving process
   - Finds models that satisfy their own constraints
   - Feasibility: LOW-MEDIUM, Effort: VERY HIGH

4. **[Other Model Checkers Study](004_other_model_checkers.md)**
   - How Alloy, NuSMV, TLA+, and others handle iteration
   - Key finding: Most avoid variable semantic functions entirely
   - ModelChecker faces a unique challenge

5. **[Summary and Recommendations](005_summary_recommendations.md)**
   - Comparative analysis of all approaches
   - Recommended solution: Evaluation Override
   - Future research directions

## Key Findings

### The Unique Challenge

ModelChecker is unusual in allowing semantic functions (verify/falsify) to vary between models during iteration. This creates a self-referential constraint problem not found in other model checkers:

- MODEL 1's constraints assume MODEL 1's verify/falsify functions
- MODEL 2 has different verify/falsify functions  
- Z3 finds MODEL 2 using MODEL 1's constraints
- This mismatch causes incorrect formula evaluations

### Recommended Solution

**Evaluation Override** - The most practical approach:
- Override formula evaluation at the proposition level
- Ensure premises evaluate true and conclusions false
- Simple implementation with minimal risk
- Can be refined or replaced in the future

### Future Research

This problem opens interesting theoretical questions:
- Self-referential constraint satisfaction
- Fixpoint algorithms for semantic functions
- Integration of semantic variation in SMT solving

---

[← Back to Specs](../README.md)