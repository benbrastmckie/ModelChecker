# Exclusion Semantics Documentation

This directory contains documentation for the exclusion semantics implementation in the ModelChecker framework. The documents trace the evolution from initial implementation through analysis, new strategy development, and a comprehensive implementation plan.

## Quick Navigation

- **Start Here**: [Guided Tour](#guided-tour-research-trajectory)
- **Current Work**: [TODO.md](TODO.md) - Active task tracking
- **Latest Results**: [findings.md](findings.md) - Implementation findings
- **Technical Plan**: [implementation_plan.md](implementation_plan.md) - Detailed phases

## Document Overview

### 1. [unilateral_semantics.md](unilateral_semantics.md) - Project Overview
**Purpose**: Provides the theoretical foundation and project overview for unilateral truthmaker semantics with exclusion operators.

**Key Topics**:
- Philosophical motivation for unilateral semantics
- Formal definitions of exclusion operators
- Comparison with bilateral semantics
- Initial implementation challenges

**Read this first** to understand the theoretical background and motivation.

### 2. [old_strategies.md](old_strategies.md) - Original Implementation Strategies
**Purpose**: Documents the various semantic strategies developed by Miguel for implementing exclusion operators.

**Strategies Covered**:
- QA (Quantify Arrays) - Conservative approach with 83.3% reliability
- QI2 (Quantify Indices 2) - Current default with balanced performance
- SK (Skolemized Functions) - Eliminates existential quantifiers
- CD (Constraint-Based Definition) - Explicit enumeration approach
- MS (Multi-Sort) - Type-safe implementation
- UF (Uninterpreted Functions) - Axiomatic approach

**Key Finding**: All strategies showed a trade-off between success rate and reliability, with false premise issues affecting all approaches.

### 3. [new_strategies.md](new_strategies.md) - New Strategic Directions
**Purpose**: Outlines new approaches to address the fundamental disconnect between constraint generation and truth evaluation.

**New Concepts**:
- Precise Constraint Translation (PCT)
- Correct recursive semantics
- Direct Computation Strategy (DCS)
- Hybrid approaches combining existing strategies

**Key Insight**: The issue isn't that `true_at` approximates, but that operator implementations don't properly reduce to verifier existence conditions.

### 4. [implementation_plan.md](implementation_plan.md) - Phased Implementation Plan
**Purpose**: Provides a detailed, phased approach to implementing correct recursive semantics.

**Phases**:
1. **Foundation and Analysis** - Understand current failures
2. **Skolemized Functions Implementation** - Implement SK with correct recursion
3. **Constraint-Based Enhancements** - Add CD optimizations
4. **Direct Computation Strategy** - Ideal implementation
5. **Integration and Documentation** - Final integration

**Timeline**: 5-week implementation with testing between phases.

### 5. [findings.md](findings.md) - Implementation Findings (In Progress)
**Purpose**: Track results and findings from each implementation phase.

**Structure**:
- Phase-by-phase test results
- Performance metrics
- Issues discovered and resolved
- Comparative analysis across strategies
- Lessons learned

**Status**: Template ready, to be populated during implementation.

### 6. [TODO.md](TODO.md) - Original Implementation Task Tracking
**Purpose**: Detailed task list following the implementation plan with 115 specific tasks across all phases for refactoring semantic_old.py and operators_old.py.

**Organization**:
- Tasks grouped by implementation phase
- Clear success criteria for each phase
- Meta tasks for ongoing quality assurance
- Progress tracking and completion metrics

**Status**: Phase 1 completed, Phase 2 in progress. False premises persist despite SK implementation.

### 7. [new_implementation.md](new_implementation.md) - Current Refactoring Plan
**Purpose**: Comprehensive plan for refactoring the current semantic.py and operators.py based on lessons learned.

**Key Innovations**:
- Simplify to single strategy FIRST
- Focus on Skolemized (SK) approach
- Use custom quantifiers for predictability
- 5-phase implementation with rigorous testing

**Timeline**: 17-22 hours across 5 phases.

### 8. [TODO_new_refactor.md](TODO_new_refactor.md) - Current Implementation Tasks
**Purpose**: Tracks 90 specific tasks for the new refactoring effort on semantic.py and operators.py.

**Organization**:
- More focused than original TODO
- Emphasizes simplification before correction
- Detailed success criteria per phase
- Progress metrics clearly defined

**Use this** to track the current refactoring effort.

## Reading Order

For **theoretical understanding**:
1. `unilateral_semantics.md` - Philosophical foundation
2. `old_strategies.md` - Current implementation landscape
3. `new_strategies.md` - Proposed improvements

For **implementation work**:
1. `new_strategies.md` - Understand the new approach
2. `implementation_plan.md` - Follow the phased plan
3. `findings.md` - Track progress and results

## Key Concepts

### The Core Problem
A disconnect between how constraints are generated (Phase 1) and how truth is evaluated (Phase 2), leading to models with false premises or true conclusions.

### The Solution
Ensure that `true_at` methods correctly implement recursive reduction to verifier existence conditions, maintaining consistency between constraint generation and truth evaluation.

### Implementation Strategy
Use Skolemized Functions (SK) as the primary approach, enhanced with Constraint-Based (CD) optimizations, ultimately developing a Direct Computation Strategy (DCS) for maximum clarity and correctness.

## Related Documentation

### Parent Directory (`../`)
- `README.md` - Theory library overview
- `semantic.py` - Core implementation file
- `operators.py` - Operator definitions
- `examples.py` - Test examples

### Test Directory (`../test/`)
- Various test files for validating implementations
- `test_suite_for_improvements.py` - Comprehensive testing framework

## Contributing

When implementing changes:
1. Follow the phased approach in `implementation_plan.md`
2. Document findings in `findings.md` after each phase
3. Run comprehensive tests before proceeding to next phase
4. Update this README if new documents are added

## Current Status

- **Theory**: Well-documented and understood
- **Problem**: Identified and analyzed  
- **Previous Attempt**: Phase 1 complete, Phase 2 in progress on semantic_old.py/operators_old.py
- **Current Effort**: New refactoring plan created for semantic.py/operators.py
- **Next Steps**: Begin Phase 1 of new implementation (simplification-first approach)

## Guided Tour: Research Trajectory

### The Journey So Far

#### 1. **The Beginning: Unilateral Semantics**
We started with a philosophical motivation: can we build a simpler truthmaker semantics using only verifiers (no falsifiers)? The exclusion operator would handle negation through a complex three-condition definition. *See [unilateral_semantics.md](unilateral_semantics.md)*

#### 2. **Initial Implementation Challenges**
Miguel developed six different strategies (QA, QI2, SK, CD, MS, UF) to implement the exclusion operator. Each showed a fundamental trade-off:
- **Conservative strategies** (QA): High reliability (83%) but low coverage (19%)
- **Aggressive strategies** (SK, CD, MS, UF): Higher coverage (50%) but more false premises

*Key Learning*: The existential quantifiers in the three-condition definition created severe implementation challenges. *See [old_strategies.md](old_strategies.md)*

#### 3. **The Core Problem Discovered**
Through extensive testing, we discovered that countermodels often had:
- Premises that evaluated to false (when they should be true)
- Conclusions that evaluated to true (when they should be false)

*Key Insight*: There was a disconnect between how constraints were generated (using Z3 formulas) and how truth was evaluated (using verifier membership). *See [new_strategies.md](new_strategies.md)*

#### 4. **The Breakthrough Understanding**
The issue wasn't that `true_at` methods approximate truthmaker semantics. Rather, the operator implementations weren't correctly implementing the recursive reduction to verifier existence conditions. The `true_at` method should recursively reduce to statements about verifier existence, maintaining consistency throughout.

*Key Learning*: We need to ensure proper recursive semantic structure, not replace the entire framework. *See [new_strategies.md](new_strategies.md) sections on PCT*

#### 5. **The Solution Path**
We developed a phased implementation plan focusing on:
- **Phase 1**: Understanding exactly where recursive reduction fails
- **Phase 2**: Implementing Skolemized Functions (SK) with correct recursion
- **Phase 3**: Adding Constraint-Based (CD) optimizations
- **Phase 4**: Developing Direct Computation Strategy (DCS)
- **Phase 5**: Integration and documentation

*See [implementation_plan.md](implementation_plan.md) for details*

### Lessons Learned

#### Technical Lessons

1. **Quantifier Complexity**: Nested existential quantifiers in logical definitions create severe implementation challenges in constraint solvers.

2. **Recursive Structure is Key**: Complex logical operators must properly implement recursive reduction to base semantic conditions.

3. **Consistency is Critical**: The same semantic logic must govern both constraint generation and truth evaluation.

4. **Trade-offs are Revealing**: The reliability/coverage trade-off in different strategies revealed the fundamental tension in the implementation.

#### Philosophical Lessons

1. **Simplicity Has Costs**: While unilateral semantics is philosophically simpler, the complexity shifts to the exclusion operator.

2. **Implementation Informs Theory**: The computational challenges reveal deep insights about the logical structure.

3. **Modularity Matters**: Maintaining clean separation between syntax and semantics is both philosophically and practically important.

### What's Next

#### Current Refactoring Effort (December 2024)

We are now undertaking a new refactoring effort that applies lessons learned from the previous implementation attempts:

1. **New Target**: Refactoring the current `semantic.py` and `operators.py` (not the old versions)
2. **Key Innovation**: Simplifying to a single exclusion strategy (Skolemized) before fixing semantics
3. **Documentation**: 
   - [new_implementation.md](new_implementation.md) - Detailed phased plan for current refactor
   - [TODO_new_refactor.md](TODO_new_refactor.md) - 90 specific tasks for the new implementation

This approach prioritizes simplification and correctness over maintaining multiple strategies.

#### Previous Implementation Work

The original implementation plan targeted `semantic_old.py` and `operators_old.py`:

*Track progress in [TODO.md](TODO.md) and results in [findings.md](findings.md)*

### For Researchers

This project demonstrates:
- How computational implementation can reveal theoretical insights
- The importance of maintaining conceptual clarity while solving technical problems
- The value of systematic, phased approaches to complex problems

### For Implementers

Key takeaways:
- Always ensure your recursive structures properly reduce to base cases
- Test extensively with automated counterexample generation
- Document the journey, not just the destination

---

*Last Updated: December 2024*