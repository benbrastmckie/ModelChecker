# Exclusion Theory: Unilateral Truthmaker Semantics

## Overview

This directory contains the implementation and evolution of exclusion theory, a unilateral truthmaker semantics developed by [Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html). The theory uses an exclusion operator as the foundation for negation, providing an alternative to bilateral semantics that tracks both verifiers and falsifiers.

## Theoretical Foundation

### Unilateral vs Bilateral Semantics

- **Bilateral Semantics**: Tracks both verifiers (states making propositions true) and falsifiers (states making propositions false)
- **Unilateral Semantics**: Tracks only verifiers, using an exclusion relation to capture negative information

### The Exclusion Operator

The exclusion operator (¬) is defined through a three-condition semantic framework:

```
A state s verifies ¬A if there exists a mapping h such that:
1. For every verifier x of A, h(x) excludes some part of x
2. For every verifier x of A, h(x) is part of s  
3. s is the minimal state satisfying conditions 1 and 2
```

This existential quantification over mappings h becomes central to both the theoretical power and implementation challenges of the framework.

## The Implementation Journey

### Phase 1: Initial Multi-Strategy Implementation (Pre-2024)

Two base strategies were developed:

1. **Strategy 1 (Original)**: Single implementation approach
2. **Strategy 2 (Multi)**: 12 different sub-strategies for handling exclusion

The multi-strategy approach included:
- Quantify Arrays (QA)
- Quantify Indices (QI, QI2)
- Skolemized Functions (SK)
- Constraint-Based (CD)
- Multi-Sort (MS) - became default
- Uninterpreted Functions (UF)
- And 6 others

### Phase 2: The False Premise Problem Emerges

Testing revealed a critical issue across all implementations:
- Models were found where premises evaluate to false
- All problematic examples involved the exclusion operator
- Examples: ¬¬A, ¬(A∧B), ¬(A∨B), DeMorgan's laws

### Phase 3: Multiple Refactoring Attempts (2024)

Four major refactoring attempts were made:

1. **Attempt 1**: Refactoring original strategy with Skolem functions
2. **Attempt 2**: Reduced semantics on multi-strategy version
3. **Attempt 3**: Various Skolem function experiments
4. **Attempt 4**: Comprehensive simplification (January 2025)

### Phase 4: Discovering the Fundamental Limitation

Through systematic investigation, we discovered:

**The false premise issue is not an implementation bug but a fundamental architectural limitation.**

#### Root Cause

1. **Skolem Function Problem**: 
   - The exclusion operator requires existential quantification (∃h)
   - Z3 creates Skolem functions during constraint generation
   - These function interpretations cannot be accessed during truth evaluation

2. **Two-Phase Architecture**:
   
   The ModelChecker uses a two-phase approach that mirrors the classical syntax-semantics distinction in logic:
   
   - **Phase 1: Constraint Generation (Syntactic)**
     - Processes syntactic structure of formulas
     - Builds logical constraints from structural requirements
     - Z3 solver finds values satisfying constraints
     - Produces a static model with fixed assignments
     - Skolem functions are created here to handle ∃h
     - Operates at the "object level" of constraint generation
   
   - **Phase 2: Truth Evaluation (Semantic)** 
     - Takes the static model from Phase 1
     - Computes semantic objects (verifier sets)
     - Evaluates truth values through satisfaction relations
     - Cannot modify or further query the Z3 solver
     - Cannot access Skolem function interpretations from Phase 1
     - Operates at the "meta level" of truth evaluation
   
   This separation creates a fundamental problem:
   - The exclusion operator requires ∃h (existential quantification)
   - In Phase 1, ∃h is a syntactic construct solved by Z3
   - In Phase 2, we need h's semantic values to compute verifiers
   - But syntactic witnesses cannot cross into semantic evaluation
   
   This mirrors philosophical tensions between:
   - Classical logic (∃h exists) vs Constructive logic (must access h)
   - Tarski's hierarchy (object language vs metalanguage)
   - Syntax (formal structure) vs Semantics (interpretation)
   
   A single-phase architecture would unify syntax and semantics, but would require fundamental framework changes.

3. **Result**:
   - Without access to the h mapping, verifiers cannot be computed correctly
   - Premises containing exclusion operators evaluate incorrectly
   - The issue persists across all implementation strategies

## Current Status

### Directory Organization

```
exclusion/
├── semantic.py, operators.py, examples.py      # Current implementation (symlinks)
├── strategy1_original/                         # Original single-strategy approach
├── strategy2_multi/                           # Multi-strategy implementation  
├── attempt1_refactor_old/                     # First refactoring attempt
├── attempt2_reduced_new/                      # Reduced semantics attempt
├── attempt3_skolem_functions/                 # Skolem experiments
├── attempt4_new_implementation/               # Latest simplification
│   ├── phase1_analysis/                       # Analysis tools
│   ├── phase2_simplified/                     # 70% code reduction
│   └── phase3_current/                        # Current production code
├── shared_resources/                          # Documentation and tools
└── archive/                                   # Historical files
```

### Key Achievements

1. **Code Simplification**: 70% reduction from multi-strategy to single strategy
2. **All Implementations Working**: 7 different approaches preserved and runnable
3. **Clear Documentation**: Comprehensive understanding of the limitation
4. **Performance**: No performance penalty from simplification

### Known Limitations

- 10 out of 32 examples have false premises
- All involve the exclusion operator
- Cannot be fixed without major architectural changes
- Well-documented and understood

## Running the Implementation

### Current Implementation
```bash
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/examples.py
```

### Historical Implementations
Each strategy and attempt can be run independently:
```bash
# Original strategies
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/strategy1_original/examples.py
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/strategy2_multi/examples.py

# Refactoring attempts  
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/attempt1_refactor_old/examples.py
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/attempt2_reduced_new/examples.py
# ... etc
```

## Future Directions

### Potential Solutions

1. **Unified Architecture**: Combine constraint generation and truth evaluation phases
2. **Constraint-Based Definition**: Explicitly enumerate all h mappings (exponential)
3. **Alternative Semantics**: Reformulate exclusion without existential quantification
4. **Extended Z3 Integration**: Capture Skolem witnesses during solving

### Research Implications

This work reveals fundamental tensions between:
- Semantic expressiveness and computational implementability
- Two-phase model checking and existential quantification
- Theoretical elegance and practical constraints

## Key Documentation

- **[FINDINGS.md](FINDINGS.md)**: Complete analysis of the implementation journey
- **[Unilateral Semantics](shared_resources/documentation/unilateral_semantics.md)**: Theoretical foundation
- **[Skolem Limitation](attempt4_new_implementation/docs/skolem_limitation.md)**: Technical explanation
- **[Implementation Findings](shared_resources/documentation/findings.md)**: Detailed test results

## References

- Bernard, J. & Champollion, L. "Unilateral Semantics" ([LingBuzz](https://ling.auf.net/lingbuzz/007730/current.html))
- Fine, K. (2017). "Truthmaker Semantics"
- Z3 Theorem Prover Documentation

---

*The exclusion theory implementation stands as a case study in the challenges of implementing philosophical logic computationally, revealing deep connections between semantic theory, automated reasoning, and software architecture.*