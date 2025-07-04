# Exclusion Theory: Three-Level Programmatic Semantics

## Overview

This directory implements exclusion theory within the ModelChecker's **three-fold programmatic semantic methodology**: **Syntax → Truth-Conditions → Extensions**. The exclusion theory provides a case study in how semantic theories requiring existential quantification interact with the three-level architecture of computational model checking.

The implementation reveals fundamental insights about information flow between syntax (sentence objects), truth-conditions (Z3 constraints), and extensions (Z3 models), particularly how different architectural patterns enable or prevent the circular information flow required by complex semantic theories.

## The Three-Level Methodology

The ModelChecker implements a systematic methodology transforming between three fundamental levels:

1. **Syntax Level**: Sentence objects, AST structures, formula representations
2. **Truth-Conditions Level**: Z3 constraints, logical requirements, semantic primitives  
3. **Extensions Level**: Z3 models, concrete interpretations, state spaces

The exclusion theory requires **circular information flow** between all three levels, making it an ideal test case for architectural approaches to programmatic semantics.

## Current Status & Key Documents

### Essential Reading

- **[FINDINGS.md](FINDINGS.md)** - Complete analysis emphasizing three-level methodology and information flow patterns
- **[Incremental Architecture Plan](attempt6_incremental/incremental_modeling.md)** - Detailed plan for maintaining circular three-level information flow
- **[Three-Level Journey](attempt6_incremental/docs/syntax_semantics.md)** - Step-by-step analysis of the syntax → truth-conditions → extensions process

### Implementation Journey

The development process uncovered that the persistent false premise issue stems from **static linear information flow** (Syntax → Truth-Conditions → Extensions) rather than the **incremental circular information flow** (Syntax ⇄ Truth-Conditions ⇄ Extensions) required by exclusion semantics.

### Current Implementation

```bash
# Run current exclusion theory implementation
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/examples.py

# Test incremental proposals (when implemented)
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/attempt6_incremental/examples.py
```

## Theoretical Significance

### For Programmatic Semantics

The exclusion theory demonstrates how **architectural patterns** in computational systems embody **methodological commitments** about the relationship between syntax, truth-conditions, and extensions. The choice between static linear and incremental circular information flow reflects deeper computational commitments about:

- The role of computational context in semantic evaluation
- The relationship between logical requirements and concrete interpretations
- The nature of truth-condition artifacts and their accessibility

### For Model Checking Architecture

The investigation reveals that some semantic theories require **persistent computational context** across all three levels of the methodology. This suggests that model checking architectures should be designed with **information flow patterns** as a first-class architectural concern.

## Future Development

This directory will be expanded as the incremental architecture is developed and tested. The three-level perspective provides a systematic framework for understanding and implementing complex semantic theories that require integration across syntax, truth-conditions, and extensions.

---

*The exclusion theory implementation exemplifies the ModelChecker's three-fold programmatic semantic methodology, demonstrating both its power and the architectural considerations needed for complex semantic theories requiring circular information flow.*