# Theory Documentation: Theoretical Foundations and Research Context

[← Back to Docs](../README.md) | [References →](REFERENCES.md) | [Hyperintensional →](HYPERINTENSIONAL.md)

## Directory Structure

```
theory/
├── README.md                       # This file - theoretical foundations hub
├── HYPERINTENSIONAL.md             # Hyperintensional logic and truthmaker semantics
├── Z3_BACKGROUND.md                # Z3 SMT solver technical background
├── REFERENCES.md                   # Complete academic bibliography
└── IMPLEMENTATION.md               # Theory implementation findings and patterns
```

## Overview

This directory contains **theoretical documentation** explaining the academic foundations, research context, and implementation insights of the ModelChecker framework. These documents bridge the gap between pure theoretical logic and practical implementation, providing essential background for researchers, theory implementers, and anyone seeking to understand the deeper principles behind the framework.

The documentation covers **hyperintensional logic foundations**, **SMT solving techniques**, **comprehensive academic references**, and **implementation patterns** discovered through the development of multiple semantic theories. This theoretical grounding ensures that ModelChecker implementations remain faithful to their academic origins while providing practical tools for logical investigation.

## Theory Examples

### Understanding Hyperintensional Semantics

The theoretical foundations enable implementations that distinguish logically equivalent formulas:

```python
# Standard example following EXAMPLES.md format
from model_checker.theory_lib.logos import get_theory

theory = get_theory()

# Hyperintensional distinction example
HYP_CM_1_premises = ["A \\wedge B"]
HYP_CM_1_conclusions = ["B \\wedge A"]
HYP_CM_1_settings = {
    'N': 3,                    # Max atomic propositions
    'contingent': True,        # Allow contingent propositions
    'expectation': True        # True = expect countermodel
}
HYP_CM_1_example = [
    HYP_CM_1_premises,
    HYP_CM_1_conclusions,
    HYP_CM_1_settings
]

# In classical logic: valid (conjunction is commutative)
# In hyperintensional logic: may have countermodels due to different content

example_range = {"HYP_CM_1": HYP_CM_1_example}
semantic_theories = {"logos": theory}
```

### SMT Solving Approach

```python
# Z3 constraints represent semantic conditions
from z3 import Bool, And, Or, Not, Solver

# Truthmaker semantics encoded as SMT constraints
p = Bool('p')  # Proposition variable
v_pos = Bool('v_pos')  # Positive verifier
v_neg = Bool('v_neg')  # Negative verifier

# Bilateral satisfaction constraints
constraints = And(
    p == v_pos,      # p true iff positively verified
    Not(p) == v_neg  # ¬p true iff negatively verified
)
```

For complete implementation examples, see the [Theory Library](../../Code/src/model_checker/theory_lib/README.md).

## Subdirectories

This directory contains only documentation files (no subdirectories). Each document serves a specific purpose:

### Core Documents

- **[HYPERINTENSIONAL.md](HYPERINTENSIONAL.md)** - Comprehensive introduction to hyperintensional logic, truthmaker semantics, and their implementation in ModelChecker
- **[Z3_BACKGROUND.md](Z3_BACKGROUND.md)** - Technical background on Z3 SMT solver, constraint generation patterns, and solving strategies
- **[REFERENCES.md](REFERENCES.md)** - Complete bibliography of academic papers, including proper citations for ModelChecker usage
- **[IMPLEMENTATION.md](IMPLEMENTATION.md)** - Findings and patterns discovered through implementing multiple semantic theories

## Documentation

### For Researchers

- **[Hyperintensional Logic](HYPERINTENSIONAL.md)** - Theoretical foundations and key concepts
- **[Academic References](REFERENCES.md)** - Complete bibliography with 11 foundational papers
- **[Implementation Findings](IMPLEMENTATION.md)** - Bridge between theory and practice

### For Theory Implementers

- **[Z3 Background](Z3_BACKGROUND.md)** - SMT solving techniques and patterns
- **[Implementation Patterns](IMPLEMENTATION.md)** - Common patterns across theories
- **[Theory Library Guide](../../Code/src/model_checker/theory_lib/README.md)** - Practical implementation

### For Framework Users

- **[Getting Started](../installation/GETTING_STARTED.md)** - Practical introduction
- **[Methodology Overview](../methodology/README.md)** - How the framework operates
- **[Usage Guide](../usage/README.md)** - Working with theories

## Key Features

### Comprehensive Coverage

- **4 foundational documents** covering theory, implementation, and references
- **11 academic papers** cited with proper attribution
- **Multiple semantic theories** analyzed for common patterns
- **Bridge documentation** connecting abstract theory to concrete code

### Research Integration

- Direct citations to primary sources (Fine, Brast-McKie)
- Implementation patterns validated against theoretical requirements
- Clear attribution guidelines for academic usage
- Comprehensive bibliography for further research

### Practical Application

- Theory concepts illustrated with code examples
- SMT encoding patterns explained with Z3 constraints
- Implementation challenges and solutions documented
- Common patterns identified across multiple theories

## References

### Primary Theoretical Sources

For the complete academic bibliography including all 11 foundational papers with proper citations, see **[REFERENCES.md](REFERENCES.md)**.

Key papers include:

- Brast-McKie, Benjamin (2025) ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic
- Brast-McKie, Benjamin (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic
- Fine, Kit (2017) ["A Theory of Truthmaker Content I"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine, Kit (2017) ["A Theory of Truthmaker Content II"](https://link.springer.com/article/10.1007/s10992-016-9419-5), Journal of Philosophical Logic
- Fine, Kit (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Companion to Philosophy of Language
- Fine, Kit (2012) ["Counterfactuals without Possible Worlds"](https://doi.org/10.1086/664753), Journal of Philosophy

### Implementation Resources

- **[Theory Library](../../Code/src/model_checker/theory_lib/)** - Concrete implementations
- **[Logos Theory](../../Code/src/model_checker/theory_lib/logos/)** - Hyperintensional framework
- **[Methodology Guide](../methodology/)** - System architecture

---

[← Back to Docs](../README.md) | [References →](REFERENCES.md) | [Implementation →](IMPLEMENTATION.md)
