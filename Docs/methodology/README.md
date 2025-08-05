# Methodology Documentation: Programmatic Semantics Framework

[← Back to Docs](../README.md) | [Architecture →](ARCHITECTURE.md) | [Builder Pattern →](BUILDER.md)

## Directory Structure

```
methodology/
├── README.md                       # This file - methodology documentation hub
├── ARCHITECTURE.md                 # System design and component integration
├── BUILDER.md                      # BuildModule/BuildExample orchestration
├── SYNTAX.md                       # Language-agnostic AST conversion pipeline
├── SEMANTICS.md                    # From syntax trees to Z3 constraint generation
├── MODELS.md                       # SMT solver interaction and result interpretation
└── ITERATOR.md                     # Model iteration and the 'iterate' setting
```

## Overview

This directory contains **comprehensive documentation** about the programmatic semantic methodology that guides the ModelChecker package design and workflow. The methodology documentation is designed to be accessible to an interdisciplinary audience including logicians, linguists, computer scientists, and AI researchers - readers may have expertise in some but not all of these areas.

The methodology implements a **systematic approach** to programmatic semantics through **6 interconnected components**: system architecture, pipeline orchestration, syntax parsing, semantic interpretation, model finding, and iteration strategies. This approach separates syntactic processing from semantic interpretation, enabling support for arbitrary logical theories while maintaining a consistent computational pipeline.

The framework treats **semantic theories as executable programs**, where truth conditions become code, constraints are computations, and models are data structures. This programmatic approach allows researchers to implement and test semantic theories systematically, comparing different approaches to logical phenomena through concrete counterexamples and model generation.

## Theory Examples

### Pipeline Processing Example

The methodology transforms logical formulas through distinct stages:

```python
# 1. Input formulas (strings)
premises = ["A \\wedge B", "B \\rightarrow C"]
conclusions = ["A \\wedge C"]

# 2. Syntax parsing creates AST
# "A \\wedge B" → Sentence(operator="\\wedge", args=["A", "B"])

# 3. Semantic constraints generation
# true_at(w, "A \\wedge B") ↔ true_at(w, "A") ∧ true_at(w, "B")

# 4. Z3 solving finds countermodel
# Model: A=True, B=True, C=False at world w1
```

### Theory Implementation Pattern

```python
# Implement a semantic theory as code
class HyperintensionalSemantics(SemanticDefaults):
    def __init__(self, settings):
        # Define Z3 primitives for states and relations
        self.verify = z3.Function('verify', StateSort, SentenceSort, z3.BoolSort())
        self.falsify = z3.Function('falsify', StateSort, SentenceSort, z3.BoolSort())
    
    def true_at(self, world, sentence, evaluation_world):
        # Truth conditions as executable code
        return z3.Exists([state], 
            z3.And(
                self.part_of(state, world),
                self.verify(state, sentence)
            )
        )
```

### Model Iteration Example

```bash
# Find multiple distinct models
model-checker examples/test.py --iterate=3

# Output shows progressively different models:
# MODEL 1: Basic countermodel
# MODEL 2: Different truth value assignment
# MODEL 3: Different world structure
```

For complete implementation examples, see the [Theory Library](../../Code/src/model_checker/theory_lib/README.md).

## Subdirectories

This directory contains only methodology documentation files (no subdirectories). Each document covers a key aspect of the programmatic semantics framework:

### Core Components

- **[ARCHITECTURE.md](ARCHITECTURE.md)** - System design philosophy, component relationships, and extension points for new theories
- **[BUILDER.md](BUILDER.md)** - Pipeline orchestration through BuildModule/BuildExample, including visual flowcharts and settings management
- **[SYNTAX.md](SYNTAX.md)** - Formula parsing, AST construction, and the language-agnostic syntax processing pipeline
- **[SEMANTICS.md](SEMANTICS.md)** - Constraint generation from syntax trees, operator patterns, and theory-agnostic semantic framework
- **[MODELS.md](MODELS.md)** - SMT solver interaction, model extraction, result interpretation, and output formatting
- **[ITERATOR.md](ITERATOR.md)** - Finding multiple models, theory-specific iteration behaviors, and configuration strategies

## Documentation

### For Researchers
- **[Architecture Overview](ARCHITECTURE.md)** - System design and theory integration
- **[Theory Examples](../theory/README.md)** - Theoretical foundations
- **[Academic References](../theory/REFERENCES.md)** - Published papers

### For Theory Implementers
- **[Builder Pattern](BUILDER.md)** - Understanding the pipeline
- **[Development Guide](../../Code/docs/DEVELOPMENT.md)** - Creating new theories
- **[Theory Library](../../Code/src/model_checker/theory_lib/README.md)** - Implementation examples

### For Framework Users
- **[Usage Workflows](../usage/WORKFLOW.md)** - Practical usage patterns
- **[Getting Started](../installation/GETTING_STARTED.md)** - First steps
- **[Theory Comparison](../usage/COMPARE_THEORIES.md)** - Comparing theories
- **[Constraint Testing](../usage/CONSTRAINTS.md)** - Proving properties by absence

## Key Features

### Three-Level Methodology
- **Syntax Level** - Structural representation of logical formulas
- **Truth-Conditions Level** - Semantic interpretation rules
- **Extensions Level** - Concrete model assignments

### Programmatic Approach
- Semantic theories as executable Python classes
- Truth conditions as code methods
- Constraints as Z3 computations
- Models as structured data

### Theory-Agnostic Framework
- Customizable truth conditions via theory implementations
- Flexible state representations (bit vectors, worlds, relations)
- Theory-specific constraint generation
- Extensible operator definitions

### Modular Architecture
- Clear separation between syntax, semantics, and solving
- Theory-independent core infrastructure
- Plugin-style theory implementations
- Composable operator libraries

## References

### Primary Sources
- Fine, Kit (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Companion to Philosophy of Language
- Brast-McKie, Benjamin (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic

### Related Resources
- **[Technical Architecture](../../Code/docs/ARCHITECTURE.md)** - Implementation details
- **[API Documentation](../../Code/src/model_checker/README.md)** - Framework APIs
- **[Test Suite](../../Code/tests/README.md)** - Validation examples

---

[← Back to Docs](../README.md) | [Architecture →](ARCHITECTURE.md) | [Syntax →](SYNTAX.md)