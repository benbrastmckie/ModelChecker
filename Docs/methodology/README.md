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

### Example Pipeline

The framework orchestrates a sophisticated transformation from logical formulas to semantic models through five interconnected stages:

**1. Syntactic Analysis and Operator Discovery**

The parser receives logical formulas like `"(A \\wedge B)"` and `"(B \\boxright C)"` without prior knowledge of their operators. Through structural analysis, it discovers `\\wedge` and `\\boxright` as operators, constructs abstract syntax trees in prefix notation, and builds a dependency graph of sentence complexity. This language-agnostic approach allows the framework to support arbitrary logical languages without hardcoded operator definitions.

**2. Semantic Theory Instantiation**

Each semantic theory defines how logical operators behave through Z3 primitive functions. For truthmaker semantics, this means creating functions like `verify: State × Sentence → Bool` and establishing mereological relations like `part_of` and `fusion`. The theory specifies that a sentence is true at a world when some state-part of that world verifies it - a non-trivial condition that differs fundamentally from classical possible-worlds semantics.

**3. Recursive Constraint Generation**

The framework traverses the syntax tree, generating Z3 constraints that capture the semantic behavior of each operator. For conjunction `(A ∧ B)`, it encodes that a state verifies the conjunction if and only if it's the fusion of states that verify A and B respectively. This recursive process handles arbitrary formula complexity while respecting the compositional structure of natural language semantics.

**4. SMT Solver Model Finding**

Z3 searches for variable assignments that satisfy all generated constraints simultaneously. With N=3, this means exploring 2³=8 possible states, their mereological relationships, and their verification patterns. The solver must balance frame constraints (like fusion closure), proposition constraints (like contingency), and the specific truth conditions of the argument.

**5. Model Extraction and Interpretation**

When Z3 finds a satisfying assignment, the framework extracts concrete extensions for each semantic primitive: which states exist, how they relate mereologically, what they verify or falsify, and ultimately which sentences are true at the evaluation world. This produces either a countermodel (demonstrating invalidity) or exhausts the search space (suggesting validity within the bounded model size).

The sophistication lies not in any single stage but in their integration: syntactic flexibility enables theory comparison, semantic theories encode complex philosophical proposals as executable code, constraint generation preserves compositional structure, and model extraction provides concrete interpretations that can reveal subtle logical phenomena invisible to pen-and-paper analysis.

### Theory Implementation Pattern

```python
# Implement a semantic theory as code
class HyperintensionalSemantics(SemanticDefaults):
    def __init__(self, settings):
        # Define Z3 primitives for states and relations
        self.verify = z3.Function('verify', StateSort, SentenceSort, z3.BoolSort())
        self.falsify = z3.Function('falsify', StateSort, SentenceSort, z3.BoolSort())
        self.possible = z3.Function('possible', StateSort, z3.BoolSort())
        
        # Define frame constraints using primitives
        x, y = z3.BitVecs("x y", self.N)
        possibility_downward_closure = ForAll([x, y],
            z3.Implies(
                z3.And(self.possible(y), self.is_part_of(x, y)),
                self.possible(x)
            )
        )
        self.frame_constraints = [possibility_downward_closure]

    def is_world(self, state):
        # Worlds defined as maximal possible states
        return z3.And(
            self.possible(state),
            self.maximal(state)
        )
    
    def maximal(self, state):
        # A state is maximal if it contains all compatible states
        x = z3.BitVec("max_x", self.N)
        return ForAll(x,
            z3.Implies(
                self.compatible(x, state),
                self.is_part_of(x, state)
            )
        )
    
    def compatible(self, state_x, state_y):
        # States are compatible if their fusion is possible
        return self.possible(self.fusion(state_x, state_y))

    def true_at(self, sentence, eval_point):
        # Truth conditions as executable code
        world = eval_point["world"]
        state = z3.BitVec("state", self.N)
        return z3.Exists([state],
            z3.And(
                self.is_part_of(state, world),
                self.verify(state, sentence)
            )
        )
```

### Model Iteration Example

```console
# Test counterfactual reasoning: ¬A, A □→ C ⊢ (A ∧ B) □→ C
model-checker counterfactual_examples.py --iterate=2

# Output:
EXAMPLE CF_CM_1: there is a countermodel.

State Space:
  □, a, b, c, d, a.c (world), b.c (world), a.d (world)
  a.b, b.d, c.d, a.b.c, a.b.d, a.c.d, b.c.d, a.b.c.d (impossible)

Evaluation world: b.c

INTERPRETED PREMISES:
1. |¬A| = < {b.c}, {a, a.b.c.d} >  (True in b.c)
   |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)

2. |(A □→ C)| = < {a.c, b.c}, {a.d} >  (True in b.c)
   |A|-alternatives to b.c = {a.c}
     |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (True in a.c)

INTERPRETED CONCLUSION:
3. |((A ∧ B) □→ C)| = < ∅, {a.c, a.d, b.c} >  (False in b.c)
   |(A ∧ B)|-alternatives to b.c = {a.d}
     |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (False in a.d)

Found 2/2 distinct models.
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

- Z3 sorts as semantic primitives
- Definitions as class methods
- Truth conditions as Z3 constraints
- Semantic theories as executable code
- Models as structured data

### Theory-Agnostic Framework

- Customizable truth conditions via theory implementations
- Flexible state representations (bit vectors, worlds, relations)
- Theory-specific constraint generation
- Extensible operator definitions

### Modular Architecture

- Clear separation between syntax, semantics, solving, and interpretation
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
