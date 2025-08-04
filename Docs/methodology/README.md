# ModelChecker Methodology: Programmatic Semantics

[← Back to Docs](../README.md) | [Builder Pattern →](BUILDER_PATTERN.md) | [Development Guide →](../../Code/docs/DEVELOPMENT.md)

## Directory Structure

```
methodology/
├── README.md               # This file - methodology documentation hub
├── BUILDER_PATTERN.md      # BuildModule/BuildExample orchestration architecture
├── SYNTAX.md               # Language-agnostic AST conversion pipeline
├── SEMANTICS.md            # From syntax trees to Z3 constraint generation
├── MODELS.md               # SMT solver interaction and result interpretation
├── WORKFLOW.md             # Using the package effectively ✓
├── ARCHITECTURE.md         # How components fit together ✓
└── ITERATOR.md             # Model iteration and the 'iterate' setting ✓
```

## Overview

This directory contains comprehensive documentation about the programmatic semantic methodology that guides the ModelChecker package design and workflow. The methodology implements a systematic approach to modal logic model checking through four interconnected stages:

1. **Orchestration** - How BuildModule and BuildExample coordinate the entire pipeline
2. **Parsing** - Converting logical formulas from strings to structured ASTs
3. **Semantic Interpretation** - Transforming ASTs into SMT solver constraints
4. **Model Finding** - Solving constraints and interpreting results

The framework separates syntactic processing from semantic interpretation, enabling support for arbitrary logical theories while maintaining a consistent computational pipeline. This separation allows new theories to be added by implementing semantic classes without modifying the core parsing and solving infrastructure.

## Quick Navigation

### Understanding the Pipeline

The ModelChecker pipeline follows a linear flow from input formulas to model output:

1. **[BUILDER_PATTERN.md](BUILDER_PATTERN.md)** - Entry point and orchestration
   - How BuildModule loads examples and manages settings
   - BuildExample pipeline from premises/conclusions to results
   - BuildProject for generating new theory implementations

2. **[SYNTAX.md](SYNTAX.md)** - Formula parsing and AST construction
   - Language-agnostic tokenization and parsing
   - Prefix notation conversion and complexity tracking
   - Sentence lifecycle and operator resolution

3. **[SEMANTICS.md](SEMANTICS.md)** - Constraint generation from syntax
   - Theory-agnostic semantic framework
   - Proposition constraints and settings interaction
   - Operator patterns and subtheory architecture

4. **[MODELS.md](MODELS.md)** - SMT solving and interpretation
   - Z3 solver setup and state isolation
   - Model extraction and sentence interpretation
   - Output generation and visualization

### Using the Framework

- **[WORKFLOW.md](WORKFLOW.md)** - Effective package usage patterns
  - Command-line workflows and debugging
  - Theory development best practices
  - Performance optimization strategies
- **[ARCHITECTURE.md](ARCHITECTURE.md)** - Component relationships
  - System design philosophy
  - Data flow between components
  - Extension points for new theories
- **[ITERATOR.md](ITERATOR.md)** - Model iteration system
  - Finding multiple distinct models
  - Theory-specific iteration behaviors
  - Configuration and tuning

### Theory Development

- **[Examples Guide](../../Code/docs/EXAMPLES.md)** - Creating and running examples
- **[Development Guide](../../Code/docs/DEVELOPMENT.md)** - Building new theories

## Core Concepts

### Three-Level Methodology

The ModelChecker implements a three-level approach to semantic modeling:

1. **Syntax Level** - Structural representation of logical formulas
   - Parse trees capture formula structure
   - Operators identified by LaTeX notation
   - Language-agnostic processing

2. **Truth-Conditions Level** - Semantic interpretation rules
   - When formulas are true/false at evaluation points
   - Operator-specific verification/falsification conditions
   - Settings modify semantic behavior

3. **Extensions Level** - Concrete model assignments
   - Which states verify/falsify atomic propositions
   - How complex formulas derive truth from components
   - Countermodel construction

### Programmatic Semantics

The framework treats semantic theories as executable programs:

```python
# Theory as code
class MySemantics(SemanticDefaults):
    def true_at(self, world, sentence, eval_point):
        """Define when sentences are true."""
        
# Constraints as computation
constraints = generate_constraints(premises, conclusions, settings)
model = solve(constraints)

# Models as data structures
countermodel = {
    'worlds': ['w1', 'w2'],
    'extensions': {'A': {'verifiers': ['s1'], 'falsifiers': ['s2']}},
    'evaluation': {'A ∧ B': 'false at w1'}
}
```

### Theory-Agnostic Framework

The methodology supports arbitrary semantic theories through:
- Customizable truth conditions via theory implementations
- Flexible state representations (bit vectors, worlds, etc.)
- Theory-specific constraint generation
- Extensible operator definitions

Example theories include:
- **Logos**: Hyperintensional semantics with verifiers/falsifiers
- **Exclusion**: Unilateral semantics with exclusion relations
- **Imposition**: Fine's imposition theory for counterfactuals
- **Classical**: Standard possible worlds semantics

## Key Features

### Modular Architecture
- Clear separation between syntax, semantics, and solving
- Theory-independent core infrastructure
- Plugin-style theory implementations
- Composable operator libraries

### Constraint-Based Approach
- Declarative specification of semantic conditions
- Automatic constraint generation from formulas
- SMT solver finds satisfying models
- Unsat cores identify conflicts

### Extensible Design
- New operators via simple class definitions
- Custom semantic theories by extending base classes
- Configurable constraints through settings
- Multiple output formats

## Implementation Flow

### Example Processing Pipeline

```
1. Input: premises = ["A ∧ B"], conclusions = ["C"]
                        ↓
2. BuildExample initialization
   - Load operators and semantics
   - Merge settings
                        ↓
3. Syntax parsing (SYNTAX.md)
   - Tokenize: ["(", "A", "∧", "B", ")"]
   - Parse to prefix: ["∧", "A", "B"]
   - Create Sentence objects
                        ↓
4. Semantic constraints (SEMANTICS.md)
   - Frame constraints (possibility closure)
   - Proposition constraints (classical, contingent)
   - Evaluation constraints (premise true, conclusion false)
                        ↓
5. Model finding (MODELS.md)
   - Z3 solver setup
   - Constraint solving
   - Model extraction or unsat core
                        ↓
6. Result interpretation
   - Extract verifier/falsifier sets
   - Evaluate sentences in model
   - Format and display output
```

## Theory Integration

New theories integrate by implementing four key classes:

```python
# 1. Semantics - core evaluation rules
class MySemantics(SemanticDefaults):
    def __init__(self, settings):
        # Define Z3 primitives
        self.my_relation = z3.Function(...)
        
# 2. Proposition - atomic constraints
class MyProposition(PropositionDefaults):
    def proposition_constraints(self, letter):
        # Define atomic behavior
        
# 3. Model - result interpretation  
class MyModel(ModelDefaults):
    def print_states(self, output):
        # Theory-specific visualization
        
# 4. Operators - logical connectives
class MyOperator(Operator):
    def extended_verify(self, state, *args):
        # Verification conditions
```

## References

### Implementation Documentation
 **[API Reference](../../Code/src/model_checker/README.md)** - Core framework APIs
 **[Theory Library](../../Code/src/model_checker/theory_lib/README.md)** - Available theories
 **[Test Suite](../../Code/tests/README.md)** - Integration and unit tests

### Related Resources
- **[Installation Guide](../installation/README.md)** - Getting started
- **[Examples](../../Examples/)** - Sample logical arguments

---

[← Back to Docs](../README.md) | [Builder Pattern →](BUILDER_PATTERN.md) | [Development Guide →](../../Code/docs/DEVELOPMENT.md)
