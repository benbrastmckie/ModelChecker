# ModelChecker Architecture Documentation

[← Back to Docs](../README.md) | [Pipeline →](PIPELINE.md) | [Builder →](BUILDER.md)

## Overview

This directory provides comprehensive architectural documentation for the ModelChecker framework, explaining how components work together to transform logical formulas into semantic models. The documentation is designed for an interdisciplinary audience, using visual diagrams and clear explanations rather than code examples.

## Directory Structure

```
architecture/
├── README.md          # This file - navigation hub
├── PIPELINE.md        # Complete data flow from inputs to outputs
├── BUILDER.md         # Pipeline orchestration and coordination
├── MODELS.md          # Model structures and constraints
├── ITERATE.md         # Model iteration and discovery
├── SETTINGS.md        # Configuration hierarchy and management
├── OUTPUT.md          # Output generation and formatting
├── SYNTACTIC.md       # Formula parsing and AST construction
├── SEMANTICS.md       # Constraint generation from syntax
├── JUPYTER.md         # Interactive exploration tools (planned)
├── THEORY_LIB.md      # Theory framework architecture (planned)
└── UTILS.md           # Shared utilities and patterns (planned)
```

## System Pipeline

- **[Data Flow Pipeline](PIPELINE.md)** - Complete flow from user inputs to outputs
- **[Technical Implementation](../../Code/docs/ARCHITECTURE.md)** - Code-level architecture details

## Core Components

### Pipeline Orchestration
- **[Builder Architecture](BUILDER.md)** - Model checking workflow orchestration
  - Links to: [Technical Docs](../../Code/src/model_checker/builder/README.md)
- **[Settings Management](SETTINGS.md)** - Configuration hierarchy and precedence
  - Links to: [Technical Docs](../../Code/src/model_checker/settings/README.md)

### Model Framework
- **[Model Structure](MODELS.md)** - Semantic models and constraints
  - Links to: [Technical Docs](../../Code/src/model_checker/models/README.md)
- **[Model Iteration](ITERATE.md)** - Discovery of distinct models
  - Links to: [Technical Docs](../../Code/src/model_checker/iterate/README.md)

### Input/Output
- **[Syntax Processing](SYNTACTIC.md)** - Formula parsing and AST construction
  - Links to: [Technical Docs](../../Code/src/model_checker/syntactic/README.md)
- **[Output Generation](OUTPUT.md)** - Multi-format result production
  - Links to: [Technical Docs](../../Code/src/model_checker/output/README.md)

### Semantic Processing
- **[Semantic Framework](SEMANTICS.md)** - Constraint generation from syntax trees
  - Links to: [Technical Docs](../../Code/src/model_checker/README.md)

### Extensions (Planned)
- **Theory Framework** - Semantic theory architecture (THEORY_LIB.md planned)
  - Links to: [Theory Library](../../Code/src/model_checker/theory_lib/README.md)
- **Interactive Tools** - Notebook and exploration tools (JUPYTER.md planned)
  - Links to: [Jupyter Docs](../../Code/src/model_checker/jupyter/README.md)
- **Shared Utilities** - Common patterns and helpers (UTILS.md planned)
  - Links to: [Utils Docs](../../Code/src/model_checker/utils/README.md)

## Key Concepts

### Programmatic Semantics

The ModelChecker treats semantic theories as executable programs:
- **Truth conditions** become Z3 constraints
- **Models** are data structures
- **Semantic rules** are class methods
- **Theories** are pluggable modules

### Three-Level Architecture

1. **Syntax Level** - Formula structure and parsing
2. **Semantic Level** - Truth conditions and constraints
3. **Model Level** - Concrete interpretations and solutions

### Data Flow Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            MODEL CHECKER DATA FLOW                          │
└─────────────────────────────────────────────────────────────────────────────┘

┌──────────────────┐    ┌──────────────────┐    ┌──────────────────┐
│   User Input     │    │    Settings      │    │     Builder      │
│ • Premises       │───▶│ • Configuration  │───▶│ • Orchestration  │
│ • Conclusions    │    │ • Parameters     │    │ • Coordination   │
└──────────────────┘    └──────────────────┘    └────────┬─────────┘
                                                         │
                                                         ▼
┌──────────────────┐    ┌──────────────────┐    ┌──────────────────┐
│     Output       │    │    Z3 Solver     │    │     Theory       │
│ • Formatting     │◀───│ • Model Finding  │◀───│ • Semantics      │
│ • Display        │    │ • SAT/UNSAT      │    │ • Constraints    │
└──────────────────┘    └──────────────────┘    └──────────────────┘
                                                         ▲
                                                         │
                                                 ┌───────┴──────────┐
                                                 │      Parser      │
                                                 │ • Syntax Process │
                                                 │ • AST Generation │
                                                 └──────────────────┘
```

## Component Relationships

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         SYSTEM COMPONENT HIERARCHY                          │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                              INPUT LAYER                                    │
│                                                                             │
│  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐           │
│  │  Example Files   │  │  CLI Interface   │  │  Configuration   │           │
│  │ • .py modules    │  │ • Command args   │  │ • Settings files │           │
│  │ • Test cases     │  │ • Flags/options  │  │ • Defaults       │           │
│  └────────┬─────────┘  └─────────┬────────┘  └─────────┬────────┘           │
│           └──────────────────────┼─────────────────────┘                    │
└──────────────────────────────────┼──────────────────────────────────────────┘
                                   ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            PROCESSING LAYER                                 │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────┐       │
│  │                      Builder Pipeline                            │       │
│  │ • Orchestrates entire model checking process                     │       │
│  │ • Manages settings and configuration                             │       │
│  │ • Coordinates component interactions                             │       │
│  └──────────────────────────────┬───────────────────────────────────┘       │
│                                 ▼                                           │
│  ┌──────────────────┐   ┌──────────────────┐   ┌────────────────────┐       │
│  │ Syntactic Parser │──▶│ Semantic Engine  │──▶│ Model Generator    │       │
│  │ • Parse formulas │   │ • Apply theory   │   │ • Generate Z3      │       │
│  │ • Build AST      │   │ • Create rules   │   │ • Solve constraints│       │
│  └──────────────────┘   └──────────────────┘   └────────┬───────────┘       │
│                                                         ▼                   │
│                                                ┌──────────────────┐         │
│                                                │  Model Iterator  │         │
│                                                │ • Find multiple  │         │
│                                                │ • Track explored │         │
│                                                └────────┬─────────┘         │
└─────────────────────────────────────────────────────────┼───────────────────┘
                                                          ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                              OUTPUT LAYER                                   │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────┐       │
│  │                      Output Formatter                            │       │
│  │ • Format results based on settings                               │       │
│  │ • Apply verbosity and display options                            │       │
│  └──────────────────────────────┬───────────────────────────────────┘       │
│                                 │                                           │
│           ┌─────────────────────┴────────────────────┐                      │
│           ▼                                          ▼                      │
│  ┌──────────────────┐                      ┌──────────────────┐             │
│  │  Display Manager │                      │   File Writer    │             │
│  │ • Console output │                      │ • JSON format    │             │
│  │ • Progress bars  │                      │ • Markdown docs  │             │
│  └──────────────────┘                      │ • Jupyter .ipynb │             │
│                                            │ • Text logs      │             │
│                                            └──────────────────┘             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Design Principles

### Modularity
- Clear separation of concerns
- Pluggable theory implementations
- Composable operator libraries
- Independent component testing

### Extensibility
- Theory-agnostic core framework
- Custom operator definitions
- Flexible output formats
- Plugin architecture

### Accessibility
- Visual documentation with flowcharts
- Minimal code in conceptual docs
- Clear explanations for non-programmers
- Cross-references to technical details

## Navigation Guide

### For Researchers
- Start with [Pipeline Overview](PIPELINE.md) for system understanding
- Review [Model Structure](MODELS.md) for semantic foundations
- Explore [Theory Examples](../theory/README.md) for theoretical background

### For Developers
- Read [Builder Architecture](BUILDER.md) for orchestration patterns
- Study [Settings Management](SETTINGS.md) for configuration
- See [Technical Docs](../../Code/docs/README.md) for implementation

### For Users
- Begin with [Getting Started](../installation/GETTING_STARTED.md)
- Follow [Usage Workflows](../usage/WORKFLOW.md)
- Consult [Output Guide](OUTPUT.md) for result interpretation

## Documentation Standards

All architecture documentation follows these principles:
- **Visual First**: Use diagrams to explain concepts
- **Code Minimal**: Reserve code for technical docs
- **Cross-Referenced**: Link to related documentation
- **Accessible**: Write for interdisciplinary audience

## See Also

### Related Documentation
- **[Theory Documentation](../theory/README.md)** - Theoretical foundations
- **[Usage Documentation](../usage/README.md)** - Practical guides
- **[Installation Documentation](../installation/README.md)** - Setup instructions

### Technical Resources
- **[Code Documentation](../../Code/docs/README.md)** - Developer guides
- **[API Reference](../../Code/src/model_checker/README.md)** - Framework APIs
- **[Theory Library](../../Code/src/model_checker/theory_lib/README.md)** - Implementations

### Maintenance
- **[Documentation Standards](../maintenance/README.md)** - Documentation guidelines
- **[Architecture Decisions](../../Code/docs/DECISIONS.md)** - Design rationale

---

[← Back to Docs](../README.md) | [Pipeline →](PIPELINE.md) | [Settings →](SETTINGS.md)
