# Documentation Hub: Exclusion Theory Resources

[← Back to Exclusion](../README.md) | [User Guide →](USER_GUIDE.md) | [API Reference →](API_REFERENCE.md)

## Directory Structure

```
docs/
├── README.md          # This file - documentation hub
├── API_REFERENCE.md   # Complete technical reference
├── ARCHITECTURE.md    # Architectural patterns and design decisions
├── DATA.md            # Test data analysis and performance metrics
├── ITERATE.md         # Model iteration and countermodel generation
├── SETTINGS.md        # Configuration and parameter guide
└── USER_GUIDE.md      # User-focused tutorial and introduction
```

## Overview

The **Documentation Hub** provides centralized navigation for all exclusion theory documentation, from user tutorials to architectural deep-dives. The exclusion theory implements Bernard and Champollion's unilateral semantics through the breakthrough witness predicate architecture.

Within the ModelChecker framework, this documentation represents one of the most comprehensive theory implementations, covering the journey from the False Premise Problem to its elegant solution. The witness predicate pattern transforms existentially quantified functions into first-class model citizens, enabling complete computational support for unilateral negation.

This hub serves all audiences: new users learning unilateral semantics, developers implementing semantic theories, and researchers exploring non-classical logics.

## Navigation

- **New to unilateral semantics?** → Start with [USER_GUIDE.md](USER_GUIDE.md)
- **Need API reference?** → See [API_REFERENCE.md](API_REFERENCE.md)
- **Understanding the architecture?** → Read [ARCHITECTURE.md](ARCHITECTURE.md)
- **Implementing a semantic theory?** → Study [LESSONS_LEARNED.md](LESSONS_LEARNED.md)
- **Configuring settings?** → See [SETTINGS.md](SETTINGS.md)

## Core Documentation

### **[USER_GUIDE.md](USER_GUIDE.md)**
Accessible introduction to unilateral semantics with practical examples. Covers theoretical background, getting started, and common usage patterns.

### **[API_REFERENCE.md](API_REFERENCE.md)**
Complete API documentation including all classes, methods, operators, and code examples. Essential reference for developers.

### **[ARCHITECTURE.md](ARCHITECTURE.md)**
System design documentation covering the witness predicate pattern, two-phase architecture, and module organization. Includes key innovations and design patterns.

### **[IMPLEMENTATION_STORY.md](IMPLEMENTATION_STORY.md)**
The complete narrative of solving the False Premise Problem through nine implementation attempts. Shows how the witness predicate solution emerged.

### **[LESSONS_LEARNED.md](LESSONS_LEARNED.md)**
Practical wisdom for implementing complex semantic theories, including Z3 patterns, architectural insights, and anti-patterns to avoid.

## Additional Resources

### **[DATA.md](DATA.md)**
Analysis of formulas, operators, and test coverage across the implementation.

### **[ITERATE.md](ITERATE.md)**
Iterator support documentation for exclusion theory.

### **[SETTINGS.md](SETTINGS.md)**
Complete documentation of all settings available in exclusion theory, including example settings, general settings, and advanced iteration configuration.

## Quick Navigation by Topic

### **Theoretical Foundation**
- Unilateral semantics basics → [USER_GUIDE.md#theoretical-background](USER_GUIDE.md#theoretical-background)
- Three-condition semantics → [TECHNICAL_REFERENCE.md#semantic-conditions](TECHNICAL_REFERENCE.md#semantic-conditions)
- False Premise Problem → [IMPLEMENTATION_STORY.md#the-false-premise-problem](IMPLEMENTATION_STORY.md#the-false-premise-problem)

### **Implementation Details**
- Witness predicate pattern → [ARCHITECTURE.md#the-core-innovation-witness-predicates-as-model-citizens](ARCHITECTURE.md#the-core-innovation-witness-predicates-as-model-citizens)
- Two-phase architecture → [ARCHITECTURE.md#two-phase-processing-pattern](ARCHITECTURE.md#two-phase-processing-pattern)
- Registry pattern → [ARCHITECTURE.md#registry-pattern](ARCHITECTURE.md#registry-pattern)

### **Practical Usage**
- Basic examples → [USER_GUIDE.md#getting-started](USER_GUIDE.md#getting-started)
- API reference → [TECHNICAL_REFERENCE.md#api-reference](TECHNICAL_REFERENCE.md#api-reference)
- Code examples → [TECHNICAL_REFERENCE.md#code-examples](TECHNICAL_REFERENCE.md#code-examples)

### **Lessons and Insights**
- Z3 patterns → [LESSONS_LEARNED.md#z3smt-solver-wisdom](LESSONS_LEARNED.md#z3smt-solver-wisdom)
- Design principles → [LESSONS_LEARNED.md#design-principles](LESSONS_LEARNED.md#design-principles)
- Implementation journey → [IMPLEMENTATION_STORY.md](IMPLEMENTATION_STORY.md)

### **Configuration and Settings**
- Settings overview → [SETTINGS.md](SETTINGS.md)
- Example settings → [SETTINGS.md#example-settings](SETTINGS.md#example-settings)
- General settings → [SETTINGS.md#general-settings](SETTINGS.md#general-settings)
- Iteration settings → [SETTINGS.md#iteration-settings](SETTINGS.md#iteration-settings)

## Documentation

### For New Users

- **[User Guide](USER_GUIDE.md)** - Start here! Tutorial introduction to unilateral semantics
- **[Settings Guide](SETTINGS.md)** - Configure models and understand parameters
- **[Data Analysis](DATA.md)** - See example results and countermodels

### For Developers

- **[API Reference](API_REFERENCE.md)** - Complete technical documentation
- **[Architecture](ARCHITECTURE.md)** - Witness predicate design patterns
- **[Model Iteration](ITERATE.md)** - Finding multiple distinct models

### For Researchers

- **[Implementation Story](../history/IMPLEMENTATION_STORY.md)** - Nine-attempt journey to success
- **[Lessons Learned](../history/LESSONS_LEARNED.md)** - Architectural insights and patterns
- **[Strategy Comparison](../history/STRATEGIES.md)** - Technical analysis of approaches

## Quick Navigation

### By Learning Path

1. **Beginners**: USER_GUIDE → SETTINGS → DATA
2. **Implementers**: API_REFERENCE → ARCHITECTURE → LESSONS_LEARNED
3. **Researchers**: IMPLEMENTATION_STORY → STRATEGIES → ARCHITECTURE

### By Topic

- **Unilateral Semantics**: USER_GUIDE, DATA
- **Witness Predicates**: ARCHITECTURE, API_REFERENCE
- **Model Generation**: SETTINGS, ITERATE
- **Development Journey**: IMPLEMENTATION_STORY, LESSONS_LEARNED

## References

### Implementation Files

- **[Semantic Module](../semantic.py)** - Core witness-aware semantics
- **[Operators Module](../operators.py)** - Unilateral negation implementation
- **[Examples Module](../examples.py)** - 38 comprehensive test cases

### Related Resources

- **[Exclusion Theory](../README.md)** - Main theory overview
- **[History](../history/)** - Development narrative and lessons
- **[Archives](../archive/)** - Historical implementations

---

[← Back to Exclusion](../README.md) | [User Guide →](USER_GUIDE.md) | [API Reference →](API_REFERENCE.md)