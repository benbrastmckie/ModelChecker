# Exclusion Theory Documentation

Welcome to the documentation for the exclusion theory implementation. This guide provides streamlined navigation to our core documentation.

## Quick Start

- **New to unilateral semantics?** → Start with [USER_GUIDE.md](USER_GUIDE.md)
- **Need API reference?** → See [TECHNICAL_REFERENCE.md](TECHNICAL_REFERENCE.md)
- **Understanding the architecture?** → Read [ARCHITECTURE.md](ARCHITECTURE.md)
- **Implementing a semantic theory?** → Study [LESSONS_LEARNED.md](LESSONS_LEARNED.md)

## Core Documentation

### **[USER_GUIDE.md](USER_GUIDE.md)**
Accessible introduction to unilateral semantics with practical examples. Covers theoretical background, getting started, and common usage patterns.

### **[TECHNICAL_REFERENCE.md](TECHNICAL_REFERENCE.md)**
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

## Related Resources

- **Main Theory README**: [../README.md](../README.md)
- **Source Code**: [../semantic.py](../semantic.py), [../operators.py](../operators.py)
- **Examples**: [../examples.py](../examples.py)
- **Framework Wisdom**: [../../../../../../../../SEMANTIC_IMPLEMENTATION_WISDOM.md](../../../../../../../../SEMANTIC_IMPLEMENTATION_WISDOM.md)