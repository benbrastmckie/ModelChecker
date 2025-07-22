# Logos Theory Jupyter Notebooks

This directory contains interactive Jupyter notebooks for exploring and learning the Logos semantic theory. The notebooks provide hands-on demonstrations of hyperintensional logic, truthmaker semantics, and the modular architecture of the Logos framework.

## Overview

The Logos theory implements a unified formal language of thought with **20 logical operators** across **5 modular subtheories**. These notebooks make this complex semantic framework accessible through interactive examples, progressive tutorials, and comparative analyses.

## Notebook Collection

### Main Theory Notebook

#### [logos_demo.ipynb](logos_demo.ipynb)
**Comprehensive introduction to the Logos theory** (41 cells)

- **Theory Overview**: Introduction to hyperintensional semantics and bilateral propositions
- **Modular Architecture**: How subtheories work together in the unified framework
- **All 5 Subtheories**: Extensional, modal, constitutive, counterfactual, and relevance operators
- **Integration Examples**: Cross-subtheory logical reasoning
- **Advanced Features**: Model exploration, constraint analysis, and debugging tools
- **Comparative Analysis**: Logos vs classical logic and other semantic frameworks

**Learning Path**: Start here for a complete introduction to the theory

### Subtheory-Specific Notebooks

#### [subtheories/modal_operators_demo.ipynb](subtheories/modal_operators_demo.ipynb)
**Focused exploration of modal logic in Logos** (27 cells)

- **Hyperintensional Modality**: Beyond classical S5 modal logic
- **Necessity and Possibility**: □ and ◇ operators with truthmaker semantics
- **Counterfactual Modality**: CFBox and CFDiamond for hypothetical reasoning
- **Modal Axioms Testing**: K, T, 4, 5, B axioms in hyperintensional context
- **Content Sensitivity**: How Logos distinguishes logically equivalent necessities

**Learning Path**: After main demo, for deeper modal logic understanding

#### [subtheories/extensional_operators_demo.ipynb](subtheories/extensional_operators_demo.ipynb)
**Truth-functional logic with hyperintensional semantics** (32 cells)

- **Bilateral Propositions**: Verifiers and falsifiers for basic operators
- **Truthmaker Semantics**: How even extensional logic becomes hyperintensional
- **Classical Operators**: ¬, ∧, ∨, →, ↔, ⊤, ⊥ with fine-grained semantics
- **Logical Principles**: Testing classical theorems in hyperintensional context
- **Foundation Understanding**: How extensional operators support other subtheories

**Learning Path**: Good starting point for those new to truthmaker semantics

## Getting Started

### Prerequisites

1. **Jupyter Environment**: Ensure Jupyter is running in the ModelChecker environment
   ```bash
   ./run_jupyter.sh
   ```

2. **Theory Loading**: The notebooks automatically load the logos theory
   ```python
   from model_checker.theory_lib import logos
   theory = logos.get_theory()
   ```

3. **Interactive Functions**: High-level functions for exploration
   ```python
   from model_checker.jupyter import check_formula, find_countermodel
   from model_checker import ModelExplorer
   ```

### Recommended Learning Sequence

1. **Beginners**: Start with `logos_demo.ipynb` for overview, then explore specific subtheories
2. **Logic Students**: Begin with `extensional_operators_demo.ipynb` for foundation
3. **Modal Logic Focus**: Go directly to `modal_operators_demo.ipynb` after main demo
4. **Researchers**: Use all notebooks as reference for specific operator behaviors

## Educational Features

### Interactive Elements

- **Live Code Cells**: Modify and run examples to see immediate results
- **Model Exploration**: Interactive widgets for examining truth conditions
- **Constraint Visualization**: See Z3 constraints for complex formulas
- **Countermodel Discovery**: Find models that refute invalid arguments

### Progressive Complexity

- **Basic Examples**: Simple atomic propositions and single operators
- **Intermediate Examples**: Multi-operator formulas and logical principles
- **Advanced Examples**: Cross-subtheory reasoning and complex semantic phenomena
- **Research Examples**: Cutting-edge applications and theoretical investigations

### Self-Assessment

- **Exercise Cells**: Try-it-yourself examples with solutions
- **Challenge Problems**: More complex reasoning tasks
- **Theoretical Questions**: Conceptual understanding checks
- **Comparative Analysis**: Compare Logos with other logical systems

## Technical Details

### Notebook Structure

Each notebook follows a consistent structure:

1. **Setup and Imports**: Theory loading and utility imports
2. **Introduction**: Context and learning objectives
3. **Basic Examples**: Fundamental operator demonstrations
4. **Logical Principles**: Testing theorems and counterexamples
5. **Advanced Features**: Model exploration and debugging
6. **Exercises**: Interactive learning activities
7. **Summary**: Key takeaways and further reading

### Code Conventions

- **Theory Loading**: Consistent patterns for accessing operators
- **Example Format**: Standardized premise/conclusion structure
- **Error Handling**: Graceful handling of invalid formulas
- **Output Formatting**: Clear presentation of results

### Performance Considerations

- **Model Size**: Examples use N=3 for fast execution (adjustable)
- **Timeout Settings**: Reasonable limits for interactive use
- **Memory Usage**: Efficient theory loading and caching
- **Batch Operations**: Multiple examples processed efficiently

## Integration with ModelChecker

### Command Line Tools

```bash
# Run examples from notebooks in CLI
./dev_cli.py -p -z src/model_checker/theory_lib/logos/examples.py

# Test specific subtheory
./run_tests.py logos --modal --examples
```

### Development Workflow

```python
# Create custom examples
from model_checker import BuildExample
model = BuildExample("my_logos_example", theory)

# Debug complex formulas  
result = model.check_validity(premises, conclusions)
if not result:
    countermodel = model.get_countermodel()
    print(f"Countermodel: {countermodel}")
```

### Theory Development

- **Operator Testing**: Validate new operator implementations
- **Example Development**: Create test cases for theory validation
- **Documentation**: Generate examples for README and documentation
- **Research**: Explore theoretical questions and hypotheses

## Related Documentation

### Core Theory Documentation
- **[Main README](../README.md)**: Complete theory reference and API
- **[Architecture Guide](../../../ARCHITECTURE.md)**: Overall system design
- **[Development Guide](../../../docs/DEVELOPMENT.md)**: Development workflow

### Subtheory Documentation
- **[Extensional Subtheory](../subtheories/extensional/README.md)**: Truth-functional operators
- **[Modal Subtheory](../subtheories/modal/README.md)**: Necessity and possibility
- **[Constitutive Subtheory](../subtheories/constitutive/README.md)**: Ground and essence
- **[Counterfactual Subtheory](../subtheories/counterfactual/README.md)**: Hypothetical reasoning
- **[Relevance Subtheory](../subtheories/relevance/README.md)**: Relevance logic

### Testing and Validation
- **[Test Documentation](../tests/README.md)**: Test suite organization
- **[Unit Test Policy](../UNIT_TESTS.md)**: Testing methodology
- **[Example Statistics](../examples.py)**: Complete example collection

## Research Applications

### Academic Use Cases

- **Logic Courses**: Teaching hyperintensional semantics
- **Research Projects**: Validating logical principles and theories
- **Thesis Work**: Exploring specific aspects of truthmaker semantics
- **Comparative Studies**: Analyzing different semantic frameworks

### Computational Applications

- **Automated Reasoning**: Model checking for logical arguments
- **Knowledge Representation**: Expressing fine-grained conceptual distinctions
- **Formal Verification**: Validating complex logical systems
- **Educational Tools**: Interactive logic learning environments

## Contributing

### Adding New Notebooks

1. **Follow Structure**: Use existing notebooks as templates
2. **Include Documentation**: Clear learning objectives and explanations
3. **Test Thoroughly**: Ensure all code cells execute correctly
4. **Link Appropriately**: Update this README and related documentation

### Improving Existing Content

1. **Clarify Explanations**: Make complex concepts more accessible
2. **Add Examples**: Provide more diverse illustration cases
3. **Fix Issues**: Correct any errors or outdated information
4. **Enhance Interactivity**: Add widgets and visualization where helpful

### Feedback and Issues

- **GitHub Issues**: Report problems or suggest improvements
- **Pull Requests**: Submit enhancements and corrections
- **Discussion**: Engage in theoretical discussions about the framework
- **Educational Feedback**: Share teaching experiences and student questions

## Further Reading

### Theoretical Background

- **Fine (2017)**: "A Theory of Truthmaker Content I & II" - Foundational truthmaker semantics
- **Brast-McKie (2021)**: "Identity and Aboutness" - Hyperintensional identity principles
- **Brast-McKie (2025)**: "Counterfactual Worlds" - Counterfactual semantics framework

### Technical Resources

- **[ModelChecker Documentation](../../../README.md)**: Complete system documentation
- **[Z3 Theorem Prover](https://z3prover.github.io/)**: Underlying constraint solver
- **[Jupyter Documentation](https://jupyter.readthedocs.io/)**: Notebook environment guide

### Related Projects

- **Fine's Truthmaker Semantics**: Theoretical foundation
- **Hyperintensional Logic**: Broader research context
- **Computational Semantics**: Applied logical reasoning

---

**Note**: These notebooks are designed for both learning and research. They provide a practical introduction to one of the most sophisticated semantic frameworks for logical reasoning, making advanced theoretical concepts accessible through interactive exploration.