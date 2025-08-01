# Technical Documentation Hub

[← Back to Code](../README.md) | [General Docs →](../../Docs/README.md) | [Theory Library →](../src/model_checker/theory_lib/README.md)

## Directory Structure

```
docs/
├── README.md                       # This file - technical documentation hub
├── DEVELOPMENT.md                  # Development workflow and contribution guide
├── ARCHITECTURE.md                 # System architecture and design principles
├── EXAMPLES.md                     # Standard form for examples.py files
├── TESTS.md                        # Testing methodology and framework usage
├── TOOLS.md                        # Advanced debugging and analysis tools
└── STYLE_GUIDE.md                  # Code style quick reference
```

## Overview

The **Technical Documentation** provides comprehensive guides for contributing to, understanding, and maintaining the ModelChecker framework. This documentation serves developers, researchers implementing new theories, and maintainers working on the core framework. For general project documentation including installation and getting started, see the [General Documentation](../../Docs/README.md).

The documentation covers key areas essential for framework development:

- **Development workflow** - Git procedures, testing practices, and contribution guidelines
- **System architecture** - Component design, extension points, and design principles  
- **Testing methodology** - Comprehensive testing strategies for theories and components
- **Coding standards** - Style guides, documentation requirements, and best practices

Whether you're fixing bugs, adding new theories, or extending core functionality, these guides provide the foundation for effective development. The development process emphasizes **systematic testing**, **modular design principles**, and **clear documentation standards** to maintain the framework's reliability and extensibility as it grows to support new semantic theories and research applications.

## Development Workflow

### Getting Started

1. **Environment Setup**: 
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   ```
   Follow [INSTALLATION.md](../../Docs/INSTALLATION.md) for detailed installation instructions.

2. **Architecture Understanding**: Read [ARCHITECTURE.md](ARCHITECTURE.md) for system overview
3. **Development Workflow**: Study [DEVELOPMENT.md](DEVELOPMENT.md) for contribution procedures
4. **Code Standards**: Review [STYLE_GUIDE.md](STYLE_GUIDE.md) and [Maintenance Standards](../maintenance/README.md)

### Common Development Tasks

```bash
# Run comprehensive tests
./run_tests.py                    # All tests
./run_tests.py --unit            # Unit tests only
./run_tests.py --examples        # Example validation
./run_tests.py logos exclusion   # Test specific theories

# Theory development
./dev_cli.py -l new_theory          # Generate theory template
./run_tests.py new_theory --examples   # Test theory implementation

# Framework development
python test_package.py --components builder settings    # Test components
python test_theories.py --theories logos exclusion      # Test theories

# Debug and analysis
./dev_cli.py examples/my_example.py    # Run example
./dev_cli.py -p -z examples/complex.py    # Show constraints and Z3 output
./run_jupyter.sh                          # Interactive development
```

### Testing Strategy

The ModelChecker uses a **dual testing architecture**:

- **Theory Tests** (`./run_tests.py`): Test semantic theory implementations
- **Package Tests** (`python test_package.py`): Test framework components

See [TESTS.md](TESTS.md) for comprehensive testing documentation.

## Documentation

### For New Contributors

- **[Installation Guide](../../Docs/INSTALLATION.md)** - Environment setup and dependencies
- **[Development Workflow](DEVELOPMENT.md)** - Testing, Git workflow, and contribution procedures
- **[Style Guide](STYLE_GUIDE.md)** - Quick reference to coding standards
- **[Maintenance Standards](../maintenance/README.md)** - Comprehensive standards document
- **[Examples Standard](EXAMPLES.md)** - Standard form for examples.py files

### For Theory Implementers

- **[Architecture Guide](ARCHITECTURE.md)** - System design and extension points
- **[Theory Library Guide](../src/model_checker/theory_lib/README.md)** - Theory implementation patterns
- **[Testing Guide](TESTS.md)** - Validation and testing methodology
- **[Examples Standard](EXAMPLES.md)** - Creating standardized example files

### For Core Developers

- **[Architecture Documentation](ARCHITECTURE.md)** - System design principles and component relationships
- **[Development Guide](DEVELOPMENT.md)** - Advanced development workflows and debugging
- **[Testing Guide](TESTS.md)** - Comprehensive testing strategies and patterns

## Key Development Principles

### Modular Architecture

- **Separation of Concerns**: Core framework vs theory implementations
- **Standardized Interfaces**: Consistent APIs across all theories
- **Extension Points**: Clear patterns for adding new functionality

### Testing Philosophy

- **Comprehensive Coverage**: Both unit tests and integration tests
- **Theory Validation**: Systematic validation of logical principles
- **Regression Prevention**: Continuous testing of all components

### Documentation Standards

- **[Maintenance Standards](../maintenance/README.md) Compliance**: All documentation follows repository standards
- **Working Examples**: All code examples must be tested and functional
- **Audience Segmentation**: Documentation organized by user type and expertise level

## Contributing Guidelines

### Code Contributions

1. **Follow Style Guide**: Adhere to [STYLE_GUIDE.md](STYLE_GUIDE.md) conventions
2. **Write Tests**: Include comprehensive test coverage for new functionality
3. **Document Changes**: Update relevant documentation and examples
4. **Test Thoroughly**: Run both theory and package test suites

### Theory Contributions

1. **Use Standard Interfaces**: Implement `get_theory()`, `get_examples()`, `get_test_examples()`
2. **Follow Patterns**: Use existing theories as architectural models
3. **Provide Documentation**: Include comprehensive README and API documentation
4. **Academic Attribution**: Include proper citations and licensing

### Documentation Contributions

1. **Follow [Maintenance Standards](../maintenance/README.md)**: Adhere to documentation standards
2. **Verify Accuracy**: Ensure all examples and references are correct
3. **Test Links**: Validate all cross-references and navigation links
4. **Audience Focus**: Write for appropriate user expertise levels

## Related Resources

- **[Code Package Documentation](../README.md)** - Package overview and quick start
- **[General Documentation](../../Docs/README.md)** - Installation and getting started
- **[Tools Guide](TOOLS.md)** - Advanced debugging and analysis features
- **[API Documentation](../src/model_checker/README.md)** - Framework API and usage patterns
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Semantic theory implementations
- **[Jupyter Integration](../src/model_checker/jupyter/README.md)** - Interactive development tools

## License

All development documentation is licensed under GPL-3.0 as part of the ModelChecker framework.

---

[← Back to Code](../README.md) | [General Docs →](../../Docs/README.md) | [Development →](DEVELOPMENT.md)
