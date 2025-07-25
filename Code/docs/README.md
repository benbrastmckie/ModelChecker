# Development Documentation Hub

[← Back to ModelChecker](../README.md) | [Theory Library →](../src/model_checker/theory_lib/README.md) | [API Documentation →](../src/model_checker/README.md)

## Directory Structure
```
docs/
├── README.md                    # This file - development documentation hub
├── DEVELOPMENT.md               # Development workflow and testing procedures
├── ARCHITECTURE.md              # System architecture and design principles
├── INSTALLATION.md              # Installation instructions and dependencies
├── STYLE_GUIDE.md               # Python coding standards and conventions
├── TESTS.md                     # Testing methodology and framework usage
└── CLEANUP_RECOMMENDATIONS.md   # Legacy maintenance recommendations
```

## Overview

The **Development Documentation** provides comprehensive guides for contributing to, understanding, and maintaining the ModelChecker framework. This documentation serves developers, researchers implementing new theories, and maintainers working on the core framework.

The documentation covers **development workflow**, **system architecture**, **testing methodology**, and **coding standards** to ensure consistent, high-quality contributions to the ModelChecker ecosystem. Whether you're fixing bugs, adding new theories, or extending core functionality, these guides provide the foundation for effective development.

The development process emphasizes **systematic testing**, **modular design principles**, and **clear documentation standards** to maintain the framework's reliability and extensibility as it grows to support new semantic theories and research applications.

## Quick Start

```bash
# Set up development environment
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Run comprehensive tests
./run_tests.py                    # All tests
./run_tests.py --unit            # Unit tests only
./run_tests.py --examples        # Example validation

# Test specific theory
./run_tests.py logos exclusion   # Test specific theories

# Development CLI
./dev_cli.py examples/my_example.py    # Run example
./dev_cli.py -p -z examples/debug.py   # Debug with constraints
```

## Files in This Directory

### DEVELOPMENT.md
Comprehensive development workflow guide covering testing procedures, Git workflow, command usage, and common development patterns. Essential reading for anyone contributing code, implementing theories, or maintaining the framework. Includes platform-specific instructions and troubleshooting.

### ARCHITECTURE.md  
System architecture documentation explaining the modular design, component relationships, and extension points. Covers the three-layer architecture, theory integration patterns, and design principles guiding framework development. Critical for understanding system structure.

### INSTALLATION.md
Installation instructions covering dependencies, environment setup, and platform-specific requirements. Includes standard pip installation, development setup, and NixOS-specific configurations. Essential for getting started with development.

### STYLE_GUIDE.md
Python coding standards and conventions for consistent code quality across the framework. Covers naming conventions, documentation standards, import organization, and ModelChecker-specific patterns. Required reading for contributors.

### TESTS.md
Testing methodology documentation covering test organization, execution patterns, and validation procedures. Explains the dual testing system (theory tests vs package tests) and provides guidance for writing effective tests.

### CLEANUP_RECOMMENDATIONS.md
Legacy maintenance recommendations and historical cleanup notes. Contains suggestions for future improvements and technical debt management. Primarily of interest to maintainers and core developers.

## Development Workflow

### Getting Started

1. **Environment Setup**: Follow [INSTALLATION.md](INSTALLATION.md) for your platform
2. **Architecture Understanding**: Read [ARCHITECTURE.md](ARCHITECTURE.md) for system overview  
3. **Development Workflow**: Study [DEVELOPMENT.md](DEVELOPMENT.md) for testing and contribution procedures
4. **Code Standards**: Review [STYLE_GUIDE.md](STYLE_GUIDE.md) for coding conventions

### Common Development Tasks

```bash
# Theory development
./dev_cli.py -l new_theory          # Generate theory template
./run_tests.py new_theory --examples   # Test theory implementation

# Framework development  
python test_package.py --components builder settings    # Test components
python test_theories.py --theories logos exclusion      # Test theories

# Debug and analysis
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
- **[Installation Guide](INSTALLATION.md)** - Environment setup and dependencies
- **[Development Workflow](DEVELOPMENT.md)** - Testing, Git workflow, and contribution procedures
- **[Style Guide](STYLE_GUIDE.md)** - Coding standards and conventions

### For Theory Implementers  
- **[Architecture Guide](ARCHITECTURE.md)** - System design and extension points
- **[Theory Library Guide](../src/model_checker/theory_lib/README.md)** - Theory implementation patterns
- **[Testing Guide](TESTS.md)** - Validation and testing methodology

### For Core Developers
- **[Architecture Documentation](ARCHITECTURE.md)** - System design principles and component relationships
- **[Cleanup Recommendations](CLEANUP_RECOMMENDATIONS.md)** - Technical debt and improvement opportunities
- **[Development Guide](DEVELOPMENT.md)** - Advanced development workflows and debugging

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
- **MAINTENANCE.md Compliance**: All documentation follows repository standards
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
1. **Follow MAINTENANCE.md**: Adhere to documentation standards
2. **Verify Accuracy**: Ensure all examples and references are correct
3. **Test Links**: Validate all cross-references and navigation links
4. **Audience Focus**: Write for appropriate user expertise levels

## Related Resources

- **[Main Package Documentation](../README.md)** - Package overview and installation
- **[API Documentation](../src/model_checker/README.md)** - Framework API and usage patterns
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Semantic theory implementations
- **[Jupyter Integration](../src/model_checker/jupyter/README.md)** - Interactive development tools

## License

All development documentation is licensed under GPL-3.0 as part of the ModelChecker framework.

---

[← Back to ModelChecker](../README.md) | [Development Guide →](DEVELOPMENT.md) | [Architecture →](ARCHITECTURE.md) | [Installation →](INSTALLATION.md)