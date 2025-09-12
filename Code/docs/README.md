# Technical Documentation: Development Resource Hub

[← Back to Code](../README.md) | [Implementation Guide →](IMPLEMENTATION.md) | [Style Guide →](STYLE_GUIDE.md) | [General Docs →](../../Docs/README.md)

## Directory Structure

```
docs/
├── README.md                       # This file - technical documentation hub
├── IMPLEMENTATION.md                # Complete feature development process guide
├── STYLE_GUIDE.md                  # Quick reference to coding and documentation standards
├── TESTS.md                        # Comprehensive testing procedures and methodologies
├── DEVELOPMENT.md                  # Development workflow and environment setup
├── ARCHITECTURE.md                 # System architecture and design principles
├── EXAMPLES.md                     # Standard form for examples.py files
├── TOOLS.md                        # Advanced debugging and analysis tools
├── LICENSE_INHERITANCE.md          # Guidelines for theory-based derivative works
└── INTERACTIVE_SAVE.md             # Interactive save mode documentation
```

## Overview

The **Technical Documentation Hub** provides comprehensive development resources for the ModelChecker framework, serving developers implementing new features, researchers adding semantic theories, and maintainers working on core framework components.

**Purpose**: This documentation collection enables systematic, high-quality development through structured processes, comprehensive testing methodologies, and clear coding standards. Following the principles outlined in [Maintenance Documentation](../../Docs/maintenance/README.md), these guides ensure consistent, maintainable contributions to the framework.

**Key Coverage Areas**:
- **[Implementation Process](IMPLEMENTATION.md)** - Complete feature development workflow with test-driven development protocols
- **[Coding Standards](STYLE_GUIDE.md)** - Quick reference for style, documentation, and quality standards
- **[Testing Methodology](TESTS.md)** - Comprehensive testing strategies for theories and framework components
- **[Development Environment](DEVELOPMENT.md)** - Environment setup, workflow procedures, and contribution guidelines
- **[System Architecture](ARCHITECTURE.md)** - Framework design principles, component relationships, and extension points

**Integration with Project Standards**: All documentation follows the comprehensive standards defined in [Maintenance Documentation](../../Docs/maintenance/README.md), ensuring consistency across the entire ModelChecker project ecosystem.

## Feature Implementation Workflow

### Quick Start Guide

For implementing new ModelChecker features, follow this systematic approach:

1. **Environment Setup**: 
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   ```
   Complete setup following [Installation Guide](../../Docs/installation/README.md).

2. **Review Essential Documentation**:
   - **[Implementation Guide](IMPLEMENTATION.md)** - Complete development process with TDD protocols
   - **[Style Guide](STYLE_GUIDE.md)** - Coding standards and quick reference
   - **[Tests Guide](TESTS.md)** - Testing procedures and best practices
   - **[Architecture Guide](ARCHITECTURE.md)** - System design and component relationships

3. **Choose Implementation Path**:
   - **New Feature**: Follow complete [Implementation Guide](IMPLEMENTATION.md) process
   - **Existing Plan**: Jump to implementation phase per [Implementation Guide § Quick Start](IMPLEMENTATION.md#quick-start-for-existing-plans)
   - **Bug Fix**: Use streamlined process with testing focus from [Tests Guide](TESTS.md)

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

## Documentation by User Type

Following [README Standards](../../Docs/maintenance/README_STANDARDS.md) for proper audience segmentation:

### For Feature Implementers

Essential guides for developing new ModelChecker features:

- **[Implementation Guide](IMPLEMENTATION.md)** - Complete development process from research to merge
- **[Style Guide](STYLE_GUIDE.md)** - Quick reference for coding and documentation standards  
- **[Tests Guide](TESTS.md)** - Comprehensive testing procedures and TDD protocols
- **[Development Guide](DEVELOPMENT.md)** - Environment setup and workflow procedures
- **[Maintenance Standards](../../Docs/maintenance/README.md)** - Complete project standards reference

### For Theory Developers

Resources for implementing new semantic theories:

- **[Theory Library Guide](../src/model_checker/theory_lib/README.md)** - Theory implementation patterns and standards
- **[Examples Standard](EXAMPLES.md)** - Creating standardized examples.py files
- **[Architecture Guide](ARCHITECTURE.md)** - System design and extension points
- **[Testing Guide](TESTS.md)** - Theory validation and testing methodology
- **[License Inheritance](LICENSE_INHERITANCE.md)** - Guidelines for theory-based derivative works

### For Framework Maintainers

Advanced documentation for core framework development:

- **[Architecture Documentation](ARCHITECTURE.md)** - System design principles and component relationships
- **[Tools Guide](TOOLS.md)** - Advanced debugging and analysis capabilities
- **[Testing Guide](TESTS.md)** - Framework testing strategies and infrastructure
- **[Development Guide](DEVELOPMENT.md)** - Advanced workflows and contribution procedures

## Usage Patterns

### Feature Development Process

Following the systematic approach outlined in [Implementation Guide](IMPLEMENTATION.md):

```bash
# 1. Create feature branch
git checkout -b feature/your-feature-name

# 2. Research phase (skip if plan exists)
# Study codebase and design implementation approach

# 3. Implementation with TDD
./run_tests.py --new-feature-tests  # Write tests first
# Implement phase by phase with testing validation

# 4. Comprehensive validation
./run_tests.py --all                # Full test suite
./run_tests.py --examples           # Example validation

# 5. Documentation updates
# Update all affected README files and guides

# 6. Prepare for merge
git rebase origin/main
git push origin feature/your-feature-name
```

### Quick Reference Commands

**Testing and Validation**:
```bash
./run_tests.py                    # All tests
./run_tests.py --unit            # Unit tests only  
./run_tests.py logos exclusion   # Test specific theories
python test_package.py --components builder settings  # Component tests
```

**Development and Debugging**:
```bash
./dev_cli.py -l new_theory          # Generate theory template
./dev_cli.py examples/my_example.py # Run example
./dev_cli.py -p -z examples/debug.py # Show constraints and Z3 output
./run_jupyter.sh                    # Interactive development
```

## Development Standards

### Code Quality Requirements

Following [Style Guide](STYLE_GUIDE.md) and [Maintenance Standards](../../Docs/maintenance/README.md):

- **UTF-8 encoding** without BOM for all files
- **LaTeX notation** in code (`\\wedge`, `\\Box`, `\\rightarrow`)  
- **Unicode symbols** in documentation for readability (∧, ∨, ¬, □, ◇)
- **No emojis** anywhere in codebase or documentation
- **Comprehensive testing** with TDD protocols

### Process Adherence

- **Test-driven development** for all new functionality
- **Phase-by-phase implementation** with user confirmation
- **Documentation updates** for all affected components  
- **Cross-platform compatibility** testing where applicable

## Contributing Guidelines

### Feature Implementation

Follow the complete process outlined in [Implementation Guide](IMPLEMENTATION.md):

1. **Research Phase**: Study codebase and identify optimal integration approaches
2. **Design Phase**: Create detailed implementation plan with TDD protocols  
3. **Implementation Phase**: Execute plan phase-by-phase with comprehensive testing
4. **Refinement Phase**: Review and improve implementation quality
5. **Documentation Phase**: Update all affected documentation throughout repository
6. **Branch Completion**: Final review and merge preparation

### Quality Standards

All contributions must meet established standards:

- **[Style Guide](STYLE_GUIDE.md)**: Coding conventions and formatting requirements
- **[Testing Standards](TESTS.md)**: Comprehensive test coverage and TDD protocols
- **[Maintenance Standards](../../Docs/maintenance/README.md)**: Documentation and code organization
- **Performance Requirements**: No regressions, maintain or improve existing benchmarks

### Theory Development

For semantic theory implementations:

1. **Standard Interfaces**: Implement required `get_theory()`, `get_examples()`, `get_test_examples()` functions
2. **Pattern Compliance**: Follow existing theory architectural patterns
3. **Documentation Requirements**: Comprehensive README following [README Standards](../../Docs/maintenance/README_STANDARDS.md)
4. **Academic Attribution**: Proper citations and theoretical background
5. **License Inheritance**: Follow [LICENSE_INHERITANCE.md](LICENSE_INHERITANCE.md) guidelines

## Related Resources

- **[Code Package Documentation](../README.md)** - Package overview and quick start
- **[General Documentation](../../Docs/README.md)** - Installation and getting started
- **[Tools Guide](TOOLS.md)** - Advanced debugging and analysis features
- **[API Documentation](../src/model_checker/README.md)** - Framework API and usage patterns
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Semantic theory implementations
- **[Jupyter Integration](../src/model_checker/jupyter/README.md)** - Interactive development tools

## License

All development documentation is licensed under GPL-3.0 as part of the ModelChecker framework.

For information about the dual licensing structure (static framework license vs inheritable theory licenses), see [LICENSE_INHERITANCE.md](LICENSE_INHERITANCE.md).

---

[← Back to Code](../README.md) | [Implementation Guide →](IMPLEMENTATION.md) | [Style Guide →](STYLE_GUIDE.md) | [General Docs →](../../Docs/README.md)
