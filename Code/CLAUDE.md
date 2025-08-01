# AI Assistant Guide: ModelChecker Framework Development

[← Back to ModelChecker](README.md) | [Development Guide →](docs/DEVELOPMENT.md) | [Maintenance Standards →](maintenance/README.md)

## Directory Structure
```
Code/
├── CLAUDE.md                    # This file - AI assistant development guide
├── README.md                    # Main package documentation
├── maintenance/README.md               # Documentation and coding standards
├── docs/                        # Development documentation
├── src/model_checker/           # Core framework implementation
└── tests/                       # Integration test suite
```

## Overview

The **AI Assistant Guide** provides comprehensive guidelines for AI agents working with the ModelChecker framework, covering **development workflows**, **code quality standards**, and **documentation practices**. This guide ensures consistent, high-quality contributions while maintaining the framework's architectural integrity and theoretical rigor.

The ModelChecker creates a **programmatic semantics framework** for implementing and comparing logical theories, with focus on **modal**, **counterfactual**, and **hyperintensional logic**. It provides tooling for defining semantic theories, testing logical principles, and finding countermodels through Z3 constraint solving.

This guide emphasizes **systematic development practices**, **comprehensive testing procedures**, and **rigorous documentation standards** to support both automated assistance and human collaboration in advancing computational logic research.

## Subdirectories

### [docs/](docs/)
Development documentation hub containing comprehensive guides for **environment setup**, **testing procedures**, **architecture documentation**, and **contribution guidelines**. See [docs/README.md](docs/README.md) for complete development resource navigation.

### [src/model_checker/](src/model_checker/)
Core framework implementation with **API documentation**, **theory library**, **component packages**, and **comprehensive test suites**. Each component includes detailed README documentation following maintenance/README.md standards.

## Code Quality Standards

### Style Guidelines

- **NO EMOJIS**: Never use emojis anywhere in the codebase, documentation, or output
- **Unicode Mathematical Symbols**: Use verified Unicode for logical operators (∧, ∨, ¬, □, ◇) only
- **LaTeX Notation**: Use LaTeX in code examples (`\\wedge`, `\\Box`, `\\rightarrow`)
- **Consistent Documentation**: Follow 9-section maintenance/README.md structure for all README files

### Character Encoding Standards

#### File Encoding Requirements
- **UTF-8 ENCODING**: All files must use UTF-8 encoding without BOM (Byte Order Mark)
- **NO CONTROL CHARACTERS**: Exclude non-printable control characters (ASCII 0-31 except tab, newline, carriage return)
- **UNICODE VALIDATION**: Verify Unicode mathematical symbols display correctly before finalizing
- **CONSISTENT TOOLS**: Use consistent text editing tools to avoid encoding conflicts

#### Quality Assurance Procedures
```bash
# Character validation
grep -n '[^[:print:][:space:]]' filename    # Check for bad characters
file -i filename                           # Verify UTF-8 encoding

# Clean up temporary files
find . -name "test_*.py" -o -name "debug_*.py" | grep -v "src/"  # Find temp files
```

## Development Guidelines

### Mathematical Symbol Usage

#### Approved Unicode Symbols
| Category | Symbol | Unicode | LaTeX Code | Usage |
|----------|--------|---------|------------|-------|
| **Logical** | ∧ | U+2227 | `\\wedge` | Conjunction |
| **Logical** | ∨ | U+2228 | `\\vee` | Disjunction |
| **Logical** | ¬ | U+00AC | `\\neg` | Negation |
| **Logical** | → | U+2192 | `\\rightarrow` | Implication |
| **Logical** | ↔ | U+2194 | `\\leftrightarrow` | Biconditional |
| **Modal** | □ | U+25A1 | `\\Box` | Necessity |
| **Modal** | ◇ | U+25C7 | `\\Diamond` | Possibility |
| **Turnstiles** | ⊨ | U+22A8 | `\\models` | Entails |
| **Turnstiles** | ⊭ | U+22AD | `\\not\\models` | Does not entail |
| **Quantifiers** | ∀ | U+2200 | `\\forall` | Universal |
| **Quantifiers** | ∃ | U+2203 | `\\exists` | Existential |

#### Symbol Usage Rules
- **Documentation**: Use Unicode symbols for readability
- **Code Examples**: Use LaTeX notation with double backslashes
- **Never**: Use ASCII substitutes (?, #, etc.) for mathematical symbols

### File Quality Assurance Checklist

#### Pre-Commit Validation
```bash
# 1. Visual inspection
# Ensure all text displays correctly in editor

# 2. Character validation  
grep -n '[^[:print:][:space:]]' filename

# 3. Encoding verification
file -i filename  # Should show: charset=utf-8

# 4. Symbol testing
# Verify Unicode symbols render in target environments

# 5. Link validation
# Test all relative links in updated documentation

# 6. Code example testing
# Verify all code examples execute correctly
```

### Temporary File Management

#### Cleanup Requirements
```bash
# Find and remove temporary files
find . -name "test_*.py" -o -name "debug_*.py" | grep -v "src/" | xargs rm -f

# Acceptable temporary file locations
src/model_checker/theory_lib/*/tests/     # Permanent test files
src/model_checker/*/tests/                # Component test files

# Prohibited temporary file locations
./test_*.py                               # Root directory
./debug_*.py                              # Root directory
./examples/temp_*.py                      # Examples directory
```

#### File Organization Standards
- **Permanent Tests**: Use designated test directories with proper structure
- **Debug Files**: Clean up immediately after debugging sessions
- **Analysis Files**: Remove temporary analysis artifacts
- **Example Files**: Use theory-specific example directories

## Documentation

### For AI Assistants
- **[Quality Standards](#code-quality-standards)** - File encoding, symbol usage, and validation procedures
- **[Development Guidelines](#development-guidelines)** - Mathematical notation and file management
- **[Quick Reference](#quick-start)** - Essential commands and workflows

### For Human Developers  
- **[Development Guide](docs/DEVELOPMENT.md)** - Comprehensive development workflow
- **[Maintenance Standards](maintenance/README.md)** - Documentation and coding standards
- **[Architecture Documentation](docs/ARCHITECTURE.md)** - System design and component relationships

### For Framework Users
- **[API Documentation](src/model_checker/README.md)** - Core framework functionality
- **[Theory Library](src/model_checker/theory_lib/README.md)** - Semantic theory implementations
- **[Jupyter Integration](src/model_checker/jupyter/README.md)** - Interactive development tools

## Interactive Learning Resources

### Theory-Specific Tutorials
- **[Logos Theory Notebooks](src/model_checker/theory_lib/logos/notebooks/README.md)** - Complete hyperintensional logic tutorial collection
- **[Exclusion Theory Notebooks](src/model_checker/theory_lib/exclusion/notebooks/README.md)** - Unilateral semantics and architectural innovations
- **[Bimodal Theory Notebooks](src/model_checker/theory_lib/bimodal/notebooks/)** - Temporal-modal reasoning examples
- **[Imposition Theory Notebooks](src/model_checker/theory_lib/imposition/notebooks/)** - Fine's imposition semantics

### Development Resources
- **[Debug Tools](src/model_checker/jupyter/debug/README.md)** - Comprehensive debugging methodology
- **[Testing Guide](docs/TESTS.md)** - Multi-level testing approach
- **[Integration Tests](tests/README.md)** - CLI and workflow validation

## Advanced Development Commands

### Theory Development
```bash
# Generate new theory from template
./dev_cli.py -l logos my_counterfactual_theory
./dev_cli.py -l my_new_theory          # Generate theory template

# Test theory implementation
./run_tests.py my_counterfactual_theory --verbose
./run_tests.py logos exclusion         # Test specific theories
./run_tests.py --examples              # Example validation only

# Debug theory constraints
./dev_cli.py -p -z examples/my_theory_test.py
./dev_cli.py examples/my_example.py    # Run example
./dev_cli.py -p -z examples/debug.py   # Debug with constraints
```

### Framework Extension
```bash
# Component testing
python test_package.py --components builder settings

# Integration testing
python tests/test_project_creation.py

# Comprehensive validation
./run_tests.py --unit --examples --package
./run_tests.py                        # All tests
./run_tests.py --unit                 # Unit tests only
```

### Interactive Development
```bash
# Launch Jupyter environment for interactive exploration
./run_jupyter.sh
```

### Documentation Development
```bash
# Validate documentation structure
grep -r "^#" docs/ src/*/README.md  # Check section headers

# Test code examples
# Manually verify all code examples execute correctly

# Cross-reference validation
# Verify all relative links work correctly
```

## References

### Implementation Documentation
- AI assistant guidelines follow maintenance/README.md standards for consistent documentation structure
- Quality assurance procedures documented with verification commands and checklists

### Related Resources
- **[Main Package Documentation](README.md)** - Package overview and installation
- **[Development Documentation Hub](docs/README.md)** - Complete development resource navigation
- **[Advanced Tools](../Docs/TOOLS.md)** - Framework debugging and analysis capabilities

## License

Part of the ModelChecker framework, licensed under GPL-3.0.

---

[← Back to ModelChecker](README.md) | [Development Guide →](docs/DEVELOPMENT.md) | [Maintenance Standards →](maintenance/README.md)
