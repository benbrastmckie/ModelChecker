# Development Documentation: Tools and Workflows for ModelChecker Development

[← Back to Docs](../README.md) | [Environment Setup →](ENVIRONMENT_SETUP.md) | [Testing Framework →](TESTING_FRAMEWORK.md)

## Directory Structure

```
development/
├── README.md                    # This file - development documentation hub
├── ENVIRONMENT_SETUP.md         # Development environment configuration guide
├── FEATURE_IMPLEMENTATION.md    # Guidelines for implementing new features
├── TESTING_FRAMEWORK.md         # Comprehensive testing strategy and tools
├── PACKAGE_TESTING.md           # Package installation and integration testing
├── TEST_RELEASES.md             # Test PyPI release workflow for pre-production testing
├── PYPI_RELEASE_GUIDE.md        # Official PyPI release process and automation
└── DEBUGGING_PROTOCOLS.md       # Systematic debugging approaches and tools
```

## Overview

This directory contains **development documentation** for the ModelChecker project, providing comprehensive guides for setting up development environments, implementing features, testing code, and releasing packages. These documents support both core maintainers and contributors in maintaining code quality and following consistent development practices.

The development workflow encompasses **7 key areas**: environment configuration, feature implementation, testing strategies, package validation, test releases, production releases, and debugging protocols. Each document provides detailed procedures, best practices, and practical examples.

## Development Workflow

### Getting Started

**[ENVIRONMENT_SETUP.md](ENVIRONMENT_SETUP.md)** establishes your development foundation:

- **Python Environment**: Virtual environment creation and dependency management
- **Development Installation**: Editable installation for active development
- **Tool Configuration**: IDE setup, linting, and formatting tools
- **Git Workflow**: Branching strategy and commit conventions
- **Dependency Management**: Working with pyproject.toml and requirements

### Feature Development

**[FEATURE_IMPLEMENTATION.md](FEATURE_IMPLEMENTATION.md)** guides new feature creation:

- **Architecture Integration**: Understanding the ModelChecker architecture
- **Theory Implementation**: Adding new semantic theories and operators
- **Component Development**: Extending builder, iterate, and output systems
- **API Design**: Maintaining consistency with existing interfaces
- **Documentation Requirements**: Inline documentation and user guides

### Testing Strategy

**[TESTING_FRAMEWORK.md](TESTING_FRAMEWORK.md)** ensures comprehensive quality assurance:

- **Test Organization**: Unit, integration, and end-to-end test structure
- **Theory Testing**: Countermodel and theorem verification patterns
- **Coverage Requirements**: Minimum coverage standards and measurement
- **Test Execution**: Running specific test suites with pytest
- **Continuous Integration**: GitHub Actions test automation

### Package Validation

**[PACKAGE_TESTING.md](PACKAGE_TESTING.md)** validates package installation and functionality:

- **Installation Testing**: Clean environment installation verification
- **Cross-Platform Validation**: Windows, macOS, and Linux compatibility
- **Dependency Resolution**: Ensuring all dependencies install correctly
- **CLI Verification**: Command-line interface functionality testing
- **Import Testing**: Module import and initialization validation

### Release Management

#### Test Releases

**[TEST_RELEASES.md](TEST_RELEASES.md)** enables safe pre-production testing:

- **Test PyPI Setup**: Configuring Test PyPI credentials and environment
- **Development Versions**: Creating uniquely versioned test releases
- **Test Workflow**: Build, upload, and installation testing process
- **Cross-Machine Validation**: Testing on multiple systems before production
- **Version Management**: Handling dev suffixes and version increments

#### Production Releases

**[PYPI_RELEASE_GUIDE.md](PYPI_RELEASE_GUIDE.md)** manages official releases:

- **Release Scripts**: Using run_update.py for automated releases
- **Version Semantics**: Major, minor, and patch version guidelines
- **GitHub Actions**: Automated testing and PyPI deployment
- **Release Verification**: Post-release validation procedures
- **Rollback Procedures**: Handling failed or problematic releases

### Problem Solving

**[DEBUGGING_PROTOCOLS.md](DEBUGGING_PROTOCOLS.md)** provides systematic debugging approaches:

- **Issue Identification**: Reproducing and isolating problems
- **Debugging Tools**: Using debuggers, profilers, and logging
- **Z3 Constraint Debugging**: Understanding and fixing constraint issues
- **Performance Analysis**: Identifying and resolving bottlenecks
- **Error Reporting**: Creating actionable bug reports

## Development Tools

### Scripts and Automation

Key development scripts in the Code directory:

- **`run_tests.py`**: Comprehensive test runner with flexible options
- **`run_update.py`**: Production release automation script
- **`test_update.py`**: Test PyPI release script for pre-production validation
- **`dev_cli.py`**: Development command-line interface for testing

### Configuration Files

Important configuration files:

- **`pyproject.toml`**: Package metadata and dependencies
- **`.github/workflows/release.yml`**: GitHub Actions release automation
- **`pytest.ini`** (in pyproject.toml): Test configuration and markers
- **`setup.py`** (if present): Legacy installation configuration

## Best Practices

### Code Quality Standards

- **Type Hints**: Use type annotations for all public APIs
- **Docstrings**: Follow NumPy style for all public functions and classes
- **Testing**: Write tests before or alongside feature implementation
- **Documentation**: Update relevant documentation with code changes
- **Reviews**: Request review for significant changes

### Version Management

- **Semantic Versioning**: Follow MAJOR.MINOR.PATCH conventions
- **Test First**: Always test on Test PyPI before production releases
- **Change Documentation**: Maintain CHANGELOG.md with all changes
- **Backward Compatibility**: Preserve API compatibility in minor releases

### Collaboration Guidelines

- **Issue Tracking**: Link commits to GitHub issues
- **Branch Protection**: Work in feature branches, merge via pull requests
- **Communication**: Document decisions and rationale in commit messages
- **Knowledge Sharing**: Update documentation for lessons learned

## Quick Reference

### Common Development Tasks

```bash
# Set up development environment
python -m venv venv
source venv/bin/activate  # or venv\Scripts\activate on Windows
pip install -e Code/

# Run tests
python Code/run_tests.py

# Test release to Test PyPI
python Code/test_update.py

# Production release
python Code/run_update.py

# Debug specific example
python Code/dev_cli.py path/to/example.py
```

### Release Workflow

1. **Development**: Implement and test features locally
2. **Test Release**: Upload to Test PyPI with `test_update.py`
3. **Validation**: Install from Test PyPI on different machines
4. **Production Release**: Use `run_update.py` for official release
5. **Verification**: Confirm installation from PyPI works correctly

## Troubleshooting

### Common Issues

- **Import Errors**: Check PYTHONPATH and virtual environment activation
- **Test Failures**: Verify all dependencies are installed with correct versions
- **Release Issues**: Ensure PyPI tokens are configured in environment/secrets
- **Cross-Platform Problems**: Test on target platform or use GitHub Actions

### Getting Help

- **Documentation**: Check relevant guides in this directory
- **Issue Tracker**: Search existing issues on GitHub
- **Debugging Guide**: Follow DEBUGGING_PROTOCOLS.md systematically
- **Community**: Ask questions in discussions or issues

## References

### Internal Documentation

- **[Code README](../../README.md)** - Package overview and user guide
- **[Architecture Documentation](../architecture/)** - System design and components
- **[API Reference](../api/)** - Complete API documentation
- **[Theory Documentation](../../src/model_checker/theory_lib/)** - Theory implementations

### External Resources

- **[Python Packaging Guide](https://packaging.python.org/)** - Official packaging documentation
- **[Test PyPI](https://test.pypi.org/)** - Test package repository
- **[PyPI](https://pypi.org/)** - Python Package Index
- **[GitHub Actions](https://docs.github.com/en/actions)** - CI/CD documentation

---

[← Back to Docs](../README.md) | [Environment Setup →](ENVIRONMENT_SETUP.md) | [Feature Implementation →](FEATURE_IMPLEMENTATION.md)