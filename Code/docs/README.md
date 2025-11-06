# ModelChecker Maintenance Standards

This directory contains comprehensive standards and guidelines for maintaining high code quality across the ModelChecker framework. The documentation is organized hierarchically to provide clear navigation from core principles to specific implementation details.

## Quick Navigation

```
docs/
├── core/                          # Foundation standards
│   ├── CODE_STANDARDS.md          # Code quality and style
│   ├── ARCHITECTURE.md            # System design patterns  
│   ├── TESTING_GUIDE.md                 # Test requirements (TDD)
│   └── DOCUMENTATION.md           # Documentation standards
│
├── development/                   # Development practices
│   ├── FEATURE_IMPLEMENTATION.md  # Feature development process
│   ├── ../core/TESTING_GUIDE.md       # Comprehensive testing guide
│   ├── DEBUGGING_PROTOCOLS.md     # Systematic debugging
│   └── ENVIRONMENT_SETUP.md       # Development environment
│
├── contracts/                     # System contracts
│   ├── ITERATOR_CONTRACTS.md      # Iterator architecture contracts
│   └── THEORY_LICENSING.md        # License inheritance guidelines
│
├── implementation/                # Development guidelines
│   ├── DEVELOPMENT_WORKFLOW.md    # Complete dev process
│   ├── REFACTORING.md             # Systematic improvement
│   ├── PERFORMANCE.md             # Optimization guidelines
│   └── ERROR_HANDLING.md          # Error management
│
├── specific/                      # Component standards
│   ├── ITERATOR.md                # Iterator implementation
│   ├── FORMULAS.md                # Formula formatting
│   ├── PACKAGES.md                # Package maintenance
│   └── UTILITIES.md               # Utility organization
│
├── quality/                       # Quality assurance
│   ├── METRICS.md                 # Quality metrics
│   ├── REVIEW_CHECKLIST.md        # Code review standards
│   ├── MANUAL_TESTING_GUIDE.md          # Manual test protocols
│   └── CONTINUOUS_IMPROVEMENT.md  # Improvement process
│
└── templates/                     # Reusable templates
    ├── theory_template.py         # Theory implementation template
    ├── examples_template.py       # Examples file template
    ├── test_template.py           # Test file template
    └── spec_template.md           # Specification template
```

## Learning Path

### 1. For New Contributors

Start with the core standards to understand fundamental principles:

1. **[core/CODE_STANDARDS.md](core/CODE_STANDARDS.md)** - Essential coding principles
2. **[core/TESTING_GUIDE.md](core/TESTING_GUIDE.md)** - Mandatory Test-Driven Development
3. **[development/ENVIRONMENT_SETUP.md](development/ENVIRONMENT_SETUP.md)** - Set up development environment
4. **[development/../core/TESTING_GUIDE.md](development/../core/TESTING_GUIDE.md)** - Comprehensive testing guide
5. **[implementation/DEVELOPMENT_WORKFLOW.md](implementation/DEVELOPMENT_WORKFLOW.md)** - Complete development process

### 2. For Code Reviewers

Focus on quality assurance and review standards:

1. **[quality/REVIEW_CHECKLIST.md](quality/REVIEW_CHECKLIST.md)** - Review criteria
2. **[quality/METRICS.md](quality/METRICS.md)** - Quality thresholds
3. **[core/ARCHITECTURE.md](core/ARCHITECTURE.md)** - Architectural patterns

### 3. For Package Maintainers

Component-specific guidelines for your package:

1. **[specific/PACKAGES.md](specific/PACKAGES.md)** - Package boundaries
2. **[specific/ITERATOR.md](specific/ITERATOR.md)** - Iterator patterns (if working on iterate)
3. **[specific/UTILITIES.md](specific/UTILITIES.md)** - Utility management

### 4. For Performance Optimization

Performance and optimization focus:

1. **[implementation/PERFORMANCE.md](implementation/PERFORMANCE.md)** - Optimization patterns
2. **[quality/METRICS.md](quality/METRICS.md)** - Performance targets
3. **[implementation/REFACTORING.md](implementation/REFACTORING.md)** - Safe optimization

## Core Principles

The ModelChecker framework follows these fundamental principles:

### 1. No Backwards Compatibility
- Clean breaks when improving code
- Complete migration in single commits
- No compatibility layers

### 2. Test-Driven Development (Mandatory)
- Write tests BEFORE implementation
- RED → GREEN → REFACTOR cycle
- No code without tests

### 3. Fail-Fast Philosophy
- Early validation of inputs
- Immediate error reporting
- User-friendly error messages

### 4. Domain Complexity Respect
- Logical reasoning is inherently complex
- Balance simplicity with correctness
- Document complexity when necessary

## Quick Reference

### File Organization

```python
# Import order (strictly enforced)
# 1. Standard library
import os
import sys
from pathlib import Path

# 2. Third-party
import z3
from typing import Dict, List

# 3. Local (relative imports preferred)
from .models import Model
from ..utils import helpers
```

### Documentation Template

```python
def function_name(param: Type) -> ReturnType:
    """Brief description (one line).
    
    Detailed explanation if needed.
    
    Args:
        param: Description of parameter.
        
    Returns:
        Description of return value.
        
    Raises:
        ExceptionType: When this happens.
    """
```

### Test Template (TDD)

```python
def test_feature_behavior():
    """Test that feature behaves correctly."""
    # Arrange
    expected = "expected_value"
    
    # Act
    result = function_under_test()
    
    # Assert
    assert result == expected, f"Expected {expected}, got {result}"
```

## Standard Categories

### Core Standards (Start Here)
Foundation principles that apply to all code:
- **CODE_STANDARDS** - Coding style, complexity, organization
- **ARCHITECTURE** - Design patterns, component boundaries
- **TESTING** - TDD requirements, test organization
- **DOCUMENTATION** - Docstrings, READMEs, comments

### Development Practices
Practical development guidance:
- **FEATURE_IMPLEMENTATION** - Feature development process
- **TESTING_FRAMEWORK** - Comprehensive testing methodology
- **DEBUGGING_PROTOCOLS** - Systematic debugging approach
- **ENVIRONMENT_SETUP** - Development environment configuration

### System Contracts
Architecture and interface contracts:
- **ITERATOR_CONTRACTS** - Iterator architecture contracts
- **THEORY_LICENSING** - License inheritance guidelines

### Implementation Guidelines
How to execute development tasks:
- **DEVELOPMENT_WORKFLOW** - Spec to deployment process
- **REFACTORING** - Systematic code improvement
- **PERFORMANCE** - Z3 optimization, benchmarks
- **ERROR_HANDLING** - Exceptions, recovery, logging

### Component-Specific Standards
Standards for specific components:
- **ITERATOR** - Constraint preservation, isomorphism
- **FORMULAS** - LaTeX notation, examples.py format
- **PACKAGES** - Package boundaries, interfaces
- **UTILITIES** - Shared vs package-specific

### Quality Assurance
Ensuring and measuring quality:
- **METRICS** - Quality thresholds, measurements
- **REVIEW_CHECKLIST** - Code review process
- **MANUAL_TESTING** - Exploratory testing
- **CONTINUOUS_IMPROVEMENT** - Feedback and evolution

## Success Metrics

Standards compliance is measured by:

- **Code Quality**: >90% type coverage, <10 cyclomatic complexity
- **Test Coverage**: >85% overall, >90% for critical paths
- **Documentation**: 100% public API coverage
- **Performance**: Meeting component-specific benchmarks
- **Review Quality**: <5% post-merge issues

## Maintenance Schedule

- **Daily**: Automated quality checks (CI/CD)
- **Weekly**: Team retrospectives, metric reviews
- **Monthly**: Standards updates, quality reports
- **Quarterly**: Major standard revisions, tool updates

## Getting Help

1. **Find the Right Standard**: Use the navigation tree above
2. **Check Templates**: Look in `templates/` for examples
3. **Review Examples**: Each standard includes good/bad examples
4. **Ask Questions**: Create issues for clarification

## Contributing to Standards

Standards evolve through:

1. **Identify Need**: Document the problem/improvement
2. **Propose Change**: Create spec with rationale
3. **Review Process**: Team review and feedback
4. **Update Standard**: Implement approved changes
5. **Communicate**: Announce to team with migration guide

## Migration from Old Structure

The maintenance documentation has been reorganized for clarity:

### Files Consolidated
- CODE_STANDARDS.md, STYLE_GUIDE.md, CODE_ORGANIZATION.md → `core/CODE_STANDARDS.md`
- TESTING_STANDARDS.md, TEST_ORGANIZATION.md → `core/TESTING_GUIDE.md`  
- ERROR_HANDLING.md, WARNINGS_AND_FIXES.md → `implementation/ERROR_HANDLING.md`
- FORMULA_FORMATTING.md, EXAMPLES_STRUCTURE.md, UNICODE_GUIDELINES.md → `specific/FORMULAS.md`

### Files Removed
- TEST_STATUS.md (snapshot data, not a standard)
- PYPI_LINK_REQUIREMENTS.md (moved to documentation guide)

### New Standards Added
- `core/DOCUMENTATION.md` - Comprehensive documentation standards
- `specific/ITERATOR.md` - Iterator implementation patterns
- `specific/PACKAGES.md` - Package-specific guidelines
- `quality/METRICS.md` - Quality metrics and thresholds
- `quality/REVIEW_CHECKLIST.md` - Code review standards
- `quality/CONTINUOUS_IMPROVEMENT.md` - Improvement process

---

*Last Updated: 2024*
*Version: 2.0 (Post-Consolidation)*
