# Quality: Quality Assurance Practices

[← Back to Docs](../README.md) | [MANUAL_TESTING →](MANUAL_TESTING.md) | [METRICS →](METRICS.md) | [REVIEW_CHECKLIST →](REVIEW_CHECKLIST.md)

## Directory Structure

```
quality/
├── MANUAL_TESTING.md              # Integration testing procedures
├── METRICS.md                     # Quality metrics and targets
└── REVIEW_CHECKLIST.md            # Code review criteria
```

## Overview

The quality directory defines quality assurance practices and standards for the ModelChecker project. These documents specify how to measure code quality, conduct thorough reviews, and perform manual testing beyond automated test suites.

Quality assurance in this project combines automated testing (covered in core standards) with manual verification, measurable quality metrics, and systematic code review. Together these practices ensure the project maintains high standards for correctness, maintainability, and performance.

Use these documents to understand quality expectations, perform comprehensive testing, measure code quality objectively, and conduct effective code reviews.

## Documents

### MANUAL_TESTING.md
- **Purpose**: Guide manual integration and acceptance testing procedures
- **Use When**: Performing end-to-end testing or validating complex scenarios
- **Key Sections**:
  - Integration testing workflows
  - Theory verification procedures
  - CLI testing patterns
  - Example-driven testing
  - Regression testing approach

### METRICS.md
- **Purpose**: Define quality metrics and acceptable thresholds
- **Use When**: Measuring code quality or setting improvement targets
- **Key Sections**:
  - Test coverage targets (>85% overall, >90% critical)
  - Type coverage requirements (>90%)
  - Cyclomatic complexity limits (<10)
  - Performance benchmarks
  - Documentation coverage

### REVIEW_CHECKLIST.md
- **Purpose**: Provide systematic code review criteria
- **Use When**: Reviewing pull requests or conducting code audits
- **Key Sections**:
  - Automated check verification
  - Code standards compliance
  - Test coverage and quality
  - Documentation completeness
  - Performance considerations
  - Breaking change assessment

## Learning Path

**Quality assurance workflow**:

1. **Before coding**: Review [METRICS.md](METRICS.md) - Understand quality targets
2. **Before PR**: Check [REVIEW_CHECKLIST.md](REVIEW_CHECKLIST.md) - Self-review your changes
3. **Before release**: Follow [MANUAL_TESTING.md](MANUAL_TESTING.md) - Comprehensive validation

## Quick Reference

### Common Tasks

- **Preparing for PR?** → Use REVIEW_CHECKLIST.md for self-review
- **Measuring quality?** → Check METRICS.md for targets and measurement tools
- **Testing integration?** → Follow MANUAL_TESTING.md procedures
- **Reviewing code?** → Apply REVIEW_CHECKLIST.md systematically
- **Improving coverage?** → See METRICS.md for coverage targets and gaps

### Quality Gates

**Before committing**:
- [ ] All automated tests pass (pytest exit code 0)
- [ ] Test coverage meets targets (>85% overall)
- [ ] Type coverage adequate (>90% of codebase)
- [ ] Code follows standards (imports, naming, error handling)

**Before PR**:
- [ ] Self-review against REVIEW_CHECKLIST.md
- [ ] Manual testing completed per MANUAL_TESTING.md
- [ ] Documentation updated
- [ ] No regression in METRICS.md measurements

**Before merge**:
- [ ] Peer review completed using REVIEW_CHECKLIST.md
- [ ] All review comments addressed
- [ ] CI/CD checks passing
- [ ] Breaking changes documented with migration guide

### Quality Metrics Targets

From [METRICS.md](METRICS.md):

- **Test Coverage**: >85% overall, >90% critical paths
- **Type Coverage**: >90% of codebase
- **Cyclomatic Complexity**: <10 per function
- **Line Length**: ~100 characters maximum
- **Documentation**: All public APIs documented

### Manual Testing Focus Areas

From [MANUAL_TESTING.md](MANUAL_TESTING.md):

- **Theory Integration**: Each theory's examples run correctly
- **CLI Workflows**: Common command sequences work end-to-end
- **Error Handling**: Invalid inputs produce clear messages
- **Edge Cases**: Boundary conditions handled gracefully
- **Performance**: Operations complete in reasonable time

## References

### Related Documentation Categories
- [Core Standards](../core/README.md) - Foundation standards including testing requirements
- [Implementation Guidelines](../implementation/README.md) - Development workflows and patterns
- [Component-Specific Standards](../specific/README.md) - Module-level quality requirements

### Testing Resources
- [Core Testing Standards](../core/TESTING.md) - TDD practices and automated testing
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - Testing in development lifecycle
- [Error Handling](../implementation/ERROR_HANDLING.md) - Validation and error reporting quality

### Code Quality
- [Code Standards](../core/CODE_STANDARDS.md) - Style requirements that impact quality
- [Refactoring Guide](../implementation/REFACTORING.md) - Improving code quality safely

[← Back to Docs](../README.md) | [MANUAL_TESTING →](MANUAL_TESTING.md)
