# IMPLEMENT: Spec Execution Guide

[← Back to Code](../README.md) | [Full Process Guide →](../docs/IMPLEMENTATION.md) | [Testing Standards →](TESTING_STANDARDS.md)

## Overview

This guide provides a **focused workflow** for implementing approved specification files. Use this document when executing `implement path/to/spec/file.md` commands.

**Purpose**: Streamlined execution of implementation plans with consistent quality standards and validation protocols.

**Relationship to IMPLEMENTATION.md**: This guide focuses on **execution**, while [IMPLEMENTATION.md](../docs/IMPLEMENTATION.md) covers the complete **planning and design process**.

## Quick Execution Workflow

### 1. Validate Specification

```bash
# Confirm spec exists and is approved
cat docs/specs/plans/00X_feature_name.md

# Verify spec contains:
# - Clear phase breakdown
# - Test requirements for each phase
# - Success criteria
# - Implementation tasks
```

### 2. Setup Implementation Branch

```bash
# Create feature branch from spec name
git checkout -b feature/spec-name

# Example:
git checkout -b feature/output-system-enhancement
```

### 3. Execute Implementation Phases

## Implementation Process

### Core Process Requirements

Each phase of implementation MUST follow this systematic approach:

1. **Research and Design Phase** (Before Implementation)
   - Analyze the current codebase structure
   - Identify all dependencies and potential impacts
   - Design the implementation approach
   - Create a detailed implementation plan
   - Document the plan in a separate spec file
   - Review and refine the plan

2. **Implementation Phase**
   - Follow the approved implementation plan
   - Use dual testing methodology throughout
   - Keep the plan updated with actual progress
   - Document any deviations or discoveries

3. **Validation Phase**
   - Run comprehensive tests
   - Verify no regressions
   - Document outcomes in findings/

### Testing Protocol

Each refactoring step MUST use BOTH testing methods to ensure comprehensive validation:

#### Method 1: Test-Driven Development (TDD) with Test Runner

1. **Write Tests First** (following TESTS.md):
   ```bash
   # Create test file BEFORE moving code
   src/model_checker/models/tests/test_component.py
   
   # Run tests to ensure they fail appropriately
   ./run_tests.py --package --components models -v
   ```

2. **Implement Changes**:
   - Move/refactor code to pass tests
   - Ensure all tests pass

3. **Run Full Test Suite**:
   ```bash
   ./run_tests.py --all
   ```

#### Method 2: Direct CLI Testing with dev_cli.py

1. **Test Individual Theories**:
   ```bash
   ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
   ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
   ```

2. **Test with Iterations** (CRITICAL for iterator regression detection):
   ```bash
   ./dev_cli.py -i 1 src/model_checker/theory_lib/logos/examples.py
   ./dev_cli.py -i 2 src/model_checker/theory_lib/logos/examples.py
   ./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py
   ```

3. **Test All Theories Systematically**:
   ```bash
   for theory in logos bimodal exclusion imposition; do
       echo "Testing $theory..."
       ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
   done
   ```

#### Success Criteria

- **Method 1**: All unit tests passing, no regressions in test suite
- **Method 2**: No warnings or AttributeErrors in output
- **Both Methods**: Consistent results before and after changes
- **No Z3 Casting Errors**: No "Symbolic expressions cannot be cast to concrete Boolean values" errors

### Debugging Philosophy

**Core Principle**: Use errors as opportunities to improve codebase quality through deep analysis and systematic improvements.

#### 1. Fail-Fast Strategy

- **Prefer deterministic failures** with helpful error messages
- **Avoid silent failures** that hide problems
- **Catch errors early** in the development cycle
- **Never mask errors** with try/except unless absolutely necessary

#### 2. Deep Root Cause Analysis

- **Trace to fundamental cause** when errors occur
- **Look for patterns** that indicate architectural issues
- **Consider improvements** to overall code quality
- **Document findings** for future reference

#### 3. Uniform High-Quality Solutions

- **Avoid cheap patches** and band-aid fixes
- **Implement systematic solutions** that benefit entire codebase
- **Remove cruft** and technical debt when discovered
- **Maintain consistency** across all components

#### Example: Iterator Constraint Issue Resolution

```python
# Problem: Iterator lost constraints due to Z3 boolean evaluation
# Root Cause: Python's implicit boolean conversion of Z3 expressions
# Solution: Explicit Z3 evaluation with proper handling

# Bad (causes implicit conversion):
if constraint:  # Python converts Z3 expr to bool
    constraints.append(constraint)

# Good (explicit Z3 evaluation):
if not z3.is_false(constraint):
    constraints.append(constraint)
```

### Update Specification Progress

After each phase:
- Mark completed tasks with ✅
- Document any deviations from original plan
- Note lessons learned or architectural discoveries
- Update timeline estimates for remaining phases

### 4. Phase Completion Protocol

After completing each phase:

```bash
# 1. Run comprehensive validation
./run_tests.py --all
grep -n '[^[:print:][:space:]]' src/  # Character validation

# 2. Commit phase with descriptive message
git add -A
git commit -m "Phase X Complete: [Brief description]

- [List key achievements]
- All tests passing
- No regressions detected

Next: Phase Y - [Next phase description]"

# 3. Push to remote
git push origin feature/spec-name
```

### 5. Documentation Updates

Throughout implementation:
- Update affected component READMEs
- Maintain cross-references
- Follow README_STANDARDS.md from this directory
- Update examples if API changes

### 6. Final Validation

Before marking implementation complete:

```bash
# Full test suite
./run_tests.py --all --verbose

# Performance check (no degradation allowed)
# Document any performance improvements

# Documentation validation
# Verify all examples in docs still work
# Check cross-references are intact
```

## Success Criteria

Implementation is complete when:
- [ ] All phases in spec marked complete
- [ ] All tests passing (both test methods)
- [ ] No performance regressions
- [ ] Documentation updated
- [ ] Spec file updated with completion status

## Common Issues and Solutions

### Z3 Boolean Evaluation Errors

```python
# WRONG - Causes "cannot cast to concrete Boolean"
if z3_expr:
    ...

# CORRECT - Explicit Z3 evaluation
if not z3.is_false(z3_expr):
    ...
```

### Import Circularity

- Move shared dependencies to separate modules
- Use proper import ordering (see CODE_ORGANIZATION.md)
- Consider interface segregation

### Test Failures After Refactoring

- Run baseline comparison before changes
- Use both testing methods to catch different issues
- Check for implicit dependencies

## Links to Detailed Guides

- **[Full Implementation Process](../docs/IMPLEMENTATION.md)** - Complete planning and design guide
- **[Testing Standards](TESTING_STANDARDS.md)** - Comprehensive testing requirements
- **[Code Standards](CODE_STANDARDS.md)** - Code quality requirements
- **[Formula Formatting](FORMULA_FORMATTING.md)** - LaTeX notation standards

## Quick Command Reference

```bash
# Testing
./run_tests.py --all                    # Full test suite
./run_tests.py component -v             # Component tests verbose
./dev_cli.py -i 3 path/to/examples.py   # CLI with iterations

# Validation
grep -n '[^[:print:][:space:]]' src/   # Bad characters
file -i filename                        # UTF-8 check

# Git workflow
git checkout -b feature/name            # New feature branch
git rebase origin/main                  # Stay current
git push -u origin feature/name         # Push with tracking
```

---

[← Back to Code](../README.md) | [Full Process Guide →](../docs/IMPLEMENTATION.md) | [Testing Standards →](TESTING_STANDARDS.md)