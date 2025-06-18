# Theory Library Test Suite

This directory contains tests for the core theory library infrastructure that supports all semantic theories in the ModelChecker framework. These tests focus on cross-theory functionality rather than theory-specific implementations.

## Overview

The theory library tests verify:

- **Metadata Management**: Version tracking, citation files, license generation
- **Theory Discovery**: Automatic loading and registration of theories
- **Cross-Theory Integration**: Compatibility between different semantic theories
- **Infrastructure**: Common functionality that all theories depend on

## Test Structure

### Core Infrastructure Tests

| Test Module | Purpose | Coverage |
|-------------|---------|----------|
| `test_meta_data.py` | Metadata system functionality | Version tracking, citations, licenses |

### Running Tests

#### Via Main Test Runner (Recommended)

```bash
# Run all theory_lib tests
python test_package.py --components theory_lib

# Run with verbose output
python test_package.py --components theory_lib -v

# Run with failfast (stop on first failure)
python test_package.py --components theory_lib -x
```

#### Direct pytest Execution

```bash
# Run all theory_lib tests
pytest src/model_checker/theory_lib/tests/

# Run specific test module
pytest src/model_checker/theory_lib/tests/test_meta_data.py

# Run with detailed output
pytest src/model_checker/theory_lib/tests/ -v -s

# Run specific test class or method
pytest src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_version_update -v
```

## Theory-Specific Testing

For tests that focus on individual semantic theories and their logical properties, see:

### Logos Theory Tests

**Main Theory:**
- [logos/tests/README.md](../logos/tests/README.md) - Central logos theory testing

**Subtheory Tests:**
- [logos/subtheories/extensional/tests/README.md](../logos/subtheories/extensional/tests/README.md) - Truth-functional operators
- [logos/subtheories/modal/tests/README.md](../logos/subtheories/modal/tests/README.md) - Necessity and possibility operators  
- [logos/subtheories/constitutive/tests/README.md](../logos/subtheories/constitutive/tests/README.md) - Content relations (ground, essence, identity)
- [logos/subtheories/counterfactual/tests/README.md](../logos/subtheories/counterfactual/tests/README.md) - Counterfactual conditionals
- [logos/subtheories/relevance/tests/README.md](../logos/subtheories/relevance/tests/README.md) - Relevance logic

### Other Theory Tests

- [default/tests/README.md](../default/tests/README.md) - Default semantic theory
- [exclusion/tests/README.md](../exclusion/tests/README.md) - Exclusion semantics
- [imposition/tests/README.md](../imposition/tests/README.md) - Imposition semantics  
- [bimodal/tests/README.md](../bimodal/tests/README.md) - Bimodal temporal logic

## Test Categories

### Infrastructure Tests (This Directory)

Focus on the theory library framework itself:

```python
# Example: Testing metadata management
def test_version_consistency():
    """Verify all theories have consistent version information."""
    # Tests cross-theory version tracking
    
def test_citation_generation():
    """Verify citation files are generated correctly."""
    # Tests bibliography management across theories
```

### Theory Tests (Individual Directories)

Focus on logical properties and semantic correctness:

```python
# Example: Testing logical validity (in theory-specific directories)
def test_modal_k_axiom():
    """Verify K axiom: Box(A implies B) and Box A entail Box B."""
    # Tests theory-specific logical principles
```

## Integration with Main Test Suite

The theory library tests integrate with the broader ModelChecker test infrastructure:

### Test Runners

1. **test_package.py** (includes theory_lib tests):
   - Focuses on framework and infrastructure
   - Includes cross-theory compatibility tests
   - Tests metadata and discovery systems

2. **test_theories.py** (theory-specific):
   - Focuses on logical properties and semantic correctness
   - Tests individual theory implementations
   - Verifies example suites and logical principles

### Discovery and Execution

Tests in this directory are automatically discovered by:

- `test_package.py --components theory_lib` (primary method)
- Direct pytest execution (alternative method)
- IDE test runners (for development)

## Development Guidelines

### Adding New Infrastructure Tests

When adding tests for new theory library functionality:

1. **Create test module** in this directory following naming pattern `test_*.py`
2. **Follow existing patterns** from `test_meta_data.py`
3. **Update `__init__.py`** to export new test classes
4. **Document in this README** under appropriate section

### Test Naming Convention

- Test modules: `test_[component].py`
- Test classes: `Test[ComponentName]`
- Test methods: `test_[specific_functionality]`

### Example Structure

```python
"""
Tests for [component] functionality.
"""

import pytest
from model_checker.theory_lib.[component] import [functions]

class Test[ComponentName]:
    """Test suite for [component]."""
    
    def test_[specific_functionality](self):
        """Test description."""
        # Test implementation
        assert [condition]
```

## Common Issues and Debugging

### Import Path Issues

If tests fail with import errors:

```bash
# Ensure PYTHONPATH is set correctly when running directly
PYTHONPATH=src pytest src/model_checker/theory_lib/tests/

# Or use the main test runner which handles paths automatically
python test_package.py --components theory_lib
```

### Cross-Theory Dependencies

Some infrastructure tests may require multiple theories to be available:

- Tests verify theory discovery across all installed theories
- Metadata tests check consistency across theory versions
- Integration tests validate cross-theory compatibility

### Performance Considerations

Infrastructure tests should be lightweight and fast:

- Focus on API and integration testing rather than heavy computations
- Use mocking for external dependencies when appropriate
- Avoid running full logical model checking in infrastructure tests

## Related Documentation

- [../../TESTS.md](../../../TESTS.md) - Overall testing strategy and guide
- [../README.md](../README.md) - Theory library overview and architecture
- [../../../docs/THEORY_ARCHITECTURE.md](../../../docs/THEORY_ARCHITECTURE.md) - Standard theory structure
- Individual theory README files for theory-specific testing information

---

This testing infrastructure ensures the reliability and maintainability of the theory library framework while supporting the development of new semantic theories and the integration of existing ones.