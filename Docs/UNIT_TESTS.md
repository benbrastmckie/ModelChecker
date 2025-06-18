# Unit Testing Policy and Standards

## Overview

This document establishes the systematic testing methodology for semantic theories in the ModelChecker framework, with the logos theory implementation serving as the reference implementation for standardized testing approaches.

> **Note**: This document provides detailed testing standards. For practical testing guides and running tests, see [../TESTS.md](../TESTS.md) and [../src/model_checker/theory_lib/tests/README.md](../src/model_checker/theory_lib/tests/README.md).

## Testing Philosophy

Following the project's design philosophy outlined in CLAUDE.md, our testing approach emphasizes:

- **Fail Fast**: Tests should expose errors clearly rather than masking them with complex conditional logic
- **Deterministic Behavior**: No fallbacks or implicit conversions that could hide issues
- **Clear Data Flow**: Explicit parameter passing and error propagation
- **Root Cause Analysis**: Tests should identify structural problems, not just symptoms

## Test Categories

### 1. Example Tests (Integration Tests)

**Purpose**: Validate that the model checker produces correct results for logical examples
**Scope**: End-to-end testing of complete logical arguments
**Location**: `subtheories/*/tests/` and `tests/test_logos_examples.py`

**Characteristics**:
- Test complete model checking pipeline from formula parsing to result validation
- Use realistic logical examples that demonstrate theory capabilities
- Validate both valid arguments (no countermodel) and invalid arguments (countermodel found)
- Cover all operator types and their interactions

### 2. Unit Tests (Implementation Tests)

**Purpose**: Validate individual software components work correctly
**Scope**: Testing specific classes, methods, and functions in isolation
**Location**: `tests/` (alongside general examples)

**Characteristics**:
- Test semantic methods directly (without full model checking pipeline)
- Test operator implementations and their semantic clauses
- Test registry and loading mechanisms
- Test error conditions and edge cases
- Validate API contracts and data structures

## Test Organization Structure

```
logos/
├── tests/
│   ├── __init__.py
│   ├── test_logos_examples.py       # All unified examples
│   ├── test_semantic_methods.py     # Test LogosSemantics methods
│   ├── test_operators.py            # Test operator implementations
│   ├── test_registry.py             # Test LogosOperatorRegistry
│   ├── test_proposition.py          # Test LogosProposition
│   └── conftest.py                  # Pytest configuration and fixtures
├── subtheories/
│   ├── extensional/tests/test_extensional_examples.py
│   ├── modal/tests/test_modal_examples.py
│   ├── constitutive/tests/test_constitutive_examples.py
│   ├── counterfactual/tests/test_counterfactual_examples.py
│   └── relevance/tests/test_relevance_examples.py
```

## Test Execution Framework

### Command-Line Interface

The testing framework follows an **inclusive-by-default** approach where flags specify restrictions rather than additions. Without restricting flags, all available tests are run.

```bash
# Test everything: all examples + all unit tests across all subtheories (DEFAULT)
python test_theories.py --theories logos

# Test everything for specific subtheory: examples + unit tests
python test_theories.py --theories logos --modal
python test_theories.py --theories logos --counterfactual

# RESTRICT to examples only (removes unit tests)
python test_theories.py --theories logos --examples
python test_theories.py --theories logos --modal --examples

# RESTRICT to unit/implementation tests only (removes examples)
python test_theories.py --theories logos --package
python test_theories.py --theories logos --modal --package

# RESTRICT to specific examples by name (removes unit tests + other examples)
python test_theories.py --theories logos --examples CF_CM_1
python test_theories.py --theories logos --examples CF_CM_1 CF_TH_2 MOD_CM_3
python test_theories.py --theories logos --examples "CF_CM_*"  # Wildcard pattern

# RESTRICT to specific unit test categories (removes examples + other unit tests)
python test_theories.py --theories logos --package --operators
python test_theories.py --theories logos --package --semantics

# Multiple restrictions can be combined
python test_theories.py --theories logos --modal --examples  # Modal examples only
python test_theories.py --theories logos --counterfactual --package --operators  # CF operator tests only
```

#### Inclusive-by-Default Philosophy

The CLI design follows these principles:

1. **Maximum Coverage by Default**: Without restriction flags, run all available tests
2. **Flags as Filters**: Each flag removes/restricts rather than adds tests
3. **Intuitive Combinations**: Multiple flags create intersection (AND logic)
4. **Clear Intent**: Flag names clearly indicate what they restrict to

#### Example Name Specification

When example names are provided as arguments:

1. **Exact Match**: Test only the specified examples (restricts all others)
   - `CF_CM_1` - Tests only this specific example
   - `CF_CM_1 CF_TH_2` - Tests only these two examples

2. **Pattern Matching**: Support wildcard patterns (restricts to matches)
   - `"CF_CM_*"` - Tests all counterfactual countermodel examples
   - `"*_TH_*"` - Tests all theorem examples across subtheories
   - `"MOD_*"` - Tests all modal examples

3. **Validation**: 
   - Unknown example names produce clear error messages
   - List available examples when name not found
   - Suggest similar names for typos

4. **Subtheory Context**:
   - When combined with subtheory flags, validate examples belong to that subtheory
   - Subtheory flags restrict to that subtheory's tests

### Test Discovery and Registration

Tests are automatically discovered through:
1. **Example Tests**: Registered through subtheory example modules
2. **Unit Tests**: Discovered through pytest's standard test discovery
3. **Parametrized Testing**: Used for systematic testing of all examples and operators

## Testing Standards

### Example Test Standards

1. **Test Structure**: Each example follows `[premises, conclusions, settings]` format
2. **Naming Convention**: `{SUBTHEORY}_{TYPE}_{NUMBER}` (e.g., `CF_CM_1`, `MOD_TH_3`)
3. **Expectation Setting**: Explicit `expectation` in settings dict (True = countermodel, False = valid)
4. **Operator Dependencies**: Tests load only required subtheories for efficiency
5. **Error Messages**: Clear failure messages indicating which example failed and why

### Unit Test Standards

1. **Isolation**: Each test should work independently without external dependencies
2. **Fixtures**: Use pytest fixtures for common setup (semantics instances, etc.)
3. **Parametrization**: Use `@pytest.mark.parametrize` for testing multiple inputs
4. **Error Testing**: Include tests for expected failure conditions
5. **Coverage**: Aim for comprehensive coverage of public API methods

### Test Data Management

1. **Example Data**: Stored in subtheory `examples.py` files, imported by test files
2. **Test Fixtures**: Common test objects defined in `conftest.py`
3. **Mock Data**: Minimal test data sets for unit testing
4. **Settings**: Standard settings dictionaries for consistent test environments

### Example Module Standards

All `examples.py` files in the logos theory and its subtheories must follow these conventions:

#### Required Variable Names

1. **`unit_tests`**: Dictionary containing all examples to be passed to the testing harness
   - This variable name must be used consistently across ALL subtheories
   - Format: `unit_tests = {example_name: example_case, ...}`
   - This ensures uniform test discovery and execution
   - No other variable names should be used for the main example dictionary

#### Example Structure

```python
# In each subtheory's examples.py file:

# Individual example collections
cf_cm_examples = {
    "CF_CM_1": [premises, conclusions, settings],
    "CF_CM_2": [premises, conclusions, settings],
    # ...
}

cf_th_examples = {
    "CF_TH_1": [premises, conclusions, settings],
    "CF_TH_2": [premises, conclusions, settings],
    # ...
}

# Combined dictionary - MUST use 'unit_tests' as variable name
unit_tests = {
    **cf_cm_examples,
    **cf_th_examples,
}
```

#### Consistency Requirements

1. **Variable Naming**: All subtheory example modules MUST use `unit_tests` as the primary variable name
2. **Dictionary Format**: Examples must be dictionaries with string keys and list values
3. **Export Convention**: The `unit_tests` dictionary must be importable from the module
4. **Documentation**: Each example file should document what examples are included

This standardization ensures:
- Consistent test discovery across all theories
- Clear expectations for test harness integration
- Clean and maintainable codebase without legacy artifacts
- Uniform structure that can be extended to other theories

## Quality Assurance

### Test Coverage Requirements

- **Example Tests**: Must cover all operators in each subtheory
- **Unit Tests**: Must test all public methods of core classes
- **Error Tests**: Must test expected failure modes
- **Integration Tests**: Must test subtheory interactions

### Performance Considerations

- **Test Timeouts**: Use reasonable timeouts for model checking tests
- **Resource Limits**: Set appropriate N values to avoid exponential explosion
- **Parallel Testing**: Structure tests to support parallel execution
- **Fast Unit Tests**: Unit tests should complete quickly for rapid feedback

### Maintenance Guidelines

1. **Test Updates**: When adding operators, add corresponding tests
2. **Breaking Changes**: Update tests to match new API contracts
3. **Documentation**: Keep test documentation current with implementation
4. **Regression Testing**: Preserve tests for fixed bugs
5. **Cleanup**: Remove obsolete tests when refactoring

## Integration with Project Testing

### Compatibility with test_theories.py

The logos testing framework integrates seamlessly with the project-wide `test_theories.py` runner:
- Automatically discovered through theory registration
- Supports standard flags (`-v`, `-x`)
- Provides consistent output format
- Integrates with CI/CD pipelines

### Extension to Other Theories

This testing methodology serves as a template for other theories:
1. **Standardized Structure**: Same directory layout and naming conventions
2. **Common Test Patterns**: Reusable test patterns and fixtures
3. **Consistent CLI**: Uniform command-line interface across all theories
4. **Shared Utilities**: Common testing utilities and helper functions

## Testing Workflow

### Development Workflow

1. **Write Failing Test**: Start with a test that exposes the missing functionality
2. **Implement Feature**: Add the minimal code to make the test pass
3. **Refactor**: Improve implementation while keeping tests green
4. **Integration Test**: Add example test that uses the new feature
5. **Documentation**: Update relevant documentation

### Debugging Workflow

1. **Isolate Issue**: Use unit tests to narrow down the problem
2. **Reproduce Bug**: Create minimal test case that demonstrates the issue
3. **Fix Root Cause**: Address the underlying problem, not just symptoms
4. **Regression Test**: Add test to prevent the bug from recurring
5. **Validate Fix**: Ensure all related tests still pass

This testing policy ensures systematic, maintainable, and comprehensive testing that supports the logos theory's role as a foundation for the entire ModelChecker project's testing strategy.

## Related Documentation

- [../TESTS.md](../TESTS.md) - Complete testing guide with practical usage information
- [../src/model_checker/theory_lib/tests/README.md](../src/model_checker/theory_lib/tests/README.md) - Theory library infrastructure testing
- [../src/model_checker/theory_lib/logos/tests/README.md](../src/model_checker/theory_lib/logos/tests/README.md) - Logos theory testing documentation
- Individual theory test documentation in respective theory directories