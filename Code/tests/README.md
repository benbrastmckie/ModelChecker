# ModelChecker Integration Test Suite

[← Back to ModelChecker](../README.md) | [Development Guide →](../docs/DEVELOPMENT.md) | [Testing Guide →](../docs/TESTS.md)

## Directory Structure

```
tests/
├── unit/                           # Fast, isolated component tests
│   ├── test_imports.py            # Import structure validation
│   └── test_ideal_architecture.py # Architecture conformance tests
├── integration/                    # Component interaction tests
│   ├── test_batch_output_integration.py
│   ├── test_build_module_interactive.py
│   ├── test_cli_interactive.py
│   └── test_model_building_sync.py
├── e2e/                           # End-to-end workflow tests
│   ├── test_project_creation.py
│   ├── test_batch_output_real.py
│   └── test_simple_output_verify.py
├── fixtures/                      # Shared test data and mocks
│   ├── example_data.py           # Standard test examples
│   └── mock_theories.py          # Mock theory implementations
├── utils/                         # Test utilities
│   ├── assertions.py             # Custom assertion functions
│   └── helpers.py                # Common test helpers
├── conftest.py                   # Pytest configuration and fixtures
└── README.md                      # This file
```

## Overview

The **Integration Test Suite** provides comprehensive validation across three levels:
- **Unit Tests**: Fast, isolated component verification
- **Integration Tests**: Component interaction and CLI functionality
- **End-to-End Tests**: Complete workflow validation with real-world scenarios

This structured approach ensures the ModelChecker framework operates correctly from both developer and user perspectives, with proper test isolation, shared fixtures, and comprehensive coverage.

## Files in This Directory

### test_project_creation.py

CLI project generation testing module validating the `dev_cli.py -l <theory>` functionality. Tests project scaffold creation, template copying, file structure validation, and automatic cleanup. Simulates non-interactive usage through piped responses and verifies generated projects have correct structure and dependencies.

## Testing Philosophy

### Integration-Level Validation

Integration tests differ from unit tests by focusing on:

- **Complete User Workflows**: Test entire command sequences from CLI invocation to result delivery
- **Cross-Component Integration**: Verify multiple framework components work together correctly
- **Real-World Simulation**: Use actual file system operations and subprocess execution
- **User Interface Validation**: Ensure CLI scripts behave correctly in production scenarios

## Test Coverage

### CLI Functionality Testing

```bash
# Project Generation Workflow
python tests/test_project_creation.py

# Tests performed:
# 1. Template theory loading and validation
# 2. New project directory creation
# 3. File copying and customization
# 4. Project structure verification
# 5. Dependency and import validation
# 6. Automatic cleanup and artifact removal
```

### Workflow Validation Scenarios

#### Project Creation Testing

- **Command**: `dev_cli.py -l logos my_new_theory`
- **Validation**: Directory structure, file contents, import functionality
- **Cleanup**: Automatic removal of test artifacts
- **Coverage**: Template copying, customization, validation

#### Non-Interactive Mode Testing

- **Method**: Piped input simulation for automated testing
- **Scenarios**: Default responses, custom project names, theory selection
- **Validation**: Correct handling of automated input streams

#### Theory and Subtheory Example Testing

The `dev_cli.py` tool can directly test theory examples without creating projects:

```bash
# Test main theory examples (use full paths)
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/logos/examples.py
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/exclusion/examples.py
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/imposition/examples.py
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/bimodal/examples.py

# Test subtheory examples (e.g., Logos subtheories)
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/logos/subtheories/extensional/examples.py
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/logos/subtheories/modal/examples.py
./dev_cli.py /path/to/Code/src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py

# Run with additional options
./dev_cli.py -p path/to/examples.py       # Show constraints
./dev_cli.py -e path/to/examples.py       # Override to make propositions non-empty
./dev_cli.py -n path/to/examples.py       # Override to make propositions non-null
```

**Note**: Theory library examples use relative imports which are automatically resolved. The framework handles the necessary Python path setup to ensure proper module importing.

## Usage Patterns

### Individual Test Execution

```bash
# Run specific integration test
cd /path/to/ModelChecker/Code
python tests/test_project_creation.py

# With verbose output
python tests/test_project_creation.py --verbose

# Test specific scenarios
python tests/test_project_creation.py --test-theory logos
```

### Comprehensive Test Integration

```bash
# Include in full test suite
./run_tests.py --package              # All package tests including integration
./run_tests.py --integration          # Integration tests only
./run_tests.py --verbose              # Detailed output across all tests

# Platform-specific testing
# On NixOS, use provided scripts for proper PYTHONPATH configuration
./run_tests.py --platform nixos
```

## Development Guidelines

### Adding New Integration Tests

When creating new integration tests:

#### 1. Test Scope Definition

```python
# Test user-facing CLI functionality
def test_cli_workflow():
    """Test complete CLI workflow from command to result."""
    # Focus on end-to-end user experience
    pass
```

#### 2. Real Execution Requirements

```python
# Use subprocess for actual command execution
import subprocess

result = subprocess.run(
    ['./dev_cli.py', '-l', 'logos', 'test_project'],
    capture_output=True,
    text=True,
    cwd=project_root
)

# Verify real file system operations
assert os.path.exists('test_project/semantic.py')
```

#### 3. Cleanup and Safety

```python
# Automatic cleanup to avoid side effects
try:
    # Test operations
    pass
finally:
    # Always clean up test artifacts
    if os.path.exists('test_project'):
        shutil.rmtree('test_project')
```

#### 4. Clear Reporting

```python
# Provide detailed success/failure messages
if test_passed:
    print(f"✓ {test_name}: Successfully validated CLI workflow")
else:
    print(f"✗ {test_name}: {specific_failure_reason}")
```

## Documentation

### For New Users

- **[Development Guide](../docs/DEVELOPMENT.md)** - Framework development workflow
- **[Testing Guide](../docs/TESTS.md)** - Comprehensive testing methodology
- **[CLI Reference](../CLAUDE.md#quick-reference)** - Command-line interface documentation

### For Developers

- **[Unit Testing](../src/model_checker/*/tests/)** - Component-level test suites
- **[Theory Testing](../src/model_checker/theory_lib/*/tests/)** - Semantic theory validation
- **[Integration Testing](#testing-philosophy)** - End-to-end workflow validation

### For Contributors

- **[Test Architecture](#testing-philosophy)** - Multi-level testing approach
- **[Development Guidelines](#development-guidelines)** - Creating new integration tests
- **[Platform Considerations](#usage-patterns)** - Cross-platform testing strategies

## Testing Architecture

### Three-Level Testing Strategy

1. **Unit Tests** (`src/model_checker/*/tests/`)

   - Individual component isolation testing
   - Fast execution and focused validation
   - Mocking and stubbing for controlled environments

2. **Theory Tests** (`src/model_checker/theory_lib/*/tests/`)

   - Semantic theory validation and correctness
   - Logic verification and countermodel testing
   - Theory-specific functionality validation

3. **Integration Tests** (this directory)
   - Complete workflow and CLI interface testing
   - Real command execution and file system operations
   - End-to-end user experience validation

### Test Coordination

All testing levels coordinate through the unified test runner:

```bash
./run_tests.py                    # All tests across all levels
./run_tests.py --unit            # Unit tests only
./run_tests.py --theories logos  # Theory tests only
./run_tests.py --package         # Integration tests only
```

## References

### Implementation Documentation

- Integration testing follows fail-fast philosophy with real execution validation
- Test cleanup and artifact management documented in individual test files

### Related Resources

- **[Main Documentation](../README.md)** - Package overview and installation
- **[Development Workflow](../docs/DEVELOPMENT.md)** - Contributing and development procedures
- **[CLI Tools](../CLAUDE.md)** - Command-line interface reference

## License

Part of the ModelChecker framework, licensed under GPL-3.0.

---

[← Back to ModelChecker](../README.md) | [Development Guide →](../docs/DEVELOPMENT.md) | [Testing Guide →](../docs/TESTS.md)
