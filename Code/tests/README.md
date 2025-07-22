# Top-Level Integration Tests

This directory contains integration tests that verify the overall functionality of the ModelChecker CLI tools and user-facing interfaces.

## Purpose

These tests differ from unit tests in that they:
- Test the complete user workflow from the command line
- Verify integration between multiple components
- Simulate actual user interactions with the tools
- Ensure the CLI scripts work correctly in real-world scenarios

## Current Tests

### test_project_creation.py
Tests the project creation functionality of `dev_cli.py`:
- Verifies that `dev_cli.py -l <theory>` creates new projects correctly
- Simulates non-interactive usage by piping responses
- Checks that the generated project has the correct structure
- Cleans up test artifacts automatically

**Usage:**
```bash
python tests/test_project_creation.py
```

## Running Tests

These integration tests can be run individually:
```bash
cd /path/to/ModelChecker/Code
python tests/test_project_creation.py
```

Or as part of the full test suite:
```bash
./run_tests.py --package
```

## Test Philosophy

These tests follow the project's fail-fast philosophy:
- They test actual command execution rather than mocking
- They verify real file system operations
- They clean up after themselves to avoid side effects
- They provide clear output about what was tested

## Adding New Integration Tests

When adding new integration tests to this directory:
1. Test user-facing CLI functionality
2. Use subprocess to execute actual commands
3. Clean up any created artifacts
4. Provide clear success/failure messages
5. Document the test purpose at the top of the file

## Relationship to Other Tests

- **Unit tests** (in `src/model_checker/*/tests/`): Test individual components in isolation
- **Theory tests** (in `src/model_checker/theory_lib/*/tests/`): Test specific semantic theories
- **Integration tests** (here): Test complete workflows and CLI interfaces

This separation ensures comprehensive coverage at all levels of the system.