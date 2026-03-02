# Settings Unit Tests

## Overview

This directory contains unit tests for the settings package, which manages configuration, validation, and theory-specific settings for the ModelChecker framework. These tests ensure that configuration management, validation rules, and setting hierarchies work correctly.

## Modules

### test_settings.py
**Purpose**: Tests core settings management and configuration handling
**Key Classes**: 
- `TestSettings` - Tests for settings initialization and access
- `TestSettingsHierarchy` - Tests for settings inheritance and overrides
**Key Functions**: Tests setting loading, merging, defaults, validation
**Dependencies**: `pytest`, `settings`
**Used By**: Configuration system validation

### test_error_handling.py
**Purpose**: Tests error handling for invalid configurations
**Key Classes**: 
- `TestSettingsErrors` - Tests for configuration error detection
- `TestErrorRecovery` - Tests for graceful error handling
**Key Functions**: Tests invalid settings, type mismatches, missing required fields
**Dependencies**: `pytest`, `settings.errors`
**Used By**: Error handling validation

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit settings

# Or directly with pytest
pytest src/model_checker/settings/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/settings/tests/unit/test_settings.py -v

# Run with verbose output
pytest src/model_checker/settings/tests/unit/test_error_handling.py -vv

# Run with coverage
pytest src/model_checker/settings/tests/unit/ --cov=model_checker.settings
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Sample configuration files
- Invalid configuration examples
- Mock theory settings
- Test validation rules

## Coverage

These unit tests provide comprehensive coverage of:
- Settings initialization and loading
- Configuration validation and type checking
- Settings hierarchy and inheritance
- Default value management
- Error handling for invalid configurations

## Contributing

When adding new unit tests:
1. Test various configuration formats (dict, file, env)
2. Verify validation rules are properly enforced
3. Test settings inheritance and overrides
4. Ensure error messages are informative
5. Test both valid and invalid configuration scenarios

## See Also

- [Settings Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Configuration Examples](../../examples/)
- [Validation Rules](../../validation.py)