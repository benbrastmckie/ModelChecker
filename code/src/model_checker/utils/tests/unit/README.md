# Utils Unit Tests

## Overview

This directory contains unit tests for the utils package, covering utility functions, Z3 helpers, formatting tools, and context management. These tests ensure that all utility components work correctly in isolation and provide reliable support for the framework.

## Modules

### test_bitvector.py
**Purpose**: Tests bitvector operations and manipulations for model encoding
**Key Classes**: 
- `TestBitVector` - Tests for bitvector creation and operations
- `TestBitVectorEncoding` - Tests for encoding/decoding model states
**Key Functions**: Tests bit manipulation, state encoding, vector operations
**Dependencies**: `pytest`, `utils.bitvector`, `z3`
**Used By**: Model encoding validation

### test_context.py
**Purpose**: Tests Z3 context management and isolation
**Key Classes**: 
- `TestContextManager` - Tests for Z3 context lifecycle
- `TestContextIsolation` - Tests for context isolation between operations
**Key Functions**: Tests context creation, cleanup, scope management
**Dependencies**: `pytest`, `utils.context`, `z3`
**Used By**: Z3 isolation validation

### test_formatting.py
**Purpose**: Tests string formatting and display utilities
**Key Classes**: 
- `TestFormatting` - Tests for text formatting functions
- `TestTableFormatting` - Tests for table generation
**Key Functions**: Tests string alignment, truncation, table formatting
**Dependencies**: `pytest`, `utils.formatting`
**Used By**: Display formatting validation

### test_parsing.py
**Purpose**: Tests parsing utilities for various input formats
**Key Classes**: 
- `TestParsing` - Tests for parsing helper functions
- `TestFormulaExtraction` - Tests for extracting formulas from text
**Key Functions**: Tests tokenization, delimiter handling, format detection
**Dependencies**: `pytest`, `utils.parsing`
**Used By**: Input parsing validation

### test_types.py
**Purpose**: Tests type definitions and type checking utilities
**Key Classes**: 
- `TestTypes` - Tests for custom type definitions
- `TestTypeValidation` - Tests for runtime type checking
**Key Functions**: Tests type aliases, protocol implementations, type guards
**Dependencies**: `pytest`, `utils.types`
**Used By**: Type system validation

### test_z3_helpers.py
**Purpose**: Tests Z3 solver helper functions and utilities
**Key Classes**: 
- `TestZ3Helpers` - Tests for Z3 utility functions
- `TestSolverConfiguration` - Tests for solver setup and configuration
**Key Functions**: Tests constraint helpers, solver options, result extraction
**Dependencies**: `pytest`, `utils.z3_helpers`, `z3`
**Used By**: Z3 integration validation

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit utils

# Or directly with pytest
pytest src/model_checker/utils/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/utils/tests/unit/test_z3_helpers.py -v

# Run with debugging output
pytest src/model_checker/utils/tests/unit/test_context.py -vv -s

# Run with coverage
pytest src/model_checker/utils/tests/unit/ --cov=model_checker.utils
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Mock Z3 contexts and solvers
- Sample bitvector encodings
- Test formatting data
- Type checking examples

## Coverage

These unit tests provide comprehensive coverage of:
- Z3 context management and isolation
- Bitvector encoding for model states
- String and table formatting utilities
- Parsing helpers for various formats
- Type system and validation utilities

## Contributing

When adding new unit tests:
1. Test utility functions with various input types
2. Verify edge cases and boundary conditions
3. Test both successful operations and error handling
4. Ensure Z3-related utilities handle solver states correctly
5. Mock external dependencies where appropriate

## See Also

- [Utils Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Z3 Helpers Module](../../z3_helpers.py)
- [Types Module](../../types.py)