# Syntactic Unit Tests

## Overview

This directory contains unit tests for the syntactic package, which handles formula parsing, operator definitions, and syntactic analysis. These tests validate the parsing pipeline, operator handling, and formula transformations in isolation.

## Modules

### test_atoms.py
**Purpose**: Tests atomic formula components and propositional variables
**Key Classes**: 
- `TestAtoms` - Tests for atomic proposition handling
- `TestAtomGeneration` - Tests for generating unique atoms
**Key Functions**: Tests atom creation, validation, comparison
**Dependencies**: `pytest`, `syntactic.atoms`
**Used By**: Formula parsing validation

### test_operators.py
**Purpose**: Tests logical operator definitions and precedence
**Key Classes**: 
- `TestOperators` - Tests for operator registration and properties
- `TestOperatorPrecedence` - Tests for operator precedence rules
**Key Functions**: Tests operator parsing, arity checking, precedence ordering
**Dependencies**: `pytest`, `syntactic.operators`
**Used By**: Operator system validation

### test_sentence.py
**Purpose**: Tests sentence structure and formula composition
**Key Classes**: 
- `TestSentence` - Tests for sentence parsing and construction
- `TestSentenceTransformation` - Tests for formula transformations
**Key Functions**: Tests formula parsing, AST generation, normalization
**Dependencies**: `pytest`, `syntactic.sentence`
**Used By**: Formula structure validation

### test_syntax.py
**Purpose**: Tests overall syntactic analysis and validation
**Key Classes**: 
- `TestSyntax` - Tests for syntax checking and validation
- `TestSyntaxErrors` - Tests for syntax error detection
**Key Functions**: Tests well-formedness checking, syntax error reporting
**Dependencies**: `pytest`, `syntactic.syntax`
**Used By**: Syntax validation system

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit syntactic

# Or directly with pytest
pytest src/model_checker/syntactic/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/syntactic/tests/unit/test_operators.py -v

# Run specific test method
pytest src/model_checker/syntactic/tests/unit/test_sentence.py::TestSentence::test_parse_complex_formula -v
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Sample formulas in various formats
- Operator collections
- Pre-parsed AST structures
- Invalid formula examples for error testing

## Coverage

These unit tests provide comprehensive coverage of:
- Formula parsing from LaTeX notation
- Operator precedence and associativity
- Atom extraction and management
- Syntax validation and error detection
- Formula normalization and transformation

## Contributing

When adding new unit tests:
1. Test parsing of increasingly complex formulas
2. Verify operator precedence is correctly applied
3. Test both valid and invalid syntax
4. Ensure error messages are informative
5. Test edge cases (empty formulas, nested operators, etc.)

## See Also

- [Syntactic Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Operators Module](../../operators.py)
- [Sentence Module](../../sentence.py)