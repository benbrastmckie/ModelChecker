# Models Unit Tests

## Overview

This directory contains unit tests for the models package, validating the core data structures and semantic models used throughout the ModelChecker framework. These tests ensure that model structures, propositions, constraints, and semantic definitions work correctly in isolation.

## Modules

### test_constraints.py
**Purpose**: Tests constraint generation and management for Z3 solver
**Key Classes**: 
- `TestConstraintBuilder` - Tests for building Z3 constraints
- `TestConstraintValidation` - Tests for constraint validation
**Key Functions**: Tests constraint creation, combination, simplification
**Dependencies**: `pytest`, `models.constraints`, `z3`
**Used By**: Constraint system validation

### test_proposition.py
**Purpose**: Tests propositional logic representations and operations
**Key Classes**: 
- `TestProposition` - Tests for proposition creation and manipulation
- `TestPropositionEvaluation` - Tests for proposition evaluation
**Key Functions**: Tests atomic propositions, compound formulas, truth evaluation
**Dependencies**: `pytest`, `models.proposition`
**Used By**: Propositional logic validation

### test_semantic.py
**Purpose**: Tests semantic model definitions and operations
**Key Classes**: 
- `TestSemanticModel` - Tests for semantic model structures
- `TestSemanticEvaluation` - Tests for semantic evaluation rules
**Key Functions**: Tests model creation, world relations, valuation functions
**Dependencies**: `pytest`, `models.semantic`
**Used By**: Semantic framework validation

### test_structure.py
**Purpose**: Tests the core ModelStructure class and its operations
**Key Classes**: 
- `TestModelStructure` - Tests for model structure creation and manipulation
- `TestModelOperations` - Tests for model operations and queries
**Key Functions**: Tests structure initialization, state management, relation handling
**Dependencies**: `pytest`, `models.structure`, `z3`
**Used By**: Core model validation

### test_structure_print.py
**Purpose**: Tests model structure printing and visualization
**Key Classes**: 
- `TestStructurePrinting` - Tests for model string representations
- `TestVisualization` - Tests for model visualization utilities
**Key Functions**: Tests ASCII art generation, LaTeX output, graph representations
**Dependencies**: `pytest`, `models.structure`
**Used By**: Model display validation

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit models

# Or directly with pytest
pytest src/model_checker/models/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/models/tests/unit/test_structure.py -v

# Run with detailed output
pytest src/model_checker/models/tests/unit/test_structure.py -vv

# Run with coverage
pytest src/model_checker/models/tests/unit/ --cov=model_checker.models
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Sample model structures
- Pre-built constraint sets
- Mock semantic definitions
- Test propositions and formulas

## Coverage

These unit tests provide comprehensive coverage of:
- ModelStructure initialization and configuration
- Constraint generation and Z3 integration
- Proposition handling and evaluation
- Semantic model operations
- Model printing and visualization

## Contributing

When adding new unit tests:
1. Test model components in isolation
2. Verify all model operations preserve invariants
3. Test edge cases (empty models, single states, etc.)
4. Ensure Z3 constraints are properly formed
5. Test both successful operations and error conditions

## See Also

- [Models Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Structure Module](../../structure.py)
- [Semantic Module](../../semantic.py)