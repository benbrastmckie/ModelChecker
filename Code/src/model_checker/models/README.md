# Models Package

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md)

## Overview

The **models** package contains the core model checking components refactored from the original monolithic `model.py` module. This refactoring improves code organization, maintainability, and testability by separating concerns into focused submodules.

## Package Structure

```
models/
├── __init__.py          # Package initialization and exports
├── README.md           # This documentation file
├── types.py            # Type definitions and protocols for type safety
├── errors.py           # Custom exception classes for model checking
├── semantic.py         # SemanticDefaults - semantic evaluation framework
├── proposition.py      # PropositionDefaults - proposition management
├── constraints.py      # ModelConstraints - Z3 constraint generation
├── structure.py        # ModelDefaults - core model structure, solving, printing, and analysis
└── tests/             # Comprehensive test suite
    ├── unit/          # Unit tests for individual components
    ├── integration/   # Integration tests for component interactions
    └── conftest.py    # Test configuration and fixtures
```

## Component Overview

### types.py - Type Definitions and Safety

The `types.py` module provides comprehensive type definitions, aliases, and protocols to ensure type safety throughout the models package.

**Key Features**:
- Z3 type aliases (Z3Expr, Z3Model, Z3Solver)
- Model checking types (Settings, OperatorDict, EvaluationPoint)
- Constraint types (ConstraintList, ConstraintGenerator)
- Protocol definitions (ISemantics, IProposition)

### errors.py - Custom Exception Classes

Custom exception classes for better error handling and debugging in model checking operations.

### semantic.py - Semantic Evaluation Framework

The `SemanticDefaults` class provides the base semantic evaluation framework that all theory implementations extend. It defines the interface for evaluating formulas at worlds and managing semantic clauses.

**Key Features**:
- Formula evaluation at worlds
- Semantic clause generation for operators
- World state management
- Extension point for theory-specific semantics

### proposition.py - Proposition Management

The `PropositionDefaults` class handles proposition creation, management, and evaluation within models. It provides the foundation for working with atomic and complex propositions.

**Key Features**:
- Proposition creation and registration
- Truth value assignment
- Proposition property management
- Integration with Z3 solver

### constraints.py - Z3 Constraint Generation

The `ModelConstraints` class manages the generation and organization of Z3 constraints from semantic clauses. It bridges the gap between high-level semantic specifications and low-level solver constraints.

**Key Features**:
- Constraint generation from semantic clauses
- Constraint organization and optimization
- Solver interaction preparation
- Constraint debugging support

### structure.py - Core Model Structure, Solving, Printing, and Analysis

The `ModelDefaults` class provides the complete model checking functionality including Z3 solving, result interpretation, output formatting, and analysis capabilities. It serves as the central orchestrator for the entire model checking process.

**Key Features**:
- Model initialization and configuration
- Z3 solver management and constraint solving
- Solution extraction and semantic interpretation
- Model validation and result checking
- Terminal-friendly output formatting and visualization
- Model comparison and difference analysis
- Counterexample presentation and debugging
- Test file generation and export functionality

## Type Safety

The models package now includes comprehensive type hints throughout all modules, providing:

- **Better IDE Support**: Full autocomplete and type checking in modern IDEs
- **Early Error Detection**: Catch type mismatches at development time
- **Improved Documentation**: Type signatures serve as inline documentation
- **Protocol-Based Design**: Clear interfaces defined through protocols

## Usage Examples

### Basic Model Creation with Type Safety

```python
from model_checker.models import ModelDefaults, SemanticDefaults
from model_checker.models.types import Settings, ConstraintList
from typing import Dict, Any

# Create settings with proper typing
settings: Settings = {"N": 3, "max_time": 5000}

# Create a model with type-safe semantics
semantics: SemanticDefaults = SemanticDefaults(settings)
model: ModelDefaults = ModelDefaults(model_constraints, settings)

# Type-safe constraint generation
constraints: ConstraintList = semantics.generate_constraints()
```

### Custom Semantic Implementation

```python
from model_checker.models import SemanticDefaults

class MyCustomSemantics(SemanticDefaults):
    """Custom semantic implementation."""
    
    def evaluate_at_world(self, model, formula, world):
        """Custom evaluation logic."""
        # Implementation specific to your theory
        pass
```

## Design Principles

Following the ModelChecker design philosophy:

1. **No Backwards Compatibility**: Interfaces are updated directly without compatibility layers
2. **Fail Fast**: Errors surface immediately rather than being masked
3. **Explicit Parameters**: No hidden conversions or implicit state
4. **Clear Separation**: Each module has a single, well-defined responsibility

## Testing

Each component has comprehensive tests in the `tests/` directory:

```bash
# Run all models tests
pytest src/model_checker/models/tests/ -v

# Run specific component tests
pytest src/model_checker/models/tests/test_semantic.py -v

# Run with coverage
pytest src/model_checker/models/tests/ --cov=model_checker.models
```

## Migration Notes

This package is the result of the v1.0 refactoring effort. Key changes from the original model.py:

1. **Direct Imports Required**: All imports must use the new module paths:
   ```python
   # OLD (no longer works):
   from model_checker.model import SemanticDefaults
   
   # NEW:
   from model_checker.models.semantic import SemanticDefaults
   ```

2. **No Backwards Compatibility**: Following the NO BACKWARDS COMPATIBILITY principle, the old model.py has been removed
3. **Enhanced Testing**: Each component now has dedicated test coverage
4. **Improved Documentation**: Comprehensive documentation for each module
5. **Better Organization**: Clear separation of concerns across focused modules

## Architecture Notes

The structure.py module (748 lines) contains all model checking functionality including:
- Core Z3 solving logic
- Result interpretation
- Output formatting and printing
- Model difference analysis

This was a deliberate decision to keep related functionality together rather than artificially splitting it, maintaining clarity and reducing cross-module dependencies.

## See Also

### Conceptual Documentation
- **[Model Structure Concepts](../../../../Docs/architecture/MODELS.md)** - High-level model theory
- **[Semantics Architecture](../../../../Docs/architecture/SEMANTICS.md)** - Semantic framework concepts
- **[Architecture Overview](../../../../Docs/architecture/ARCHITECTURE.md)** - System design philosophy

### Technical Documentation
- **[Technical Architecture](../../../docs/ARCHITECTURE.md)** - Model system architecture
- **[Implementation Guide](../../../docs/IMPLEMENTATION.md)** - Implementing model structures
- **[Testing Guide](../../../docs/TESTS.md)** - Testing model components

### Related Components
- **[Builder Package](../builder/README.md)** - Uses models for constraint solving
- **[Theory Library](../theory_lib/README.md)** - Theory implementations using these models
- **[Iterate Package](../iterate/README.md)** - Model iteration and discovery

---

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md)
