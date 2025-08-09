# Imposition Theory Tests

[← Back to Imposition](../README.md) | [Examples →](../examples.py) | [Notebooks →](../notebooks/README.md)

## Directory Structure
```
tests/
├── README.md               # This file - test documentation
├── __init__.py            # Test package initialization
├── test_imposition.py     # Core imposition semantic tests
└── test_iterate.py        # Model iteration tests
```

## Overview

The **imposition theory test suite** validates Kit Fine's counterfactual semantics implementation through comprehensive unit and integration testing. Tests verify the imposition operation, counterfactual operators, frame constraints, and model iteration functionality. The suite ensures both theoretical correctness and implementation reliability across all 86 examples.

## Test Files

### test_imposition.py

**Purpose**: Core tests for imposition semantics and counterfactual operators

**Coverage**:
- **Imposition Operation**: Tests the primitive imposition relation `impose(w, a, u)`
- **Frame Constraints**: Validates all five Fine constraints:
  - Possibility downward closure
  - Inclusion constraint
  - Actuality constraint
  - Incorporation constraint
  - Completeness constraint
- **Counterfactual Operators**: Tests `\boxright` and `\diamondright` truth conditions
- **Bilateral Semantics**: Verifies both verification and falsification
- **Model Structure**: Tests `ImpositionModelStructure` display and relations

**Key Test Areas**:
- **Basic Imposition**: Simple imposition triples and outcome calculation
- **Complex Counterfactuals**: Nested and combined counterfactual formulas
- **Edge Cases**: Empty verifier sets, contradictory antecedents
- **Integration**: Interaction with imported Logos operators

### test_iterate.py

**Purpose**: Tests model iteration functionality for counterfactuals

**Coverage**:
- **Basic Iteration**: Finding multiple distinct models
- **Counterfactual Variation**: Models with different imposition relations
- **Constraint Preservation**: Ensuring frame constraints hold across iterations
- **Performance**: Iteration timeout and attempt limits

**Key Test Areas**:
- **Model Uniqueness**: Verifying non-isomorphic models
- **Imposition Differences**: Models differing only in imposition relation
- **Operator Coverage**: Iteration with both must and might counterfactuals

## Running Tests

### Run All Tests
```bash
# From theory directory
python -m pytest tests/

# From project root
./run_tests.py imposition
```

### Run Specific Test File
```bash
python -m pytest tests/test_imposition.py -v
python -m pytest tests/test_iterate.py -v
```

### Run with Coverage
```bash
python -m pytest tests/ --cov=src.model_checker.theory_lib.imposition --cov-report=html
```

## Test Examples

### Testing Imposition Operation
```python
def test_imposition_basic():
    """Test basic imposition operation."""
    semantics = ImpositionSemantics()
    # Test that imposing verifier states changes world evaluation
    # Verify outcome calculation follows Fine's semantics
```

### Testing Counterfactual Operators
```python
def test_must_counterfactual():
    """Test must-counterfactual operator."""
    model = create_test_model()
    # Test A ▷ B is true when all impositions of A-verifiers lead to B
    # Test falsification conditions
```

### Testing Frame Constraints
```python
def test_possibility_constraint():
    """Test possibility downward closure."""
    # Verify if a →_w u and u is possible, then u' ⊆ u implies a →_w u'
    # Check constraint generation in Z3
```

## Test Patterns

### Model Creation Pattern
```python
@pytest.fixture
def imposition_model():
    """Create test model with imposition relation."""
    theory = get_theory()
    settings = {'N': 3, 'contingent': True}
    return create_model_with_imposition(theory, settings)
```

### Counterfactual Testing Pattern
```python
def test_counterfactual_principle(imposition_model):
    """Test specific counterfactual principle."""
    # Setup: Create formula
    # Execute: Evaluate in model
    # Assert: Check expected result
```

## Integration with Examples

The test suite validates all 86 examples from `examples.py`:
- **62 Countermodels**: Each tested to ensure invalid principles fail
- **24 Theorems**: Each tested to ensure valid principles succeed

## Documentation

### For Test Writers
- Follow pytest conventions and fixtures
- Document theoretical principles being tested
- Include references to Fine's papers where relevant

### For Maintainers
- Keep tests synchronized with `examples.py`
- Update tests when frame constraints change
- Maintain coverage above 90%

## References

- Fine, K. (2012). "Counterfactuals without Possible Worlds"
- Fine, K. (2017). "Truthmaker Semantics"
- ModelChecker test documentation standards

---

[← Back to Imposition](../README.md) | [Examples →](../examples.py) | [API Reference →](../docs/API_REFERENCE.md)