# Iterate Package Tests

This directory contains tests for the iterate package following the builder pattern structure.

## Test Organization

### unit/
Unit tests for individual iterator components:
- `test_base_iterator.py` - BaseModelIterator class tests
- `test_core.py` - Core iterator functionality
- `test_core_abstract_methods.py` - Abstract method implementation tests
- `test_core_no_state_transfer.py` - State isolation tests
- `test_simplified_iterator.py` - SimplifiedIterator tests
- `test_constraints.py` - Constraint handling tests
- `test_validation.py` - Validation logic tests

### integration/
Integration tests for component interactions:
- `test_build_example.py` - Iterator with BuildExample integration
- `test_constraint_preservation.py` - Constraint preservation across iterations
- `test_enhanced_tracking.py` - Enhanced tracking features
- `test_generator_interface.py` - Generator interface tests
- `test_graph_utils.py` - Graph utility integration
- `test_isomorphism.py` - Isomorphism detection tests
- `test_iteration_control.py` - Iteration control flow
- `test_metrics.py` - Metrics collection tests
- `test_models.py` - Model integration tests

### e2e/
End-to-end tests for complete workflows:
- `test_edge_cases.py` - Edge cases and boundary conditions

### fixtures/
Shared test data and mock objects (to be populated as needed)

### utils/
Test utilities and helpers (to be populated as needed)

## Running Tests

```bash
# Run all iterate tests
pytest src/model_checker/iterate/tests/

# Run specific test category
pytest src/model_checker/iterate/tests/unit/
pytest src/model_checker/iterate/tests/integration/
pytest src/model_checker/iterate/tests/e2e/

# Run with coverage
pytest src/model_checker/iterate/tests/ --cov=model_checker.iterate
```

## Test Guidelines

1. **Unit Tests**: Test single classes or functions in isolation
2. **Integration Tests**: Test interactions between iterate components
3. **E2E Tests**: Test complete iteration workflows

All tests use pytest fixtures defined in `conftest.py` for consistent test setup and teardown.