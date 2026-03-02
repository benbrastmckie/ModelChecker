"""Tests for the counterfactual subtheory.

This package contains tests for the counterfactual conditional operators
including strict (□→) and variably strict (◇→) counterfactuals.

The test suite includes:
- Example tests validating logical properties of counterfactual operators
- Unit tests for operator implementations
- Integration tests with modal operators

For running these tests:
    # All counterfactual tests
    pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/
    
    # Specific test file
    pytest src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counterfactual_examples.py
    
    # With verbose output
    pytest -v src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/
"""