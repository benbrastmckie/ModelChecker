"""Tests for the relevance subtheory.

This package contains tests for the content-sensitive relevance operators
that implement relevance logic principles within the logos framework.

The test suite includes:
- Example tests validating logical properties of relevance operators
- Unit tests for operator implementations
- Tests for relevance constraints and content preservation
- Integration tests with constitutive operators

For running these tests:
    # All relevance tests
    pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/
    
    # Specific test file
    pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py
    
    # With verbose output
    pytest -v src/model_checker/theory_lib/logos/subtheories/relevance/tests/
"""