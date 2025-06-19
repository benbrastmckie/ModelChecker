"""Tests for the constitutive subtheory.

This package contains tests for the constitutive operators that deal with
content relations including ground (≤), essence (⊑), and identity (≡).

The test suite includes:
- Example tests validating logical properties of constitutive operators
- Unit tests for operator implementations
- Integration tests with other subtheories

For running these tests:
    # All constitutive tests
    pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/
    
    # Specific test file
    pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py
    
    # With verbose output
    pytest -v src/model_checker/theory_lib/logos/subtheories/constitutive/tests/
"""