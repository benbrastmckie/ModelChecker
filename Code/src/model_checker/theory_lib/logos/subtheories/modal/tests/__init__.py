"""Tests for the modal subtheory.

This package contains tests for the modal operators including necessity (□)
and possibility (◇), as well as their interaction with other operators.

The test suite includes:
- Example tests validating logical properties of modal operators
- Unit tests for operator implementations
- Tests for modal axioms (K, T, 4, 5, etc.)
- Integration tests with extensional operators

For running these tests:
    # All modal tests
    pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/
    
    # Specific test file
    pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py
    
    # With verbose output
    pytest -v src/model_checker/theory_lib/logos/subtheories/modal/tests/
"""