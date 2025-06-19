"""Tests for the extensional subtheory.

This package contains tests for the truth-functional operators that form
the foundation of logos theory, including negation (¬), conjunction (∧),
disjunction (∨), material conditional (→), biconditional (↔), and the
truth constants (⊤, ⊥).

The test suite includes:
- Example tests validating logical properties of extensional operators
- Unit tests for operator implementations
- Foundation tests that other subtheories depend upon

For running these tests:
    # All extensional tests
    pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/
    
    # Specific test file
    pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py
    
    # With verbose output
    pytest -v src/model_checker/theory_lib/logos/subtheories/extensional/tests/
"""