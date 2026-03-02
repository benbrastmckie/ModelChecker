"""
Theory Library Test Suite

This package contains tests for the common functionality in theory_lib that spans
across multiple theories, including:

- Metadata management system (versioning, citations, licenses)
- Theory loading and discovery mechanisms  
- Cross-theory compatibility and integration
- Theory library infrastructure

For theory-specific tests, see individual theory directories:
- logos/tests/ - Tests for the Logos semantic theory and its subtheories
- default/tests/ - Tests for the default semantic theory
- exclusion/tests/ - Tests for the exclusion semantic theory
- imposition/tests/ - Tests for the imposition semantic theory
- bimodal/tests/ - Tests for the bimodal semantic theory

API:
    This module is tested via test_package.py which discovers and runs all tests
    in this package. Individual test modules can also be run directly with pytest.

Usage:
    # Run all theory_lib tests via the main test runner
    python test_package.py --components theory_lib
    
    # Run specific theory_lib tests with pytest
    pytest src/model_checker/theory_lib/tests/
    
    # Run individual test module
    pytest src/model_checker/theory_lib/tests/test_meta_data.py
"""

# Re-export main test classes for easier discovery
from .test_meta_data import TestMetadataSystem

__all__ = [
    'TestMetadataSystem'
]