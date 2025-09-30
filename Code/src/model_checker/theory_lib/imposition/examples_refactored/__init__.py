"""
Imposition theory examples package.

This package provides organized collections of examples for Kit Fine's
imposition semantic framework, split into logical groups for better
maintainability and understanding.

Example Categories:
    basic: Fundamental examples demonstrating core properties
    complex: Advanced patterns and edge cases
    edge_cases: Boundary conditions and special scenarios
    test_suite: Organized test collections and configurations

Usage:
    from model_checker.theory_lib.imposition.examples import (
        basic_examples, complex_examples, all_examples
    )
"""

from .basic import (
    basic_examples,
    basic_countermodels,
    basic_theorems,
)
from .complex import (
    complex_examples,
    complex_countermodels,
    complex_theorems,
)
from .edge_cases import edge_case_examples
from .test_suite import (
    all_examples,
    all_countermodels,
    all_theorems,
    unit_tests,
    test_example_range,
    all_imposition_examples,
    general_settings,
    semantic_theories,
    test_suites,
    quick_tests,
    benchmark_tests,
    constraint_tests,
    get_test_suite,
    get_available_suites,
    get_suite_info,
    imposition_theory,
)

# Export all public components
__all__ = [
    # Basic examples
    'basic_examples',
    'basic_countermodels',
    'basic_theorems',

    # Complex examples
    'complex_examples',
    'complex_countermodels',
    'complex_theorems',

    # Edge cases
    'edge_case_examples',

    # Combined collections
    'all_examples',
    'all_countermodels',
    'all_theorems',

    # Backward compatibility aliases
    'unit_tests',
    'test_example_range',
    'all_imposition_examples',

    # Configuration
    'general_settings',
    'semantic_theories',
    'imposition_theory',

    # Test suite management
    'test_suites',
    'quick_tests',
    'benchmark_tests',
    'constraint_tests',
    'get_test_suite',
    'get_available_suites',
    'get_suite_info',
]

# Default example range (curated subset for direct execution)
# This is required by the ModelChecker framework
example_range = {
    # COUNTERMODELS
    "IM_CM_1": basic_examples["IM_CM_1"],    # COUNTERFACTUAL ANTECEDENT STRENGTHENING

    # THEOREMS
    "IM_TH_5": basic_examples["IM_TH_5"],    # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
}

# Add example_range to exports
__all__.append('example_range')