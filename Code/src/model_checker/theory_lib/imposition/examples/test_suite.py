"""
Test suite definitions for imposition theory.

This module contains organized test collections and configuration settings
for running comprehensive test suites of the imposition theory examples.
"""

from typing import Dict, List, Any
from .basic import basic_examples, basic_countermodels, basic_theorems
from .complex import complex_examples, complex_countermodels, complex_theorems
from .edge_cases import edge_case_examples

# Import specific theory configuration
imposition_theory = {
    'semantics': 'ImpositionSemantics',
    'model_structure': 'ImpositionModelStructure',
    'proposition': 'Proposition',
    'operators': 'imposition_operators',
}

# Default settings for the examples module
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    "derive_imposition": False,
    "max_time": 5,  # Default timeout in seconds
    "expectation": True,  # Default expectation for validity
}


# Helper function to merge general settings with example settings
def merge_with_general_settings(examples_dict: Dict[str, List], is_theorem: bool = False) -> Dict[str, List]:
    """Merge general_settings with each example's settings.

    Args:
        examples_dict: Dictionary of examples to process
        is_theorem: If True, sets expectation to False (expecting no countermodel)
    """
    merged = {}
    for key, example in examples_dict.items():
        premises, conclusions, settings = example
        # Merge general_settings with example-specific settings
        # Example settings take precedence over general settings
        merged_settings = {**general_settings, **settings}
        # For theorems, we expect no countermodel (expectation should be False)
        # But only override if not explicitly set in the example
        if (is_theorem or key.startswith('IM_TH')) and 'expectation' not in settings:
            merged_settings['expectation'] = False
        merged[key] = [premises, conclusions, merged_settings]
    return merged


# Combined collections for comprehensive testing
all_countermodels = {**basic_countermodels, **complex_countermodels}
all_theorems = {**basic_theorems, **complex_theorems}
all_examples_raw = {**basic_examples, **complex_examples, **edge_case_examples}

# Apply general settings to all examples
all_examples = merge_with_general_settings(all_examples_raw)
all_countermodels = merge_with_general_settings(all_countermodels)
all_theorems = merge_with_general_settings(all_theorems, is_theorem=True)


# Test suite configurations
test_suites = {
    'basic': {
        'examples': merge_with_general_settings(basic_examples),
        'description': 'Basic imposition theory examples',
        'expected_runtime': 'fast',
    },
    'complex': {
        'examples': merge_with_general_settings(complex_examples),
        'description': 'Complex imposition theory examples',
        'expected_runtime': 'medium',
    },
    'edge_cases': {
        'examples': merge_with_general_settings(edge_case_examples),
        'description': 'Edge cases and special scenarios',
        'expected_runtime': 'variable',
    },
    'countermodels_only': {
        'examples': all_countermodels,
        'description': 'All countermodel examples',
        'expected_runtime': 'medium',
    },
    'theorems_only': {
        'examples': all_theorems,
        'description': 'All theorem examples',
        'expected_runtime': 'medium',
    },
    'comprehensive': {
        'examples': all_examples,
        'description': 'Complete test suite',
        'expected_runtime': 'long',
    },
}


# Quick test configurations for development
quick_tests = {
    'smoke': {
        'examples': merge_with_general_settings({
            'IM_CM_1': basic_examples['IM_CM_1'],
            'IM_TH_5': basic_examples['IM_TH_5'],
        }),
        'description': 'Smoke test with one countermodel and one theorem',
    },
    'basic_sample': {
        'examples': merge_with_general_settings({
            'IM_CM_1': basic_examples['IM_CM_1'],
            'IM_CM_7': basic_examples['IM_CM_7'],
            'IM_TH_1': basic_examples['IM_TH_1'],
            'IM_TH_2': basic_examples['IM_TH_2'],
        }),
        'description': 'Small sample of basic examples',
    },
}


# Performance benchmark configurations
benchmark_tests = {
    'small_state_space': {
        'examples': {k: v for k, v in all_examples.items()
                    if v[2].get('N', 3) <= 3},  # N <= 3
        'description': 'Examples with small state spaces (N <= 3)',
    },
    'medium_state_space': {
        'examples': {k: v for k, v in all_examples.items()
                    if v[2].get('N', 3) == 4},  # N == 4
        'description': 'Examples with medium state spaces (N == 4)',
    },
    'large_state_space': {
        'examples': {k: v for k, v in all_examples.items()
                    if v[2].get('N', 3) >= 5},  # N >= 5
        'description': 'Examples with large state spaces (N >= 5)',
    },
}


# Test configurations by constraint settings
constraint_tests = {
    'minimal_constraints': {
        'examples': {k: v for k, v in all_examples.items()
                    if not any([v[2].get('contingent', False),
                               v[2].get('non_empty', False),
                               v[2].get('non_null', False),
                               v[2].get('disjoint', False)])},
        'description': 'Examples with minimal constraint settings',
    },
    'maximal_constraints': {
        'examples': {k: v for k, v in all_examples.items()
                    if all([v[2].get('contingent', False),
                           v[2].get('non_empty', False),
                           v[2].get('non_null', False)])},
        'description': 'Examples with maximum constraint settings',
    },
}


# Semantic theories configuration
semantic_theories = {
    "Fine": imposition_theory,
}


def get_test_suite(suite_name: str) -> Dict[str, Any]:
    """Get a specific test suite configuration.

    Args:
        suite_name: Name of the test suite

    Returns:
        Dictionary containing test configuration

    Raises:
        KeyError: If suite_name is not found
    """
    if suite_name in test_suites:
        return test_suites[suite_name]
    elif suite_name in quick_tests:
        return quick_tests[suite_name]
    elif suite_name in benchmark_tests:
        return benchmark_tests[suite_name]
    elif suite_name in constraint_tests:
        return constraint_tests[suite_name]
    else:
        raise KeyError(f"Test suite '{suite_name}' not found")


def get_available_suites() -> List[str]:
    """Get list of all available test suite names."""
    return list(test_suites.keys()) + list(quick_tests.keys()) + \
           list(benchmark_tests.keys()) + list(constraint_tests.keys())


def get_suite_info(suite_name: str) -> str:
    """Get description of a test suite."""
    suite = get_test_suite(suite_name)
    return suite.get('description', 'No description available')


# Aliases for backward compatibility
unit_tests = all_examples
test_example_range = all_examples
all_imposition_examples = all_examples