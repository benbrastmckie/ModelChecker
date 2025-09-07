"""Shared test data for ModelChecker tests.

This module provides standardized test data for use across all test modules,
ensuring consistency and reducing duplication.
"""

# Standard test formulas
VALID_FORMULAS = [
    "(A \\wedge B)",
    "\\Box (A \\rightarrow B)",
    "\\neg (A \\vee B)",
    "(A \\rightarrow (B \\rightarrow A))",
    "\\Diamond (A \\wedge B)",
]

INVALID_FORMULAS = [
    "(A ∧ B)",  # Unicode instead of LaTeX
    "A \\wedge B",  # Missing parentheses
    "(A \\wedge)",  # Incomplete
    "\\Box \\Box",  # Missing proposition
    "",  # Empty formula
]

# Modal logic formulas
MODAL_FORMULAS = [
    "\\Box A",
    "\\Diamond B",
    "\\Box (A \\rightarrow \\Diamond B)",
    "\\Box \\Box A",
    "\\Diamond \\Diamond B",
]

# Complex formulas for stress testing
COMPLEX_FORMULAS = [
    "((A \\wedge B) \\rightarrow (C \\vee D))",
    "\\Box ((A \\vee B) \\rightarrow \\Diamond C)",
    "\\neg \\Box \\neg (A \\wedge B)",
    "(\\Box A \\wedge \\Diamond B) \\rightarrow (C \\vee \\neg D)",
]

# Standard test settings configurations
TEST_SETTINGS = {
    'minimal': {
        'N': 2,
        'max_time': 1
    },
    'standard': {
        'N': 3,
        'max_time': 10,
        'print_constraints': False
    },
    'complex': {
        'N': 5,
        'max_time': 30,
        'print_constraints': True,
        'print_z3': False
    },
    'debug': {
        'N': 3,
        'max_time': 10,
        'print_constraints': True,
        'print_z3': True,
        'print_impossible': True
    },
    'performance': {
        'N': 10,
        'max_time': 60,
        'print_constraints': False,
        'print_z3': False
    }
}

# Standard example configurations
def get_test_example(name='basic'):
    """Get standardized test example by name.
    
    Args:
        name: Name of the test example to retrieve
        
    Returns:
        list: [assumptions, conclusions, settings] for the example
    """
    examples = {
        'basic': [
            [],  # No assumptions
            ['A'],  # Simple conclusion
            {'N': 2}  # Minimal settings
        ],
        'standard': [
            ['A'],  # One assumption
            ['B'],  # One conclusion
            {'N': 3}  # Standard settings
        ],
        'complex': [
            ['A', 'B'],  # Multiple assumptions
            ['(A \\wedge B)'],  # Complex conclusion
            {'N': 3, 'max_time': 10}  # Extended settings
        ],
        'modal': [
            ['\\Box A'],  # Modal assumption
            ['\\Diamond B'],  # Modal conclusion
            {'N': 3}
        ],
        'counterfactual': [
            ['A \\boxright B'],  # Counterfactual
            ['\\neg A \\vee B'],  # Material conditional
            {'N': 4}
        ],
        'empty': [
            [],  # No assumptions
            [],  # No conclusions
            {'N': 2}
        ],
        'invalid': [
            ['(A ∧ B)'],  # Invalid Unicode
            ['C'],
            {'N': 2}
        ]
    }
    
    return examples.get(name, examples['basic'])


# Theory names for testing
THEORY_NAMES = [
    'logos',
    'exclusion',
    'bimodal',
    'imposition'
]

# CLI argument combinations for testing
CLI_TEST_ARGS = {
    'basic': ['-N', '3', 'test.py'],
    'with_theory': ['-l', 'logos', 'test.py'],
    'with_output': ['--save-output', 'test.py'],
    'debug': ['--print-z3', '--print-constraints', 'test.py'],
    'complex': ['-N', '5', '--max-time', '30', '-l', 'exclusion', 'test.py'],
    'interactive': ['--interactive', 'test.py'],
    'comparison': ['--comparison', 'test.py'],
}

# Expected error messages for validation
ERROR_MESSAGES = {
    'file_not_found': 'file not found',
    'invalid_theory': 'theory',
    'invalid_formula': 'formula',
    'syntax_error': 'syntax',
    'timeout': 'timeout',
    'unsatisfiable': 'unsatisfiable',
}

# Module content templates for testing
MODULE_TEMPLATES = {
    'minimal': '''
theory = None
semantic_theories = {}
example_range = {}
''',
    'standard': '''
from model_checker.theory_lib import logos

theory = logos.get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
general_settings = {}
''',
    'complex': '''
from model_checker.theory_lib import logos, exclusion

logos_theory = logos.get_theory(['extensional'])
exclusion_theory = exclusion.get_theory()

semantic_theories = {
    "Logos": logos_theory,
    "Exclusion": exclusion_theory
}

example_range = {
    "TEST1": [["A"], ["B"], {"N": 3}],
    "TEST2": [["\\Box A"], ["\\Diamond B"], {"N": 4}]
}

general_settings = {
    "print_constraints": True,
    "print_z3": False
}
'''
}