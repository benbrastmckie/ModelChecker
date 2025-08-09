"""
Examples template for ModelChecker theories.

Follow EXAMPLES_STRUCTURE.md standards from Code/maintenance/.
Replace 'TEMPLATE' prefix with your theory's abbreviation.
"""

# Required imports
from typing import Dict, List, Any

# ========================================
# UNIT TESTS - Required for all theories
# ========================================

# Basic theorem example
TEMPLATE_TH_1_premises = ["(A \\rightarrow B)", "A"]
TEMPLATE_TH_1_conclusions = ["B"]
TEMPLATE_TH_1_settings = {
    'N': 3,                    # Number of atomic propositions
    'contingent': False,       # Theory-specific setting
    'expectation': False       # False = expect theorem (countermodel not found)
}

# Non-theorem example
TEMPLATE_NT_1_premises = ["A"]
TEMPLATE_NT_1_conclusions = ["B"]
TEMPLATE_NT_1_settings = {
    'N': 3,
    'contingent': False,
    'expectation': True        # True = expect non-theorem (countermodel found)
}

# Required unit_tests list
unit_tests = [
    {
        'premises': TEMPLATE_TH_1_premises,
        'conclusions': TEMPLATE_TH_1_conclusions,
        'settings': TEMPLATE_TH_1_settings
    },
    {
        'premises': TEMPLATE_NT_1_premises,
        'conclusions': TEMPLATE_NT_1_conclusions,
        'settings': TEMPLATE_NT_1_settings
    },
    # Add more unit tests following naming convention
]

# ========================================
# TEST EXAMPLES - For framework validation
# ========================================

test_examples = [
    # Copy unit_tests or add specific test cases
    *unit_tests
]

# ========================================
# SEMANTIC THEORIES - Required
# ========================================

semantic_theories = ['template']  # Your theory name

# ========================================
# EXAMPLE RANGE - For CLI testing
# ========================================

# Define which examples to run by default
example_range = range(1, len(unit_tests) + 1)