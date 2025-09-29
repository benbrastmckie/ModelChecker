"""
Edge cases and special scenarios for imposition theory.

This module contains edge cases and special test scenarios for imposition theory,
including boundary conditions and unusual configurations that test the limits
of the theory.
"""

from typing import Dict, List, Any


# Special edge case examples - these would be additional examples
# not covered in the basic or complex categories

# EXAMPLE IM_TR_0: NO PREMISES OR CONCLUSIONS (Test case for trivial scenario)
IM_TR_0_premises = []
IM_TR_0_conclusions = []
IM_TR_0_settings = {
    'N': 2,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_TR_0_example = [
    IM_TR_0_premises,
    IM_TR_0_conclusions,
    IM_TR_0_settings,
]

# EXAMPLE IM_EC_1: MINIMAL STATE SPACE
IM_EC_1_premises = ['A']
IM_EC_1_conclusions = ['A']
IM_EC_1_settings = {
    'N': 1,  # Minimal state space
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
}

IM_EC_1_example = [
    IM_EC_1_premises,
    IM_EC_1_conclusions,
    IM_EC_1_settings,
]

# EXAMPLE IM_EC_2: MAXIMAL CONSTRAINT CONDITIONS
IM_EC_2_premises = ['(A \\boxright B)']
IM_EC_2_conclusions = ['(A \\rightarrow B)']
IM_EC_2_settings = {
    'N': 4,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,  # All constraint types enabled
    'max_time': 20,
}

IM_EC_2_example = [
    IM_EC_2_premises,
    IM_EC_2_conclusions,
    IM_EC_2_settings,
]

# EXAMPLE IM_EC_3: DERIVED IMPOSITION TEST
IM_EC_3_premises = ['(A \\boxright B)']
IM_EC_3_conclusions = ['(A \\rightarrow B)']
IM_EC_3_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'derive_imposition': True,  # Test derived imposition mode
}

IM_EC_3_example = [
    IM_EC_3_premises,
    IM_EC_3_conclusions,
    IM_EC_3_settings,
]

# EXAMPLE IM_EC_4: LARGE STATE SPACE
IM_EC_4_premises = ['(A \\boxright B)', '(B \\boxright C)', '(C \\boxright D)']
IM_EC_4_conclusions = ['(A \\boxright D)']
IM_EC_4_settings = {
    'N': 5,  # Larger state space to test performance
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'max_time': 30,
}

IM_EC_4_example = [
    IM_EC_4_premises,
    IM_EC_4_conclusions,
    IM_EC_4_settings,
]

# EXAMPLE IM_EC_5: TIMEOUT SCENARIO
IM_EC_5_premises = [
    '(A \\boxright B)', '(B \\boxright C)', '(C \\boxright D)', '(D \\boxright E)',
    '(E \\boxright F)', '(F \\boxright G)', '(G \\boxright H)', '(H \\boxright I)',
]
IM_EC_5_conclusions = ['(A \\boxright I)']
IM_EC_5_settings = {
    'N': 6,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': True,
    'max_time': 1,  # Very short timeout to test timeout handling
}

IM_EC_5_example = [
    IM_EC_5_premises,
    IM_EC_5_conclusions,
    IM_EC_5_settings,
]

# EXAMPLE IM_EC_6: ITERATION TEST
IM_EC_6_premises = ['(A \\boxright B)']
IM_EC_6_conclusions = ['(A \\rightarrow B)']
IM_EC_6_settings = {
    'N': 3,
    'contingent': True,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'iterate': 5,  # Test multiple iterations
}

IM_EC_6_example = [
    IM_EC_6_premises,
    IM_EC_6_conclusions,
    IM_EC_6_settings,
]


# Organize edge case examples
edge_case_examples = {
    "IM_TR_0": IM_TR_0_example,   # NO PREMISES OR CONCLUSIONS
    "IM_EC_1": IM_EC_1_example,   # MINIMAL STATE SPACE
    "IM_EC_2": IM_EC_2_example,   # MAXIMAL CONSTRAINT CONDITIONS
    "IM_EC_3": IM_EC_3_example,   # DERIVED IMPOSITION TEST
    "IM_EC_4": IM_EC_4_example,   # LARGE STATE SPACE
    "IM_EC_5": IM_EC_5_example,   # TIMEOUT SCENARIO
    "IM_EC_6": IM_EC_6_example,   # ITERATION TEST
}