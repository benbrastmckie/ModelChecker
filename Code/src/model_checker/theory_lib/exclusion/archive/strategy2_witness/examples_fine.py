"""
Examples Module for Fine Preclusion Testing

This module tests the FineUniNegation operator alongside the CB preclusion operator
to verify CLAIM_1 and evaluate computational tractability.

Usage:
------
Run with:
   ./dev_cli.py path/to/this/examples_fine.py
"""

import os
import sys

# Import witness uninegation components
from .semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition
from .operators import witness_operators
from .semantic import WitnessStructure

##########################
### SET UP THE EXAMPLE ###
##########################

# Define semantic theories for testing
unilateral_theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}
}

#######################
### DEFINE SETTINGS ###
#######################

general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

example_settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}

###################################
### FINE PRECLUSION TEST EXAMPLES ###
###################################

# Test 1: Basic Fine preclusion
FINE_BASIC_premises = []
FINE_BASIC_conclusions = ['\\set_unineg A']
FINE_BASIC_settings = {
    'N': 2,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
FINE_BASIC_example = [
    FINE_BASIC_premises,
    FINE_BASIC_conclusions,
    FINE_BASIC_settings,
]

# Test 2: Fine preclusion with premise
FINE_WITH_PREMISE_premises = ['A']
FINE_WITH_PREMISE_conclusions = ['\\set_unineg A']
FINE_WITH_PREMISE_settings = {
    'N': 2,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
FINE_WITH_PREMISE_example = [
    FINE_WITH_PREMISE_premises,
    FINE_WITH_PREMISE_conclusions,
    FINE_WITH_PREMISE_settings,
]

# Test 3: CLAIM_1_A Verification - CB implies Fine
COMPARE_CB_FINE_premises = ['\\func_unineg A']
COMPARE_CB_FINE_conclusions = ['\\set_unineg A']
COMPARE_CB_FINE_settings = {
    'N': 2,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
COMPARE_CB_FINE_example = [
    COMPARE_CB_FINE_premises,
    COMPARE_CB_FINE_conclusions,
    COMPARE_CB_FINE_settings,
]

# Test 4: Double Fine negation
FINE_DOUBLE_NEG_premises = ['A']
FINE_DOUBLE_NEG_conclusions = ['\\set_unineg \\set_unineg A']
FINE_DOUBLE_NEG_settings = {
    'N': 2,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': True,
}
FINE_DOUBLE_NEG_example = [
    FINE_DOUBLE_NEG_premises,
    FINE_DOUBLE_NEG_conclusions,
    FINE_DOUBLE_NEG_settings,
]

# Test 5: Fine DeMorgan's Law
FINE_DEMORGAN_premises = ['\\set_unineg (A \\uniwedge B)']
FINE_DEMORGAN_conclusions = ['(\\set_unineg A \\univee \\set_unineg B)']
FINE_DEMORGAN_settings = {
    'N': 2,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': False,  # Expected to fail like CB version
}
FINE_DEMORGAN_example = [
    FINE_DEMORGAN_premises,
    FINE_DEMORGAN_conclusions,
    FINE_DEMORGAN_settings,
]

# Test 6: CLAIM_1_B Verification - Fine implies CB
CLAIM1_CB_IMPLIES_FINE_premises = ['\\set_unineg A']
CLAIM1_CB_IMPLIES_FINE_conclusions = ['\\func_unineg A']
CLAIM1_CB_IMPLIES_FINE_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': True,  # CB-precluder should be Fine-precluder
}
CLAIM1_CB_IMPLIES_FINE_example = [
    CLAIM1_CB_IMPLIES_FINE_premises,
    CLAIM1_CB_IMPLIES_FINE_conclusions,
    CLAIM1_CB_IMPLIES_FINE_settings,
]

########################
### EXAMPLE REGISTRY ###
########################

# Which examples to run - full test suite
example_range = {
    # Basic Fine preclusion tests
    "Fine Basic": FINE_BASIC_example,
    "Fine with Premise": FINE_WITH_PREMISE_example,
    
    # CLAIM_1 verification tests
    "CLAIM_1_A: CB implies Fine": COMPARE_CB_FINE_example,
    "CLAIM_1_B: Fine implies CB": CLAIM1_CB_IMPLIES_FINE_example,
    
    # More complex tests
    "Fine Double Negation": FINE_DOUBLE_NEG_example,
    "Fine DeMorgan's Law": FINE_DEMORGAN_example,
}

# Test subset for quick testing
test_example_range = {
    "Fine Basic": FINE_BASIC_example,
    "CLAIM_1_A: CB implies Fine": COMPARE_CB_FINE_example,
}

# Use full test suite
# example_range = test_example_range  # Uncomment to use test subset

# Which semantic theories to compare
semantic_theories = {
    "unilateral_theory": unilateral_theory,
}

if __name__ == "__main__":
    # This allows the module to be run with dev_cli.py
    pass
