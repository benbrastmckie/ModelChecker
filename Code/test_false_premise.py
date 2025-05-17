"""
Test script for checking false premise handling in exclusion theory
"""

##########################
### DEFINE THE IMPORTS ###
##########################

# Standard imports
import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from src.model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
    exclusion_operators
)

# Create a single example with the problematic premise
premises = ['\\exclude (A \\univee \\exclude A)']
conclusions = []
settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}

exclusion_theory = {
    "semantics": ExclusionSemantics,
    "proposition": UnilateralProposition,
    "model": ExclusionStructure,
    "operators": exclusion_operators,
}

semantic_theories = {
    "exclusion": exclusion_theory,
}

example_range = {
    "False Premise Test": [premises, conclusions, settings],
}

# Used by model-checker command to run examples
general_settings = {
    "print_constraints": True,
    "print_impossible": False,
    "print_z3": True,
    "save_output": False,
    "maximize": False,
}

example_settings = settings