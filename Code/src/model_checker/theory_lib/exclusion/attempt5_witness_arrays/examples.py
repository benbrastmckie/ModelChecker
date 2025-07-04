"""
Examples Module for Witness Array Exclusion Theory

This module tests the witness array implementation of exclusion semantics,
demonstrating whether using Z3 arrays to store witness mappings can solve
the Skolem function accessibility problem.

Key Innovation Being Tested:
---------------------------
- Replace Skolem functions h_sk and y_sk with Z3 arrays h_array and y_array
- Arrays become part of the model and can be queried after solving
- Attempt to correctly compute verifiers using extracted array values

Expected Outcomes:
-----------------
If the witness array approach works:
- Double negation examples should have true premises
- DeMorgan's law examples should have true premises  
- All exclusion-based examples should evaluate correctly

If it still faces the fundamental limitation:
- Same false premise pattern as previous attempts
- Demonstrates that the issue is architectural, not representational

Usage:
------
Run with: ./dev_cli.py path/to/this/examples.py
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

# Witness Array Exclusion Implementation
from semantic import (
    WitnessArraySemantics,
)
from operators import (
    create_operators,
    witness_array_operators,
)

# Import other necessary components from the main exclusion theory
parent_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'semantic.py')
import importlib.util
spec = importlib.util.spec_from_file_location("parent_semantic", parent_path)
parent_semantic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent_semantic)

UnilateralProposition = parent_semantic.UnilateralProposition
ExclusionStructure = parent_semantic.ExclusionStructure

##################################
### DEFINE SEMANTIC DICTIONARY ###
##################################

# Define the witness array exclusion theory
witness_array_theory = {
    "semantics": WitnessArraySemantics,
    "proposition": UnilateralProposition,
    "model": ExclusionStructure,
    "operators": witness_array_operators,
}

# Dictionary of semantic theories to test
semantic_theories = {
    'witness_array': witness_array_theory,
}

################################
### DEFINE EXAMPLE PROBLEMS ###
################################

# DOUBLE NEGATION ELIMINATION
DN_ELIM_premises = ['\\exclude \\exclude A']
DN_ELIM_conclusions = ['A']
DN_ELIM_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
DN_ELIM_example = [
    DN_ELIM_premises,
    DN_ELIM_conclusions,
    DN_ELIM_settings
]

# TRIPLE NEGATION
TN_ENTAIL_premises = ['\\exclude \\exclude \\exclude A']
TN_ENTAIL_conclusions = ['\\exclude A']
TN_ENTAIL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
TN_ENTAIL_example = [
    TN_ENTAIL_premises,
    TN_ENTAIL_conclusions,
    TN_ENTAIL_settings
]

# CONJUNCTION DEMORGAN LR
CONJ_DM_LR_premises = ['\\exclude (A \\uniwedge B)']
CONJ_DM_LR_conclusions = ['(\\exclude A \\univee \\exclude B)']
CONJ_DM_LR_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
CONJ_DM_LR_example = [
    CONJ_DM_LR_premises,
    CONJ_DM_LR_conclusions,
    CONJ_DM_LR_settings
]

# CONJUNCTION DEMORGAN RL
CONJ_DM_RL_premises = ['(\\exclude A \\univee \\exclude B)']
CONJ_DM_RL_conclusions = ['\\exclude (A \\uniwedge B)']
CONJ_DM_RL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
CONJ_DM_RL_example = [
    CONJ_DM_RL_premises,
    CONJ_DM_RL_conclusions,
    CONJ_DM_RL_settings
]

# DISJUNCTION DEMORGAN LR  
DISJ_DM_LR_premises = ['\\exclude (A \\univee B)']
DISJ_DM_LR_conclusions = ['(\\exclude A \\uniwedge \\exclude B)']
DISJ_DM_LR_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
DISJ_DM_LR_example = [
    DISJ_DM_LR_premises,
    DISJ_DM_LR_conclusions,
    DISJ_DM_LR_settings
]

# DISJUNCTION DEMORGAN RL
DISJ_DM_RL_premises = ['(\\exclude A \\uniwedge \\exclude B)']
DISJ_DM_RL_conclusions = ['\\exclude (A \\univee B)']
DISJ_DM_RL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
DISJ_DM_RL_example = [
    DISJ_DM_RL_premises,
    DISJ_DM_RL_conclusions,
    DISJ_DM_RL_settings
]

# NO GLUTS
NO_GLUTS_premises = ['(A \\uniwedge \\exclude A)']
NO_GLUTS_conclusions = []
NO_GLUTS_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
NO_GLUTS_example = [
    NO_GLUTS_premises,
    NO_GLUTS_conclusions,
    NO_GLUTS_settings
]

# DISJUNCTIVE SYLLOGISM
DISJ_SYLL_premises = ['(A \\univee B)', '\\exclude A']
DISJ_SYLL_conclusions = ['B']
DISJ_SYLL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
DISJ_SYLL_example = [
    DISJ_SYLL_premises,
    DISJ_SYLL_conclusions,
    DISJ_SYLL_settings
]

# SIMPLE EXCLUSION TEST
SIMPLE_EXCL_premises = ['\\exclude A']
SIMPLE_EXCL_conclusions = []
SIMPLE_EXCL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
SIMPLE_EXCL_example = [
    SIMPLE_EXCL_premises,
    SIMPLE_EXCL_conclusions,
    SIMPLE_EXCL_settings
]

# Basic conjunction test (should work fine)
BASIC_CONJ_premises = ['A', 'B']
BASIC_CONJ_conclusions = ['(A \\uniwedge B)']
BASIC_CONJ_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}
BASIC_CONJ_example = [
    BASIC_CONJ_premises,
    BASIC_CONJ_conclusions,
    BASIC_CONJ_settings
]

#######################################
### CHOOSE EXAMPLES AND RUN THEM ###
#######################################

# Dictionary of examples to run
example_range = {
    # Basic tests (should work)
    "Basic Conjunction": BASIC_CONJ_example,
    "Simple Exclusion": SIMPLE_EXCL_example,
    
    # Critical tests - these had false premises in previous attempts
    "Double Negation Elimination": DN_ELIM_example,
    "Triple Negation": TN_ENTAIL_example,
    
    # DeMorgan's laws - also problematic in previous attempts
    "Conjunction DeMorgan LR": CONJ_DM_LR_example,
    "Conjunction DeMorgan RL": CONJ_DM_RL_example,
    "Disjunction DeMorgan LR": DISJ_DM_LR_example,
    "Disjunction DeMorgan RL": DISJ_DM_RL_example,
    
    # Additional tests
    "No Gluts": NO_GLUTS_example,
    "Disjunctive Syllogism": DISJ_SYLL_example,
}

####################
### RUN EXAMPLES ###
####################

if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)