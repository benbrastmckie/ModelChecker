"""
Examples Module for Incremental Exclusion Theory

This module tests the incremental exclusion semantics implementation,
focusing on the problematic examples that fail with the static approach.

The incremental approach maintains persistent computational context across
Syntax → Truth-Conditions → Extensions, enabling correct evaluation of
formulas with existential quantification.
"""

import os
import sys

# Import incremental exclusion components
from .semantic import ExclusionSemantics, UnilateralProposition
from .operators import exclusion_operators
from .incremental_model import IncrementalModelStructure

# Import default theory for comparison
from model_checker.theory_lib.default import (
    Semantics,
    Proposition,
    ModelStructure,
    default_operators,
)

##########################
### SET UP THE EXAMPLE ###
##########################

# Define semantic theories for testing
exclusion_theory = {
    "semantics": ExclusionSemantics,
    "proposition": UnilateralProposition,
    "model": IncrementalModelStructure,
    "operators": exclusion_operators,
    "dictionary": {}  # No translation needed for exclusion theory
}

default_dictionary = {
    "\\exclude": "\\neg",
    "\\uniwedge": "\\wedge",
    "\\univee": "\\vee",
    "\\uniequiv": "\\equiv",
}

default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "model": ModelStructure,
    "operators": default_operators,
    "dictionary": default_dictionary,
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
    'N': 3,
    'possible': False,
    'contingent': False,
    'disjoint': False,
    'non_empty': False,
    'non_null': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': True,
}

########################
### PROBLEMATIC CASES ###
########################

# DOUBLE NEGATION ELIMINATION (False premise in static approach)
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
    'iterate': 1,
    'expectation': True,
}
DN_ELIM_example = [
    DN_ELIM_premises,
    DN_ELIM_conclusions,
    DN_ELIM_settings
]

# TRIPLE NEGATION ENTAILMENT (False premise in static approach)
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
    'max_time': 10,
    'expectation': True,
}
TN_ENTAIL_example = [
    TN_ENTAIL_premises,
    TN_ENTAIL_conclusions,
    TN_ENTAIL_settings
]

# QUADRUPLE NEGATION (False premise in static approach)
QN_ENTAIL_premises = ['\\exclude \\exclude \\exclude \\exclude A']
QN_ENTAIL_conclusions = ['\\exclude \\exclude A']
QN_ENTAIL_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 20,
    'expectation': True,
}
QN_ENTAIL_example = [
    QN_ENTAIL_premises,
    QN_ENTAIL_conclusions,
    QN_ENTAIL_settings
]

# DISJUNCTIVE SYLLOGISM (False premise in static approach)
DISJ_SYLL_premises = ['(A \\univee B)', '\\exclude B']
DISJ_SYLL_conclusions = ['A']
DISJ_SYLL_settings = {
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
DISJ_SYLL_example = [
    DISJ_SYLL_premises,
    DISJ_SYLL_conclusions,
    DISJ_SYLL_settings
]

# CONJUNCTION DEMORGANS LR (False premise in static approach)
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
    'expectation': False,
}
CONJ_DM_LR_example = [
    CONJ_DM_LR_premises,
    CONJ_DM_LR_conclusions,
    CONJ_DM_LR_settings
]

# CONJUNCTION DEMORGANS RL (False premise in static approach)
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
    'expectation': False,
}
CONJ_DM_RL_example = [
    CONJ_DM_RL_premises,
    CONJ_DM_RL_conclusions,
    CONJ_DM_RL_settings
]

# DISJUNCTION DEMORGANS LR (False premise in static approach)
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
    'expectation': False,
}
DISJ_DM_LR_example = [
    DISJ_DM_LR_premises,
    DISJ_DM_LR_conclusions,
    DISJ_DM_LR_settings
]

# DISJUNCTION DEMORGANS RL (False premise in static approach)
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
    'expectation': False,
}
DISJ_DM_RL_example = [
    DISJ_DM_RL_premises,
    DISJ_DM_RL_conclusions,
    DISJ_DM_RL_settings
]

# NO GLUTS (False premise in static approach)
NO_GLUT_premises = []
NO_GLUT_conclusions = ['\\exclude (A \\uniwedge \\exclude A)']
NO_GLUT_settings = {
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
NO_GLUT_example = [
    NO_GLUT_premises,
    NO_GLUT_conclusions,
    NO_GLUT_settings,
]

# THEOREM 17 (Complex exclusion formula)
T17_premises = []
T17_conclusions = ['((\\exclude (A \\univee B) \\uniequiv (\\exclude A \\uniwedge \\exclude B)) \\uniwedge (\\exclude (A \\uniwedge B) \\uniequiv (\\exclude A \\univee \\exclude B)))']
T17_settings = {
    'N': 4,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': True,
}
T17_example = [
    T17_premises,
    T17_conclusions,
    T17_settings,
]

########################
### WORKING EXAMPLES ###
########################

# Some examples that work even in static approach for comparison

# EMPTY CASE FOR CHECKING FRAME CONSTRAINTS
EMPTY_premises = []
EMPTY_conclusions = []
EMPTY_settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 2,
    'iterate': 1,
    'expectation': True,
}
EMPTY_example = [
    EMPTY_premises,
    EMPTY_conclusions,
    EMPTY_settings,
]

# ATOMIC EXAMPLE
ATOMIC_premises = ['A']
ATOMIC_conclusions = ['A']
ATOMIC_settings = {
    'N': 2,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 2,
    'expectation': True,
}
ATOMIC_example = [
    ATOMIC_premises,
    ATOMIC_conclusions,
    ATOMIC_settings,
]

########################
### EXAMPLE REGISTRY ###
########################

# Which examples to run
example_range = {
    # Problematic examples (these should work with incremental approach)
    "DN_ELIM_example": DN_ELIM_example,
    "TN_ENTAIL_example": TN_ENTAIL_example,
    "QN_ENTAIL_example": QN_ENTAIL_example,
    "DISJ_SYLL_example": DISJ_SYLL_example,
    "CONJ_DM_LR_example": CONJ_DM_LR_example,
    "CONJ_DM_RL_example": CONJ_DM_RL_example,
    "DISJ_DM_LR_example": DISJ_DM_LR_example,
    "DISJ_DM_RL_example": DISJ_DM_RL_example,
    "NO_GLUT_example": NO_GLUT_example,
    "T17_example": T17_example,
    
    # Working examples for comparison
    # "EMPTY_example": EMPTY_example,
    # "ATOMIC_example": ATOMIC_example,
}

# Which semantic theories to compare
semantic_theories = {
    "exclusion_theory": exclusion_theory,
    # "default_theory": default_theory,  # Uncomment to compare with classical logic
}

if __name__ == "__main__":
    # This allows the module to be run with dev_cli.py
    # The ModelChecker framework will use example_range and semantic_theories
    pass