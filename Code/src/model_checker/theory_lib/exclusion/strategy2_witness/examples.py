"""
Examples Module for Witness UniNegation Theory

This module tests the witness uninegation semantics implementation,
demonstrating that the FALSE PREMISE PROBLEM has been solved through
witness predicates in the model structure.

The witness predicate approach makes witness functions first-class model
citizens, enabling correct evaluation of formulas with existential quantification.

Usage:
------
This module can be run in two ways:

1. Command Line:
   ```bash
   model-checker path/to/this/examples.py
   # or
   ./dev_cli.py path/to/this/examples.py
   ```

2. IDE (VSCodium/VSCode):
   - Open this file in VSCodium/VSCode
   - Use the "Run Python File" play button in the top-right corner

Configuration:
-------------
The examples and theories to be run can be configured by:

1. Modifying which examples are run:
   - Edit the example_range dictionary
   - Comment/uncomment specific examples

2. To add new examples:
   - Define premises, conclusions, and settings
   - Add to example_range dictionary

Module Structure:
----------------
1. Imports:
   - Witness predicate unilateral components (semantic, operators)
   - Default theory components for comparison (optional)

2. Semantic Theories:
   - unilateral_theory: Witness unilateral logic
   - default_theory: Bilateral logic implementation for comparison (optional)

3. Example Categories:
   - Frame Examples: Basic frame constraint tests
   - Negation Examples: Double/triple/quadruple negation tests
   - DeMorgan's Laws: All four forms
   - Distribution Laws: Conjunction/disjunction distribution
   - Absorption Laws: Various absorption patterns
   - Associativity Laws: Associativity tests
   - Identity Examples: Various logical identities

Example Format:
--------------
Each example is structured as a list: [premises, conclusions, settings]
- premises: List of formulas that serve as assumptions
- conclusions: List of formulas to be tested
- settings: Dictionary of specific settings for this example

Notes:
------
- The witness predicate theory solves examples that fail with static unilateral semantics
- Examples marked with "FALSE PREMISE" comments failed in static approach
- At least one semantic theory must be included in semantic_theories
- At least one example must be included in example_range
"""

import os
import sys

# Import witness uninegation components
from .semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition
from .operators import witness_operators

# Import custom structure that includes witness printing
from .semantic import WitnessStructure

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
unilateral_theory = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
    "dictionary": {}  # No translation needed for unilateral theory
}

default_dictionary = {
    "\\func_unineg": "\\neg",
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

#####################
### FRAME EXAMPLES ###
#####################

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

#############################
### NEGATION EXAMPLES     ###
### (PROBLEMATIC IN STATIC) #
#############################

# NEGATION TO SENTENCE
NEG_TO_SENT_premises = ['\\func_unineg A']
NEG_TO_SENT_conclusions = ['A']
NEG_TO_SENT_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,  # Note: expectation differs from elimination
}
NEG_TO_SENT_example = [
    NEG_TO_SENT_premises,
    NEG_TO_SENT_conclusions,
    NEG_TO_SENT_settings
]

# SENTENCE TO NEGATION
SENT_TO_NEG_premises = ['A']
SENT_TO_NEG_conclusions = ['\\func_unineg A']
SENT_TO_NEG_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,  # Note: expectation differs from elimination
}
SENT_TO_NEG_example = [
    SENT_TO_NEG_premises,
    SENT_TO_NEG_conclusions,
    SENT_TO_NEG_settings
]

# DOUBLE NEGATION ELIMINATION (FALSE PREMISE in static approach)
DN_ELIM_premises = ['\\func_unineg \\func_unineg A']
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
TN_ENTAIL_premises = ['\\func_unineg \\func_unineg \\func_unineg A']
TN_ENTAIL_conclusions = ['\\func_unineg A']
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

# DISJUNCTIVE SYLLOGISM (False premise in static approach)
DISJ_SYLL_premises = ['(A \\univee B)', '\\func_unineg B']
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
CONJ_DM_LR_premises = ['\\func_unineg (A \\uniwedge B)']
CONJ_DM_LR_conclusions = ['(\\func_unineg A \\univee \\func_unineg B)']
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

# NO GLUTS (False premise in static approach)
NO_GLUT_premises = []
NO_GLUT_conclusions = ['\\func_unineg (A \\uniwedge \\func_unineg A)']
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

# DOUBLE NEGATION INTRODUCTION
DN_INTRO_premises = ['A']
DN_INTRO_conclusions = ['\\func_unineg \\func_unineg A']
DN_INTRO_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,  # Note: expectation differs from elimination
}
DN_INTRO_example = [
    DN_INTRO_premises,
    DN_INTRO_conclusions,
    DN_INTRO_settings
]

# DOUBLE NEGATION IDENTITY
DN_ID_premises = []
DN_ID_conclusions = ['(A \\uniequiv \\func_unineg \\func_unineg A)']
DN_ID_settings = {
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
DN_ID_example = [
    DN_ID_premises,
    DN_ID_conclusions,
    DN_ID_settings,
]

# TRIPLE NEGATION IDENTITY
TN_ID_premises = []
TN_ID_conclusions = ['(\\func_unineg A \\uniequiv \\func_unineg \\func_unineg \\func_unineg A)']
TN_ID_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': True,
}
TN_ID_example = [
    TN_ID_premises,
    TN_ID_conclusions,
    TN_ID_settings,
]

# QUADRUPLE NEGATION (False premise in static approach)
QN_ENTAIL_premises = ['\\func_unineg \\func_unineg \\func_unineg \\func_unineg A']
QN_ENTAIL_conclusions = ['\\func_unineg \\func_unineg A']
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

# CONJUNCTION DEMORGANS RL (False premise in static approach)
CONJ_DM_RL_premises = ['(\\func_unineg A \\univee \\func_unineg B)']
CONJ_DM_RL_conclusions = ['\\func_unineg (A \\uniwedge B)']
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
DISJ_DM_LR_premises = ['\\func_unineg (A \\univee B)']
DISJ_DM_LR_conclusions = ['(\\func_unineg A \\uniwedge \\func_unineg B)']
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
DISJ_DM_RL_premises = ['(\\func_unineg A \\uniwedge \\func_unineg B)']
DISJ_DM_RL_conclusions = ['\\func_unineg (A \\univee B)']
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

# GLUTS (Check for contradictions)
GLUTS_premises = ['(A \\uniwedge \\func_unineg A)']
GLUTS_conclusions = []
GLUTS_settings = {
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
GLUTS_example = [
    GLUTS_premises,
    GLUTS_conclusions,
    GLUTS_settings,
]

# NO GAPS
GAPS_premises = []
GAPS_conclusions = ['(A \\univee \\func_unineg A)']
GAPS_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
GAPS_example = [
    GAPS_premises,
    GAPS_conclusions,
    GAPS_settings,
]

# THEOREM 17 (Complex unilateral formula)
T17_premises = []
T17_conclusions = ['((\\func_unineg (A \\univee B) \\uniequiv (\\func_unineg A \\uniwedge \\func_unineg B)) \\uniwedge (\\func_unineg (A \\uniwedge B) \\uniequiv (\\func_unineg A \\univee \\func_unineg B)))']
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

################################
### DISTRIBUTION LAWS        ###
################################

# DISJUNCTION DISTRIBUTION LR
DISJ_DIST_LR_premises = ['(A \\univee (B \\uniwedge C))']
DISJ_DIST_LR_conclusions = ['((A \\univee B) \\uniwedge (A \\univee C))']
DISJ_DIST_LR_settings = {
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
DISJ_DIST_LR_example = [
    DISJ_DIST_LR_premises,
    DISJ_DIST_LR_conclusions,
    DISJ_DIST_LR_settings
]

# DISJUNCTION DISTRIBUTION RL
DISJ_DIST_RL_premises = ['((A \\univee B) \\uniwedge (A \\univee C))']
DISJ_DIST_RL_conclusions = ['(A \\univee (B \\uniwedge C))']
DISJ_DIST_RL_settings = {
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
DISJ_DIST_RL_example = [
    DISJ_DIST_RL_premises,
    DISJ_DIST_RL_conclusions,
    DISJ_DIST_RL_settings
]

# CONJUNCTION DISTRIBUTION LR
CONJ_DIST_LR_premises = ['(A \\uniwedge (B \\univee C))']
CONJ_DIST_LR_conclusions = ['((A \\uniwedge B) \\univee (A \\uniwedge C))']
CONJ_DIST_LR_settings = {
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
CONJ_DIST_LR_example = [
    CONJ_DIST_LR_premises,
    CONJ_DIST_LR_conclusions,
    CONJ_DIST_LR_settings
]

# CONJUNCTION DISTRIBUTION RL
CONJ_DIST_RL_premises = ['((A \\uniwedge B) \\univee (A \\uniwedge C))']
CONJ_DIST_RL_conclusions = ['(A \\uniwedge (B \\univee C))']
CONJ_DIST_RL_settings = {
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
CONJ_DIST_RL_example = [
    CONJ_DIST_RL_premises,
    CONJ_DIST_RL_conclusions,
    CONJ_DIST_RL_settings
]

###############################
### ABSORPTION LAWS         ###
###############################

# CONJUNCTION ABSORPTION RL
CONJ_ABS_RL_premises = ['(A \\uniwedge (A \\univee B))']
CONJ_ABS_RL_conclusions = ['A']
CONJ_ABS_RL_settings = {
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
CONJ_ABS_RL_example = [
    CONJ_ABS_RL_premises,
    CONJ_ABS_RL_conclusions,
    CONJ_ABS_RL_settings
]

# CONJUNCTION ABSORPTION LR
CONJ_ABS_LR_premises = ['A']
CONJ_ABS_LR_conclusions = ['(A \\uniwedge (A \\univee B))']
CONJ_ABS_LR_settings = {
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
CONJ_ABS_LR_example = [
    CONJ_ABS_LR_premises,
    CONJ_ABS_LR_conclusions,
    CONJ_ABS_LR_settings
]

# DISJUNCTION ABSORPTION RL
DISJ_ABS_RL_premises = ['(A \\univee (A \\uniwedge B))']
DISJ_ABS_RL_conclusions = ['A']
DISJ_ABS_RL_settings = {
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
DISJ_ABS_RL_example = [
    DISJ_ABS_RL_premises,
    DISJ_ABS_RL_conclusions,
    DISJ_ABS_RL_settings
]

# DISJUNCTION ABSORPTION LR
DISJ_ABS_LR_premises = ['A']
DISJ_ABS_LR_conclusions = ['(A \\univee (A \\uniwedge B))']
DISJ_ABS_LR_settings = {
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
DISJ_ABS_LR_example = [
    DISJ_ABS_LR_premises,
    DISJ_ABS_LR_conclusions,
    DISJ_ABS_LR_settings
]

##################################
### ASSOCIATIVITY LAWS         ###
##################################

# CONJUNCTION ASSOCIATIVITY RL
CONJ_ASSOC_RL_premises = ['((A \\uniwedge B) \\uniwedge C)']
CONJ_ASSOC_RL_conclusions = ['(A \\uniwedge (B \\uniwedge C))']
CONJ_ASSOC_RL_settings = {
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
CONJ_ASSOC_RL_example = [
    CONJ_ASSOC_RL_premises,
    CONJ_ASSOC_RL_conclusions,
    CONJ_ASSOC_RL_settings
]

# CONJUNCTION ASSOCIATIVITY LR
CONJ_ASSOC_LR_premises = ['(A \\uniwedge (B \\uniwedge C))']
CONJ_ASSOC_LR_conclusions = ['((A \\uniwedge B) \\uniwedge C)']
CONJ_ASSOC_LR_settings = {
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
CONJ_ASSOC_LR_example = [
    CONJ_ASSOC_LR_premises,
    CONJ_ASSOC_LR_conclusions,
    CONJ_ASSOC_LR_settings
]

# DISJUNCTION ASSOCIATIVITY RL
DISJ_ASSOC_RL_premises = ['((A \\univee B) \\univee C)']
DISJ_ASSOC_RL_conclusions = ['(A \\univee (B \\univee C))']
DISJ_ASSOC_RL_settings = {
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
DISJ_ASSOC_RL_example = [
    DISJ_ASSOC_RL_premises,
    DISJ_ASSOC_RL_conclusions,
    DISJ_ASSOC_RL_settings
]

# DISJUNCTION ASSOCIATIVITY LR
DISJ_ASSOC_LR_premises = ['(A \\univee (B \\univee C))']
DISJ_ASSOC_LR_conclusions = ['((A \\univee B) \\univee C)']
DISJ_ASSOC_LR_settings = {
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
DISJ_ASSOC_LR_example = [
    DISJ_ASSOC_LR_premises,
    DISJ_ASSOC_LR_conclusions,
    DISJ_ASSOC_LR_settings
]

##############################
### ADDITIONAL EXAMPLES    ###
##############################

# DE MORGAN NOT/OR (from t_unilateral.py test_CMP_T1)
EX_TH_17_premises = ['\\func_unineg (A \\univee B)']
EX_TH_17_conclusions = ['(\\func_unineg A \\uniwedge \\func_unineg B)']
EX_TH_17_settings = {
    'N': 3,
    'possible': True,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
EX_TH_17_example = [
    EX_TH_17_premises,
    EX_TH_17_conclusions,
    EX_TH_17_settings
]

# DE MORGAN NOT/AND (from t_unilateral.py test_IMP_T2)
EX_TH_18_premises = ['(A \\uniwedge (B \\univee C))']
EX_TH_18_conclusions = ['((A \\univee B) \\uniwedge (A \\univee B))']
EX_TH_18_settings = {
    'N': 3,
    'possible': True,
    'contingent': True,
    'non_empty': True,
    'non_null': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
EX_TH_18_example = [
    EX_TH_18_premises,
    EX_TH_18_conclusions,
    EX_TH_18_settings
]

#########################
### IDENTITY EXAMPLES ###
#########################

# DISTRIBUTION IDENTITY: CONJUNCTION OVER DISJUNCTION
CONJ_DIST_ID_premises = []
CONJ_DIST_ID_conclusions = ['((A \\uniwedge (B \\univee C)) \\uniequiv ((A \\uniwedge B) \\univee (A \\uniwedge C)))']
CONJ_DIST_ID_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'expectation': False,
}
CONJ_DIST_ID_example = [
    CONJ_DIST_ID_premises,
    CONJ_DIST_ID_conclusions,
    CONJ_DIST_ID_settings,
]

# DISTRIBUTION IDENTITY: DISJUNCTION OVER CONJUNCTION
DISJ_DIST_ID_premises = []
DISJ_DIST_ID_conclusions = ['((A \\univee (B \\uniwedge C)) \\uniequiv ((A \\univee B) \\uniwedge (A \\univee C)))']
DISJ_DIST_ID_settings = {
    'N': 3,
    'possible': False,
    'contingent': False,
    'non_empty': True,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,
}
DISJ_DIST_ID_example = [
    DISJ_DIST_ID_premises,
    DISJ_DIST_ID_conclusions,
    DISJ_DIST_ID_settings,
]

# CONJUNCTIVE DEMORGANS IDENTITY
CONJ_DM_ID_premises = []
CONJ_DM_ID_conclusions = ["(\\func_unineg (P \\uniwedge Q) \\uniequiv (\\func_unineg P \\univee \\func_unineg Q))"]
CONJ_DM_ID_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
CONJ_DM_ID_example = [
    CONJ_DM_ID_premises,
    CONJ_DM_ID_conclusions,
    CONJ_DM_ID_settings
]

# DISJUNCTIVE DEMORGANS IDENTITY
DISJ_DM_ID_premises = []
DISJ_DM_ID_conclusions = ["(\\func_unineg (P \\univee Q) \\uniequiv (\\func_unineg P \\uniwedge \\func_unineg Q))"]
DISJ_DM_ID_settings = {
    'N': 3,
    'possible': False,
    'contingent': True,
    'non_empty': False,
    'non_null': False,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'expectation': False,
}
DISJ_DM_ID_example = [
    DISJ_DM_ID_premises,
    DISJ_DM_ID_conclusions,
    DISJ_DM_ID_settings
]

############################
### COUNTERMODEL EXAMPLES ###
############################

# CONTRADICTION CASE
EX_CM_1_premises = []
EX_CM_1_conclusions = ['\\func_unineg (A \\univee \\func_unineg A)']
EX_CM_1_settings = {
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
EX_CM_1_example = [
    EX_CM_1_premises,
    EX_CM_1_conclusions,
    EX_CM_1_settings,
]

# DISTRIBUTION AND/OR
EX_CM_15_premises = ['((A \\uniwedge B) \\univee (A \\uniwedge C))']
EX_CM_15_conclusions = ['(A \\uniwedge (B \\univee C))']
EX_CM_15_settings = {
    'N': 3,
    'possible': True,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'fusion_closure': False,
    'max_time': 5,
    'iterate': 1,
    'expectation': True,
}
EX_CM_15_example = [
    EX_CM_15_premises,
    EX_CM_15_conclusions,
    EX_CM_15_settings,
]

########################
### EXAMPLE REGISTRY ###
########################

# Which examples to run - comprehensive test suite
example_range = {
    # Frame examples
    "Only Frame Constraints": EMPTY_example,                    # COUNTERMODEL
    "No Gaps": GAPS_example,                                    # COUNTERMODEL
    "No Gluts": NO_GLUT_example,                                # COUNTERMODEL
    "Atomic Example": ATOMIC_example,                           # THEOREM
    
    # Basic countermodel examples
    "EX_CM_1": EX_CM_1_example,                                 # COUNTERMODEL
    "EX_CM_15": EX_CM_15_example,                               # THEOREM
    
    # Bilateral negation examples (Problematic in static)
    "Negation to Sentence": NEG_TO_SENT_example,                # COUNTERMODEL
    "Sentence to Negation": SENT_TO_NEG_example,                # COUNTERMODEL
    "Double Negation Introduction": DN_INTRO_example,           # COUNTERMODEL
    "Double Negation Elimination": DN_ELIM_example,             # COUNTERMODEL
    "Triple Negation Entailment": TN_ENTAIL_example,            # COUNTERMODEL
    "Quadruple Negation Entailment": QN_ENTAIL_example,         # COUNTERMODEL
    "Disjunctive Syllogism": DISJ_SYLL_example,                 # THEOREM

    # DeMorgan's laws (Problematic in static)
    "Conjunctive DeMorgan's LR": CONJ_DM_LR_example,            # COUNTERMODEL
    "Conjunctive DeMorgan's RL": CONJ_DM_RL_example,            # COUNTERMODEL
    "Disjunctive DeMorgan's LR": DISJ_DM_LR_example,            # COUNTERMODEL
    "Disjunctive DeMorgan's RL": DISJ_DM_RL_example,            # COUNTERMODEL

    # Distribution laws
    "Conjunctive Distribution LR": CONJ_DIST_LR_example,        # THEOREM
    "Conjunctive Distribution RL": CONJ_DIST_RL_example,        # THEOREM
    "Disjunctive Distribution LR": DISJ_DIST_LR_example,        # THEOREM
    "Disjunctive Distribution RL": DISJ_DIST_RL_example,        # THEOREM

    # Absorption laws
    "Conjunctive Absorption LR": CONJ_ABS_LR_example,           # THEOREM
    "Conjunctive Absorption RL": CONJ_ABS_RL_example,           # THEOREM
    "Disjunctive Absorption LR": DISJ_ABS_LR_example,           # THEOREM
    "Disjunctive Absorption RL": DISJ_ABS_RL_example,           # THEOREM

    # Associativity laws
    "Conjunctive Associativity LR": CONJ_ASSOC_LR_example,      # THEOREM
    "Conjunctive Associativity RL": CONJ_ASSOC_RL_example,      # THEOREM
    "Disjunctive Associativity LR": DISJ_ASSOC_LR_example,      # THEOREM
    "Disjunctive Associativity RL": DISJ_ASSOC_RL_example,      # THEOREM

    # Identity examples
    "Double Negation Identity": DN_ID_example,                  # COUNTERMODEL
    "Triple Negation Identity": TN_ID_example,                  # COUNTERMODEL
    "Conjunctive DeMorgan's Identity": CONJ_DM_ID_example,      # COUNTERMODEL
    "Disjunctive DeMorgan's Identity": DISJ_DM_ID_example,      # COUNTERMODEL
    "Conjunctive Distribution Identity": CONJ_DIST_ID_example,  # THEOREM
    "Disjunctive Distribution Identity": DISJ_DIST_ID_example,  # COUNTERMODEL

    # Complex examples
    "T17 (DeMorgan Theorem)": T17_example,                      # COUNTERMODEL
    "EX_TH_17": EX_TH_17_example,                               # COUNTERMODEL  
    "EX_TH_18": EX_TH_18_example,                               # THEOREM
}

# Test subset - uncomment to run just problematic examples
# Strategy 2 examples dictionary - combined collection
unit_tests = test_example_range = {
    # Additional quick tests to get theorem/countermodel status
    "EMPTY": EMPTY_example,
    "ATOMIC": ATOMIC_example,
    "GAPS": GAPS_example,
    "GLUTS": GLUTS_example,
    "NEG_TO_SENT": NEG_TO_SENT_example,
    "SENT_TO_NEG": SENT_TO_NEG_example,
    "DN_INTRO": DN_INTRO_example,
    "DN_ID": DN_ID_example,
    "TN_ID": TN_ID_example,
}

# Switch between full suite and test subset
# example_range = test_example_range  # Uncomment to use test subset

# Which semantic theories to compare
semantic_theories = {
    "unilateral_theory": unilateral_theory,
    # "default_theory": default_theory,  # Uncomment to compare with bilateral logic
}

if __name__ == "__main__":
    # This allows the module to be run with dev_cli.py
    # The ModelChecker framework will use example_range and semantic_theories
    pass
