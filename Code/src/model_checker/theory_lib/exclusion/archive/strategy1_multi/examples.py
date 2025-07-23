"""
Examples Module for Exclusion Theory

This module tests the unilateral exclusion semantics, providing a means by which
to evaluate the logical relationships in a language with an exclusion operator
and comparing the result to the bilateral semantics.

Usage:
------
This module can be run in two ways:

1. Command Line:
   ```bash
   model-checker path/to/this/examples.py
   ```

2. IDE (VSCodium/VSCode):
   - Open this file in VSCodium/VSCode
   - Use the "Run Python File" play button in the top-right corner
   - Or right-click in the editor and select "Run Python File"

Configuration:
-------------
The examples and theories to be run can be configured by:

1. Modifying which examples are run:
   - Edit the example_range dictionary
   - Comment/uncomment specific examples
   - Modify semantic_theories to change which theories to compare

2. To add new examples:
   - Define premises, conclusions, and settings
   - Follow the naming conventions:
     - Countermodels: EX_CM_*
     - Theorems: EX_TH_*
   - Add to example_range dictionary

Module Structure:
----------------
1. Imports:
   - System utilities (os, sys)
   - Local semantic definitions (ExclusionSemantics, UnilateralProposition, ExclusionStructure)
   - Local operator definitions (exclusion_operators)
   - Default theory components for comparison

2. Semantic Theories:
   - exclusion_theory: Implements exclusion logic with unilateral operators
   - default_theory: Classical logic implementation for comparison
   - default_dictionary: Translates from unilateral to bilateral sentences

3. Example Categories:
   - Countermodels (EX_CM_*): Examples demonstrating invalid inferences
   - Logical Consequences (EX_TH_*): Examples of valid logical relationships

Example Format:
--------------
Each example is structured as a list: [premises, conclusions, settings]
- premises: List of formulas that serve as assumptions
- conclusions: List of formulas to be tested
- settings: Dictionary of specific settings for this example

Settings Options:
----------------
- N: Number of atomic propositions (default: 3)
- contingent: Whether to use contingent valuations
- disjoint: Whether to enforce disjoint valuations
- non_empty: Whether to enforce non-empty valuations
- non_null: Whether to enforce non-null valuations
- fusion_closure: Whether to enforce fusion closure
- max_time: Maximum computation time in seconds
- iterate: Number of iterations for modal operators
- expectation: Whether the example is expected to be valid

Notes:
------
- At least one semantic theory must be included in semantic_theories
- At least one example must be included in example_range
- Some examples may require adjusting the settings to produce good models

Help:
-----
More information can be found in the README.md for the exclusion theory.
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

# # OLD Exclusion
# from semantic_old import (
#     ExclusionSemantics,
#     UnilateralProposition,
#     ExclusionStructure,
# )
# from operators_old import exclusion_operators

# NEW Exclusion
from semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from operators import exclusion_operators

# Default + Utils
from model_checker.theory_lib.default import (
    Semantics,
    Proposition,
    ModelStructure,
    default_operators,
)

__all__ = [
    'general_settings',
    'example_settings',
    'exclusion_theory',
    'semantic_theories',
    'test_example_range',
    'all_example_range',
]

####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

exclusion_theory = {
    "semantics": ExclusionSemantics,
    "proposition": UnilateralProposition,
    "model": ExclusionStructure,
    "operators": exclusion_operators,
    # base theory does not require a translation dictionary for comparison
    # since the examples are stated in the language of the default theory
}

default_dictionary = {
    "\\exclude" : "\\neg",
    "\\uniwedge" : "\\wedge",
    "\\univee" : "\\vee",
    "\\uniequiv" : "\\equiv",
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : True,
}

# premises = ['\\exclude (A \\univee B)']
# conclusions = ['(\\exclude A \\uniwedge \\exclude B)']

# premises = ['\\exclude (A \\uniwedge B)']
# conclusions = ['(\\exclude A \\univee \\exclude B)']

# premises = ['(A \\uniequiv B)']

# premises = []
# conclusions = ["(\\exclude (A \\uniwedge B) \\uniequiv (\\exclude A \\univee \\exclude B))"]
# settings['N'] = 4

# premises = []
# conclusions = ["(\\exclude (A \\univee B) \\uniequiv (\\exclude A \\uniwedge \\exclude B))"]

# premises = []
# conclusions = ["((A \\univee (B \\uniwedge C)) \\uniequiv ((A \\univee B) \\uniwedge (A \\univee C)))"]
# settings['N'] = 4

# premises = []
# conclusions = ["((A \\uniwedge (B \\univee C)) \\uniequiv ((A \\uniwedge B) \\univee (A \\uniwedge C)))"]

# premises = ['(A \\uniwedge (B \\univee C))']
# conclusions = ['((A \\univee B) \\uniwedge (A \\univee C))']

# premises = ['\\exclude (A \\uniwedge B)']
# conclusions = ['(\\exclude A \\univee \\exclude B)']




#####################
### COUNTERMODELS ###
#####################

# TRIVIAL CASE FOR CHECKING FRAME CONSTRAINTS
EMPTY_premises = []
EMPTY_conclusions = []
EMPTY_settings = {
    'N' : 2,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 2,
    'iterate' : 1,
    'expectation' : True,
}
EMPTY_example = [
    EMPTY_premises,
    EMPTY_conclusions,
    EMPTY_settings,
]

# CONTRADICTION CASE FOR TESTING
# EX_CM_1_premises = ['\\exclude (A \\univee \\exclude A)'] # FALSE PREMISE MODEL
# EX_CM_1_premises = ['(A \\uniwedge \\exclude A)']
EX_CM_1_premises = [] # FALSE PREMISE MODEL
EX_CM_1_conclusions = ['\\exclude (A \\univee \\exclude A)'] # FALSE PREMISE MODEL
# EX_CM_1_conclusions = []
EX_CM_1_settings = {
    'N' : 2,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'iterate' : 1,
    'expectation' : True,
}
EX_CM_1_example = [
    EX_CM_1_premises,
    EX_CM_1_conclusions,
    EX_CM_1_settings,
]

# NO GLUTS
# GLUTS_premises = ['A', '\\exclude A']
GLUTS_premises = ['(A \\uniwedge \\exclude A)']
GLUTS_conclusions = []
GLUTS_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'iterate' : 1,
    'expectation' : True,
}
GLUTS_example = [
    GLUTS_premises,
    GLUTS_conclusions,
    GLUTS_settings,
]

# NO GAPS
GAPS_premises = []
GAPS_conclusions = ['(A \\univee \\exclude A)']
GAPS_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
GAPS_example = [
    GAPS_premises,
    GAPS_conclusions,
    GAPS_settings,
]

# DISTRIBUTION AND/OR (from t_exclusion.py test_CMP_CM1)
EX_CM_15_premises = ['((A \\uniwedge B) \\univee (A \\uniwedge C))']
EX_CM_15_conclusions = ['(A \\uniwedge (B \\univee C))']
EX_CM_15_settings = {
    'N' : 3,
    'possible' : True,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'iterate' : 1,
    'expectation' : True,
}
EX_CM_15_example = [
    EX_CM_15_premises,
    EX_CM_15_conclusions,
    EX_CM_15_settings,
]

# TODO: scan many models
# DOUBLE NEGATION IDENTITY
DN_ID_premises = []
DN_ID_conclusions = ['(A \\uniequiv \\exclude \\exclude A)']
DN_ID_settings = {
    'N' : 2,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'iterate' : 1,
    'expectation' : True,
}
DN_ID_example = [
    DN_ID_premises,
    DN_ID_conclusions,
    DN_ID_settings,
]

# DOUBLE NEGATION ELIMINATION
DN_ELIM_premises = ['\\exclude \\exclude A']
DN_ELIM_conclusions = ['A']
DN_ELIM_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'iterate' : 1,
    'expectation' : True,
}
DN_ELIM_example = [
    DN_ELIM_premises,
    DN_ELIM_conclusions,
    DN_ELIM_settings
]

# DOUBLE NEGATION INTRODUCTION
DN_INTRO_premises = ['A']
DN_INTRO_conclusions = ['\\exclude \\exclude A']
DN_INTRO_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False, # CHECK
}
DN_INTRO_example = [
    DN_INTRO_premises,
    DN_INTRO_conclusions,
    DN_INTRO_settings
]

# TRIPLE NEGATION ENTAILMENT
TN_ENTAIL_premises = ['\\exclude \\exclude \\exclude A']
TN_ENTAIL_conclusions = ['\\exclude A']
TN_ENTAIL_settings = { # TODO: print discrepancies
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'expectation' : True,
}
TN_ENTAIL_example = [
    TN_ENTAIL_premises,
    TN_ENTAIL_conclusions,
    TN_ENTAIL_settings
]

# TRIPLE NEGATION IDENTITY
TN_ID_premises = []
TN_ID_conclusions = ['(\\exclude A \\uniequiv \\exclude \\exclude \\exclude A)']
TN_ID_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : True,
    'non_null' : True,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'expectation' : True,
}
TN_ID_example = [
    TN_ID_premises,
    TN_ID_conclusions,
    TN_ID_settings, # these can be customized by example
]

# QUADRUPLE NEGATION
QN_ENTAIL_premises = ['\\exclude \\exclude \\exclude \\exclude A']
QN_ENTAIL_conclusions = ['\\exclude \\exclude A']
QN_ENTAIL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 20,
    'expectation' : True,
}
QN_ENTAIL_example = [
    QN_ENTAIL_premises,
    QN_ENTAIL_conclusions,
    QN_ENTAIL_settings
]



############################
### LOGICAL CONSEQUENCES ###
############################

# DISJUNCTIVE SYLLOGISM
DISJ_SYLL_premises = ['(A \\univee B)', '\\exclude B']
DISJ_SYLL_conclusions = ['A']
DISJ_SYLL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
DISJ_SYLL_example = [
    DISJ_SYLL_premises,
    DISJ_SYLL_conclusions,
    DISJ_SYLL_settings
]

# CONJUNCTION DEMORGANS LR
CONJ_DM_LR_premises = ['\\exclude (A \\uniwedge B)']
CONJ_DM_LR_conclusions = ['(\\exclude A \\univee \\exclude B)']
CONJ_DM_LR_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
CONJ_DM_LR_example = [
    CONJ_DM_LR_premises,
    CONJ_DM_LR_conclusions,
    CONJ_DM_LR_settings
]

# CONJUNCTION DEMORGANS RL
CONJ_DM_RL_premises = ['(\\exclude A \\univee \\exclude B)']
CONJ_DM_RL_conclusions = ['\\exclude (A \\uniwedge B)']
CONJ_DM_RL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
CONJ_DM_RL_example = [
    CONJ_DM_RL_premises,
    CONJ_DM_RL_conclusions,
    CONJ_DM_RL_settings
]

# DISJUNCTION DEMORGANS LR
DISJ_DM_LR_premises = ['\\exclude (A \\univee B)']
DISJ_DM_LR_conclusions = ['(\\exclude A \\uniwedge \\exclude B)']
DISJ_DM_LR_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
DISJ_DM_LR_example = [
    DISJ_DM_LR_premises,
    DISJ_DM_LR_conclusions,
    DISJ_DM_LR_settings
]

# DISJUNCTION DEMORGANS RL
DISJ_DM_RL_premises = ['(\\exclude A \\uniwedge \\exclude B)']
DISJ_DM_RL_conclusions = ['\\exclude (A \\univee B)']
DISJ_DM_RL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
DISJ_DM_RL_example = [
    DISJ_DM_RL_premises,
    DISJ_DM_RL_conclusions,
    DISJ_DM_RL_settings
]

# DISJUNCTION DISTRIBUTION LR
DISJ_DIST_LR_premises = ['(A \\univee (B \\uniwedge C))']
DISJ_DIST_LR_conclusions = ['((A \\univee B) \\uniwedge (A \\univee C))']
DISJ_DIST_LR_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
CONJ_DIST_RL_example = [
    CONJ_DIST_RL_premises,
    CONJ_DIST_RL_conclusions,
    CONJ_DIST_RL_settings
]

# CONJUNCTION ABSORPTION RL
CONJ_ABS_RL_premises = ['(A \\uniwedge (A \\univee B))']
CONJ_ABS_RL_conclusions = ['A']
CONJ_ABS_RL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
DISJ_ABS_LR_example = [
    DISJ_ABS_LR_premises,
    DISJ_ABS_LR_conclusions,
    DISJ_ABS_LR_settings
]

# CONJUNCTION ASSOCIATIVITY RL
CONJ_ASSOC_RL_premises = ['((A \\uniwedge B) \\uniwedge C)']
CONJ_ASSOC_RL_conclusions = ['(A \\uniwedge (B \\uniwedge C))']
CONJ_ASSOC_RL_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
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
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
DISJ_ASSOC_LR_example = [
    DISJ_ASSOC_LR_premises,
    DISJ_ASSOC_LR_conclusions,
    DISJ_ASSOC_LR_settings
]

# DE MORGAN NOT/OR (from t_exclusion.py test_CMP_T1)
EX_TH_17_premises = ['\\exclude (A \\univee B)']
EX_TH_17_conclusions = ['(\\exclude A \\uniwedge \\exclude B)']
EX_TH_17_settings = {
    'N' : 3,
    'possible' : True,
    'contingent' : True,
    'non_empty' : True,
    'non_null' : True,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
EX_TH_17_example = [
    EX_TH_17_premises,
    EX_TH_17_conclusions,
    EX_TH_17_settings
]

# DE MORGAN NOT/AND (from t_exclusion.py test_IMP_T2)
EX_TH_18_premises = ['(A \\uniwedge (B \\univee C))']
EX_TH_18_conclusions = ['((A \\univee B) \\uniwedge (A \\univee B))']
EX_TH_18_settings = {
    'N' : 3,
    'possible' : True,
    'contingent' : True,
    'non_empty' : True,
    'non_null' : True,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
EX_TH_18_example = [
    EX_TH_18_premises,
    EX_TH_18_conclusions,
    EX_TH_18_settings
]

# DISTRIBUTION IDENTITY: CONJUNCTION OVER DISJUNCTION 
CONJ_DIST_ID_premises = []
CONJ_DIST_ID_conclusions = ['((A \\uniwedge (B \\univee C)) \\uniequiv ((A \\uniwedge B) \\univee (A \\uniwedge C)))']
CONJ_DIST_ID_settings = { # agree
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'expectation' : False,
}
CONJ_DIST_ID_example = [
    CONJ_DIST_ID_premises,
    CONJ_DIST_ID_conclusions,
    CONJ_DIST_ID_settings,
]

# DISTRIBUTION IDENTITY: DISJUNCTION OVER CONJUNCTION  
DISJ_DIST_ID_premises = []
DISJ_DIST_ID_conclusions = ['((A \\univee (B \\uniwedge C)) \\uniequiv ((A \\univee B) \\uniwedge (A \\univee C)))']
DISJ_DIST_ID_settings = { # agree
    'N' : 3,
    'possible' : False,
    'contingent' : False,
    'non_empty' : True,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 10,
    'iterate' : 1,
    'expectation' : True,
}
DISJ_DIST_ID_example = [
    DISJ_DIST_ID_premises,
    DISJ_DIST_ID_conclusions,
    DISJ_DIST_ID_settings,
]

# CONJUNCTIVE DEMORGANS IDENTITY
CONJ_DM_ID_premises = []
CONJ_DM_ID_conclusions = ["(\\exclude (P \\uniwedge Q) \\uniequiv (\\exclude P \\univee \\exclude Q))"] # should find cm if here
CONJ_DM_ID_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : True,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
CONJ_DM_ID_example = [
    CONJ_DM_ID_premises,
    CONJ_DM_ID_conclusions,
    CONJ_DM_ID_settings
]

# DISJUNCTIVE DEMORGANS IDENTITY
DISJ_DM_ID_premises = []
DISJ_DM_ID_conclusions = ["(\\exclude (P \\uniwedge Q) \\uniequiv (\\exclude P \\univee \\exclude Q))"] # should find cm if here
DISJ_DM_ID_settings = {
    'N' : 3,
    'possible' : False,
    'contingent' : True,
    'non_empty' : False,
    'non_null' : False,
    'disjoint' : False,
    'fusion_closure' : False,
    'max_time' : 5,
    'expectation' : False,
}
DISJ_DM_ID_example = [
    DISJ_DM_ID_premises,
    DISJ_DM_ID_conclusions,
    DISJ_DM_ID_settings
]




###############################################
### DEFINE EXAMPLES AND THEORIES TO COMPUTE ###
###############################################

# NOTE: at least one theory is required, multiple are permitted for comparison
semantic_theories = {
    "exclusion" : exclusion_theory,
    # "default" : default_theory,
}

# Strategy 1 examples dictionary - combined collection
unit_tests = test_example_range = {
    # Countermodels
    "EX_CM_0" : EMPTY_example,
    "EX_CM_1" : EX_CM_1_example,
    "EX_CM_5" : DISJ_DIST_ID_example,
    "EX_CM_8" : DN_ID_example,
    "EX_CM_9" : DN_ELIM_example,
    "EX_CM_10" : DN_INTRO_example,
    "EX_CM_11" : TN_ENTAIL_example,
    "EX_CM_12" : TN_ID_example,
    "EX_CM_13" : QN_ENTAIL_example,
    "EX_CM_15" : EX_CM_15_example,

    # # Theorems
    "EX_TH_1" : DISJ_SYLL_example,
    "EX_TH_2" : CONJ_DM_LR_example,
    "EX_TH_3" : CONJ_DM_RL_example,
    "DISJ_DM_LR" : DISJ_DM_LR_example,
    "EX_TH_4" : DISJ_DM_RL_example,
    "EX_TH_5" : DISJ_DIST_LR_example,
    "EX_TH_6" : DISJ_DIST_RL_example,
    "EX_TH_7" : CONJ_DIST_LR_example,
    "EX_TH_8" : CONJ_DIST_RL_example,
    "EX_TH_9" : CONJ_ABS_RL_example,
    "EX_TH_10" : CONJ_ABS_LR_example,
    "EX_TH_11" : DISJ_ABS_RL_example,
    "EX_TH_12" : DISJ_ABS_LR_example,
    "EX_TH_13" : CONJ_ASSOC_RL_example,
    "EX_TH_14" : CONJ_ASSOC_LR_example,
    "EX_TH_15" : DISJ_ASSOC_RL_example,
    "EX_TH_16" : DISJ_ASSOC_LR_example,
    "EX_TH_17" : EX_TH_17_example,
    "EX_TH_18" : EX_TH_18_example,
    "EX_CM_2" : CONJ_DIST_ID_example,
}

# Comprehensive example range including all examples for enhanced testing
all_example_range = {
    # Frame examples
    "EMPTY" : EMPTY_example,
    "GLUTS" : GLUTS_example,
    "GAPS" : GAPS_example,
    
    # Basic countermodel examples
    "EX_CM_1" : EX_CM_1_example,
    "EX_CM_15" : EX_CM_15_example,
    
    # Classical negation examples
    "DN_ID" : DN_ID_example,
    "DN_ELIM" : DN_ELIM_example,
    "DN_INTRO" : DN_INTRO_example,
    "TN_ENTAIL" : TN_ENTAIL_example,
    "TN_ID" : TN_ID_example,
    "QN_ENTAIL" : QN_ENTAIL_example,
    
    # Logical operations
    "DISJ_SYLL" : DISJ_SYLL_example,
    
    # DeMorgan's laws
    "CONJ_DM_LR" : CONJ_DM_LR_example,
    "CONJ_DM_RL" : CONJ_DM_RL_example,
    "DISJ_DM_LR" : DISJ_DM_LR_example,
    "DISJ_DM_RL" : DISJ_DM_RL_example,
    
    # Distribution laws
    "DISJ_DIST_LR" : DISJ_DIST_LR_example,
    "DISJ_DIST_RL" : DISJ_DIST_RL_example,
    "CONJ_DIST_LR" : CONJ_DIST_LR_example,
    "CONJ_DIST_RL" : CONJ_DIST_RL_example,
    
    # Absorption laws
    "CONJ_ABS_RL" : CONJ_ABS_RL_example,
    "CONJ_ABS_LR" : CONJ_ABS_LR_example,
    "DISJ_ABS_RL" : DISJ_ABS_RL_example,
    "DISJ_ABS_LR" : DISJ_ABS_LR_example,
    
    # Associativity laws
    "CONJ_ASSOC_RL" : CONJ_ASSOC_RL_example,
    "CONJ_ASSOC_LR" : CONJ_ASSOC_LR_example,
    "DISJ_ASSOC_RL" : DISJ_ASSOC_RL_example,
    "DISJ_ASSOC_LR" : DISJ_ASSOC_LR_example,
    
    # Additional examples
    "EX_TH_17" : EX_TH_17_example,
    "EX_TH_18" : EX_TH_18_example,
    
    # Identity examples
    "CONJ_DIST_ID" : CONJ_DIST_ID_example,
    "DISJ_DIST_ID" : DISJ_DIST_ID_example,
    "CONJ_DM_ID" : CONJ_DM_ID_example,
    "DISJ_DM_ID" : DISJ_DM_ID_example,
}

# NOTE: at least one example is required, multiple are permitted for comparison
example_range = {

    # # Frame

    # "Only Frame Constraints" : EMPTY_example,
    "No Gaps" : GAPS_example, # countermodel
    "No Gluts" : GLUTS_example,
    # "EX_CM_1" : EX_CM_1_example, # countermodel


    # # Classical Negation Theorems (All should hold)

    "Double Negation Introduction" : DN_INTRO_example,
    "Double Negation Elimination" : DN_ELIM_example, # countermodel
    "Triple Negation Entailment" : TN_ENTAIL_example, # false_premise
    "Quadruple Negation Entailment" : QN_ENTAIL_example,
    "Disjunctive Syllogism" : DISJ_SYLL_example,

    "Conjunctive DeMorgan's LR" : CONJ_DM_LR_example, # countermodel
    "Conjunctive DeMorgan's RL" : CONJ_DM_RL_example, # false premise
    "Disjunctive DeMorgan's LR" : DISJ_DM_LR_example, # no countermodel
    "Disjunctive DeMorgan's RL" : DISJ_DM_RL_example, # false premise


    # Classical And/Or Theorems (All should hold)

    "Conjunctive Distribution LR" : CONJ_DIST_LR_example,
    "Conjunctive Distribution RL" : CONJ_DIST_RL_example,
    "Disjunctive Distribution LR" : DISJ_DIST_LR_example,
    "Disjunctive Distribution RL" : DISJ_DIST_RL_example,

    "Conjunctive Absorption LR" : CONJ_ABS_LR_example,
    "Conjunctive Absorption RL" : CONJ_ABS_RL_example,
    "Disjunctive Absorption LR" : DISJ_ABS_LR_example,
    "Disjunctive Absorption RL" : DISJ_ABS_RL_example,

    "Conjunctive Associativity LR" : CONJ_ASSOC_LR_example,
    "Conjunctive Associativity RL" : CONJ_ASSOC_RL_example,
    "Disjunctive Associativity LR" : DISJ_ASSOC_LR_example,
    "Disjunctive Associativity RL" : DISJ_ASSOC_RL_example,


    # Identity

    "Double Negation Identity" : DN_ID_example, # has countermodel
    "Triple Negation Identity" : TN_ID_example, # has countermodel
    "Conjuctive DeMorgan's Identity" : CONJ_DM_ID_example, # expect CM
    "Disjunctive DeMorgan's Identity" : DISJ_DM_ID_example, # countermodel
    "Conjunctive Distribution Identity" : CONJ_DIST_ID_example, # expect THM
    "Disjuctive Distribution Identity" : DISJ_DIST_ID_example, # expect CM

        # NOTE: this is invalid for the same reason as in the bilateral semantics
        # however, here the dual is valid, breaking the duality of the operators


    # Other

    "EX_CM_15" : EX_CM_15_example,
    "EX_TH_17" : EX_TH_17_example,
    "EX_TH_18" : EX_TH_18_example,

}



####################
### RUN EXAMPLES ###
####################

if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
