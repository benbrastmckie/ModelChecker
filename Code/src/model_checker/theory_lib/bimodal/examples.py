"""
INSTRUCTIONS: this module defines the semantic_theories and example_range.
From the project directory, run: model_checker examples.py
"""

##########################
### DEFINE THE IMPORTS ###
##########################

import sys
import os
sys.path.append(os.path.dirname(__file__))  # Add the current directory to sys.path

from semantic import (
    BimodalStructure,
    BimodalSemantics,
    BimodalProposition,
)

from operators import (
    intensional_operators,
)


########################
### DEFAULT SETTINGS ###
########################

general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

example_settings = {  # defaults can be tailored to each example
    'N' : 2,  # 2^N number of states
    'M' : 2, # M + 1 number of times
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
}


####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

intensional_theory = {
    "semantics": BimodalSemantics,
    "proposition": BimodalProposition,
    "model": BimodalStructure,
    "operators": intensional_operators,
    # translation dictionary is only required for comparison theories
}


###########################
### MODAL COUNTERMODELS ###
###########################


# BM_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_1_premises = ['\\Box (A \\vee B)']
BM_CM_1_conclusions = ['(\\Box A \\vee \\Box B)']
BM_CM_1_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
BM_CM_1_example = [
    BM_CM_1_premises,
    BM_CM_1_conclusions,
    BM_CM_1_settings,
]

# BM_CM_2: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_2_premises = ['(A \\vee B)']
BM_CM_2_conclusions = ['(A \\wedge B)']
BM_CM_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_2_example = [
    BM_CM_2_premises,
    BM_CM_2_conclusions,
    BM_CM_2_settings,
]

# BM_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_3_premises = ['A', '\\neg B']
BM_CM_3_conclusions = ['\\Diamond (A \\wedge B)']
BM_CM_3_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_3_example = [
    BM_CM_3_premises,
    BM_CM_3_conclusions,
    BM_CM_3_settings,
]

# BM_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_4_premises = ['A']
BM_CM_4_conclusions = ['\\Box A']
BM_CM_4_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_4_example = [
    BM_CM_4_premises,
    BM_CM_4_conclusions,
    BM_CM_4_settings,
]


# BM_CM_5: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_5_premises = ['\\Diamond A', '\\Diamond B']
BM_CM_5_conclusions = ['\\Diamond (A \\wedge B)']
BM_CM_5_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_5_example = [
    BM_CM_5_premises,
    BM_CM_5_conclusions,
    BM_CM_5_settings,
]


# BM_CM_6: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_6_premises = ['\\Diamond A']
BM_CM_6_conclusions = ['\\Box A']
BM_CM_6_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_6_example = [
    BM_CM_6_premises,
    BM_CM_6_conclusions,
    BM_CM_6_settings,
]


# BM_CM_7: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_7_premises = ['\\Diamond A', '\\Diamond B']
BM_CM_7_conclusions = ['(A \\wedge \\neg B)']
BM_CM_7_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_7_example = [
    BM_CM_7_premises,
    BM_CM_7_conclusions,
    BM_CM_7_settings,
]



###########################
### MODAL COUNTERMODELS ###
###########################

# BM_CM_8: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_CM_8_premises = ['A']
BM_CM_8_conclusions = ['\\Future A']
BM_CM_8_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_CM_8_example = [
    BM_CM_8_premises,
    BM_CM_8_conclusions,
    BM_CM_8_settings,
]



############################
### LOGICAL CONSEQUENCES ###
############################

# BM_TH_2: COUNTERFACTUAL MODUS PONENS
BM_TH_1_premises = ['\\Box (A \\rightarrow B)']
BM_TH_1_conclusions = ['(\\Box A \\rightarrow \\Box B)']
BM_TH_1_settings = {
    'N' : 3,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : False,
}
BM_TH_1_example = [
    BM_TH_1_premises,
    BM_TH_1_conclusions,
    BM_TH_1_settings,  # can use example_settings from above
]

# BM_TH_2: COUNTERFACTUAL ANTECEDENT STRENGTHENING
BM_TH_2_premises = ['A']
BM_TH_2_conclusions = ['\\Future \\past A']
BM_TH_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
BM_TH_2_example = [
    BM_TH_2_premises,
    BM_TH_2_conclusions,
    BM_TH_2_settings,
]




###############################################
### DEFINE EXAMPLES AND THEORIES TO COMPUTE ###
###############################################

# NOTE: at least one theory is required, multiple are permitted for comparison
semantic_theories = {
    "Brast-McKie" : intensional_theory,
    # additional theories will require their own translation dictionaries
}

# NOTE: at least one example is required, multiple are permitted for comparison
example_range = {
    # Counterfactual Countermodels
    # "BM_CM_1" : BM_CM_1_example,
    # "BM_CM_2" : BM_CM_2_example,
    # "BM_CM_3" : BM_CM_3_example,
    # "BM_CM_4" : BM_CM_4_example,
    # "BM_CM_5" : BM_CM_5_example,
    # "BM_CM_6" : BM_CM_6_example,
    "BM_CM_7" : BM_CM_7_example,
    # "BM_CM_8" : BM_CM_8_example,

    # Counterfactual Theorems
    # "BM_TH_1" : BM_TH_1_example,
    # "BM_TH_2" : BM_TH_2_example,
}
