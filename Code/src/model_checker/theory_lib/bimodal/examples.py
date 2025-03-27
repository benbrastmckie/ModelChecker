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


#####################
### COUNTERMODELS ###
#####################

# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_1_premises = ['\\Box (A \\vee B)']
CF_CM_1_conclusions = ['(\\Box A \\vee \\Box B)']
CF_CM_1_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 5,
    'expectation' : True,
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]

# CF_CM_2: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_2_premises = ['(A \\vee B)']
CF_CM_2_conclusions = ['(A \\wedge B)']
CF_CM_2_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_2_example = [
    CF_CM_2_premises,
    CF_CM_2_conclusions,
    CF_CM_2_settings,
]

# CF_CM_3: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_3_premises = ['A', '\\neg B']
CF_CM_3_conclusions = ['\\Diamond (A \\wedge B)']
CF_CM_3_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_3_example = [
    CF_CM_3_premises,
    CF_CM_3_conclusions,
    CF_CM_3_settings,
]

# CF_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_4_premises = ['A']
CF_CM_4_conclusions = ['\\Box A']
CF_CM_4_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_4_example = [
    CF_CM_4_premises,
    CF_CM_4_conclusions,
    CF_CM_4_settings,
]


# CF_CM_5: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_5_premises = ['\\Diamond A', '\\Diamond B']
CF_CM_5_conclusions = ['\\Diamond (A \\wedge B)']
CF_CM_5_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_5_example = [
    CF_CM_5_premises,
    CF_CM_5_conclusions,
    CF_CM_5_settings,
]


# CF_CM_6: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_6_premises = ['\\Diamond A']
CF_CM_6_conclusions = ['\\Box A']
CF_CM_6_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_6_example = [
    CF_CM_6_premises,
    CF_CM_6_conclusions,
    CF_CM_6_settings,
]


# CF_CM_4: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_7_premises = ['\\Diamond A', '\\Diamond B']
# CF_CM_7_premises = ['\\neg \\Box \\neg A', '\\neg \\Box \\neg B']
CF_CM_7_conclusions = ['(A \\wedge \\neg B)']
CF_CM_7_settings = {
    'N' : 2,
    'M' : 2,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : True,
}
CF_CM_7_example = [
    CF_CM_7_premises,
    CF_CM_7_conclusions,
    CF_CM_7_settings,
]



############################
### LOGICAL CONSEQUENCES ###
############################

# CF_TH_2: COUNTERFACTUAL MODUS PONENS
CF_TH_1_premises = ['\\Box (A \\rightarrow B)']
CF_TH_1_conclusions = ['(\\Box A \\rightarrow \\Box B)']
CF_TH_1_settings = {
    'N' : 3,
    'M' : 3,
    'contingent' : False,
    'disjoint' : False,
    'max_time' : 1,
    'expectation' : False,
}
CF_TH_1_example = [
    CF_TH_1_premises,
    CF_TH_1_conclusions,
    CF_TH_1_settings,  # can use example_settings from above
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
    "CF_CM_1" : CF_CM_1_example,
    # "CF_CM_2" : CF_CM_2_example,
    # "CF_CM_3" : CF_CM_3_example,
    # "CF_CM_4" : CF_CM_4_example,
    # "CF_CM_5" : CF_CM_5_example,
    # "CF_CM_6" : CF_CM_6_example,
    # "CF_CM_7" : CF_CM_7_example,

    # Counterfactual Theorems
    # "CF_TH_1" : CF_TH_1_example,
}
