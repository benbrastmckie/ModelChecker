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
    Semantics,
    Proposition,
)

from operators import (
    default_operators,
)


########################
### DEFAULT SETTINGS ###
########################

general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "compare_theories": False,
}

example_settings = {  # defaults can be tailored to each example
    'N' : 3,
    'contingent' : False,
    'disjoint' : False,
    'non_empty' : False,
    'non_null' : False,
    'max_time' : 1,
}


####################################
### DEFINE THE SEMANTIC THEORIES ###
####################################

default_theory = {
    "semantics": Semantics,
    "proposition": Proposition,
    "operators": default_operators,
    # default theory does not require a translation dictionary for comparison
    # since the examples are stated in the language of the default theory
}


#####################
### COUNTERMODELS ###
#####################

# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_1_premises = ['(A \\boxright C)']
CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]

# CF_CM_2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
CF_CM_2_premises = ['(A \\circleright C)']
CF_CM_2_conclusions = ['((A \\wedge B) \\circleright C)']
CF_CM_2_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CF_CM_2_example = [
    CF_CM_2_premises,
    CF_CM_2_conclusions,
    CF_CM_2_settings,
]

# CF_CM_7: COUNTERFACTUAL CONTRAPOSITION
CF_CM_7_premises = ['(A \\boxright B)']
CF_CM_7_conclusions = ['(\\neg B \\boxright \\neg A)']
CF_CM_7_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CF_CM_7_example = [
    CF_CM_7_premises,
    CF_CM_7_conclusions,
    CF_CM_7_settings,
]

# CF_CM_10: TRANSITIVITY
CF_CM_10_premises = ['(A \\boxright B)','(B \\boxright C)']
CF_CM_10_conclusions = ['(A \\boxright C)']
CF_CM_10_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CF_CM_10_example = [
    CF_CM_10_premises,
    CF_CM_10_conclusions,
    CF_CM_10_settings,
]

# CF_CM_13: SOBEL SEQUENCE
CF_CM_13_premises = [
    '(A \\boxright X)',
    '\\neg ((A \\wedge B) \\boxright X)',
    '(((A \\wedge B) \\wedge C) \\boxright X)',
    '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)',
    '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)',
    '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)',
    '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
]
CF_CM_13_conclusions = []
CF_CM_13_settings = {
    'N' : 4,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CF_CM_13_example = [
    CF_CM_13_premises,
    CF_CM_13_conclusions,
    CF_CM_13_settings,
]

### CONSTITUTIVE OPERATORS ###

# CL_CM_3: GROUND CONJUNCTION SUPPLEMENTATION
CL_CM_3_premises = ['(A \\leq B)','(C \\leq D)']
CL_CM_3_conclusions = ['((A \\wedge C) \\leq (B \\wedge D))']
CL_CM_3_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CL_CM_3_example = [
    CL_CM_3_premises,
    CL_CM_3_conclusions,
    CL_CM_3_settings,
]

# CL_CM_4: ESSENCE DISJUNCTION SUPPLEMENTATION
CL_CM_4_premises = ['(A \\sqsubseteq B)','(C \\sqsubseteq D)']
CL_CM_4_conclusions = ['((A \\vee C) \\sqsubseteq (B \\vee D))']
CL_CM_4_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CL_CM_4_example = [
    CL_CM_4_premises,
    CL_CM_4_conclusions,
    CL_CM_4_settings,
]

# CL_CM_5: IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
CL_CM_5_premises = []
CL_CM_5_conclusions = ['(A \\equiv (A \\vee (A \\wedge B)))']
CL_CM_5_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CL_CM_5_example = [
    CL_CM_5_premises,
    CL_CM_5_conclusions,
    CL_CM_5_settings,
]

# CL_CM_6: IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
CL_CM_6_premises = []
CL_CM_6_conclusions = ['(A \\equiv (A \\wedge (A \\vee B)))']
CL_CM_6_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CL_CM_6_example = [
    CL_CM_6_premises,
    CL_CM_6_conclusions,
    CL_CM_6_settings,
]

# CL_CM_10: IDENTITY DISTRIBUTION
CL_CM_10_premises = []
CL_CM_10_conclusions = ['((A \\vee (B \\wedge C)) \\equiv ((A \\vee B) \\wedge (A \\vee C)))']
CL_CM_10_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}
CL_CM_10_example = [
    CL_CM_10_premises,
    CL_CM_10_conclusions,
    CL_CM_10_settings,
]



############################
### LOGICAL CONSEQUENCES ###
############################

# CF_TH_2: COUNTERFACTUAL MODUS PONENS
CF_TH_2_premises = ['A','(A \\boxright B)']
CF_TH_2_conclusions = ['B']
CF_TH_2_example = [
    CF_TH_2_premises,
    CF_TH_2_conclusions,
    example_settings,  # can use example_settings from above
]

# CF_TH_3: WEAKENED TRANSITIVITY
CF_TH_3_premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
CF_TH_3_conclusions = ['(A \\boxright C)']
CF_TH_3_example = [
    CF_TH_3_premises,
    CF_TH_3_conclusions,
    example_settings,
]

# CF_TH_5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
CF_TH_5_premises = ['((A \\vee B) \\boxright C)']
CF_TH_5_conclusions = ['(A \\boxright C)']
CF_TH_5_example = [
    CF_TH_5_premises,
    CF_TH_5_conclusions,
    example_settings,
]

# CF_TH_10: MIGHT FACTIVITY
CF_TH_10_settings = example_settings  # copy defaults
CF_TH_10_settings['N'] = 4  # change atomic number
CF_TH_10_premises = ['A','B']
CF_TH_10_conclusions = ['(A \\circleright B)']
CF_TH_10_example = [
    CF_TH_10_premises,
    CF_TH_10_conclusions,
    CF_TH_10_settings,
]

# CF_TH_11: DEFINITION OF NEC
CF_TH_11_premises = ['(\\neg A \\boxright \\bot)']
CF_TH_11_conclusions = ['(\\top \\boxright A)']
CF_TH_11_example = [
    CF_TH_11_premises,
    CF_TH_11_conclusions,
    example_settings,
]

### CONSTITUTIVE OPERATORS ###

# CL_TH_1: GROUND TO ESSENCE
CL_TH_1_premises = ['(A \\leq B)']
CL_TH_1_conclusions = ['(\\neg A \\sqsubseteq \\neg B)']
CL_TH_1_example = [
    CL_TH_1_premises,
    CL_TH_1_conclusions,
    example_settings,
]

# CL_TH_2: ESSENCE TO GROUND 
CL_TH_2_premises = ['(A \\sqsubseteq B)']
CL_TH_2_conclusions = ['(\\neg A \\leq \\neg B)']
CL_TH_2_example = [
    CL_TH_2_premises,
    CL_TH_2_conclusions,
    example_settings,
]

# CL_TH_3: ESSENCE TO IDENTITY
CL_TH_3_premises = ['(A \\sqsubseteq B)']
CL_TH_3_conclusions = ['((A \\wedge B) \\equiv B)']
CL_TH_3_example = [
    CL_TH_3_premises,
    CL_TH_3_conclusions,
    example_settings,
]

# CL_TH_4: IDENTITY TO ESSENCE 
CL_TH_4_premises = ['((A \\wedge B) \\equiv B)']
CL_TH_4_conclusions = ['(A \\sqsubseteq B)']
CL_TH_4_example = [
    CL_TH_4_premises,
    CL_TH_4_conclusions,
    example_settings,
]

# CL_TH_5: GROUND TO IDENTITY
CL_TH_5_premises = ['(A \\leq B)']
CL_TH_5_conclusions = ['((A \\vee B) \\equiv B)']
CL_TH_5_example = [
    CL_TH_5_premises,
    CL_TH_5_conclusions,
    example_settings,
]

# CL_TH_6: IDENTITY TO GROUND 
CL_TH_6_premises = ['((A \\vee B) \\equiv B)']
CL_TH_6_conclusions = ['(A \\leq B)']
CL_TH_6_example = [
    CL_TH_6_premises,
    CL_TH_6_conclusions,
    example_settings,
]

# CL_TH_7: NEGATION TRANSPARENCY
CL_TH_7_premises = ['(A \\equiv B)']
CL_TH_7_conclusions = ['(\\neg A \\equiv \\neg B)']
CL_TH_7_example = [
    CL_TH_7_premises,
    CL_TH_7_conclusions,
    example_settings,
]

# CL_TH_8: REVERSE NEGATION TRANSPARENCY
CL_TH_8_premises = ['(\\neg A \\equiv \\neg B)']
CL_TH_8_conclusions = ['(A \\equiv B)']
CL_TH_8_example = [
    CL_TH_8_premises,
    CL_TH_8_conclusions,
    example_settings,
]



###############################################
### DEFINE EXAMPLES AND THEORIES TO COMPUTE ###
###############################################

# NOTE: at least one theory is required, multiple are permitted for comparison
semantic_theories = {
    "Brast-McKie" : default_theory,
    # additional theories will require their own translation dictionaries
}

# NOTE: at least one example is required, multiple are permitted for comparison
example_range = {
    # Counterfactual Countermodels
    "CF_CM_1" : CF_CM_1_example,
    # "CF_CM_2" : CF_CM_2_example,
    # "CF_CM_7" : CF_CM_7_example,
    # "CF_CM_10" : CF_CM_10_example,
    # "CF_CM_13" : CF_CM_13_example,

    # Counterfactual Theorems
    # "CF_TH_2" : CF_TH_2_example,
    # "CF_TH_3" : CF_TH_3_example,
    # "CF_TH_5" : CF_TH_5_example,
    # "CF_TH_10" : CF_TH_10_example,
    # "CF_TH_11" : CF_TH_11_example,
}
