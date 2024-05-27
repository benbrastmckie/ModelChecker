"""
module for user inputs.
"""
import os
parent_directory = os.path.dirname(__file__)
file_name = os.path.basename(__file__)

################################
########## SETTINGS ############
################################

# number of atomic states
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# print all states including impossible states
print_impossible_states_bool = True

# present option to append output to file
save_bool = False






################################
######### NOT WORKING ##########
################################

### FALSE PREMISE MODEL ###

# # SOBEL SEQUENCE (N = 3)
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 14.8 seconds locally
#     '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
#     'neg ((((A wedge B) wedge C) wedge D) boxright X)', # 7.8 seconds locally
# ]
# conclusions = []




################################
########### CRASHED ############
################################

### MODALITY ###

# # CRASH: MIT servers killed process
# # TOP-TO-BOX EQUIVALENCE
# premises = ['(top boxright A)']
# conclusions = ['Box A']

# # CRASH: MIT servers killed process
# # K AXIOM (TOP)
# premises = ['(top boxright (A rightarrow B))']
# conclusions = ['((top boxright A) rightarrow (top boxright B))']

# # CRASH: MIT servers killed process
# # COUNTERFACTUAL IMPLIES STRICT CONDITIONAL
# premises = ['(A boxright B)']
# conclusions = ['Box (A rightarrow B)']

# # CRASH: MIT servers killed process
# premises = ['Box A','(A boxright B)']
# conclusions = ['Box B']





### COUNTERFACTUAL IMPORTATION ###

# # CRASH: MIT servers killed process
# # COUNTERFACTUAL IMPORTATION WITH POSSIBILITY
# premises = ['(A boxright (B boxright C))','Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']



### COUNTERFACTUAL TRANSITIVITY WITH NEGATION ###

# # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# # NOTE: does not find counter models with N = 3
# premises = ['neg A','neg B','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']
