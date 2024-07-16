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
##### COUNTERFACTUAL LOGIC #####
################################

### INVALID ###

# NOTE: DOES NOT FIND COUNTERMODEL
N = 2
premises = ['(A \\boxright (B \\boxright C))']
conclusions = ['((A \\wedge B) \\boxright C)']

# # # COUNTERFACTUAL ANTECEDENT STRENGTHENING
# premises = ['(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
# premises = ['(A circleright C)']
# conclusions = ['((A wedge B) circleright C)']

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# premises = ['(A boxright C)', 'Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# # SLOW: requires N = 4 and 242 seconds on the MIT server
# N = 4
# premises = ['neg A','(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# # SLOW: requires N = 4 and 347 seconds on the MIT server
# N = 4
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL CONTRAPOSITION
# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# # SLOW: requires N = 4 and 125 seconds on the MIT server
# N = 4
# premises = ['neg B','(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# # TRANSITIVITY
# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# # SLOW: 78 seconds on the MIT server
# N = 4
# premises = ['neg A','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # SOBEL SEQUENCE (N = 3)
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 1.4 seconds locally
#     '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
#     # 'neg ((((A wedge B) wedge C) wedge D) boxright X)', # 7.8 seconds locally
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # 20.5 seconds locally
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # 64 seconds on the MIT servers
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # 327.2 seconds on the MIT servers
# ]
# conclusions = []

# # SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
# premises = [
#     'Diamond A',
#     '(A boxright X)', # 0.7 seconds locally
#     'Diamond (A wedge B)',
#     'neg ((A wedge B) boxright X)', # N = 3 took 4.8 seconds N = 4 took 155.4 seconds on the MIT servers
#     # 'Diamond ((A wedge B) wedge C)',
#     # '(((A wedge B) wedge C) boxright X)', # ? seconds
#     # 'Diamond (((A wedge B) wedge C) wedge D)',
#     # 'neg ((((A wedge B) wedge C) wedge D) boxright X)', # ? seconds
#     # 'Diamond ((((A wedge B) wedge C) wedge D) wedge E)',
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # ? seconds
#     # 'Diamond (((((A wedge B) wedge C) wedge D) wedge E) wedge F)',
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # ? seconds
#     # 'Diamond ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G)',
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # ? seconds
# ]
# conclusions = []

# # COUNTERFACTUAL EXCLUDED MIDDLE
# premises = ['neg A']
# conclusions = ['(A boxright B)','(A boxright neg B)']

# # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']

# # # DISJUNCTIVE ANTECEDENT
# N = 4 # ran for 40 seconds locally
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A vee B) boxright C)']

# # MUST FACTIVITY
# premises = ['A','B']
# conclusions = ['(A boxright B)']

# # COUNTERFACTUAL EXPORTATION
# premises = ['((A wedge B) boxright C)']
# conclusions = ['(A boxright (B boxright C))']

# # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# premises = ['((A wedge B) boxright C)','Diamond (A wedge B)']
# conclusions = ['(A boxright (B boxright C))']

# # COUNTERFACTUAL IMPORTATION
# # SLOW: MIT servers found a model in 467 seconds
# premises = ['(A boxright (B boxright C))']
# conclusions = ['((A wedge B) boxright C)']





### VALID ###

# # FACTIVITY MIGHT
# premises = ['A','B']
# conclusions = ['(A circleright B)']

# premises = ['A','(A rightarrow B)']
# conclusions = ['B']

# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

# premises = ['(A boxright C)','(B boxright C)','((A wedge B) boxright C)']
# conclusions = ['((A vee B) boxright C)']

# premises = ['(A boxright (B wedge C))']
# conclusions = ['(A boxright B)']

# SLOW: 8.4 seconds locally
# premises = ['(A boxright B)','(A boxright C)']
# conclusions = ['(A boxright (B wedge C))']

# # COUNTERFACTUAL MODUS PONENS
# premises = ['A','(A boxright B)']
# conclusions = ['B']

# premises = ['((A vee B) boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # SLOW: 48.3 seconds locally
# premises = ['(A boxright B)','((A wedge B) boxright C)']
# conclusions = ['(A boxright C)']
