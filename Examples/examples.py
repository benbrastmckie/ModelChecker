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
print_impossible_states_bool = False

# present option to append output to file
save_bool = False


################################
########### WORKING ############
################################

# # NOTE: this works
# premises = ['not A','(neg A boxright B)']
# premises = ['neg A','(neg A boxright B)']
# conclusions = ['B']

# # NOTE: false premise model?
premises = ['neg A','(not A boxright B)']
# premises = ['not A','(not A boxright B)']
# premises = ['A','(not neg A boxright B)']
# premises = ['A','(neg not A boxright B)']
# premises = ['neg A','(not neg neg A boxright B)']
# premises = ['neg A','(neg not neg A boxright B)']
# premises = ['neg A','(neg neg not A boxright B)']
conclusions = ['B']

# # NOTE: this works
# premises = ['neg A','(neg neg neg A boxright B)']
# conclusions = ['B']

# premises = ['A','(neg not neg not A boxright B)']
# conclusions = ['B']


### INVALID ###

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING
# premises = ['(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# premises = ['(A boxright C)', 'Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# # SLOW: requires N = 4 and 242 seconds on the MIT server
# premises = ['neg A','(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL CONTRAPOSITION
# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# # SLOW: requires N = 4 and 125 seconds on the MIT server
# premises = ['neg B','(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# # TRANSITIVITY
# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# # SLOW: 78 seconds on the MIT server
# premises = ['neg A','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # SOBEL SEQUENCE (N = 3)
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 14.8 seconds locally
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
#     'neg ((A wedge B) boxright X)', # 155.4 seconds on the MIT servers
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

# # FACTIVITY
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

# premises = ['A','(A rightarrow B)']
# conclusions = ['B']

# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

# premises = ['(A boxright C)','(B boxright C)','((A wedge B) boxright C)']
# conclusions = ['((A vee B) boxright C)']

# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A vee B) boxright C)']

# premises = ['(A boxright (B wedge C))']
# conclusions = ['(A boxright B)']

# SLOW: 8.4 seconds locally
# premises = ['(A boxright B)','(A boxright C)']
# conclusions = ['(A boxright (B wedge C))']

# # SLOW: 13.8 seconds locally
# premises = ['(A boxright B)']
# conclusions = ['(A rightarrow B)']

# # SLOW: 41.6 seconds locally
# premises = ['(A boxright B)','((A wedge B) boxright C)']
# conclusions = ['(A boxright C)']

# # SLOW: crashed locally; MIT servers found a model in 5 seconds
# premises = ['((A vee B) boxright C)']
# conclusions = ['((A wedge B) boxright C)']





### MODAL LOGIC ###

# # K axiom (box)
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']

# # T axiom (top)
# # SLOW: crashed locally; MIT servers found a model in 5 seconds
# premises = ['(top boxright A)']
# conclusions = ['A']

# # T axiom (box)
# premises = ['Box A']
# conclusions = ['A']

# # 4 axiom (top)
# premises = ['(top boxright A)']
# conclusions = ['(top boxright (top boxright A))']

# # 4 axiom (box)
# premises = ['Box A']
# conclusions = ['Box Box A']

# # B axiom (top)
# # SLOW: crashed locally; MIT servers found a model in 1600 seconds
# premises = ['A']
# conclusions = ['(top boxright neg (top boxright neg A))']

# # B axiom (box)
# premises = ['A']
# conclusions = ['Box Diamond A']

# # 5 axiom (top)
# # SLOW: 12.9 seconds locally
# premises = ['(top boxright A)']
# conclusions = ['(top boxright neg (top boxright neg A))']

# # 5 axiom (box)
# premises = ['Box A']
# conclusions = ['Box Diamond A']

# # box-to-top equivalence
# premises = ['Box A']
# conclusions = ['(top boxright A)']






################################
######### NOT WORKING ##########
################################

### FALSE PREMISE MODEL ###

# SOBEL SEQUENCE (N = 3)
premises = [
    '(A boxright X)', # 0.03 seconds locally
    'neg ((A wedge B) boxright X)', # 14.8 seconds locally
    '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
    'neg ((((A wedge B) wedge C) wedge D) boxright X)', # 7.8 seconds locally
]
conclusions = []



### CRASHED: MODALITY ###

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



### CRASHED: ANTECEDENT STRENGTHENING/WEAKENING ###

# # CRASH: MIT servers killed process
# # DOUBLE COUNTERFACTUAL ANTECEDENT STRENGTHENING
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # CRASH: MIT servers killed process
# # COUNTERFACTUAL ANTECEDENT WEAKENING
# premises = ['Box A', '((A wedge B) boxright C)']
# conclusions = ['(B boxright C)']



### CRASHED: IMPORTATION ###

# # CRASH: MIT servers killed process
# # COUNTERFACTUAL IMPORTATION WITH POSSIBILITY
# premises = ['(A boxright (B boxright C))','Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']



### CRASHED: TRANSITIVITY ###

# # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# # NOTE: does not find counter models with N = 3
# premises = ['neg A','neg B','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

