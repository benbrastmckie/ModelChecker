"""
NOTE:

This file includes a number of selected examples to help get a sense of the semantics.
Further examples files are included in the parent directory.
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

# COUNTERFACTUAL ANTECEDENT STRENGTHENING
premises = ['(A boxright C)']
conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# premises = ['(A boxright C)', 'Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL CONTRAPOSITION
# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# # TRANSITIVITY
# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # COUNTERFACTUAL EXCLUDED MIDDLE
# premises = ['neg A']
# conclusions = ['(A boxright B)','(A boxright neg B)']

# # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']

# # COUNTERFACTUAL MUST FACTIVITY
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

# # SOBEL SEQUENCE
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 14.8 seconds locally
#     '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
# ]
# conclusions = []

# # SOBEL SEQUENCE WITH POSSIBILITY
# premises = [
#     'Diamond A',
#     '(A boxright X)', # 0.7 seconds locally
#     'Diamond (A wedge B)',
#     'neg ((A wedge B) boxright X)', # 4.8 seconds locally
# ]
# conclusions = []



### VALID ###

# # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
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





################################
########## MODAL LOGIC #########
################################

# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']

# # K axiom (box)
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']

# # T axiom (box)
# premises = ['Box A']
# conclusions = ['A']

# # 4 axiom (box)
# premises = ['Box A']
# conclusions = ['Box Box A']

# # B axiom (box)
# premises = ['A']
# conclusions = ['Box Diamond A']

# # 5 axiom (box)
# premises = ['Box A']
# conclusions = ['Box Diamond A']

# # box-to-top equivalence
# premises = ['Box A']
# conclusions = ['(top boxright A)']





################################
###### CONSTITUTIVE LOGIC ######
################################

### DEFINITIONAL EQUIVALENTS ###

# # GROUND TO ESSENCE
# premises = ['(A leq B)']
# conclusions = ['(neg A sqsubseteq neg B)']

# # ESSENCE TO GROUND
# premises = ['(A sqsubseteq B)']
# conclusions = ['(neg A leq neg B)']

# # ESSENCE TO IDENTITY
# premises = ['(A sqsubseteq B)']
# conclusions = ['((A wedge B) equiv B)']

# # IDENTITY TO ESSENCE
# # SLOW: 12.7 seconds locally
# premises = ['((A wedge B) equiv B)']
# conclusions = ['(A sqsubseteq B)']

# # GROUND TO IDENTITY
# premises = ['(A leq B)']
# conclusions = ['((A vee B) equiv B)']

# # IDENTITY TO GROUND
# # SLOW: 18.1 seconds locally
# premises = ['((A vee B) equiv B)']
# conclusions = ['(A leq B)']

# # NEGATION TRANSPARENCY
# premises = ['(A equiv B)']
# conclusions = ['(neg A equiv neg B)']

# # REVERSE NEGATION TRANSPARENCY
# premises = ['(neg A equiv neg B)']
# conclusions = ['(A equiv B)']



### MODAL INTERACTION ###

# # GROUND TO STRICT IMPLICATION
# premises = ['(A leq B)']
# conclusions = ['Box (A rightarrow B)']

# # ESSENCE TO STRICT IMPLICATION
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (B rightarrow A)']

# conclusions = ['(A sqsubseteq (A wedge B))']
# conclusions = ['(neg A leq neg (A wedge B))']
# conclusions = ['((A wedge B) leq (A vee B))']

# premises = ['(A leq B)','(B leq C)']
# conclusions = ['(A leq C)']

# premises = ['(A leq C)','(B leq C)']
# conclusions = ['((A vee B) leq C)']

# premises = ['(A leq B)','(B leq A)']
# conclusions = ['(A equiv B)']

# premises = ['((A wedge B) equiv B)']
# conclusions = ['(A sqsubseteq B)']



### INVALID ###

# # STRICT IMPLICATION TO GROUND
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A leq B)']

# # STRICT IMPLICATION TO ESSENCE
# premises = ['Box (B rightarrow A)']
# conclusions = ['(A sqsubseteq B)']





################################
###### EXCLUSION OPERATOR ######
################################

### INVALID ###

# premises = ['Box (A leftrightarrow B)']
# conclusions = ['(not A equiv not B)']

# premises = []
conclusions = ['(A equiv not not A)']
# conclusions = ['(A equiv not not not not A)']



### VALID ###

# premises = ['(A equiv B)']
# conclusions = ['(not A equiv not B)']

# premises = []
# conclusions = ['(A vee not A)']
# conclusions = ['not (A wedge not A)']

# premises = ['A']
# conclusions = ['not not A']

# premises = []
# conclusions = ['(not not A equiv not not not not A)']
