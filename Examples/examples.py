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

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING
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





################################
########## MODAL LOGIC #########
################################

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
# conclusions = ['(A equiv not not A)']



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



### TESTING ###

# # SLOW: ?? seconds
# premises = []
# conclusions = ['(not A equiv not not not A)']

# # SLOW: ?? seconds
# premises = ['(not A equiv not B)']
# conclusions = ['Box (A leftrightarrow B)']

# # CRASH: only tested locally
# premises = ['(not A equiv not B)']
# conclusions = ['(A equiv B)']

# # NOTE: false premise model?
# premises = ['not A','(not A boxright B)']
# # premises = ['not A','Diamond A','Diamond B','(not A boxright B)']
# conclusions = ['B']


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
