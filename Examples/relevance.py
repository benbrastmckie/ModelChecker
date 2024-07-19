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

# find critical value of N
optimize = False

# time cutoff for increasing N
max_time = 1

# make all propositions contingent
contingent = False

# print all Z3 constraints if a model is found
print_cons_bool = False

# print all states including impossible states
print_impossible_states_bool = False

# present option to append output to file
save_bool = False



###################################
##### RELEVANCE COUNTERMODELS #####
###################################

"""RL_CM1: ANTECEDENT STRENGTHENING"""
N = 3
premises = []
conclusions = ['((A wedge B) preceq A)']
contingent = True

# """RL_CM2: ANTECEDENT WEAKENING"""
# N = 3
# premises = []
# conclusions = ['((A vee B) preceq A)']
# contingent = True

# """RL_CM3: RELEVANCE TRANSITIVITY"""
# N = 3
# premises = ['(A preceq B)', '(B preceq C)']
# conclusions = ['(A preceq C)']
# contingent = True

# """RL_CM4: RELEVANT IMPLICATION: GROUND"""
# N = 3
# premises = ['Box (A rightarrow B)','(A preceq B)']
# conclusions = ['(A leq B)']
# contingent = True

# """RL_CM5: RELEVANT IMPLICATION: ESSENCE"""
# N = 3
# premises = ['Box (B rightarrow A)','(A preceq B)']
# conclusions = ['(A sqsubseteq B)']
# contingent = True

# """RL_CM6: RELEVANT IMPLICATION: IDENTITY"""
# N = 3
# premises = ['Box (A leftrightarrow B)','(A preceq B)','(B preceq A)']
# conclusions = ['(A equiv B)']
# contingent = True

# """RL_CM7: STRICT IMPLICATION"""
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A preceq B)']
# contingent = True

# """RL_CM8: REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']
# contingent = True

# """RL_CM9: REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(((A wedge B) vee (A wedge C)) preceq (A wedge (B vee C)))']
# contingent = True

# """RL_CM10: CONJUNCTION INTRODUCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['(A preceq (B wedge C))']
# contingent = True

# """RL_CM11: DISJUNCTION INTRODUCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['(A preceq (B vee C))']
# contingent = True






###########################
##### RELEVANCE LOGIC #####
###########################

### DEFINITIONAL EQUIVALENTS

# """RL1: RELEVANCE TO CONJUNCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['((A wedge B) leq B)']
# contingent = False

# """RL2: RELEVANCE TO DISJUNCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['((A vee B) sqsubseteq B)']
# contingent = False

# """RL3: CONJUNCTION TO RELEVANCE"""
# N = 3
# premises = ['((A wedge B) leq B)']
# conclusions = ['(A preceq B)']
# contingent = False

# """RL4: DISJUNCTION TO RELEVANCE"""
# N = 3
# premises = ['((A vee B) sqsubseteq B)']
# conclusions = ['(A preceq B)']
# contingent = False



### AXIOMS

# """RL5: CONJUNCTION INTRODUCTION"""
# N = 3
# premises = []
# conclusions = ['(A preceq (A wedge B))']
# contingent = False

# """RL6: DISJUNCTION INTRODUCTION"""
# N = 3
# premises = []
# conclusions = ['(A preceq (A vee B))']
# contingent = False




### CONSTITUTIVE INTERACTION

# """RL7: GROUNDING RELEVANCE"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['(A preceq B)']
# contingent = False

# """RL8: ESSENCE RELEVANCE"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['(A preceq B)']
# contingent = False

# """RL9: IDENTITY RELEVANCE"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(A preceq B)']
# contingent = False
