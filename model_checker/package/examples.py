"""
module for user inputs.
"""
import os
parent_directory = os.path.dirname(__file__)

################################
########## SETTINGS ############
################################

# length of bitvectors
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to append output to file
save_bool = False


################################
########### WORKING ############
################################


### INVALID ###

# premises = []
# conclusions = []

# premises = ['A']
# conclusions = []

# premises = ['\\neg A','(A \\boxright (B \\vee C))']
# conclusions = ['(A \\boxright B)','(A \\boxright C)']

# # NOTE: if null verifiers are permitted, then null state verifies A
# # but possible state c does not?
# premises = ['A','B']
# conclusions = ['(A \\boxright B)']

# premises = ['A',]
# conclusions = ['\\neg A']

# premises = ['\\neg A']
# conclusions = ['A \\boxright B','(A \\boxright \\neg B)']

# premises = ['(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

# premises = ['(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# premises = ['A \\boxright C', '\\neg (A \\boxright \\neg B)']
# conclusions = ['\\neg ((A \\wedge B) \\boxright C)']

# premises = ['\\neg (\\top \\boxright \\neg (A \\wedge B))','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']









### VALID ###

# # NOTE: unsat_core seems satisfiable
# premises = []
# conclusions = ['(A \\vee \\neg A)']

# # NOTE: unsat_core seems satisfiable
# premises = []
# conclusions = ['\\neg (A \\wedge \\neg A)']

# premises = ['A','(A \\rightarrow B)']
# conclusions = ['B']

# premises = ['(A \\boxright B)']
# conclusions = ['(A \\rightarrow B)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)','((A \\wedge B) \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\vee B) \\boxright C)']

# premises = ['(A \\boxright (B \\wedge C))']
# conclusions = ['(A \\boxright B)']

# premises = ['(A \\boxright B)','(A \\boxright C)']
# conclusions = ['(A \\boxright (B \\wedge C))']

# premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright C)']

# premises = ['(\\top \\boxright A)']
# conclusions = ['A']

# premises = ['(\\top \\boxright A)']
# conclusions = ['(\\top \\boxright (\\top \\boxright A))']

premises = ['A']
conclusions = ['(\\top \\boxright \\neg (\\top \\boxright \\neg A))']


################################
######### NOT WORKING ##########
################################


### HIGH PRIORITY: NEGATION PROBLEM ###

# # NOTE: only works without \neg B
# premises = ['\\neg B','(A \\boxright B)']
# conclusions = ['(\\neg B \\boxright \\neg A)']

# # NOTE: only works without \neg A
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: only works without \neg A and \neg B
# premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
# conclusions = ['(A \\boxright C)']

### MEDIUM PRIORITY: NESTED COUNTERFACTUALS ###

# # NOTE: this does not find models for N = 3
# # NOTE: N = 4 ran for minutes on ssh
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: ssh killed process
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
