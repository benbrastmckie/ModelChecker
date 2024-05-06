"""
Example module for user inputs.
Premises are conjoined and conclusions are disjoined.
To save the output, change 'save_bool' to 'True' below.
The examples below can be turned on and off by (un)commenting the premises an conclusions.
The final pair of premises and conclusions to be defined will be run when the file is tested.
"""
import os
parent_directory = os.path.dirname(__file__)

################################
########## SETTINGS ############
################################

# number of atomic states included in the models
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to append output to file
save_bool = False


################################
######## COUNTER MODELS ########
################################

### INVALID ###

premises = ['\\neg A','(A \\boxright (B \\vee C))']
conclusions = ['(A \\boxright B)','(A \\boxright C)']

# premises = ['A','B']
# conclusions = ['(A \\boxright B)']

# premises = ['\\neg A']
# conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']

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

# premises = ['\\Diamond (A \\wedge B)','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# premises = ['\\neg (\\top \\boxright \\neg (A \\wedge B))','((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# premises = ['(\\Box A \\vee \\Box B)']
# conclusions = ['(A \\wedge B)']

# premises = ['\\Diamond A', '\\Diamond B']
# conclusions = ['\\Diamond (A \\wedge B)']

# premises = ['(A \\boxright B)']
# conclusions = ['\\Box (A \\rightarrow B)']


################################
############ LOGIC #############
################################

# premises = []
# conclusions = ['(A \\vee \\neg A)']

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


### MODAL LOGIC ###

# # K axiom (box)
# premises = ['\\Box (A \\rightarrow B)']
# conclusions = ['(\\Box A \\rightarrow \\Box B)']

# # T axiom (top)
# premises = ['(\\top \\boxright A)']
# conclusions = ['A']

# # T axiom (box)
# premises = ['\\Box A']
# conclusions = ['A']

# # 4 axiom (top)
# premises = ['(\\top \\boxright A)']
# conclusions = ['(\\top \\boxright (\\top \\boxright A))']

# # 4 axiom (box)
# premises = ['\\Box A']
# conclusions = ['\\Box \\Box A']

# # B axiom (top)
# # NOTE: this crashed
# premises = ['A']
# conclusions = ['(\\top \\boxright \\neg (\\top \\boxright \\neg A))']

# # B axiom (box)
# premises = ['A']
# conclusions = ['\\Box \\Diamond A']

# # 5 axiom (top)
# premises = ['(\\top \\boxright A)']
# conclusions = ['(\\top \\boxright \\neg (\\top \\boxright \\neg A))']

# # 5 axiom (box)
# premises = ['\\Box A']
# conclusions = ['\\Box \\Diamond A']

# # box-to-top equivalence
# premises = ['\\Box A']
# conclusions = ['(\\top \\boxright A)']

# premises = ['\\Box A', '\\Diamond B']
# conclusions = ['\\Diamond (A \\wedge B)']

# premises = ['\\Box (A \\rightarrow B)']
# conclusions = ['(A \\boxright B)']
