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



