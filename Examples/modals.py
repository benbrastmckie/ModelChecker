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
########## MODAL LOGIC #########
################################

# premises = ['A','(A rightarrow B)']
# conclusions = ['B']

# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']

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


