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

# # k AXIOM (BOX)
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']

# # K AXIOM (TOP)
# premises = ['(top boxright (A rightarrow B))']
# conclusions = ['((top boxright A) rightarrow (top boxright B))']

# # T AXIOM (TOP)
# # SLOW: crashed locally; MIT servers found a model in 5 seconds
# premises = ['(top boxright A)']
# conclusions = ['A']

# # T AXIOM (BOX)
# premises = ['Box A']
# conclusions = ['A']

# # 4 AXIOM (TOP)
# premises = ['(top boxright A)']
# conclusions = ['(top boxright (top boxright A))']

# # 4 AXIOM (BOX)
# premises = ['Box A']
# conclusions = ['Box Box A']

# # B AXIOM (TOP)
# # SLOW: crashed locally; MIT servers found a model in 1600 seconds
# premises = ['A']
# conclusions = ['(top boxright neg (top boxright neg A))']

# # B AXIOM (BOX)
# premises = ['A']
# conclusions = ['Box Diamond A']

# # 5 AXIOM (TOP)
# # SLOW: 12.9 seconds locally
# premises = ['(top boxright A)']
# conclusions = ['(top boxright neg (top boxright neg A))']

# # 5 AXIOM (BOX)
# premises = ['Box A']
# conclusions = ['Box Diamond A']

# # BOX-TO-TOP EQUIVALENCE
# premises = ['Box A']
# conclusions = ['(top boxright A)']

# # TOP-TO-BOX EQUIVALENCE
# premises = ['(top boxright A)']
# conclusions = ['Box A']

# # NECESSARY EQUIVALENCE
# conclusions = ['Box ((A vee neg A) leftrightarrow (B vee neg B))']





################################
######## COUNTERMODELS #########
################################

# # NECESSITATED ARGUMENTS COUNTERFACTUAL MODUS PONENS
# premises = ['Box A','(A boxright B)']
# conclusions = ['Box B']

# # COUNTERFACTUAL IMPLIES STRICT CONDITIONAL
# premises = ['(A boxright B)']
# conclusions = ['Box (A rightarrow B)']
