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

# time cutoff for increasing N
max_time = 1

# find critical value of N
optimize_bool = False

# make all propositions contingent
contingent_bool = True

# print all Z3 constraints if a model is found
print_cons_bool = False

# print all states including impossible states
print_impossible_states_bool = True

# present option to append output to file
save_bool = False




###############################
##### MODAL COUNTERMODELS #####
###############################

# """CM1:  NECESSITATED ARGUMENTS COUNTERFACTUAL MODUS PONENS """
N = 3
premises = ['Box A','(A rightarrow B)']
conclusions = ['Box B']
contingent = False

# # """CM2:  COUNTERFACTUAL IMPLIES STRICT CONDITIONAL """
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['Box (A rightarrow B)']
# contingent = True






################################
######### MODAL LOGIC ##########
################################


# # """ML1: """
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']
# contingent = False

# # ML2: K AXIOM (BOX)
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']
# contingent = False

# # ML3: K AXIOM (TOP)
# N = 3
# premises = ['(top boxright (A rightarrow B))']
# conclusions = ['((top boxright A) rightarrow (top boxright B))']
# contingent = False

# # ML4: T AXIOM (TOP)
# N = 3
# premises = ['(top boxright A)']
# conclusions = ['A']
# contingent = False

# # ML5: T AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['A']
# contingent = False

# # ML6: 4 AXIOM (TOP)
# N = 3
# premises = ['(top boxright A)']
# conclusions = ['(top boxright (top boxright A))']
# contingent = False

# # ML7: 4 AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['Box Box A']
# contingent = False

# # ML8: B AXIOM (TOP) NOTE: with Z3 quantifiers MIT ran for 1600 seconds; now .0328 seconds locally
# N = 3
# premises = ['A']
# conclusions = ['(top boxright neg (top boxright neg A))']
# contingent = False

# # ML9: B AXIOM (BOX)
# N = 3
# premises = ['A']
# conclusions = ['Box Diamond A']
# contingent = False

# # ML10: 5 AXIOM (TOP) SLOW: 12.9 seconds locally
# N = 3
# premises = ['(top boxright A)']
# conclusions = ['(top boxright neg (top boxright neg A))']
# contingent = False

# # ML11: 5 AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['Box Diamond A']
# contingent = False

# # ML12: BOX-TO-TOP EQUIVALENCE
# N = 3
# premises = ['Box A']
# conclusions = ['(top boxright A)']
# contingent = False

# # ML13: # TOP-TO-BOX EQUIVALENCE
# N = 3
# premises = ['(top boxright A)']
# conclusions = ['Box A']
# contingent = False

# # ML14: NECESSARY EQUIVALENCE
# N = 3
# premises = []
# conclusions = ['Box ((A vee neg A) leftrightarrow (B vee neg B))']
# contingent = False
