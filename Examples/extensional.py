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



#####################################
##### EXTENSIONAL COUNTERMODELS #####
#####################################

# # EXT_CM1
# N = 3
# premises = ['A']
# conclusions = ['neg A']
# contingent = True






#############################
##### EXTENSIONAL LOGIC #####
#############################

# # EXT1
# N = 3
# premises = ['A','(A rightarrow B)']
# conclusions = ['B']
# contingent = False

# # EXT2
# N = 3
# premises = []
# conclusions = ['(A rightarrow (B rightarrow A))']
# contingent = False

# # EXT3
# N = 3
# premises = []
# conclusions = ['((A rightarrow (B rightarrow C)) rightarrow ((A rightarrow B) rightarrow (A rightarrow C)))']
# contingent = False

# # EXT4
# N = 3
# premises = []
# conclusions = ['((neg A rightarrow neg B) rightarrow (B rightarrow A))']
# contingent = False
