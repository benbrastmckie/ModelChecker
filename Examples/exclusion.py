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
###### EXCLUSION OPERATOR ######
################################

### INVALID ###

# premises = ['Box (A leftrightarrow B)']
# conclusions = ['(not A equiv not B)']

# # premises = []
# conclusions = ['(A equiv not not A)']
# # conclusions = ['(A equiv not not not not A)']



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
# # premises = ['not A','(not A boxright B)']
# premises = ['not A','Diamond A','Diamond B','(not A boxright B)']
# conclusions = ['B']

# NOTE: false premise model?
premises = ['not A','(not A boxright B)']
# premises = ['pre A','Diamond A','Diamond B','(pre A boxright B)']
conclusions = ['B']






################################
##### PRECLUSION OPERATOR ######
################################

### INVALID ###

# premises = ['Box (A leftrightarrow B)']
# conclusions = ['(pre A equiv pre B)']

# # premises = []
# conclusions = ['(A equiv not not A)']
# # conclusions = ['(A equiv not not not not A)']



### VALID ###

# premises = ['(A equiv B)']
# conclusions = ['(not A equiv not B)']

# premises = []
# conclusions = ['(A vee not A)']
# conclusions = ['not (A wedge not A)']

# premises = ['A']
# conclusions = ['pre pre A']

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
# # premises = ['not A','(not A boxright B)']
# premises = ['not A','Diamond A','Diamond B','(not A boxright B)']
# conclusions = ['B']

