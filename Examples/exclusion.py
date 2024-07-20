"""
NOTE: the semantics for exclusion expressed by 'not' and preclusion expressed by 'pre' is
under development. This semantics was developed for the sake of comparison with 
[Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html).
"""
import os
parent_directory = os.path.dirname(__file__)
file_name = os.path.basename(__file__)

################################
########## SETTINGS ############
################################

# time cutoff for increasing N
max_time = 1

# find critical value of N
optimize_bool = False

# print all Z3 constraints if a model is found
print_cons_bool = False

# print all states including impossible states
print_impossible_states_bool = False

# present option to append output to file
save_bool = False



################################
###### EXCLUSION OPERATOR ######
################################

### INVALID ###

# premises = ['Box (A leftrightarrow B)']
# conclusions = ['(not A equiv not B)']

# conclusions = ['(A equiv not not A)']
# conclusions = ['(not A equiv not not not A)']
# # conclusions = ['(A equiv not not not not A)']

# conclusions = ['(not A equiv neg A)']
# conclusions = ['Diamond A','(not A equiv neg A)']
# conclusions = ['Diamond neg A','(not A equiv neg A)']

# premises = ['Box (A leftrightarrow B)', '(C sqsubseteq not A)']
# conclusions = ['(C sqsubseteq not B)']

# premises = ['Diamond A','Diamond neg A']
# conclusions = ['(not A equiv neg A)']




### VALID ###

# premises = ['(A equiv B)']
# conclusions = ['(not A equiv not B)']

# conclusions = ['(A vee not A)']
# conclusions = ['not (A wedge not A)']

# premises = ['A']
# conclusions = ['not not A']

# premises = []
# conclusions = ['(not not A equiv not not not not A)']



### TESTING ###

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

# # NOTE: false premise model?
# premises = ['not A','(not A boxright B)']
# # premises = ['pre A','Diamond A','Diamond B','(pre A boxright B)']
# conclusions = ['B']





################################
##### PRECLUSION OPERATOR ######
################################

### INVALID ###

# premises = ['Box (A leftrightarrow B)']
# conclusions = ['(pre A equiv pre B)']

# premises = ['(pre A equiv pre B)']
# conclusions = ['Box (A leftrightarrow B)']


# conclusions = ['(A equiv pre pre A)']
# conclusions = ['(A equiv not not not not A)']

# premises = ['Diamond A', 'Diamond neg A']
# conclusions = ['(pre A equiv not A)']

# premises = ['Diamond A','Diamond neg A']
# conclusions = ['(pre A equiv neg A)']


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
# premises = ['not A','(not A boxright B)']
# # premises = ['not A','Diamond A','Diamond B','(not A boxright B)']
# conclusions = ['B']

