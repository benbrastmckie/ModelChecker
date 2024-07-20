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






################################
######### NOT WORKING ##########
################################

### FALSE PREMISE MODEL ###

# # SOBEL SEQUENCE (N = 3)
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 1.4 seconds locally
#     '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
#     # 'neg ((((A wedge B) wedge C) wedge D) boxright X)', # FALSE PREMISE MODELS BEGIN HERE
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # 20.5 seconds locally
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # 64 seconds on the MIT servers
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
# ]
# conclusions = []

# # SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
# N = 4
# premises = [
#     'Diamond A',
#     '(A boxright X)',
#     'Diamond (A wedge B)',
#     'neg ((A wedge B) boxright X)', # N = 4: 155.4 seconds on the MIT servers; now .1587 seconds
#     'Diamond ((A wedge B) wedge C)',
#     '(((A wedge B) wedge C) boxright X)',
#     'Diamond (((A wedge B) wedge C) wedge D)', # requires N > 3 to avoid FALSE PREMISE
#     'neg ((((A wedge B) wedge C) wedge D) boxright X)', # FALSE PREMISE MODELS BEGIN HERE
#     # 'Diamond ((((A wedge B) wedge C) wedge D) wedge E)',
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # ? seconds
#     # 'Diamond (((((A wedge B) wedge C) wedge D) wedge E) wedge F)',
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # ? seconds
#     # 'Diamond ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G)',
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # ? seconds
# ]
# conclusions = []





################################
######### CONSTITUTIVE #########
################################

# DISTRIBUTION LAWS

# # TODO: true conclusion model with Not(true_at(...)) but not with false_at(...)
# conclusions = ['((A wedge (B vee C)) equiv ((A wedge B) vee (A wedge C)))']

# TODO: true conclusion model
# conclusions = ['((A wedge (B vee C)) leq ((A wedge B) vee (A wedge C)))']
# conclusions = ['((A vee (B wedge C)) leq ((A vee B) wedge (A vee C)))']

# TODO: true conclusion model
# conclusions = ['((A wedge (B vee C)) sqsubseteq ((A wedge B) vee (A wedge C)))']
# conclusions = ['((A vee (B wedge C)) sqsubseteq ((A vee B) wedge (A vee C)))']

# TODO: true conclusion model with false_at(...) and not with Not(true_at(...))
# conclusions = ['(((A vee B) wedge (A vee C)) leq (A vee (B wedge C)))']

# TODO: true conclusion model
# conclusions = ['(((A wedge B) vee (A wedge C)) sqsubseteq (A wedge (B vee C)))']

# TODO: true conclusion model






###############################
####### COUNTERFACTUALS #######
###############################

### COUNTERFACTUAL IMPORTATION ###

# # COUNTERFACTUAL IMPORTATION WITH POSSIBILITY
# premises = ['(A boxright (B boxright C))','Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']

# # COUNTERFACTUAL IMPORTATION
# # NOTE: MIT servers found a model in 467 seconds with Z3 quantifiers
# premises = ['(A boxright (B boxright C))']
# conclusions = ['((A wedge B) boxright C)']








#############################
######### RELEVANCE #########
#############################

# DISTRIBUTION

# # TODO: true conclusion model
# contingent = True
# conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']

# # TODO: true conclusion model
# conclusions = ['((A wedge (B vee C)) preceq ((A wedge B) vee (A wedge C)))']

# # TODO: true conclusion model
# conclusions = ['((A vee (B wedge C)) preceq ((A vee B) wedge (A vee C)))']
