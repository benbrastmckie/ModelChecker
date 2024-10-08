"""
module for user inputs.
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
print_constraints_bool = False

# print all states including impossible states
print_impossible_states_bool = False

# present option to append output to file
save_bool = False





################################
######### NOT WORKING ##########
################################

### FALSE PREMISE MODEL ###

# # SOBEL SEQUENCE (N = 3)
# N = 3
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 1.4 seconds locally
#     '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
#     'neg ((((A wedge B) wedge C) wedge D) boxright X)', # FALSE PREMISE MODELS BEGIN HERE
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # 20.5 seconds locally
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # 64 seconds on the MIT servers
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # 327.2 seconds on the MIT servers; now .01244 seconds
# ]
# conclusions = []
# contingent_bool = False
# optimize_bool = True
# disjoint_bool = False

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
# N = 3
# premises = []
# conclusions = ['((A wedge (B vee C)) equiv ((A wedge B) vee (A wedge C)))']
# contingent_bool = True
# disjoint_bool = False

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
# N = 3
# premises = ['(A boxright (B boxright C))','Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']
# contingent_bool = False
# disjoint_bool = False
# optimize_bool = True

# # COUNTERFACTUAL IMPORTATION
# # NOTE: MIT servers found a model in 467 seconds with Z3 quantifiers
# N = 3
# premises = ['(A boxright (B boxright C))']
# conclusions = ['((A wedge B) boxright C)']
# contingent_bool = True
# disjoint_bool = True
# optimize_bool = True




##########################
####### IMPOSITION #######
##########################

# # CF11: IMPOSITION TO COUNTERFACTUAL
# N = 3
# premises = ['(A imposition B)']
# conclusions = ['(A boxright B)']
# contingent_bool = True
# disjoint_bool = False

# # CF12: COUNTERFACTUAL TO IMPOSITION
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['(A imposition B)']
# contingent_bool = True
# disjoint_bool = False





# # NOTE: TRUE CONCLUSION MODEL
# # CF3: WEAKENED TRANSITIVITY HALF IMPOSITION
# N = 3
# premises = ['(A boxright B)','((A wedge B) boxright C)']
# conclusions = ['(A imposition C)']
# # conclusions = ['(A boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF3: WEAKENED TRANSITIVITY HALF IMPOSITION
# N = 3
# premises = ['(A imposition B)','((A wedge B) imposition C)']
# conclusions = ['(A boxright C)']
# # conclusions = ['(A boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
# premises = ['((A vee B) imposition C)']
# conclusions = ['((A wedge B) boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A vee B) boxright C)']
# conclusions = ['((A boxright C) wedge (B boxright C))']
# contingent_bool = False
# disjoint_bool = False

# # CF7:
# N = 3
# premises = ['(A boxright C)', '(B boxright C)', '((A wedge B) boxright C)']
# conclusions = ['((A vee B) boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF8:
# N = 3
# premises = ['(A boxright (B wedge C))']
# conclusions = ['(A boxright B)']
# contingent_bool = False
# disjoint_bool = False

# # NOTE: optimizer works for max_time = 1 but not max_time > 1
# # CF9:
# N = 3
# premises = ['(A boxright B)','(A boxright C)']
# conclusions = ['(A boxright (B wedge C))']
# contingent_bool = False
# disjoint_bool = False

# # CF10: FACTIVITY MIGHT
# N = 3
# premises = ['A','B']
# conclusions = ['(A circleright B)']
# contingent_bool = False
# disjoint_bool = False




### IMPOSITION ###

# # CF11: COUNTERFACTUAL TO IMPOSITION
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['(A imposition B)']
# contingent_bool = False
# disjoint_bool = False

# # CF12: IMPOSITION TO COUNTERFACTUAL
# N = 3
# premises = ['(A imposition B)']
# conclusions = ['(A boxright B)']
# contingent_bool = False
# disjoint_bool = False








#############################
######### RELEVANCE #########
#############################

# DISTRIBUTION

# # TODO: true conclusion model
# contingent_bool = True
# conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']

# # TODO: true conclusion model
# conclusions = ['((A wedge (B vee C)) preceq ((A wedge B) vee (A wedge C)))']

# # TODO: true conclusion model
# conclusions = ['((A vee (B wedge C)) preceq ((A vee B) wedge (A vee C)))']
