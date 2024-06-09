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
####### RELEVANCE LOGIC ########
################################

# DEFINITIONAL EQUIVALENTS

# premises = ['(A preceq B)']
# conclusions = ['((A wedge B) leq B)']

# premises = ['(A preceq B)']
# conclusions = ['((A vee B) sqsubseteq B)']

# premises = ['((A wedge B) leq B)']
# conclusions = ['(A preceq B)']

# premises = ['((A vee B) sqsubseteq B)']
# conclusions = ['(A preceq B)']




# DISTRIBUTION

# # TODO: true conclusion model
# conclusions = ['((A wedge (B vee C)) preceq ((A wedge B) vee (A wedge C)))']

# # TODO: true conclusion model
# conclusions = ['((A vee (B wedge C)) preceq ((A vee B) wedge (A vee C)))']






# CONSTITUTIVE INTERACTION

# premises = ['(A leq B)']
# conclusions = ['(A preceq B)']

# premises = ['(A sqsubseteq B)']
# conclusions = ['(A preceq B)']







# INVALID

# conclusions = ['((A wedge B) preceq A)']
conclusions = ['((A vee B) preceq A)']

# # TRANSITIVITY
# # premises = ['(A preceq B)', '(B preceq C)']
# premises = ['Diamond A','Diamond neg A','Diamond B','Diamond neg B','(A preceq B)', '(B preceq C)']
# conclusions = ['(A preceq C)']

# # RELEVANT IMPLICATION: GROUND
# premises = ['Box (A rightarrow B)','(A preceq B)']
# conclusions = ['(A leq B)']

# # RELEVANT IMPLICATION: ESSENCE
# premises = ['Box (B rightarrow A)','(A preceq B)']
# conclusions = ['(A sqsubseteq B)']

# # RELEVANT IMPLICATION: IDENTITY
# # premises = ['Box (A leftrightarrow B)','(A preceq B)','(B preceq A)']
# premises = ['Box (A leftrightarrow B)','(A preceq B)','(B preceq A)','Diamond A','Diamond B']
# conclusions = ['(A equiv B)']

# # STRICT IMPLICATION
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A preceq B)']

# # DISTRIBUTION
# conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']
# conclusions = ['(((A wedge B) vee (A wedge C)) preceq (A wedge (B vee C)))']

# # DISTRIBUTION WITH POSSIBILITY: TRUE
# premises = [
#     'Diamond A',
#     'Diamond B',
#     'Diamond C',
# ]
# # TODO: true conclusion model
# conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']
# # conclusions = ['(((A wedge B) vee (A wedge C)) preceq (A wedge (B vee C)))']

# # TODO: true conclusion model
# # DISTRIBUTION WITH POSSIBILITY: FALSE
# premises = [
#     'Diamond neg A',
#     'Diamond neg B',
#     'Diamond neg C',
# ]
# conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']
# # conclusions = ['(((A wedge B) vee (A wedge C)) preceq (A wedge (B vee C)))']


# # # DISTRIBUTION WITH CONTINGENCY
# premises = [
#     'Diamond A',
#     'Diamond neg A',
#     'Diamond B',
#     'Diamond neg B',
#     'Diamond C',
#     'Diamond neg C',
# ]
# # # TODO: true conclusion model
# # conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']
# conclusions = ['(((A wedge B) vee (A wedge C)) preceq (A wedge (B vee C)))']
