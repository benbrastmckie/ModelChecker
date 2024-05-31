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
# # SLOW: 17.2 seconds locally
# premises = ['((A wedge B) equiv B)']
# conclusions = ['(A sqsubseteq B)']

# # GROUND TO IDENTITY
# premises = ['(A leq B)']
# conclusions = ['((A vee B) equiv B)']

# # IDENTITY TO GROUND
# premises = ['((A vee B) equiv B)']
# conclusions = ['(A leq B)']

# # NEGATION TRANSPARENCY
# premises = ['(A equiv B)']
# conclusions = ['(neg A equiv neg B)']

# # REVERSE NEGATION TRANSPARENCY
# premises = ['(neg A equiv neg B)']
# conclusions = ['(A equiv B)']


### AXIOMS AND RULES: GROUND ###

# conclusions = ['(A leq (A vee B))']
# conclusions = ['(neg A leq neg (A wedge B))']
# conclusions = ['((A wedge B) leq (A vee B))']

# premises = ['(A leq B)','(B leq C)']
# conclusions = ['(A leq C)']

# premises = ['(A leq C)','(B leq C)']
# conclusions = ['((A vee B) leq C)']

# premises = ['(A leq B)','(B leq A)']
# conclusions = ['(A equiv B)']

# premises = ['A','(A leq B)']
# conclusions = ['B']

# premises = ['neg B','(A leq B)']
# conclusions = ['neg A']





### AXIOMS AND RULES: ESSENCE ###

# conclusions = ['(A sqsubseteq (A wedge B))']

# premises = ['(A sqsubseteq B)','(B sqsubseteq C)']
# conclusions = ['(A sqsubseteq C)']

# premises = ['B','(A sqsubseteq B)']
# conclusions = ['A']

# premises = ['neg A','(A sqsubseteq B)']
# conclusions = ['neg B']










### MODAL INTERACTION ###

# # GROUND TO STRICT IMPLICATION
# premises = ['(A leq B)']
# conclusions = ['Box (A rightarrow B)']

# # NECESSITY OF GROUND
# premises = ['(A leq B)']
# conclusions = ['Box (A leq B)']

# # ESSENCE TO STRICT IMPLICATION
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (B rightarrow A)']

# # NECESSITY OF ESSENCE
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (A sqsubseteq B)']

# # GROUND DISJUNCTION SUPPLEMENTATION
# premises = ['(A leq B)','(C leq D)']
# conclusions = ['((A vee C) leq (B vee D))']

# # ESSENCE CONJUNCTION SUPPLEMENTATION
# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A vee C) sqsubseteq (B vee D))']




### IDENTITY


# # IDEMPOTENCE
# conclusions = ['(A equiv (A wedge A))']
# conclusions = ['(A equiv (A vee A))']

# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A vee C) sqsubseteq (B vee D))']












### INVALID ###

# # STRICT IMPLICATION TO GROUND
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A leq B)']

# # STRICT IMPLICATION TO ESSENCE
# premises = ['Box (B rightarrow A)']
# conclusions = ['(A sqsubseteq B)']

# # GROUND CONJUNCTION SUPPLEMENTATION WITH POSSIBILITY
# premises = [
#     'Diamond A',
#     'Diamond B',
#     'Diamond C',
#     'Diamond D',
#     'Diamond neg A',
#     'Diamond neg B',
#     'Diamond neg C',
#     'Diamond neg D',
#     '(A leq B)',
#     '(C leq D)'
# ]
# conclusions = ['((A wedge C) leq (B wedge D))']

# # ESSENCE DISJUNCTION SUPPLEMENTATION WITH POSSIBILITY
# premises = [
#     'Diamond A',
#     'Diamond B',
#     'Diamond C',
#     'Diamond D',
#     'Diamond neg A',
#     'Diamond neg B',
#     'Diamond neg C',
#     'Diamond neg D',
#     '(A sqsubseteq B)',
#     '(C sqsubseteq D)'
# ]
# conclusions = ['((A vee C) sqsubseteq (B vee D))']

# # IDENTITY ABSORPTION
# conclusions = ['(A equiv (A vee (A wedge B)))']
# conclusions = ['(A equiv (A wedge (A vee B)))']

# conclusions = ['((A vee neg A) equiv (B vee neg B))']




# DISTRIBUTION LAWS

# TODO: true conclusion model with Not(true_at(...)) but not with false_at(...)
# conclusions = ['((A wedge (B vee C)) equiv ((A wedge B) vee (A wedge C)))']

# TODO: true conclusion model
# premises = [
#     'Diamond A',
#     # 'Diamond neg A',
#     'Diamond B',
#     # 'Diamond neg B',
#     'Diamond C',
#     # 'Diamond neg C',
# ]
# conclusions = ['((A wedge (B vee C)) leq ((A wedge B) vee (A wedge C)))']
# conclusions = ['((A vee (B wedge C)) leq ((A vee B) wedge (A vee C)))']


# TODO: true conclusion model
# conclusions = ['((A wedge (B vee C)) sqsubseteq ((A wedge B) vee (A wedge C)))']
# conclusions = ['((A vee (B wedge C)) sqsubseteq ((A vee B) wedge (A vee C)))']

# TODO: true conclusion model with false_at(...) and not with Not(true_at(...))
# conclusions = ['(((A vee B) wedge (A vee C)) leq (A vee (B wedge C)))']

# TODO: true conclusion model with false_at(...) and not with Not(true_at(...))
# conclusions = ['(((A vee B) wedge (A vee C)) sqsubseteq (A vee (B wedge C)))']

# TODO: true conclusion model
# conclusions = ['(((A wedge B) vee (A wedge C)) leq (A wedge (B vee C)))']
# conclusions = ['(((A wedge B) vee (A wedge C)) sqsubseteq (A wedge (B vee C)))']

# TODO: true conclusion model
# conclusions = ['((A vee (B wedge C)) equiv ((A vee B) wedge (A vee C)))']









