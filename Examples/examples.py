"""
module for user inputs.
"""
import os
parent_directory = os.path.dirname(__file__)

################################
########## SETTINGS ############
################################

# length of bitvectors
N = 3

# print all Z3 constraints if a model is found
print_cons_bool = False

# print core unsatisfiable Z3 constraints if no model exists
print_unsat_core_bool = True

# present option to append output to file
save_bool = False


################################
########### WORKING ############
################################


### INVALID ###

premises = ['\\neg A','(A boxright (B vee C))']
conclusions = ['(A boxright B)','(A boxright C)']

# # NOTE: if null verifiers are permitted, then null state verifies A
# # but possible state c does not?
# premises = ['A','B']
# conclusions = ['(A boxright B)']

# premises = ['Ball_is_red','Mary_likes_it']
# conclusions = ['(Ball_is_red boxright Mary_likes_it)']

# premises = ['A',]
# conclusions = ['neg A']

# premises = ['neg A']
# conclusions = ['(A boxright B)','(A boxright neg B)']

# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# premises = ['neg A']
# conclusions = ['(A boxright B)','(A boxright neg B)']

# premises = ['(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# premises = ['A boxright C', 'neg (A boxright neg B)']
# conclusions = ['neg ((A wedge B) boxright C)']

# premises = ['Diamond (A wedge B)','((A wedge B) boxright C)']
# conclusions = ['(A boxright (B boxright C))']

# premises = ['neg (top boxright neg (A wedge B))','((A wedge B) boxright C)']
# conclusions = ['(A boxright (B boxright C))']

# premises = ['A','(A boxright (B boxright (C boxright D)))']
# conclusions = []

# premises = ['(Box A vee Box B)']
# conclusions = ['(A wedge B)']

# # NOTE: slow
# premises = [
#     '(A boxright B)',
#     'neg ((A wedge C) boxright B)',
#     '(((A wedge C) wedge D) boxright B)',
# ]
# conclusions = []

# premises = ['Diamond A', 'Diamond B']
# conclusions = ['Diamond (A wedge B)']

# # NOTE: ssh finds a model
# premises = ['(A boxright B)']
# conclusions = ['Box (A rightarrow B)']



### VALID ###

# # NOTE: unsat_core seems satisfiable
# premises = []
# conclusions = ['(A vee neg A)']

# # NOTE: unsat_core seems satisfiable
# premises = []
# conclusions = ['neg (A wedge neg A)']

# premises = ['A','(A rightarrow B)']
# conclusions = ['B']

# premises = ['(A boxright B)']
# conclusions = ['(A rightarrow B)']

# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']

# premises = ['((A vee B) boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# premises = ['(A boxright C)','(B boxright C)','((A wedge B) boxright C)']
# conclusions = ['((A vee B) boxright C)']

# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A vee B) boxright C)']

# premises = ['(A boxright (B wedge C))']
# conclusions = ['(A boxright B)']

# premises = ['(A boxright B)','(A boxright C)']
# conclusions = ['(A boxright (B wedge C))']

# premises = ['(A boxright B)','((A wedge B) boxright C)']
# conclusions = ['(A boxright C)']



### MODAL LOGIC ###

# # K axiom (box)
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']

# # T axiom (top)
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
# # NOTE: this crashed
# premises = ['A']
# conclusions = ['(top boxright neg (top boxright neg A))']

# # B axiom (box)
# premises = ['A']
# conclusions = ['Box Diamond A']

# # 5 axiom (top)
# premises = ['(top boxright A)']
# conclusions = ['(top boxright neg (top boxright neg A))']

# # 5 axiom (box)
# premises = ['Box A']
# conclusions = ['Box Diamond A']

# # box-to-top equivalence
# premises = ['Box A']
# conclusions = ['(top boxright A)']

# premises = ['Box A', 'Diamond B']
# conclusions = ['Diamond (A wedge B)']

# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']





################################
######### NOT WORKING ##########
################################


### HIGH PRIORITY: NEGATION PROBLEM ###

# # NOTE: only works without \neg B
# premises = ['neg B','(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

# # NOTE: only works without \neg A
# premises = ['neg A','(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']

# # NOTE: only works without \neg A and \neg B
# premises = ['neg A','neg B','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # NOTE: only works without \neg A
# premises = ['neg A', '(A boxright B)', 'neg ((A wedge C) boxright B)']
# conclusions = []

### MEDIUM PRIORITY: NESTED COUNTERFACTUALS ###

# # NOTE: this does not find models for N = 3
# # NOTE: N = 4 ran for minutes on ssh
# premises = ['(A boxright (B boxright C))']
# conclusions = ['((A wedge B) boxright C)']

# # NOTE: ssh killed process
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A wedge B) boxright C)']

### LOW PRIORITY: MODAL EQUIVALENCE ###

# # NOTE: killed in ssh
# # K axiom (top)
# premises = ['(top boxright (A rightarrow B))']
# conclusions = ['((top boxright A) rightarrow (top boxright B))']

# # NOTE: killed in ssh
# # top-to-box equivalence
# premises = ['(top boxright A)']
# conclusions = ['Box A']
