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


######################################
##### CONSTITUTIVE COUNTERMODELS #####
######################################

# """CM1: STRICT IMPLICATION TO GROUND"""
N = 3
premises = ['Box (A rightarrow B)']
conclusions = ['(A leq B)']
contingent_bool = True
disjoint_bool = False

# # """CM2: STRICT IMPLICATION TO ESSENCE"""
# N = 3
# premises = ['Box (B rightarrow A)']
# conclusions = ['(A sqsubseteq B)']
# contingent_bool = True
# disjoint_bool = False

# # """CM3: GROUND CONJUNCTION SUPPLEMENTATION WITH POSSIBILITY"""
# N = 3
# premises = ['(A leq B)','(C leq D)']
# conclusions = ['((A wedge C) leq (B wedge D))']
# contingent_bool = True
# disjoint_bool = False

# # """CM4: ESSENCE CONJUNCTION SUPPLEMENTATION"""
# N = 3
# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A vee C) sqsubseteq (B vee D))']
# contingent_bool = True
# disjoint_bool = False

# # """CM5: IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(A equiv (A vee (A wedge B)))']
# contingent_bool = True
# disjoint_bool = False

# # """CM6: IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(A equiv (A wedge (A vee B)))']
# contingent_bool = True
# disjoint_bool = False

# # """CM7: NECESSARY EQUIVALENTS"""
# N = 3
# premises = []
# conclusions = ['((A vee neg A) equiv (B vee neg B))']
# contingent_bool = True
# disjoint_bool = False

# # """CM8: ESSENCE DISTRIBUTION"""
# N = 3
# premises = []
# conclusions = ['(((A vee B) wedge (A vee C)) sqsubseteq (A vee (B wedge C)))']
# contingent_bool = True
# disjoint_bool = False

# # """CM9: GROUND DISTRIBUTION"""
# N = 3
# premises = []
# conclusions = ['(((A wedge B) vee (A wedge C)) leq (A wedge (B vee C)))']
# contingent_bool = True
# disjoint_bool = False

# # """CM10: IDENTITY DISTRIBUTION"""
# N = 3
# premises = []
# conclusions = ['((A vee (B wedge C)) equiv ((A vee B) wedge (A vee C)))']
# contingent_bool = True
# disjoint_bool = False





################################
###### CONSTITUTIVE LOGIC ######
################################

### DEFINITIONAL EQUIVALENTS ###

# # """CL1: GROUND TO ESSENCE"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['(neg A sqsubseteq neg B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL2: ESSENCE TO GROUND"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['(neg A leq neg B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL3: ESSENCE TO IDENTITY"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['((A wedge B) equiv B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL4: IDENTITY TO ESSENCE"""
# # NOTE: with Z3 quantifiers 17.2 seconds locally; now .0103 seconds locally
# N = 3
# premises = ['((A wedge B) equiv B)']
# conclusions = ['(A sqsubseteq B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL5: GROUND TO IDENTITY"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['((A vee B) equiv B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL6: IDENTITY TO GROUND"""
# N = 3
# premises = ['((A vee B) equiv B)']
# conclusions = ['(A leq B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL7: NEGATION TRANSPARENCY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(neg A equiv neg B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL8: REVERSE NEGATION TRANSPARENCY"""
# N = 3
# premises = ['(neg A equiv neg B)']
# conclusions = ['(A equiv B)']
# contingent_bool = False
# disjoint_bool = False



### AXIOMS AND RULES: GROUND ###

# # """CL9: DISJUNCTS GROUND DISJUNCTIONS"""
# N = 3
# premises = []
# conclusions = ['(A leq (A vee B))']
# contingent_bool = False
# disjoint_bool = False

# # """CL10: CONJUNCTIONS GROUND DISJUNCTIONS"""
# N = 3
# premises = []
# conclusions = ['((A wedge B) leq (A vee B))']
# contingent_bool = False
# disjoint_bool = False

# # """CL11: GROUNDING NEGATED CONJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(neg A leq neg (A wedge B))']
# contingent_bool = False
# disjoint_bool = False

# # """CL12: GROUNDING TRANSITIVITY"""
# N = 3
# premises = ['(A leq B)','(B leq C)']
# conclusions = ['(A leq C)']
# contingent_bool = False
# disjoint_bool = False

# # """CL13: DISJUNCTION INTRODUCTION GROUNDING ANTECEDENT"""
# N = 3
# premises = ['(A leq C)','(B leq C)']
# conclusions = ['((A vee B) leq C)']
# contingent_bool = False
# disjoint_bool = False

# # """CL14: GROUNDING ANTISYMMETRY"""
# N = 3
# premises = ['(A leq B)','(B leq A)']
# conclusions = ['(A equiv B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL15: GROUNDING MODUS PONENS"""
# N = 3
# premises = ['A','(A leq B)']
# conclusions = ['B']
# contingent_bool = False
# disjoint_bool = False

# # """CL16: GROUNDING MODUS TOLLENS"""
# N = 3
# premises = ['neg B','(A leq B)']
# conclusions = ['neg A']
# contingent_bool = False
# disjoint_bool = False

# # """CL17: GROUND DISJUNCTION SUPPLEMENTATION"""
# N = 3
# premises = ['(A leq B)','(C leq D)']
# conclusions = ['((A vee C) leq (B vee D))']
# contingent_bool = False
# disjoint_bool = False





### AXIOMS AND RULES: ESSENCE ###

# # """CL18: CONJUNCTS ESSENTIAL TO CONJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(A sqsubseteq (A wedge B))']
# contingent_bool = False
# disjoint_bool = False

# # """CL19: DISJUNCTIONS ESSENTIAL TO CONJUNCTIONS"""
# N = 3
# premises = []
# conclusions = ['((A vee B) sqsubseteq (A wedge B))']
# contingent_bool = False
# disjoint_bool = False

# # """CL20: ESSENCE NEGATED DISJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(neg A sqsubseteq neg (A vee B))']
# contingent_bool = False
# disjoint_bool = False

# # """CL21: ESSENCE TRANSITIVITY"""
# N = 3
# premises = ['(A sqsubseteq B)','(B sqsubseteq C)']
# conclusions = ['(A sqsubseteq C)']
# contingent_bool = False
# disjoint_bool = False

# # """CL22: CONJUNCTION INTRODUCTION ESSENCE ANTECEDENT"""
# N = 3
# premises = ['(A sqsubseteq C)','(B sqsubseteq C)']
# conclusions = ['((A wedge B) sqsubseteq C)']
# contingent_bool = False
# disjoint_bool = False

# # """CL23: ESSENCE ANTISYMMETRY"""
# N = 3
# premises = ['(A sqsubseteq B)','(B sqsubseteq A)']
# conclusions = ['(A equiv B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL24: ESSENCE MODUS PONENS"""
# N = 3
# premises = ['B','(A sqsubseteq B)']
# conclusions = ['A']
# contingent_bool = False
# disjoint_bool = False

# # """CL25: ESSENCE MODUS TOLLENS"""
# N = 3
# premises = ['neg A','(A sqsubseteq B)']
# conclusions = ['neg B']
# contingent_bool = False
# disjoint_bool = False

# # """CL26: ESSENCE CONJUNCTION SUPPLEMENTATION"""
# N = 3
# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A wedge C) sqsubseteq (B wedge D))']
# contingent_bool = False
# disjoint_bool = False





### AXIOMS AND RULES: IDENTITY ###

# # """CL27: CONJUNCTION IDEMPOTENCE"""
# N = 3
# premises = []
# conclusions = ['(A equiv (A wedge A))']
# contingent_bool = False
# disjoint_bool = False

# # """CL28: DISJUNCTION IDEMPOTENCE"""
# N = 3
# premises = []
# conclusions = ['(A equiv (A vee A))']
# contingent_bool = False
# disjoint_bool = False

# # """CL29: COMMUTATIVITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(B equiv A)']
# contingent_bool = False
# disjoint_bool = False

# # """CL30: NEGATION TRANSPARENCY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(neg B equiv neg A)']
# contingent_bool = False
# disjoint_bool = False

# # """CL31: TRANSITIVITY"""
# N = 3
# premises = ['(A equiv B)', '(B equiv C)']
# conclusions = ['(A equiv C)']
# contingent_bool = False
# disjoint_bool = False

# # """CL32: CONJUNCTION MONOTONICITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['((A wedge C) equiv (B wedge C))']
# contingent_bool = False
# disjoint_bool = False

# # """CL33: DISJUNCTION MONOTONICITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['((A vee C) equiv (B vee C))']
# contingent_bool = False
# disjoint_bool = False





### MODAL INTERACTION ###

# # """CL34: GROUND TO STRICT IMPLICATION"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['Box (A rightarrow B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL35: ESSENCE TO STRICT IMPLICATION"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (B rightarrow A)']
# contingent_bool = False
# disjoint_bool = False

# # """CL36: IDENTITY TO NECESSARY EQUIVALENCE"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['Box (B leftrightarrow A)']
# contingent_bool = False
# disjoint_bool = False

# # """CL37: NECESSITY OF GROUND"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['Box (A leq B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL38: NECESSITY OF ESSENCE"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (A sqsubseteq B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL39: NECESSITY OF IDENTITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['Box (A equiv B)']
# contingent_bool = False
# disjoint_bool = False
