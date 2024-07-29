"""
NOTE:

This file includes a number of selected examples to help get a sense of the semantics.
Further examples files are included in the parent directory.
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



########################################
##### COUNTERFACTUAL COUNTERMODELS #####
########################################

# # CF_CM1: COUNTERFACTUAL ANTECEDENT STRENGTHENING
N = 3
premises = ['(A boxright C)']
conclusions = ['((A wedge B) boxright C)']
contingent_bool = True
disjoint_bool = False

# # CF_CM6: COUNTERFACTUAL CONTRAPOSITION
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM9: TRANSITIVITY
# N = 3
# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM14: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 3
# premises = ['neg A']
# conclusions = ['(A boxright B)','(A boxright neg B)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM15: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM17: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A boxright B)']
# contingent_bool = True
# disjoint_bool = False




################################
##### COUNTERFACTUAL LOGIC #####
################################

# # CF2: COUNTERFACTUAL MODUS PONENS
# N = 3
# premises = ['A','(A boxright B)']
# conclusions = ['B']
# contingent_bool = False
# disjoint_bool = False

# # CF3: WEAKENED TRANSITIVITY
# N = 3
# premises = ['(A boxright B)','((A wedge B) boxright C)']
# conclusions = ['(A boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']
# contingent_bool = False
# disjoint_bool = False

# # CF10: FACTIVITY MIGHT
# N = 3
# premises = ['A','B']
# conclusions = ['(A circleright B)']
# contingent_bool = False
# disjoint_bool = False





###############################
##### MODAL COUNTERMODELS #####
###############################

# # CM1:  NECESSITATED ARGUMENTS COUNTERFACTUAL MODUS PONENS
# N = 3
# premises = ['Box A','(A rightarrow B)']
# conclusions = ['Box B']
# contingent_bool = False
# disjoint_bool = False

# # CM2:  COUNTERFACTUAL IMPLIES STRICT CONDITIONAL
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['Box (A rightarrow B)']
# contingent_bool = True
# disjoint_bool = False






################################
######### MODAL LOGIC ##########
################################


# # ML1: STRICT CONDITIONAL TO COUNTERFACTUAL
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']
# contingent_bool = False
# disjoint_bool = False

# # ML2: K AXIOM (BOX)
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']
# contingent_bool = False
# disjoint_bool = False

# # ML6: T AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['A']
# contingent_bool = False
# disjoint_bool = False

# # ML12: 5 AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['Box Diamond A']
# contingent_bool = False
# disjoint_bool = False

# # ML13: BOX-TO-TOP
# N = 3
# premises = ['Box A']
# conclusions = ['(top boxright A)']
# contingent_bool = False
# disjoint_bool = False

# # ML14: # TOP-TO-BOX
# N = 3
# premises = ['(top boxright A)']
# conclusions = ['Box A']
# contingent_bool = False
# disjoint_bool = False







######################################
##### CONSTITUTIVE COUNTERMODELS #####
######################################

# # CM1: STRICT IMPLICATION TO GROUND
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A leq B)']
# contingent_bool = True
# disjoint_bool = False

# # CM2: STRICT IMPLICATION TO ESSENCE
# N = 3
# premises = ['Box (B rightarrow A)']
# conclusions = ['(A sqsubseteq B)']
# contingent_bool = True
# disjoint_bool = False

# # CM3: GROUND CONJUNCTION SUPPLEMENTATION
# N = 3
# premises = ['(A leq B)','(C leq D)']
# conclusions = ['((A wedge C) leq (B wedge D))']
# contingent_bool = True
# disjoint_bool = False

# # CM4: ESSENCE CONJUNCTION SUPPLEMENTATION
# N = 3
# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A vee C) sqsubseteq (B vee D))']
# contingent_bool = True
# disjoint_bool = False

# # CM5: IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
# N = 3
# premises = []
# conclusions = ['(A equiv (A vee (A wedge B)))']
# contingent_bool = True
# disjoint_bool = False

# # CM6: IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION
# N = 3
# premises = []
# conclusions = ['(A equiv (A wedge (A vee B)))']
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

# # """CL3: ESSENCE TO IDENTITY"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['((A wedge B) equiv B)']
# contingent_bool = False
# disjoint_bool = False

# # """CL6: IDENTITY TO GROUND"""
# N = 3
# premises = ['((A vee B) equiv B)']
# conclusions = ['(A leq B)']
# contingent_bool = False
# disjoint_bool = False







### AXIOMS AND RULES: GROUND ###

# # """CL9: DISJUNCTS GROUND DISJUNCTIONS"""
# N = 3
# premises = []
# conclusions = ['(A leq (A vee B))']
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








###################################
##### RELEVANCE COUNTERMODELS #####
###################################

# """RL_CM1: ANTECEDENT STRENGTHENING"""
# N = 3
# premises = []
# conclusions = ['((A wedge B) preceq A)']
# contingent_bool = True
# disjoint_bool = False

# """RL_CM2: ANTECEDENT WEAKENING"""
# N = 3
# premises = []
# conclusions = ['((A vee B) preceq A)']
# contingent_bool = True
# disjoint_bool = False

# """RL_CM3: RELEVANCE TRANSITIVITY"""
# N = 3
# premises = ['(A preceq B)', '(B preceq C)']
# conclusions = ['(A preceq C)']
# contingent_bool = True
# disjoint_bool = False

# """RL_CM4: RELEVANT IMPLICATION: GROUND"""
# N = 3
# premises = ['Box (A rightarrow B)','(A preceq B)']
# conclusions = ['(A leq B)']
# contingent_bool = True
# disjoint_bool = False

# """RL_CM5: RELEVANT IMPLICATION: ESSENCE"""
# N = 3
# premises = ['Box (B rightarrow A)','(A preceq B)']
# conclusions = ['(A sqsubseteq B)']
# contingent_bool = True
# disjoint_bool = False

# """RL_CM6: RELEVANT IMPLICATION: IDENTITY"""
# N = 3
# premises = ['Box (A leftrightarrow B)','(A preceq B)','(B preceq A)']
# conclusions = ['(A equiv B)']
# contingent_bool = True
# disjoint_bool = False







###########################
##### RELEVANCE LOGIC #####
###########################

### DEFINITIONAL EQUIVALENTS

# """RL1: RELEVANCE TO CONJUNCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['((A wedge B) leq B)']
# contingent_bool = False
# disjoint_bool = False

# """RL2: RELEVANCE TO DISJUNCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['((A vee B) sqsubseteq B)']
# contingent_bool = False
# disjoint_bool = False

# """RL3: CONJUNCTION TO RELEVANCE"""
# N = 3
# premises = ['((A wedge B) leq B)']
# conclusions = ['(A preceq B)']
# contingent_bool = False
# disjoint_bool = False

# """RL4: DISJUNCTION TO RELEVANCE"""
# N = 3
# premises = ['((A vee B) sqsubseteq B)']
# conclusions = ['(A preceq B)']
# contingent_bool = False
# disjoint_bool = False






### AXIOMS

# """RL5: CONJUNCTION INTRODUCTION"""
# N = 3
# premises = []
# conclusions = ['(A preceq (A wedge B))']
# contingent_bool = False
# disjoint_bool = False

# """RL6: DISJUNCTION INTRODUCTION"""
# N = 3
# premises = []
# conclusions = ['(A preceq (A vee B))']
# contingent_bool = False
# disjoint_bool = False




### CONSTITUTIVE INTERACTION

# """RL7: GROUNDING RELEVANCE"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['(A preceq B)']
# contingent_bool = False
# disjoint_bool = False

# """RL8: ESSENCE RELEVANCE"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['(A preceq B)']
# contingent_bool = False
# disjoint_bool = False

# """RL9: IDENTITY RELEVANCE"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(A preceq B)']
# contingent_bool = False
# disjoint_bool = False
