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

# number of atomic states
N = 3

# find critical value of N
optimize = False

# time cutoff for increasing N
max_time = 1

# make all propositions contingent
contingent = False

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
contingent = True

# # CF_CM6: COUNTERFACTUAL CONTRAPOSITION
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']
# contingent = True

# # CF_CM9: TRANSITIVITY
# N = 3
# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']
# contingent = True

# # CF_CM14: COUNTERFACTUAL EXCLUDED MIDDLE
# N = 3
# premises = ['neg A']
# conclusions = ['(A boxright B)','(A boxright neg B)']
# contingent = True

# # CF_CM15: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']
# contingent = True

# # CF_CM17: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A boxright B)']
# contingent = True




################################
##### COUNTERFACTUAL LOGIC #####
################################

# # CF2: COUNTERFACTUAL MODUS PONENS
# N = 3
# premises = ['A','(A boxright B)']
# conclusions = ['B']
# contingent = False

# # CF3: WEAKENED TRANSITIVITY
# N = 3
# premises = ['(A boxright B)','((A wedge B) boxright C)']
# conclusions = ['(A boxright C)']
# contingent = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']
# contingent = False

# # CF10: FACTIVITY MIGHT
# N = 3
# premises = ['A','B']
# conclusions = ['(A circleright B)']
# contingent = False





###############################
##### MODAL COUNTERMODELS #####
###############################

# # CM1:  NECESSITATED ARGUMENTS COUNTERFACTUAL MODUS PONENS
# N = 3
# premises = ['Box A','(A rightarrow B)']
# conclusions = ['Box B']
# contingent = False

# # CM2:  COUNTERFACTUAL IMPLIES STRICT CONDITIONAL
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['Box (A rightarrow B)']
# contingent = True






################################
######### MODAL LOGIC ##########
################################


# # ML1: STRICT CONDITIONAL TO COUNTERFACTUAL
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A boxright B)']
# contingent = False

# # ML2: K AXIOM (BOX)
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(Box A rightarrow Box B)']
# contingent = False

# # ML6: T AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['A']
# contingent = False

# # ML12: 5 AXIOM (BOX)
# N = 3
# premises = ['Box A']
# conclusions = ['Box Diamond A']
# contingent = False

# # ML13: BOX-TO-TOP
# N = 3
# premises = ['Box A']
# conclusions = ['(top boxright A)']
# contingent = False

# # ML14: # TOP-TO-BOX
# N = 3
# premises = ['(top boxright A)']
# conclusions = ['Box A']
# contingent = False







######################################
##### CONSTITUTIVE COUNTERMODELS #####
######################################

# # CM1: STRICT IMPLICATION TO GROUND
# N = 3
# premises = ['Box (A rightarrow B)']
# conclusions = ['(A leq B)']
# contingent = True

# # CM2: STRICT IMPLICATION TO ESSENCE
# N = 3
# premises = ['Box (B rightarrow A)']
# conclusions = ['(A sqsubseteq B)']
# contingent = True

# # CM3: GROUND CONJUNCTION SUPPLEMENTATION
# N = 3
# premises = ['(A leq B)','(C leq D)']
# conclusions = ['((A wedge C) leq (B wedge D))']
# contingent = True

# # CM4: ESSENCE CONJUNCTION SUPPLEMENTATION
# N = 3
# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A vee C) sqsubseteq (B vee D))']
# contingent = True

# # CM5: IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION
# N = 3
# premises = []
# conclusions = ['(A equiv (A vee (A wedge B)))']
# contingent = True

# # CM6: IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION
# N = 3
# premises = []
# conclusions = ['(A equiv (A wedge (A vee B)))']
# contingent = True






################################
###### CONSTITUTIVE LOGIC ######
################################

### DEFINITIONAL EQUIVALENTS ###

# # """CL1: GROUND TO ESSENCE"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['(neg A sqsubseteq neg B)']
# contingent = False

# # """CL3: ESSENCE TO IDENTITY"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['((A wedge B) equiv B)']
# contingent = False

# # """CL6: IDENTITY TO GROUND"""
# N = 3
# premises = ['((A vee B) equiv B)']
# conclusions = ['(A leq B)']
# contingent = False







### AXIOMS AND RULES: GROUND ###

# # """CL9: DISJUNCTS GROUND DISJUNCTIONS"""
# N = 3
# premises = []
# conclusions = ['(A leq (A vee B))']
# contingent = False

# # """CL12: GROUNDING TRANSITIVITY"""
# N = 3
# premises = ['(A leq B)','(B leq C)']
# conclusions = ['(A leq C)']
# contingent = False

# # """CL13: DISJUNCTION INTRODUCTION GROUNDING ANTECEDENT"""
# N = 3
# premises = ['(A leq C)','(B leq C)']
# conclusions = ['((A vee B) leq C)']
# contingent = False

# # """CL14: GROUNDING ANTISYMMETRY"""
# N = 3
# premises = ['(A leq B)','(B leq A)']
# conclusions = ['(A equiv B)']
# contingent = False

# # """CL15: GROUNDING MODUS PONENS"""
# N = 3
# premises = ['A','(A leq B)']
# conclusions = ['B']
# contingent = False

# # """CL17: GROUND DISJUNCTION SUPPLEMENTATION"""
# N = 3
# premises = ['(A leq B)','(C leq D)']
# conclusions = ['((A vee C) leq (B vee D))']
# contingent = False





### AXIOMS AND RULES: ESSENCE ###

# # """CL18: CONJUNCTS ESSENTIAL TO CONJUNCTION"""
# N = 3
# premises = []
# conclusions = ['(A sqsubseteq (A wedge B))']
# contingent = False

# # """CL21: ESSENCE TRANSITIVITY"""
# N = 3
# premises = ['(A sqsubseteq B)','(B sqsubseteq C)']
# conclusions = ['(A sqsubseteq C)']
# contingent = False

# # """CL22: CONJUNCTION INTRODUCTION ESSENCE ANTECEDENT"""
# N = 3
# premises = ['(A sqsubseteq C)','(B sqsubseteq C)']
# conclusions = ['((A wedge B) sqsubseteq C)']
# contingent = False

# # """CL23: ESSENCE ANTISYMMETRY"""
# N = 3
# premises = ['(A sqsubseteq B)','(B sqsubseteq A)']
# conclusions = ['(A equiv B)']
# contingent = False

# # """CL24: ESSENCE MODUS PONENS"""
# N = 3
# premises = ['B','(A sqsubseteq B)']
# conclusions = ['A']
# contingent = False

# # """CL26: ESSENCE CONJUNCTION SUPPLEMENTATION"""
# N = 3
# premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
# conclusions = ['((A wedge C) sqsubseteq (B wedge D))']
# contingent = False





### AXIOMS AND RULES: IDENTITY ###

# # """CL27: CONJUNCTION IDEMPOTENCE"""
# N = 3
# premises = []
# conclusions = ['(A equiv (A wedge A))']
# contingent = False

# # """CL28: DISJUNCTION IDEMPOTENCE"""
# N = 3
# premises = []
# conclusions = ['(A equiv (A vee A))']
# contingent = False

# # """CL30: NEGATION TRANSPARENCY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(neg B equiv neg A)']
# contingent = False

# # """CL31: TRANSITIVITY"""
# N = 3
# premises = ['(A equiv B)', '(B equiv C)']
# conclusions = ['(A equiv C)']
# contingent = False

# # """CL32: CONJUNCTION MONOTONICITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['((A wedge C) equiv (B wedge C))']
# contingent = False

# # """CL33: DISJUNCTION MONOTONICITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['((A vee C) equiv (B vee C))']
# contingent = False





### MODAL INTERACTION ###

# # """CL34: GROUND TO STRICT IMPLICATION"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['Box (A rightarrow B)']
# contingent = False

# # """CL35: ESSENCE TO STRICT IMPLICATION"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (B rightarrow A)']
# contingent = False

# # """CL36: IDENTITY TO NECESSARY EQUIVALENCE"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['Box (B leftrightarrow A)']
# contingent = False

# # """CL37: NECESSITY OF GROUND"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['Box (A leq B)']
# contingent = False

# # """CL38: NECESSITY OF ESSENCE"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['Box (A sqsubseteq B)']
# contingent = False

# # """CL39: NECESSITY OF IDENTITY"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['Box (A equiv B)']
# contingent = False








###################################
##### RELEVANCE COUNTERMODELS #####
###################################

# """RL_CM1: ANTECEDENT STRENGTHENING"""
# N = 3
# premises = []
# conclusions = ['((A wedge B) preceq A)']
# contingent = True

# """RL_CM2: ANTECEDENT WEAKENING"""
# N = 3
# premises = []
# conclusions = ['((A vee B) preceq A)']
# contingent = True

# """RL_CM3: RELEVANCE TRANSITIVITY"""
# N = 3
# premises = ['(A preceq B)', '(B preceq C)']
# conclusions = ['(A preceq C)']
# contingent = True

# """RL_CM4: RELEVANT IMPLICATION: GROUND"""
# N = 3
# premises = ['Box (A rightarrow B)','(A preceq B)']
# conclusions = ['(A leq B)']
# contingent = True

# """RL_CM5: RELEVANT IMPLICATION: ESSENCE"""
# N = 3
# premises = ['Box (B rightarrow A)','(A preceq B)']
# conclusions = ['(A sqsubseteq B)']
# contingent = True

# """RL_CM6: RELEVANT IMPLICATION: IDENTITY"""
# N = 3
# premises = ['Box (A leftrightarrow B)','(A preceq B)','(B preceq A)']
# conclusions = ['(A equiv B)']
# contingent = True







###########################
##### RELEVANCE LOGIC #####
###########################

### DEFINITIONAL EQUIVALENTS

# """RL1: RELEVANCE TO CONJUNCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['((A wedge B) leq B)']
# contingent = False

# """RL2: RELEVANCE TO DISJUNCTION"""
# N = 3
# premises = ['(A preceq B)']
# conclusions = ['((A vee B) sqsubseteq B)']
# contingent = False

# """RL3: CONJUNCTION TO RELEVANCE"""
# N = 3
# premises = ['((A wedge B) leq B)']
# conclusions = ['(A preceq B)']
# contingent = False

# """RL4: DISJUNCTION TO RELEVANCE"""
# N = 3
# premises = ['((A vee B) sqsubseteq B)']
# conclusions = ['(A preceq B)']
# contingent = False






### AXIOMS

# """RL5: CONJUNCTION INTRODUCTION"""
# N = 3
# premises = []
# conclusions = ['(A preceq (A wedge B))']
# contingent = False

# """RL6: DISJUNCTION INTRODUCTION"""
# N = 3
# premises = []
# conclusions = ['(A preceq (A vee B))']
# contingent = False




### CONSTITUTIVE INTERACTION

# """RL7: GROUNDING RELEVANCE"""
# N = 3
# premises = ['(A leq B)']
# conclusions = ['(A preceq B)']
# contingent = False

# """RL8: ESSENCE RELEVANCE"""
# N = 3
# premises = ['(A sqsubseteq B)']
# conclusions = ['(A preceq B)']
# contingent = False

# """RL9: IDENTITY RELEVANCE"""
# N = 3
# premises = ['(A equiv B)']
# conclusions = ['(A preceq B)']
# contingent = False
