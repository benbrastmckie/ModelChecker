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

# # CF_CM2: MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
# N = 3
# premises = ['(A circleright C)']
# conclusions = ['((A wedge B) circleright C)']
# contingent = True

# # CF_CM3: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# N = 3
# premises = ['(A boxright C)', 'Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']
# contingent = True

# # CF_CM4: COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 242 seconds on the MIT server; now .1928 seconds locally
# N = 4
# premises = ['neg A','(A boxright C)']
# conclusions = ['((A wedge B) boxright C)']
# contingent = True

# # CF_CM5: COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# # NOTE: with Z3 quantifiers ran for 347 seconds on the MIT server; now .1949 seconds locally
# N = 4
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A wedge B) boxright C)']
# contingent = True

# # CF_CM6: COUNTERFACTUAL CONTRAPOSITION
# N = 3
# premises = ['(A boxright B)']
# conclusions = ['(neg B boxright neg A)']
# contingent = True

# # CF_CM7: COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 125 seconds on the MIT server; now .181 seconds locally
# N = 4
# premises = ['neg B','(A boxright B)']
# conclusions = ['(neg B boxright neg A)']
# contingent = True

# # CF_CM8: COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
# premises = ['neg A','neg B','(A boxright B)']
# conclusions = ['(neg B boxright neg A)']
# contingent = True

# # CF_CM9: TRANSITIVITY
# N = 3
# premises = ['(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']
# contingent = True

# # CF_CM10: COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# # NOTE: with Z3 quantifiers 78 seconds on the MIT server; now .1311 seconds locally
# N = 4
# premises = ['neg A','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']
# contingent = True

# # CF_CM11: COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
# premises = ['neg A','neg B','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']
# contingent = True

# # CF_CM12: SOBEL SEQUENCE (N = 3)
# N = 3
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
# contingent = True

# # CF_CM13: SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
# N = 4
# premises = [
#     'Diamond A',
#     '(A boxright X)',
#     'Diamond (A wedge B)',
#     'neg ((A wedge B) boxright X)', # N = 4: 155.4 seconds on the MIT servers; now .1587 seconds
#     'Diamond ((A wedge B) wedge C)',
#     '(((A wedge B) wedge C) boxright X)',
#     'Diamond (((A wedge B) wedge C) wedge D)', # requires N > 3 to avoid FALSE PREMISE
#     # 'neg ((((A wedge B) wedge C) wedge D) boxright X)', # FALSE PREMISE MODELS BEGIN HERE
#     # 'Diamond ((((A wedge B) wedge C) wedge D) wedge E)',
#     # '(((((A wedge B) wedge C) wedge D) wedge E) boxright X)', # ? seconds
#     # 'Diamond (((((A wedge B) wedge C) wedge D) wedge E) wedge F)',
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) boxright X)', # ? seconds
#     # 'Diamond ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G)',
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) boxright X)', # ? seconds
# ]
# conclusions = []
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

# # CF_CM16: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# # NOTE: with Z3 quantifiers for 40 seconds locally; now .2785 seconds locally
# N = 4
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A vee B) boxright C)']
# contingent = True

# # CF_CM17: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A boxright B)']
# contingent = True

# # CF_CM18: COUNTERFACTUAL EXPORTATION
# N = 3
# premises = ['((A wedge B) boxright C)']
# conclusions = ['(A boxright (B boxright C))']
# contingent = True

# # CF_CM19: COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# N = 3
# premises = ['((A wedge B) boxright C)','Diamond (A wedge B)']
# conclusions = ['(A boxright (B boxright C))']
# contingent = True

# # CF_CM20
# N = 3
# premises = ['\\neg A','\\neg (A \\boxright B)']
# conclusions = ['(A \\boxright \\neg B)']
# contingent = True





### VALID ###

# # CF1: COUNTERFACTUAL IDENTITY
# N = 3
# premises = []
# conclusions = ['(A boxright A)']
# contingent = False

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

# # CF4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
# premises = ['((A \\vee B) \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']
# contingent = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A vee B) boxright C)']
# conclusions = ['(A boxright C)']
# contingent = False

# # CF6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A vee B) boxright C)']
# conclusions = ['((A boxright C) wedge (B boxright C))']
# contingent = False

# # CF7:
# N = 3
# premises = ['(A boxright C)', '(B boxright C)', '((A wedge B) boxright C)']
# conclusions = ['((A vee B) boxright C)']
# contingent = False

# # CF8:
# N = 3
# premises = ['(A boxright (B wedge C))']
# conclusions = ['(A boxright B)']
# contingent = False

# # CF9:
# N = 3
# premises = ['(A boxright B)','(A boxright C)']
# conclusions = ['(A boxright (B wedge C))']
# contingent = False

# # CF10: FACTIVITY MIGHT
# N = 3
# premises = ['A','B']
# conclusions = ['(A circleright B)']
# contingent = False
