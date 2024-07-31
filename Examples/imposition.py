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
print_impossible_states_bool = True

# present option to append output to file
save_bool = False



####################################
##### IMPOSITION COUNTERMODELS #####
####################################

# # CF_CM1: IMPOSITION ANTECEDENT STRENGTHENING
# N = 3
# premises = ['(A imposition C)']
# conclusions = ['((A wedge B) imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM2: IMPOSITION ANTECEDENT STRENGTHENING WITH POSSIBILITY
# N = 3
# premises = ['(A imposition C)', 'Diamond (A wedge B)']
# conclusions = ['((A wedge B) imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM3: IMPOSITION ANTECEDENT STRENGTHENING WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 242 seconds on the MIT server; now .1928 seconds locally
# N = 4
# premises = ['neg A','(A imposition C)']
# conclusions = ['((A wedge B) imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM4: IMPOSITION DOUBLE ANTECEDENT STRENGTHENING
# # NOTE: with Z3 quantifiers ran for 347 seconds on the MIT server; now .1949 seconds locally
# N = 4
# premises = ['(A imposition C)','(B imposition C)']
# conclusions = ['((A wedge B) imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM5: IMPOSITION CONTRAPOSITION
# N = 3
# premises = ['(A imposition B)']
# conclusions = ['(neg B imposition neg A)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM6: IMPOSITION CONTRAPOSITION WITH NEGATION
# # NOTE: with Z3 quantifiers ran for 125 seconds on the MIT server; now .181 seconds locally
# N = 4
# premises = ['neg B','(A imposition B)']
# conclusions = ['(neg B imposition neg A)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM7: IMPOSITION CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
# premises = ['neg A','neg B','(A imposition B)']
# conclusions = ['(neg B imposition neg A)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM8: TRANSITIVITY
# N = 3
# premises = ['(A imposition B)','(B imposition C)']
# conclusions = ['(A imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM9: IMPOSITION TRANSITIVITY WITH NEGATION
# # NOTE: with Z3 quantifiers 78 seconds on the MIT server; now .1311 seconds locally
# N = 4
# premises = ['neg A','(A imposition B)','(B imposition C)']
# conclusions = ['(A imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM10: IMPOSITION TRANSITIVITY WITH TWO NEGATIONS
# N = 4
# premises = ['neg A','neg B','(A imposition B)','(B imposition C)']
# conclusions = ['(A imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM11: SOBEL SEQUENCE (N = 3)
# N = 1
# premises = [
#     '(A imposition X)', # 0.03 seconds locally
#     'neg ((A wedge B) imposition X)', # 1.4 seconds locally
#     '(((A wedge B) wedge C) imposition X)', # 4.9 seconds locally
#     # 'neg ((((A wedge B) wedge C) wedge D) imposition X)', # FALSE PREMISE MODELS BEGIN HERE
#     # '(((((A wedge B) wedge C) wedge D) wedge E) imposition X)', # 20.5 seconds locally
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) imposition X)', # 64 seconds on the MIT servers
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) imposition X)', # 327.2 seconds on the MIT servers; now .01244 seconds
# ]
# conclusions = []
# contingent_bool = True
# disjoint_bool = False

# # CF_CM12: SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
# N = 4
# premises = [
#     'Diamond A',
#     '(A imposition X)',
#     'Diamond (A wedge B)',
#     'neg ((A wedge B) imposition X)', # N = 4: 155.4 seconds on the MIT servers; now .1587 seconds
#     'Diamond ((A wedge B) wedge C)',
#     '(((A wedge B) wedge C) imposition X)',
#     'Diamond (((A wedge B) wedge C) wedge D)', # requires N > 3 to avoid FALSE PREMISE
#     # 'neg ((((A wedge B) wedge C) wedge D) imposition X)', # FALSE PREMISE MODELS BEGIN HERE
#     # 'Diamond ((((A wedge B) wedge C) wedge D) wedge E)',
#     # '(((((A wedge B) wedge C) wedge D) wedge E) imposition X)', # ? seconds
#     # 'Diamond (((((A wedge B) wedge C) wedge D) wedge E) wedge F)',
#     # 'neg ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) imposition X)', # ? seconds
#     # 'Diamond ((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G)',
#     # '(((((((A wedge B) wedge C) wedge D) wedge E) wedge F) wedge G) imposition X)', # ? seconds
# ]
# conclusions = []
# contingent_bool = True
# disjoint_bool = False

# # CF_CM13: IMPOSITION EXCLUDED MIDDLE
# N = 3
# premises = ['neg A']
# conclusions = ['(A imposition B)','(A imposition neg B)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM14: SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# N = 3
# premises = ['neg A','(A imposition (B vee C))']
# conclusions = ['(A imposition B)','(A imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM15: INTRODUCTION OF DISJUNCTIVE ANTECEDENT
# # NOTE: with Z3 quantifiers for 40 seconds locally; now .2785 seconds locally
# N = 4
# premises = ['(A imposition C)','(B imposition C)']
# conclusions = ['((A vee B) imposition C)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM16: MUST FACTIVITY
# N = 3
# premises = ['A','B']
# conclusions = ['(A imposition B)']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM17: IMPOSITION EXPORTATION
# N = 3
# premises = ['((A wedge B) imposition C)']
# conclusions = ['(A imposition (B imposition C))']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM18: IMPOSITION EXPORTATION WITH POSSIBILITY
# N = 3
# premises = ['((A wedge B) imposition C)','Diamond (A wedge B)']
# conclusions = ['(A imposition (B imposition C))']
# contingent_bool = True
# disjoint_bool = False

# # CF_CM19
# N = 3
# premises = ['\\neg A','\\neg (A \\imposition B)']
# conclusions = ['(A \\imposition \\neg B)']
# contingent_bool = True
# disjoint_bool = False





### VALID ###

# # CF1: IMPOSITION IDENTITY
# N = 3
# premises = []
# conclusions = ['(A imposition A)']
# contingent_bool = True
# disjoint_bool = False

# # CF2: IMPOSITION MODUS PONENS
# N = 3
# premises = ['A','(A imposition B)']
# conclusions = ['B']
# contingent_bool = True
# disjoint_bool = False

# # CF3: WEAKENED TRANSITIVITY
# N = 3
# premises = ['(A imposition B)','((A wedge B) imposition C)']
# conclusions = ['(A imposition C)']
# contingent_bool = False
# disjoint_bool = False

# # CF4: ANTECEDENT DISJUNCTION TO CONJUNCTION
# N = 3
# premises = ['((A \\vee B) \\imposition C)']
# conclusions = ['((A \\wedge B) \\imposition C)']
# contingent_bool = False
# disjoint_bool = False

# # CF5: SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 4
# premises = ['((A vee B) imposition C)']
# conclusions = ['(A imposition C)']
# contingent_bool = False
# disjoint_bool = False

# # CF6: DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
# N = 3
# premises = ['((A vee B) imposition C)']
# conclusions = ['((A imposition C) wedge (B imposition C))']
# contingent_bool = False
# disjoint_bool = False

# # CF7:
# N = 3
# premises = ['(A imposition C)', '(B imposition C)', '((A wedge B) imposition C)']
# conclusions = ['((A vee B) imposition C)']
# contingent_bool = False
# disjoint_bool = False

# # CF8:
# N = 3
# premises = ['(A imposition (B wedge C))']
# conclusions = ['(A imposition B)']
# contingent_bool = False
# disjoint_bool = False

# # NOTE: optimizer works for max_time = 1 but not max_time > 1
# # CF9:
# N = 3
# premises = ['(A imposition B)','(A imposition C)']
# conclusions = ['(A imposition (B wedge C))']
# contingent_bool = False
# disjoint_bool = False
